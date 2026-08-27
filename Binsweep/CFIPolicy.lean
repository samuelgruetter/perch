import Kraken.X64.Syntax
import Binsweep.InstructionProperties

/-!
Implements the CFI policy described in sections 3.3 and 4.3 of the
Binsweep paper (https://dl.acm.org/doi/10.1145/3689938.3694778),
in functional style rather than as a state machine.
-/

def MAGIC : UInt32 := 0x05E1F00D

abbrev InstrId := Nat

structure InstrNode where
  instr : Instr
  predecessors : List InstrId

abbrev Graph := List InstrNode

def acceptable_instr (_instr : Instr) : Bool :=
  -- TODO (later) check that the instruction uses no forbidden prefix or segment override
  true

-- TODO (later) in general, what register widths are used/acceptable?

-- TODO (now) replace all usages by cfi_checking_stage
def get_acceptable_instr (g : Graph) (idx : InstrId)
    (check : Instr → List InstrId → Bool) : Bool :=
  match g[idx]? with
  | .some (InstrNode.mk instr predecessors) =>
      acceptable_instr instr && check instr predecessors
  | .none => false

structure cfi_checker_context where
  -- The 64-bit register containing the indirect branch destination.
  -- When the matcher crosses `MOV target, source` while walking backward,
  -- `source` becomes the tracked target register.
  target: Reg .W64
  -- The 32-bit register to which `MAGIC` is added. Walking farther backward,
  -- the matcher requires this same register to receive the word loaded from
  -- the target address.
  check_register: Reg .W32
   -- The complete memory address used by a target read that is not
   -- simply `[target]`. The matcher uses it to find an earlier `LEA` or
   -- `MOV` proving that this address equals the branch target.
  target_read_address: AddrExpr -- TODO (now) find_target_origin's addr argument becomes this

/-- Looks up `idx` in `g`, checks if it is acceptable, and runs `check` on
the instruction found there and its predecessors, with one less unit of
fuel. `check` is handed `rec`, the same check but with decreased fuel. -/
def cfi_checking_stage
    (fuel : Nat)
    (g : Graph)
    (idx : InstrId)
    (ctx : cfi_checker_context)
    (check : Nat → (rec : InstrId → cfi_checker_context → Bool) →
             cfi_checker_context → Instr → List InstrId → Bool)
     : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match g[idx]? with
    | .some (InstrNode.mk instr predecessors) =>
        acceptable_instr instr &&
          check fuel' (fun idx ctx => cfi_checking_stage fuel' g idx ctx check) ctx instr predecessors
    | .none => false

-- non-empty forall
def neForall {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  !xs.isEmpty && xs.all p

/-- The full 64-bit register underlying `r`; e.g. `ah`, `eax` and `rax` all
report `rax` as their base register. -/
def reg_base {w : Width} (r : Reg w) : Reg64 :=
  match r with
  | .low r64 _ => r64
  | .ah => .rax
  | .bh => .rbx
  | .ch => .rcx
  | .dh => .rdx

/-- The addressing expression `[r]`, i.e. dereferencing `r` with no
index or displacement. -/
def deref_addr (r : Reg64) : AddrExpr :=
  { base := some (.reg r), idx := none }

/-- If `instr` is `mov target, src` for some 64-bit register `src`, returns
`src`: `target`'s value then provably equals whatever `src` held just
before. Lets the search below follow register-to-register copies backwards
through the graph, so e.g. `mov rbx, rax; jmp rbx` is checked the same way
`jmp rax` would be. -/
def copies_into (target : Reg .W64) (instr : Instr) : Option (Reg .W64) :=
  match instr with
  | .regular _ .W64 (.mov (.reg dst) (.regOrMem (.reg src))) =>
      if dst == target then some src else none
  | _ => none

/-- Checks whether, at instruction `idx`, register `target` is set up so
that dereferencing it yields the same value as `addr`. This holds when
`target` is loaded directly from `addr` (`lea target, addr`), or when the
register underlying `addr` was itself round-tripped through `[target]`
(loaded from `[target]`, or stored into `[target]`). x86 has no
memory-to-memory `mov`, so the latter two cases are the closest faithful
encoding of "the value at `addr` was copied from/to `[target]`". -/
def find_target_origin (g : Graph) (idx : InstrId)
    (target : Reg .W64) (addr : AddrExpr) : Bool :=
  get_acceptable_instr g idx fun instr _predecessors =>
    match instr with
    | .regular _ .W64 (.lea t src) =>
        t == target && src == addr
    | .regular _ .W32 (.mov (.reg r) (.regOrMem (.mem src))) =>
        src == deref_addr (reg_base target) && addr.base == some (.reg (reg_base r))
    | .regular _ .W32 (.mov (.mem dst) (.regOrMem (.reg r))) =>
        dst == deref_addr (reg_base target) && addr.base == some (.reg (reg_base r))
    | _ => false

/-- Checks whether, walking backwards from instruction `idx`, `check_register`
is guaranteed to hold the 32-bit value read from `[target]`, possibly after
being routed through another register or memory location whose provenance
traces back to `[target]` (see `find_target_origin`). Instructions that
touch neither `target` nor `check_register` are skipped over.

`fuel` bounds how many instructions this walk may inspect, so that a cyclic
control-flow graph cannot make the check loop forever; see `cfi_check`. -/
def find_target_read (fuel : Nat) (g : Graph)
    (target : Reg .W64) (check_register : Reg .W32) (idx : InstrId) : Bool :=
  cfi_checking_stage fuel g (fun _fuel' rec instr predecessors (_ : Unit) =>
      match instr with
      | .regular _ .W32 (.mov (.reg cr) (.regOrMem (.mem addr))) =>
          cr == check_register &&
          (addr == deref_addr (reg_base target) ||
           neForall (fun j => find_target_origin g j target addr) predecessors)
      | _ =>
          let written := written_regs instr
          !(written.contains (reg_base target) || written.contains (reg_base check_register)) &&
          neForall (fun j => rec j ()) predecessors)
    idx ()

/-- If `instr` is `add check_register, MAGIC` where `check_register` is the
32-bit alias of `target`, returns `check_register`. -/
def is_magic_add (target : Reg .W64) (instr : Instr) : Option (Reg .W32) :=
  match instr with
  | .regular _ .W32 (.add (.reg check_register) (.imm (.int64 imm))) =>
      if reg_base check_register == reg_base target && imm == Int64.ofInt (MAGIC.toNat : Int)
      then some check_register else none
  | _ => none

/-- Checks whether, walking backwards from instruction `idx`, register
`target` (or a register copied into it) is validated by adding `MAGIC` to
the 32-bit value read from `[target]`, per `find_target_read`.
Instructions that touch neither `target` nor the flags are skipped over,
since the flags set by the `add` must survive unclobbered until the `jcc`
that consumes them (see `find_branch`). -/
def find_add (fuel : Nat) (g : Graph) (target : Reg .W64) (idx : InstrId) : Bool :=
  cfi_checking_stage fuel g (fun fuel' rec instr predecessors target =>
      match is_magic_add target instr with
      | some check_register =>
          neForall (fun j => find_target_read fuel' g target check_register j) predecessors
      | none =>
        match copies_into target instr with
        | some src => neForall (fun j => rec j src) predecessors
        | none =>
            !((written_regs instr).contains (reg_base target) || modifies_flags instr) &&
            neForall (fun j => rec j target) predecessors)
    idx target

/-- Whether `instr` is the conditional jump that is meant to trap when the
`MAGIC`-based check (see `find_add`/`find_target_read`) fails. -/
def is_cfi_check_jcc (instr : Instr) : Bool :=
  match instr with
  | .regular _ _ (.jcc cc _) => cc == .z || cc == .nz
  | _ => false

/-- Checks whether, walking backwards from instruction `idx`, register
`target` (or a register copied into it) is validated by `find_add` before
reaching the `jz`/`jnz` that acts on the check. Instructions that don't
touch `target` are skipped over. -/
-- TODO (later) also confirm that the failure path of that `jz`/`jnz` actually
-- traps (e.g. reaches an `int3`/`ud2`). This isn't checked yet: `Graph`/
-- `InstrNode` only record predecessor edges, not the successors or labels
-- needed to follow the failure path, and Kraken's `Operation` type has no
-- trap instruction to look for in the first place.
def find_branch (fuel : Nat) (g : Graph) (target : Reg .W64) (idx : InstrId) : Bool :=
  cfi_checking_stage fuel g (fun fuel' rec instr predecessors target =>
      if is_cfi_check_jcc instr then
        neForall (fun j => find_add fuel' g target j) predecessors
      else
        match copies_into target instr with
        | some src => neForall (fun j => rec j src) predecessors
        | none =>
            !((written_regs instr).contains (reg_base target)) &&
            neForall (fun j => rec j target) predecessors)
    idx target

-- Binsweep enforces a hard cutoff of 48 instructions per backward walk, to
-- guarantee termination even when the control-flow graph contains cycles.
def cfi_check_fuel : Nat := 48

/-- The top-level CFI check: an indirect `call`/`jmp` through a 64-bit
register `target` is accepted only if every path leading to it passes
through a validated `find_branch` check on `target`. -/
def cfi_check (g : Graph) (idx : InstrId) : Bool :=
  get_acceptable_instr g idx fun instr predecessors =>
    match instr with
    | .regular _ _ (.call (.reg target)) | .regular _ _ (.jmp (.reg target)) =>
        neForall (fun j => find_branch cfi_check_fuel g target j) predecessors
    | _ => false
