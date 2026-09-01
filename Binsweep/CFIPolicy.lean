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

def acceptable_instr (instr : Instr) : Bool :=
  -- TODO (later) check that the instruction uses no forbidden prefix or segment override
  -- TODO (later) explore allow-list-based as well as deny-list-based solutions
  match instr with
  | .regular _ _ op =>
    match op with
    -- The RET instruction is not allowed because it would enable return-oriented-programming
    -- attacks. Instead, we expect that the compiler replaced all RETs by forward jumps.
    | .ret => false
    | _ => true
  | .avx _ _ _ => true

-- TODO (later) in general, what register widths are used/acceptable?

structure cfi_checker_context where
  -- The 64-bit register containing the indirect branch destination.
  -- When the matcher crosses `MOV target, source` while walking backward,
  -- `source` becomes the tracked target register.
  target : Reg .W64
  -- The 32-bit register to which `MAGIC` is added. Walking farther backward,
  -- the matcher requires this same register to receive the word loaded from
  -- the target address.
  check_register : Reg .W32
  -- The complete memory address used by a target read that is not
  -- simply `[target]`. The matcher uses it to find an earlier `LEA` or
  -- `MOV` proving that this address equals the branch target.
  target_read_address : AddrExpr

/-- A `cfi_checker_context` to use where its fields haven't been
determined yet -- e.g. `cfi_check` doesn't know the branch target until
it has looked at the instruction at `idx`, and `check_register`/
`target_read_address` aren't known until `find_add`/`find_target_read`
find the check/address that determine them. Its field values are never
read before being replaced with real ones, so what they are doesn't
matter. -/
def cfi_checker_context.empty : cfi_checker_context :=
  { target := .rax,
    check_register := .eax,
    target_read_address := { base := none, idx := none } }

/-- Looks up `idx` in `g`, checks it is acceptable, and runs `check` on
the instruction found there and its predecessors, with one less unit of
fuel. `check` is handed the decreased fuel, `rec` -- the same check, but
with that decreased fuel, to call at every recursive step of a backward
walk over `g` (typically at a different `idx` and, via `ctx`, possibly a
different tracked register too; see `find_add`/`find_branch` below) --
and `ctx` itself. A walk that needs to call into a *different* one of
these checks partway through, with whatever fuel it has left, does that
with the plain decreased fuel value instead of `rec` (see `find_add`
calling `find_target_read`): `rec`'s recursive calls are exactly what
must stay nameless for termination to hold, since `cfi_checking_stage`'s
own recursive call, hidden inside `rec`, is otherwise invisible to the
termination checker. Returns `false` once fuel runs out, `idx` is
missing from `g`, or the instruction there isn't acceptable. -/
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

/-- Checks whether, at instruction `idx`, register `ctx.target` is set up
so that dereferencing it yields the same value as `ctx.target_read_address`.
This holds when `ctx.target` is loaded directly from that address
(`lea target, addr`), or when the register underlying it was itself
round-tripped through `[target]` (loaded from `[target]`, or stored into
`[target]`). x86 has no memory-to-memory `mov`, so the latter two cases
are the closest faithful encoding of "the value at `addr` was copied
from/to `[target]`". -/
def find_target_origin (fuel : Nat) (g : Graph) (ctx : cfi_checker_context) (idx : InstrId) : Bool :=
  cfi_checking_stage fuel g idx ctx fun _fuel' _rec ctx instr _predecessors =>
    match instr with
    | .regular _ .W64 (.lea t src) =>
        t == ctx.target && src == ctx.target_read_address
    | .regular _ .W32 (.mov (.reg r) (.regOrMem (.mem src))) =>
        src == deref_addr (reg_base ctx.target) &&
          ctx.target_read_address.base == some (.reg (reg_base r))
    | .regular _ .W32 (.mov (.mem dst) (.regOrMem (.reg r))) =>
        dst == deref_addr (reg_base ctx.target) &&
          ctx.target_read_address.base == some (.reg (reg_base r))
    | _ => false

/-- Checks whether, walking backwards from instruction `idx`,
`ctx.check_register` is guaranteed to hold the 32-bit value read from
`[ctx.target]`, possibly after being routed through another register or
memory location whose provenance traces back to `[ctx.target]` (see
`find_target_origin`). Instructions that touch neither register are
skipped over.

`fuel` bounds how many instructions this walk may inspect, so that a cyclic
control-flow graph cannot make the check loop forever; see `cfi_check`. -/
def find_target_read (fuel : Nat) (g : Graph) (ctx : cfi_checker_context) (idx : InstrId) : Bool :=
  cfi_checking_stage fuel g idx ctx fun fuel' rec ctx instr predecessors =>
    match instr with
    | .regular _ .W32 (.mov (.reg cr) (.regOrMem (.mem addr))) =>
        cr == ctx.check_register &&
        (addr == deref_addr (reg_base ctx.target) ||
         neForall (fun j => find_target_origin fuel' g { ctx with target_read_address := addr } j)
           predecessors)
    | _ =>
        let written := written_regs instr
        !(written.contains (reg_base ctx.target) || written.contains (reg_base ctx.check_register)) &&
        neForall (fun j => rec j ctx) predecessors

/-- If `instr` is `add check_register, MAGIC` where `check_register` is the
32-bit alias of `target`, returns `check_register`. -/
def is_magic_add (target : Reg .W64) (instr : Instr) : Option (Reg .W32) :=
  match instr with
  | .regular _ .W32 (.add (.reg check_register) (.imm (.int64 imm))) =>
      if reg_base check_register == reg_base target && imm == Int64.ofInt (MAGIC.toNat : Int)
      then some check_register else none
  | _ => none

/-- Checks whether, walking backwards from instruction `idx`, register
`ctx.target` (or a register copied into it) is validated by adding `MAGIC`
to the 32-bit value read from `[ctx.target]`, per `find_target_read`.
Instructions that touch neither `ctx.target` nor the flags are skipped
over, since the flags set by the `add` must survive unclobbered until the
`jcc` that consumes them (see `find_branch`). -/
def find_add (fuel : Nat) (g : Graph) (ctx : cfi_checker_context) (idx : InstrId) : Bool :=
  cfi_checking_stage fuel g idx ctx fun fuel' rec ctx instr predecessors =>
    match is_magic_add ctx.target instr with
    | some check_register =>
        neForall (fun j => find_target_read fuel' g { ctx with check_register } j) predecessors
    | none =>
      match copies_into ctx.target instr with
      | some src => neForall (fun j => rec j { ctx with target := src }) predecessors
      | none =>
          !((written_regs instr).contains (reg_base ctx.target) || modifies_flags instr) &&
          neForall (fun j => rec j ctx) predecessors

/-- Whether `instr` is the conditional jump that is meant to trap when the
`MAGIC`-based check (see `find_add`/`find_target_read`) fails. -/
def is_cfi_check_jcc (instr : Instr) : Bool :=
  match instr with
  | .regular _ _ (.jcc cc _) => cc == .z || cc == .nz
  | _ => false

/-- Checks whether, walking backwards from instruction `idx`, register
`ctx.target` (or a register copied into it) is validated by `find_add`
before reaching the `jz`/`jnz` that acts on the check. Instructions that
don't touch `ctx.target` are skipped over. -/
-- TODO (later) also confirm that the failure path of that `jz`/`jnz` actually
-- traps (e.g. reaches an `int3`/`ud2`). This isn't checked yet: `Graph`/
-- `InstrNode` only record predecessor edges, not the successors or labels
-- needed to follow the failure path, and Kraken's `Operation` type has no
-- trap instruction to look for in the first place.
def find_branch (fuel : Nat) (g : Graph) (ctx : cfi_checker_context) (idx : InstrId) : Bool :=
  cfi_checking_stage fuel g idx ctx fun fuel' rec ctx instr predecessors =>
    if is_cfi_check_jcc instr then
      neForall (fun j => find_add fuel' g ctx j) predecessors
    else
      match copies_into ctx.target instr with
      | some src => neForall (fun j => rec j { ctx with target := src }) predecessors
      | none =>
          !((written_regs instr).contains (reg_base ctx.target)) &&
          neForall (fun j => rec j ctx) predecessors

-- Binsweep enforces a hard cutoff of 48 instructions per backward walk, to
-- guarantee termination even when the control-flow graph contains cycles.
def cfi_check_fuel : Nat := 48

/-- The top-level CFI check: an indirect `call`/`jmp` through a 64-bit
register `target` is accepted only if every path leading to it passes
through a validated `find_branch` check on `target`. -/
def cfi_check (g : Graph) (idx : InstrId) : Bool :=
  cfi_checking_stage cfi_check_fuel g idx cfi_checker_context.empty fun fuel' _rec _ctx instr predecessors =>
    match instr with
    | .regular _ _ (.call (.reg target)) | .regular _ _ (.jmp (.reg target)) =>
        neForall (fun j => find_branch fuel' g { cfi_checker_context.empty with target } j)
          predecessors
    | _ => false
