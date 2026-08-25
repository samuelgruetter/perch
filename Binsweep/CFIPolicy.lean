import Kraken.X64.Syntax

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

def get_acceptable_instr (g : Graph) (idx : InstrId)
    (check : Instr → List InstrId → Bool) : Bool :=
  match g[idx]? with
  | .some (InstrNode.mk instr predecessors) =>
      acceptable_instr instr && check instr predecessors
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

/-- The base registers written by `instr`, used to check whether an
instruction can be skipped while walking the graph backwards because it is
known not to disturb the register(s) currently being tracked. -/
def written_regs (instr : Instr) : List Reg64 :=
  match instr with
  | .avx .. => []
  | .regular _ _ op =>
    match op with
    | .mov dst _ | .add dst _ | .adc dst _ | .sub dst _ | .sbb dst _
    | .and dst _ | .or dst _ | .xor dst _ | .not dst
    | .shl dst _ | .shr dst _ | .sar dst _
    | .rol dst _ | .ror dst _ | .rcl dst _ | .rcr dst _
    | .shld dst _ _ | .shrd dst _ _
    | .inc dst | .dec dst | .neg dst | .pop dst
    | .movsx dst _ | .movzx dst _ =>
        match dst with | .reg r => [reg_base r] | .mem _ => []
    | .setcc _ dst =>
        match dst with | .reg r => [reg_base r] | .mem _ => []
    | .imul dst _ _ =>
        match dst with | some (.reg r) => [reg_base r] | _ => []
    | .lea r _ | .cmovcc _ r _ | .bswap r | .adcx r _ | .adox r _ =>
        [reg_base r]
    | .mulx hi lo _ => [reg_base hi, reg_base lo]
    | .push _ | .test _ _ | .cmp _ _ | .mul _ | .imul1 _
    | .jcc _ _ | .jmp _ | .call _ | .ret | .nop _ | .nopalign _ _ => []

/-- Whether `instr` may modify the x86 condition flags (carry, zero, sign,
overflow, ...). Used to check that nothing clobbers the flags between the
`add` that computes a check value and the `jcc` that tests it. -/
def modifies_flags (instr : Instr) : Bool :=
  match instr with
  | .avx .. => false
  | .regular _ _ op =>
    match op with
    | .add _ _ | .adc _ _ | .adcx _ _ | .adox _ _
    | .inc _ | .dec _ | .neg _ | .sub _ _ | .sbb _ _ | .cmp _ _
    | .mul _ | .mulx .. | .imul1 _ | .imul ..
    | .test _ _ | .and _ _ | .or _ _ | .xor _ _
    | .shl _ _ | .shr _ _ | .sar _ _ | .rol _ _ | .ror _ _ | .rcl _ _ | .rcr _ _
    | .shld _ _ _ | .shrd _ _ _ => true
    | .mov _ _ | .movsx _ _ | .movzx _ _ | .push _ | .pop _
    | .setcc _ _ | .cmovcc _ _ _ | .lea _ _ | .not _ | .bswap _
    | .jcc _ _ | .jmp _ | .call _ | .ret | .nop _ | .nopalign _ _ => false

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
def find_target_read (g : Graph) (idx : InstrId)
    (target : Reg .W64) (check_register : Reg .W32) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    get_acceptable_instr g idx fun instr predecessors =>
      match instr with
      | .regular _ .W32 (.mov (.reg cr) (.regOrMem (.mem addr))) =>
          cr == check_register &&
          (addr == deref_addr (reg_base target) ||
           neForall (fun j => find_target_origin g j target addr) predecessors)
      | _ =>
          let written := written_regs instr
          !(written.contains (reg_base target) || written.contains (reg_base check_register)) &&
          neForall (fun j => find_target_read g j target check_register fuel') predecessors

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
def find_add (g : Graph) (idx : InstrId) (target : Reg .W64) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    get_acceptable_instr g idx fun instr predecessors =>
      match is_magic_add target instr with
      | some check_register =>
          neForall (fun j => find_target_read g j target check_register fuel') predecessors
      | none =>
        match copies_into target instr with
        | some src => neForall (fun j => find_add g j src fuel') predecessors
        | none =>
            !((written_regs instr).contains (reg_base target) || modifies_flags instr) &&
            neForall (fun j => find_add g j target fuel') predecessors

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
def find_branch (g : Graph) (idx : InstrId) (target : Reg .W64) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    get_acceptable_instr g idx fun instr predecessors =>
      if is_cfi_check_jcc instr then
        neForall (fun j => find_add g j target fuel') predecessors
      else
        match copies_into target instr with
        | some src => neForall (fun j => find_branch g j src fuel') predecessors
        | none =>
            !((written_regs instr).contains (reg_base target)) &&
            neForall (fun j => find_branch g j target fuel') predecessors

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
        neForall (fun j => find_branch g j target cfi_check_fuel) predecessors
    | _ => false
