import Kraken.X64.Semantics
import Binsweep.InterpEffects

/-!
Syntactic over-approximations of what an instruction can touch, together
with proofs that they are sound with respect to Kraken's X64 semantics
(`Operation.interp`/`Instr.interp` in `Kraken.X64.Semantics`).

These are used by `Binsweep.CFIPolicy` to skip instructions while walking a
control-flow graph backwards, so soundness here means: an instruction that
is *not* reported can be skipped without missing a way for it to disturb
the register/flags being tracked.
-/

/-- The base registers written by `instr`, identified by their full 64-bit
register (e.g. writing `eax` is reported as writing `rax`), used to check
whether an instruction can be skipped while walking a graph backwards
because it is known not to disturb the register(s) currently being
tracked. This is a sound over-approximation: it may list a register that
turns out not to change (e.g. `cmovcc` when its condition is false, or a
shift by zero), but never omits one that can. -/
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
    | .inc dst | .dec dst | .neg dst
    | .movsx dst _ | .movzx dst _ =>
        match dst with | .reg r => [r.base] | .mem _ => []
    | .setcc _ dst =>
        match dst with | .reg r => [r.base] | .mem _ => []
    | .imul (some dst) _ _ =>
        match dst with | .reg r => [r.base] | .mem _ => []
    | .imul none src1 _ =>
        match src1 with | .reg r => [r.base] | .mem _ => []
    | .lea r _ | .cmovcc _ r _ | .bswap r | .adcx r _ | .adox r _ =>
        [r.base]
    | .mulx hi lo _ => [hi.base, lo.base]
    -- `mul`/`imul1` always write `rax`, and write `rdx` too unless the
    -- operand width is 8 bits (in which case the full result fits in `ax`).
    | .mul _ | .imul1 _ => [.rax, .rdx]
    | .pop dst =>
        .rsp :: match dst with | .reg r => [r.base] | .mem _ => []
    -- `push`/`call`/`ret` all adjust the stack pointer.
    | .push _ | .call _ | .ret => [.rsp]
    | .test _ _ | .cmp _ _ | .jcc _ _ | .jmp _ | .nop _ | .nopalign _ _ => []

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

/-!
### Soundness

`Operation.interp`/`Instr.interp` describe an instruction's effect in
continuation-passing style: running one produces an `Effects` tree whose
leaves either report a genuine failure (`unimplemented`, `gp_unaligned`,
an access outside `dmem`), ask the caller to resolve some choice
(`undefined`, an access permission) before continuing, or hand a final
`MachineState` to the instruction's `next`/`jmp` continuation.

We phrase soundness in terms of `Binsweep.InterpEffects`'s
`Effects.Exists e final`, which holds when *some* way of resolving `e`'s
choices reaches `final`. Think of `Effects.Exists e final` like a small-step
`-->* final` judgement, with `e` playing the role of "the current
configuration" -- it already has the starting `MachineData` baked in (from
whoever called `.interp`), so unlike a textbook `-->*` it doesn't take an
initial state as a separate argument. Each lemma below states directly what
relation between the reached `final` and the inputs it's proving, rather
than going through a generic postcondition parameter.

TODO (now): this is a work in progress switching from an earlier
`Effects.PreservesOutside` (a direct, universally-quantified "every
resolution reaches a state satisfying `post`" predicate) to the above
`Effects.Exists`-based phrasing throughout. Only the theorem *statements*
below have been adapted so far; every proof is a placeholder `sorry`
(the old, actually-checked proofs are kept as comments immediately above
their replacement, for reference while the new ones are being written). -/

/-- No register write outside `r64` can change `Reg64s.get64 r64`. -/
theorem Reg64s.get64_set64_of_ne {regs : Reg64s} {r r' : Reg64} (h : r' ≠ r) (v : UInt64) :
    (regs.set64 r v).get64 r' = regs.get64 r' := by
  cases r <;> cases r' <;> simp_all [Reg64s.set64, Reg64s.get64]

/-- Writing register `rd` (of any width) can only change `Reg64s.get64` at
`rd`'s base register: `Reg64s.set` always routes through `Reg64s.set64` on
`rd.base`. -/
theorem Reg64s.get64_set_of_ne {w : Width} {regs : Reg64s} (rd : Reg w) (v : w.type) {r : Reg64}
    (h : r ≠ rd.base) : (regs.set rd v).get64 r = regs.get64 r := by
  cases rd with
  | low r64 _ =>
      simp only [Reg.base] at h
      cases w <;> simp only [Reg64s.set] <;> exact Reg64s.get64_set64_of_ne h _
  | ah => exact Reg64s.get64_set64_of_ne h _
  | bh => exact Reg64s.get64_set64_of_ne h _
  | ch => exact Reg64s.get64_set64_of_ne h _
  | dh => exact Reg64s.get64_set64_of_ne h _

/-- `MachineData.setReg` only ever changes registers, and only at the
written register's base. -/
theorem MachineData.setReg_get64_of_ne {w : Width} (s : MachineData) (rd : Reg w) (v : w.type)
    {r : Reg64} (h : r ≠ rd.base) : (s.setReg rd v).regs.get64 r = s.regs.get64 r :=
  Reg64s.get64_set_of_ne rd v h

theorem MachineData.setReg_status (s : MachineData) {w : Width} (rd : Reg w) (v : w.type) :
    (s.setReg rd v).status = s.status := rfl

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- Loading from memory hands its continuation a state whose `regs`/`status`
are unchanged (only `dmem` may differ, if the address is outside the
modeled memory). -/
theorem MachineData.load_preservesOutside {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (ret : w.type → MachineData → Effects)
    (post : MachineData → Prop)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      Effects.PreservesOutside post (ret a s')) :
    Effects.PreservesOutside post (MachineData.load s addr w ret) := by
  simp only [MachineData.load, Effects.PreservesOutside]
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | some i => exact h _ s rfl rfl
  | none => exact fun v dmem => h v { s with dmem } rfl rfl
-/

/-- Loading from memory hands its continuation a state whose `regs`/`status`
are unchanged (only `dmem` may differ, if the address is outside the
modeled memory). -/
theorem MachineData.load_reaches {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.load s addr w ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- Storing to memory hands its continuation a state whose `regs`/`status`
are unchanged (only `dmem` differs). -/
theorem MachineData.store_preservesOutside {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (v : w.type) (ret : MachineData → Effects)
    (post : MachineData → Prop)
    (h : ∀ s', s'.regs = s.regs → s'.status = s.status → Effects.PreservesOutside post (ret s')) :
    Effects.PreservesOutside post (s.store addr v ret) := by
  simp only [MachineData.store, Effects.PreservesOutside]
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | some _ => exact h _ rfl rfl
  | none => exact fun dmem => h { s with dmem } rfl rfl
-/

/-- Storing to memory hands its continuation a state whose `regs`/`status`
are unchanged (only `dmem` differs). -/
theorem MachineData.store_reaches {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (v : w.type) (ret : MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (s.store addr v ret) final) :
    ∃ s', s'.regs = s.regs ∧ s'.status = s.status ∧ Effects.Exists (ret s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- Reading a `RegOrMem` operand hands its continuation a state whose
`regs`/`status` are unchanged (only `dmem` may differ, if the read went to
an address outside the modeled memory). -/
theorem RegOrMem.interp_preservesOutside {w : Width} [Labels] [AddressSize]
    (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      Effects.PreservesOutside post (ret a s')) :
    Effects.PreservesOutside post (o.interp s p ret) := by
  cases o with
  | reg r => exact h _ s rfl rfl
  | mem a =>
      simp only [RegOrMem.interp]
      exact MachineData.load_preservesOutside s _ ret post h
-/

/-- Reading a `RegOrMem` operand hands its continuation a state whose
`regs`/`status` are unchanged (only `dmem` may differ, if the read went to
an address outside the modeled memory). -/
theorem RegOrMem.interp_reaches {w : Width} [Labels] [AddressSize]
    (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- Reading an `Operand` hands its continuation a state whose
`regs`/`status` are unchanged. -/
theorem Operand.interp_preservesOutside {w : Width} [Labels] [AddressSize]
    (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      Effects.PreservesOutside post (ret a s')) :
    Effects.PreservesOutside post (o.interp s p ret) := by
  cases o with
  | regOrMem rm => exact RegOrMem.interp_preservesOutside rm s p ret post h
  | imm v => exact h _ s rfl rfl
-/

/-- Reading an `Operand` hands its continuation a state whose
`regs`/`status` are unchanged. -/
theorem Operand.interp_reaches {w : Width} [Labels] [AddressSize]
    (o : Operand w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- Reading a plain `Reg` (as opposed to a `RegOrMem`/`Operand`) never
touches memory, so it hands its continuation back the very same state. -/
theorem Reg.interp_preservesOutside {w : Width} (reg : Reg w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      Effects.PreservesOutside post (ret a s')) :
    Effects.PreservesOutside post (reg.interp s p ret) := by
  simp only [Reg.interp]; exact h _ s rfl rfl
-/

/-- Reading a plain `Reg` (as opposed to a `RegOrMem`/`Operand`) never
touches memory, so it hands its continuation back the very same state. -/
theorem Reg.interp_reaches {w : Width} (reg : Reg w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (reg.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- Reading a `RelRegOrMem` (the target of a `jmp`/`call`) hands its
continuation a state whose `regs`/`status` are unchanged. -/
theorem RelRegOrMem.interp_preservesOutside [Labels] [AddressSize]
    (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
    (ret : BitVec 64 → MachineData → Effects) (post : MachineData → Prop)
    (h : ∀ (a : BitVec 64) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      Effects.PreservesOutside post (ret a s')) :
    Effects.PreservesOutside post (o.interp s p ret) := by
  cases o with
  | rel c => exact h _ s rfl rfl
  | reg r => exact h _ s rfl rfl
  | mem a =>
      simp only [RelRegOrMem.interp]
      exact MachineData.load_preservesOutside s _ ret post h
-/

/-- Reading a `RelRegOrMem` (the target of a `jmp`/`call`) hands its
continuation a state whose `regs`/`status` are unchanged. -/
theorem RelRegOrMem.interp_reaches [Labels] [AddressSize]
    (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64) (ret : BitVec 64 → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : BitVec 64) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- Writing a `Dst` never changes the flags, whether it lands in a register
or in memory. -/
theorem MachineData.set_status_preservesOutside {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (post : MachineData → Prop)
    (h : ∀ s', s'.status = s.status → Effects.PreservesOutside post (ret s')) :
    Effects.PreservesOutside post (MachineData.set s d v p ret) := by
  cases d with
  | reg rd => exact h _ (MachineData.setReg_status s rd v)
  | mem a =>
      simp only [MachineData.set]
      exact MachineData.store_preservesOutside s _ v ret post (fun s' _ hstatus => h s' hstatus)
-/

/-- Writing a `Dst` never changes the flags, whether it lands in a register
or in memory. -/
theorem MachineData.set_reaches_status {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.set s d v p ret) final) :
    ∃ s', s'.status = s.status ∧ Effects.Exists (ret s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- Writing a `Dst` can only change `regs.get64 r` when the destination is a
register whose base is `r`. -/
theorem MachineData.set_get64_of_ne {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (post : MachineData → Prop) (r : Reg64) (hd : ∀ rd, d = .reg rd → r ≠ rd.base)
    (h : ∀ s', s'.regs.get64 r = s.regs.get64 r → Effects.PreservesOutside post (ret s')) :
    Effects.PreservesOutside post (MachineData.set s d v p ret) := by
  cases d with
  | reg rd => exact h _ (MachineData.setReg_get64_of_ne s rd v (hd rd rfl))
  | mem a =>
      simp only [MachineData.set]
      exact MachineData.store_preservesOutside s _ v ret post (fun s' hregs _ => h s' (by rw [hregs]))
-/

/-- Writing a `Dst` can only change `regs.get64 r` when the destination is a
register whose base is `r`. -/
theorem MachineData.set_get64_of_ne {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (r : Reg64) (hd : ∀ rd, d = .reg rd → r ≠ rd.base)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.set s d v p ret) final) :
    ∃ s', s'.regs.get64 r = s.regs.get64 r ∧ Effects.Exists (ret s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- AVX operations never touch the general-purpose registers or flags this
file reasons about (they only ever change `zmms`/`dmem`), so reading an AVX
operand hands its continuation a state whose `regs`/`status` are unchanged,
exactly like `RegOrMem.interp_preservesOutside`. Unlike GP memory reads, an
AVX read of unmapped memory is a hard `unimplemented` failure rather than a
resolvable choice, which `Effects.PreservesOutside` already treats as
vacuously fine (no `MachineData` results). -/
theorem AvxRegOrMem.interp_preservesOutside {w : AvxWidth} [Labels] [AddressSize]
    (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop) (checkAlign : Bool)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      Effects.PreservesOutside post (ret a s')) :
    Effects.PreservesOutside post (o.interp s p ret checkAlign) := by
  cases o with
  | avx r => exact h _ s rfl rfl
  | mem a =>
      simp only [AvxRegOrMem.interp, MachineData.loadAvx]
      split
      · trivial
      · simp only [Effects.PreservesOutside]
        cases Mem.loadInt s.dmem ((AddrExpr.interp a s.regs p).zeroExtend _) w.bytes with
        | some i => exact h _ s rfl rfl
        | none => trivial
-/

/-- AVX operations never touch the general-purpose registers or flags this
file reasons about (they only ever change `zmms`/`dmem`), so reading an AVX
operand hands its continuation a state whose `regs`/`status` are unchanged,
exactly like `RegOrMem.interp_reaches`. Unlike GP memory reads, an AVX read
of unmapped memory is a hard `unimplemented` failure rather than a
resolvable choice, which `Effects.Exists` already treats as impossible
(no `final` it can reach). -/
theorem AvxRegOrMem.interp_reaches {w : AvxWidth} [Labels] [AddressSize]
    (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (checkAlign : Bool)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret checkAlign) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
theorem AvxOperand.interp_preservesOutside {w : AvxWidth} [Labels] [AddressSize]
    (o : AvxOperand w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop) (checkAlign : Bool)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      Effects.PreservesOutside post (ret a s')) :
    Effects.PreservesOutside post (o.interp s p ret checkAlign) := by
  cases o with
  | regOrMem rm => exact AvxRegOrMem.interp_preservesOutside rm s p ret post checkAlign h
-/

theorem AvxOperand.interp_reaches {w : AvxWidth} [Labels] [AddressSize]
    (o : AvxOperand w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (checkAlign : Bool)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret checkAlign) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- Writing an AVX `Dst` never touches `regs`/`status` at all: it only ever
changes `zmms` (register destination) or `dmem` (memory destination, or a
hard `unimplemented` failure on unmapped memory). -/
theorem MachineData.setAvx_preservesOutside {w : AvxWidth} [Labels] [AddressSize]
    (d : AvxDst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (post : MachineData → Prop) (checkAlign : Bool)
    (h : ∀ s', s'.regs = s.regs → s'.status = s.status → Effects.PreservesOutside post (ret s')) :
    Effects.PreservesOutside post (MachineData.setAvx s d v p ret checkAlign) := by
  cases d with
  | avx r => exact h _ rfl rfl
  | mem a =>
      simp only [MachineData.setAvx, MachineData.storeAvx]
      split
      · trivial
      · simp only [Effects.PreservesOutside]
        cases Mem.loadInt s.dmem ((AddrExpr.interp a s.regs p).zeroExtend _) w.bytes with
        | some _ => exact h _ rfl rfl
        | none => trivial
-/

/-- Writing an AVX `Dst` never touches `regs`/`status` at all: it only ever
changes `zmms` (register destination) or `dmem` (memory destination, or a
hard `unimplemented` failure on unmapped memory). -/
theorem MachineData.setAvx_reaches {w : AvxWidth} [Labels] [AddressSize]
    (d : AvxDst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (checkAlign : Bool)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.setAvx s d v p ret checkAlign) final) :
    ∃ s', s'.regs = s.regs ∧ s'.status = s.status ∧ Effects.Exists (ret s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
theorem MachineData.setAvxLegacy_preservesOutside {w : AvxWidth} [Labels] [AddressSize]
    (d : AvxDst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (post : MachineData → Prop) (checkAlign : Bool)
    (h : ∀ s', s'.regs = s.regs → s'.status = s.status → Effects.PreservesOutside post (ret s')) :
    Effects.PreservesOutside post (MachineData.setAvxLegacy s d v p ret checkAlign) := by
  cases d with
  | avx r => exact h _ rfl rfl
  | mem a =>
      simp only [MachineData.setAvxLegacy, MachineData.storeAvx]
      split
      · trivial
      · simp only [Effects.PreservesOutside]
        cases Mem.loadInt s.dmem ((AddrExpr.interp a s.regs p).zeroExtend _) w.bytes with
        | some _ => exact h _ rfl rfl
        | none => trivial
-/

theorem MachineData.setAvxLegacy_reaches {w : AvxWidth} [Labels] [AddressSize]
    (d : AvxDst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (checkAlign : Bool)
    (final : MachineState)
    (hfinal : Effects.Exists (MachineData.setAvxLegacy s d v p ret checkAlign) final) :
    ∃ s', s'.regs = s.regs ∧ s'.status = s.status ∧ Effects.Exists (ret s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- `AvxOperation.interp` never touches `regs`/`status`. -/
theorem AvxOperation.preservesOutside [Labels] [address_size : AddressSize] {w : AvxWidth}
    (op : AvxOperation w) (p : Std.Rco Int64) (s : MachineData) (post : MachineData → Prop)
    (hpost : ∀ s' : MachineData, s'.regs = s.regs → s'.status = s.status → post s') :
    Effects.PreservesOutside post
      (AvxOperation.interp op p s (fun s' => .done (s', (0 : Int64)))) := by
  have hpost' : ∀ s' : MachineData, s'.regs = s.regs → s'.status = s.status →
      Effects.PreservesOutside post (Effects.done (s', (0 : Int64))) := by
    intro s' hregs hstatus; simpa [Effects.PreservesOutside] using hpost s' hregs hstatus
  cases op with
  | movups dst src =>
      simp only [AvxOperation.interp]
      exact AvxRegOrMem.interp_preservesOutside src s p _ post false (fun a s' hregs hstatus =>
        MachineData.setAvxLegacy_preservesOutside dst s' a p _ post false (fun s'' hregs' hstatus' =>
          hpost' s'' (hregs'.trans hregs) (hstatus'.trans hstatus)))
  | vmovups dst src =>
      simp only [AvxOperation.interp]
      exact AvxRegOrMem.interp_preservesOutside src s p _ post false (fun a s' hregs hstatus =>
        MachineData.setAvx_preservesOutside dst s' a p _ post false (fun s'' hregs' hstatus' =>
          hpost' s'' (hregs'.trans hregs) (hstatus'.trans hstatus)))
  | movaps dst src =>
      simp only [AvxOperation.interp]
      exact AvxRegOrMem.interp_preservesOutside src s p _ post true (fun a s' hregs hstatus =>
        MachineData.setAvxLegacy_preservesOutside dst s' a p _ post true (fun s'' hregs' hstatus' =>
          hpost' s'' (hregs'.trans hregs) (hstatus'.trans hstatus)))
  | subps dst src =>
      simp only [AvxOperation.interp]
      exact AvxRegOrMem.interp_preservesOutside src s p _ post true (fun a s' hregs hstatus =>
        AvxRegOrMem.interp_preservesOutside dst s' p _ post false (fun b s'' hregs' hstatus' =>
          MachineData.setAvxLegacy_preservesOutside dst s'' _ p _ post false (fun s''' hregs'' hstatus'' =>
            hpost' s''' (hregs''.trans (hregs'.trans hregs)) (hstatus''.trans (hstatus'.trans hstatus)))))
  | addps dst src =>
      simp only [AvxOperation.interp]
      exact AvxRegOrMem.interp_preservesOutside src s p _ post true (fun a s' hregs hstatus =>
        AvxRegOrMem.interp_preservesOutside dst s' p _ post false (fun b s'' hregs' hstatus' =>
          MachineData.setAvxLegacy_preservesOutside dst s'' _ p _ post false (fun s''' hregs'' hstatus'' =>
            hpost' s''' (hregs''.trans (hregs'.trans hregs)) (hstatus''.trans (hstatus'.trans hstatus)))))
-/

/-- `AvxOperation.interp` never touches `regs`/`status`. -/
theorem AvxOperation.interp_reaches [Labels] [address_size : AddressSize] {w : AvxWidth}
    (op : AvxOperation w) (p : Std.Rco Int64) (s : MachineData) (next : MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (AvxOperation.interp op p s next) final) :
    ∃ s', s'.regs = s.regs ∧ s'.status = s.status ∧ Effects.Exists (next s') final := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- `modifies_flags` is a sound over-approximation of `Operation.interp`:
running an operation it reports as not modifying the flags really does
leave `status` unchanged, for every way of resolving any nondeterminism in
its semantics (see `Effects.PreservesOutside`). `next`/`jmp` are fixed to
immediately finish (`Effects.done`), matching how Kraken's own `step1`
observes a single instruction's effect. -/
theorem Operation.modifies_flags_sound [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData)
    (h : modifies_flags (.regular address_size.address_size w op) = false) :
    Effects.PreservesOutside (fun s' => s'.status = s.status)
      (Operation.interp op p s (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc))) := by
  cases op with
  | mov dst src =>
      simp only [Operation.interp]
      exact Operand.interp_preservesOutside src s p _ _ (fun a s' _ hstatus =>
        MachineData.set_status_preservesOutside dst s' a p _ _ (fun s'' hstatus' => by simp only [Effects.PreservesOutside]; rw [hstatus', hstatus]))
  | movsx dst src =>
      simp only [Operation.interp]
      exact RegOrMem.interp_preservesOutside src s p _ _ (fun a s' _ hstatus =>
        MachineData.set_status_preservesOutside dst s' _ p _ _ (fun s'' hstatus' => by simp only [Effects.PreservesOutside]; rw [hstatus', hstatus]))
  | movzx dst src =>
      simp only [Operation.interp]
      exact RegOrMem.interp_preservesOutside src s p _ _ (fun a s' _ hstatus =>
        MachineData.set_status_preservesOutside dst s' _ p _ _ (fun s'' hstatus' => by simp only [Effects.PreservesOutside]; rw [hstatus', hstatus]))
  | push src =>
      simp only [Operation.interp]
      exact Operand.interp_preservesOutside src s p _ _ (fun a s' _ hstatus =>
        MachineData.store_preservesOutside _ _ a _ _ (fun s'' _ hstatus' => by
          simp only [Effects.PreservesOutside]; rw [hstatus', hstatus]))
  | pop dst =>
      simp only [Operation.interp]
      exact MachineData.load_preservesOutside s _ _ _ (fun a s' _ hstatus =>
        MachineData.set_status_preservesOutside dst _ a p _ _ (fun s'' hstatus' => by simp only [Effects.PreservesOutside]; rw [hstatus', hstatus]))
  | setcc cc dst =>
      simp only [Operation.interp]
      exact MachineData.set_status_preservesOutside dst s _ p _ _ (fun s'' hstatus' => by simp only [Effects.PreservesOutside]; rw [hstatus'])
  | cmovcc cc dst src =>
      simp only [Operation.interp]
      exact RegOrMem.interp_preservesOutside src s p _ _ (fun a s' _ hstatus => by
        simp only [Effects.PreservesOutside]
        split <;> exact hstatus ▸ MachineData.setReg_status s' dst _)
  | lea dst src =>
      simp only [Operation.interp, Effects.PreservesOutside]
      exact MachineData.setReg_status s dst _
  | add dst src => simp [modifies_flags] at h
  | adc dst src => simp [modifies_flags] at h
  | adcx dst src => simp [modifies_flags] at h
  | adox dst src => simp [modifies_flags] at h
  | inc dst => simp [modifies_flags] at h
  | dec dst => simp [modifies_flags] at h
  | neg dst => simp [modifies_flags] at h
  | sub dst src => simp [modifies_flags] at h
  | sbb dst src => simp [modifies_flags] at h
  | cmp a b => simp [modifies_flags] at h
  | mul src => simp [modifies_flags] at h
  | mulx hi lo src => simp [modifies_flags] at h
  | imul1 src => simp [modifies_flags] at h
  | imul dst src1 src2 => simp [modifies_flags] at h
  | test a b => simp [modifies_flags] at h
  | and dst src => simp [modifies_flags] at h
  | or dst src => simp [modifies_flags] at h
  | xor dst src => simp [modifies_flags] at h
  | not dst =>
      simp only [Operation.interp]
      exact RegOrMem.interp_preservesOutside dst s p _ _ (fun a s' _ hstatus =>
        MachineData.set_status_preservesOutside dst s' _ p _ _ (fun s'' hstatus' => by simp only [Effects.PreservesOutside]; rw [hstatus', hstatus]))
  | shl dst c => simp [modifies_flags] at h
  | shr dst c => simp [modifies_flags] at h
  | sar dst c => simp [modifies_flags] at h
  | shld dst src c => simp [modifies_flags] at h
  | shrd dst src c => simp [modifies_flags] at h
  | rol dst c => simp [modifies_flags] at h
  | ror dst c => simp [modifies_flags] at h
  | rcl dst c => simp [modifies_flags] at h
  | rcr dst c => simp [modifies_flags] at h
  | bswap dst =>
      simp only [Operation.interp]
      cases w with
      | W32 | W64 => simp only [Effects.PreservesOutside]; exact MachineData.setReg_status s dst _
      | W8 | W16 => simp only [Effects.PreservesOutside]; intro v; exact MachineData.setReg_status s dst _
  | jcc cc l =>
      simp only [Operation.interp]
      split <;> rfl
  | jmp tgt =>
      simp only [Operation.interp]
      exact RelRegOrMem.interp_preservesOutside tgt s p _ _ (fun a s' _ hstatus => hstatus)
  | call tgt =>
      simp only [Operation.interp]
      exact RelRegOrMem.interp_preservesOutside tgt s p _ _ (fun a s' _ hstatus =>
        MachineData.store_preservesOutside _ _ _ _ _ (fun s'' _ hstatus' => by
          simp only [Effects.PreservesOutside]; rw [hstatus', hstatus]))
  | ret =>
      simp only [Operation.interp]
      exact MachineData.load_preservesOutside s _ _ _ (fun a s' _ hstatus => by
        simp only [Effects.PreservesOutside]; rw [hstatus])
  | nop n => simp only [Operation.interp, Effects.PreservesOutside]
  | nopalign a b => simp only [Operation.interp, Effects.PreservesOutside]
-/

/-- `modifies_flags` is a sound over-approximation of `Operation.interp`:
running an operation it reports as not modifying the flags really does
leave `status` unchanged, for every state its execution can reach.
`next`/`jmp` are fixed to immediately finish (`Effects.done`), matching
how Kraken's own `step1` observes a single instruction's effect. -/
theorem modifies_flags_sound [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (initial final : MachineData)
    (arbitrary_pc final_pc : Int64)
    (h : modifies_flags (.regular address_size.address_size w op) = false)
    (hfinal : (op.interp p initial
                  (fun s' => .done (s', arbitrary_pc))
                  (fun pc s' => .done (s', pc))).Exists (final, final_pc)) :
    final.status = initial.status := by
  sorry

/-- `Reg64`'s derived `BEq` is decided pointwise, so a failed comparison
witnesses disequality -- proved once here by brute-force case split, since
that avoids relying on a `LawfulBEq Reg64` instance being available to
`simp`. -/
theorem Reg64.ne_of_beq_eq_false {a b : Reg64} (h : (a == b) = false) : a ≠ b := by
  cases a <;> cases b <;> first | decide | exact absurd h (by decide)

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- `written_regs` is a sound over-approximation of `Operation.interp`:
running an operation can only change `regs.get64 r` for a register `r`
it reports as written. Same setup as `modifies_flags_sound` (`next`/`jmp`
fixed to `Effects.done`). -/
theorem Operation.written_regs_sound [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData) (r : Reg64)
    (hr : (written_regs (.regular address_size.address_size w op)).contains r = false) :
    Effects.PreservesOutside (fun s' => s'.regs.get64 r = s.regs.get64 r)
      (Operation.interp op p s (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc))) := by
  cases op with
  | mov dst src =>
      simp only [Operation.interp]
      apply Operand.interp_preservesOutside
      intro a s' hregs _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | movsx dst src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | movzx dst src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | lea dst src =>
      simp only [Operation.interp, Effects.PreservesOutside]
      have hne : r ≠ dst.base := by exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      exact MachineData.setReg_get64_of_ne s dst _ hne
  | setcc cc dst =>
      simp only [Operation.interp]
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget]
  | cmovcc cc dst src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      have hne : r ≠ dst.base := by exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      simp only [Effects.PreservesOutside]
      split <;> rw [MachineData.setReg_get64_of_ne s' dst _ hne, hregs]
  | add dst src =>
      simp only [Operation.interp]
      apply Operand.interp_preservesOutside
      intro a s' hregs _
      apply RegOrMem.interp_preservesOutside
      intro b s'' hregs' _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s''' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs', hregs]
  | adc dst src =>
      simp only [Operation.interp]
      apply Operand.interp_preservesOutside
      intro a s' hregs _
      apply RegOrMem.interp_preservesOutside
      intro b s'' hregs' _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s''' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs', hregs]
  | sub dst src =>
      simp only [Operation.interp]
      apply Operand.interp_preservesOutside
      intro a s' hregs _
      apply RegOrMem.interp_preservesOutside
      intro b s'' hregs' _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s''' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs', hregs]
  | sbb dst src =>
      simp only [Operation.interp]
      apply Operand.interp_preservesOutside
      intro a s' hregs _
      apply RegOrMem.interp_preservesOutside
      intro b s'' hregs' _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s''' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs', hregs]
  | cmp a b =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro va s' hregs _
      apply Operand.interp_preservesOutside
      intro vb s'' hregs' _
      simp only [Effects.PreservesOutside]
      rw [hregs', hregs]
  | mul src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro b s' hregs _
      have hr' : (r == Reg64.rax) = false ∧ (r == Reg64.rdx) = false := by simpa [written_regs] using hr
      have hrax : r ≠ Reg64.rax := Reg64.ne_of_beq_eq_false hr'.1
      have hrdx : r ≠ Reg64.rdx := Reg64.ne_of_beq_eq_false hr'.2
      simp only [Effects.PreservesOutside]
      split
      · intro _ _ _ _
        rw [MachineData.setReg_get64_of_ne s' _ _ hrax, hregs]
      · intro _ _ _ _
        rw [MachineData.setReg_get64_of_ne _ _ _ hrdx, MachineData.setReg_get64_of_ne s' _ _ hrax, hregs]
  | imul1 src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro b s' hregs _
      have hr' : (r == Reg64.rax) = false ∧ (r == Reg64.rdx) = false := by simpa [written_regs] using hr
      have hrax : r ≠ Reg64.rax := Reg64.ne_of_beq_eq_false hr'.1
      have hrdx : r ≠ Reg64.rdx := Reg64.ne_of_beq_eq_false hr'.2
      simp only [Effects.PreservesOutside]
      split
      · intro _ _ _ _
        rw [MachineData.setReg_get64_of_ne s' _ _ hrax, hregs]
      · intro _ _ _ _
        rw [MachineData.setReg_get64_of_ne _ _ _ hrdx, MachineData.setReg_get64_of_ne s' _ _ hrax, hregs]
  | imul dst src1 src2 =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply Operand.interp_preservesOutside
      intro b s'' hregs' _
      apply MachineData.set_get64_of_ne (r := r)
      · intro rd hrd
        cases dst with
        | some d => exact Reg64.ne_of_beq_eq_false (by simp_all [written_regs])
        | none => exact Reg64.ne_of_beq_eq_false (by simp_all [written_regs])
      · intro s''' hget
        simp only [Effects.PreservesOutside]
        intro _ _ _ _
        rw [hget, hregs', hregs]
  | mulx hi lo src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      have hr' : (r == hi.base) = false ∧ (r == lo.base) = false := by simpa [written_regs] using hr
      have hhi : r ≠ hi.base := Reg64.ne_of_beq_eq_false hr'.1
      have hlo : r ≠ lo.base := Reg64.ne_of_beq_eq_false hr'.2
      simp only [Effects.PreservesOutside]
      rw [MachineData.setReg_get64_of_ne _ hi _ hhi, MachineData.setReg_get64_of_ne s' lo _ hlo, hregs]
  | test a b =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro va s' hregs _
      apply Operand.interp_preservesOutside
      intro vb s'' hregs' _
      simp only [Effects.PreservesOutside]
      intro _
      rw [hregs', hregs]
  | and dst src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply Operand.interp_preservesOutside
      intro b s'' hregs' _
      simp only [Effects.PreservesOutside]
      intro _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s''' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs', hregs]
  | or dst src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply Operand.interp_preservesOutside
      intro b s'' hregs' _
      simp only [Effects.PreservesOutside]
      intro _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s''' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs', hregs]
  | xor dst src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply Operand.interp_preservesOutside
      intro b s'' hregs' _
      simp only [Effects.PreservesOutside]
      intro _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s''' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs', hregs]
  | not dst =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | inc dst =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | dec dst =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | neg dst =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | adcx dst src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply Reg.interp_preservesOutside
      intro b s'' hregs' _
      have hne : r ≠ dst.base := by exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      simp only [Effects.PreservesOutside]
      rw [Reg64s.get64_set_of_ne dst _ hne, hregs', hregs]
  | adox dst src =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply Reg.interp_preservesOutside
      intro b s'' hregs' _
      have hne : r ≠ dst.base := by exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      simp only [Effects.PreservesOutside]
      rw [Reg64s.get64_set_of_ne dst _ hne, hregs', hregs]
  | shl dst c =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      split
      · simp only [Effects.PreservesOutside]; rw [hregs]
      · simp only [Effects.PreservesOutside]
        intro af
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals apply MachineData.set_get64_of_ne
        all_goals first
          | (intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr))
          | (intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs])
  | shr dst c =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      split
      · simp only [Effects.PreservesOutside]; rw [hregs]
      · simp only [Effects.PreservesOutside]
        intro af
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals apply MachineData.set_get64_of_ne
        all_goals first
          | (intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr))
          | (intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs])
  | sar dst c =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      split
      · simp only [Effects.PreservesOutside]; rw [hregs]
      · simp only [Effects.PreservesOutside]
        intro af
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals apply MachineData.set_get64_of_ne
        all_goals first
          | (intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr))
          | (intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs])
  | rol dst c =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      split
      · simp only [Effects.PreservesOutside]; rw [hregs]
      · split
        · apply MachineData.set_get64_of_ne
          · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
          · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
        · simp only [Effects.PreservesOutside]
          intro of
          apply MachineData.set_get64_of_ne
          · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
          · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | ror dst c =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      split
      · simp only [Effects.PreservesOutside]; rw [hregs]
      · split
        · apply MachineData.set_get64_of_ne
          · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
          · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
        · simp only [Effects.PreservesOutside]
          intro of
          apply MachineData.set_get64_of_ne
          · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
          · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | rcl dst c =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      split
      · simp only [Effects.PreservesOutside]; rw [hregs]
      · split
        · apply MachineData.set_get64_of_ne
          · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
          · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
        · simp only [Effects.PreservesOutside]
          intro of
          apply MachineData.set_get64_of_ne
          · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
          · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | rcr dst c =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      split
      · simp only [Effects.PreservesOutside]; rw [hregs]
      · split
        · apply MachineData.set_get64_of_ne
          · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
          · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
        · simp only [Effects.PreservesOutside]
          intro of
          apply MachineData.set_get64_of_ne
          · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
          · intro s'' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs]
  | shld dst src c =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply Reg.interp_preservesOutside
      intro b s'' hregs' _
      split
      · simp only [Effects.PreservesOutside]; rw [hregs', hregs]
      · all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals apply MachineData.set_get64_of_ne
        all_goals first
          | (intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr))
          | (intro s''' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs', hregs])
  | shrd dst src c =>
      simp only [Operation.interp]
      apply RegOrMem.interp_preservesOutside
      intro a s' hregs _
      apply Reg.interp_preservesOutside
      intro b s'' hregs' _
      split
      · simp only [Effects.PreservesOutside]; rw [hregs', hregs]
      · all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals (try split)
        all_goals (try (simp only [Effects.PreservesOutside]; intro _))
        all_goals apply MachineData.set_get64_of_ne
        all_goals first
          | (intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr))
          | (intro s''' hget; simp only [Effects.PreservesOutside]; rw [hget, hregs', hregs])
  | bswap dst =>
      simp only [Operation.interp]
      have hne : r ≠ dst.base := by exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      cases w with
      | W32 | W64 => simp only [Effects.PreservesOutside]; exact MachineData.setReg_get64_of_ne s dst _ hne
      | W8 | W16 => simp only [Effects.PreservesOutside]; intro v; exact MachineData.setReg_get64_of_ne s dst _ hne
  | push src =>
      simp only [Operation.interp]
      apply Operand.interp_preservesOutside
      intro a s' hregs _
      have hne : r ≠ Reg64.rsp := by exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      apply MachineData.store_preservesOutside
      intro s'' hregs' _
      simp only [Effects.PreservesOutside]
      rw [hregs', Reg64s.get64_set64_of_ne hne, hregs]
  | pop dst =>
      simp only [Operation.interp]
      apply MachineData.load_preservesOutside
      intro a s' hregs _
      have hr' : (r == Reg64.rsp) = false ∧
          (match dst with | .reg r' => [r'.base] | .mem _ => ([] : List Reg64)).contains r = false := by
        simpa [written_regs] using hr
      have hnersp : r ≠ Reg64.rsp := Reg64.ne_of_beq_eq_false hr'.1
      apply MachineData.set_get64_of_ne
      · intro rd hrd; subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa using hr'.2)
      · intro s'' hget
        simp only [Effects.PreservesOutside]
        rw [hget]
        show Reg64s.get64 (Reg64s.set64 s'.regs .rsp _) r = s.regs.get64 r
        rw [Reg64s.get64_set64_of_ne hnersp, hregs]
  | jcc cc l =>
      simp only [Operation.interp]
      split <;> rfl
  | jmp tgt =>
      simp only [Operation.interp]
      apply RelRegOrMem.interp_preservesOutside
      intro a s' hregs _
      simp only [Effects.PreservesOutside]
      rw [hregs]
  | call tgt =>
      simp only [Operation.interp]
      apply RelRegOrMem.interp_preservesOutside
      intro a s' hregs _
      have hne : r ≠ Reg64.rsp := by exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      apply MachineData.store_preservesOutside
      intro s'' hregs' _
      simp only [Effects.PreservesOutside]
      rw [hregs', Reg64s.get64_set64_of_ne hne, hregs]
  | ret =>
      simp only [Operation.interp]
      apply MachineData.load_preservesOutside
      intro a s' hregs _
      have hne : r ≠ Reg64.rsp := by exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      show Reg64s.get64 (Reg64s.set64 s'.regs .rsp _) r = s.regs.get64 r
      rw [Reg64s.get64_set64_of_ne hne, hregs]
  | nop n => simp only [Operation.interp, Effects.PreservesOutside]
  | nopalign a b => simp only [Operation.interp, Effects.PreservesOutside]
-/

/-- `written_regs` is a sound over-approximation of `Operation.interp`:
running an operation can only change `regs.get64 r` for a register `r`
it reports as written. Same setup as `modifies_flags_sound` (`next`/`jmp`
fixed to `Effects.done`). -/
theorem Operation.written_regs_sound [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData) (r : Reg64)
    (hr : (written_regs (.regular address_size.address_size w op)).contains r = false)
    (final : MachineState)
    (hfinal : Effects.Exists
      (Operation.interp op p s (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc)))
      final) :
    final.1.regs.get64 r = s.regs.get64 r := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- `modifies_flags` is sound for every `Instr`: `.regular` instructions are
covered by `Operation.modifies_flags_sound`, and `.avx` instructions never
touch the flags at all. -/
theorem Instr.modifies_flags_sound [Labels] (i : Instr) (p : Std.Rco Int64) (s : MachineData)
    (h : modifies_flags i = false) :
    Effects.PreservesOutside (fun s' => s'.status = s.status)
      (i.interp s p (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc))) := by
  cases i with
  | regular addr_sz op_sz op =>
      simp only [Instr.interp, Effects.PreservesOutside]
      exact Operation.modifies_flags_sound (address_size := .mk addr_sz) op p s h
  | avx addr_sz op_sz op =>
      simp only [Instr.interp, Effects.PreservesOutside]
      exact AvxOperation.preservesOutside (address_size := .mk addr_sz) op p s _
        (fun s' _ hstatus => hstatus)
-/

/-- `modifies_flags` is sound for every `Instr`: `.regular` instructions are
covered by `Operation.modifies_flags_sound`, and `.avx` instructions never
touch the flags at all. -/
theorem Instr.modifies_flags_sound [Labels] (i : Instr) (p : Std.Rco Int64) (s : MachineData)
    (h : modifies_flags i = false) (final : MachineState)
    (hfinal : Effects.Exists
      (i.interp s p (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc))) final) :
    final.1.status = s.status := by
  sorry

-- TODO (now) restore/fix this proof for the Effects.Exists-based statement below.
/-
/-- `written_regs` is sound for every `Instr`: `.regular` instructions are
covered by `Operation.written_regs_sound`, and `.avx` instructions never
touch any general-purpose register. -/
theorem Instr.written_regs_sound [Labels] (i : Instr) (p : Std.Rco Int64) (s : MachineData)
    (r : Reg64) (hr : (written_regs i).contains r = false) :
    Effects.PreservesOutside (fun s' => s'.regs.get64 r = s.regs.get64 r)
      (i.interp s p (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc))) := by
  cases i with
  | regular addr_sz op_sz op =>
      simp only [Instr.interp, Effects.PreservesOutside]
      exact Operation.written_regs_sound (address_size := .mk addr_sz) op p s r hr
  | avx addr_sz op_sz op =>
      simp only [Instr.interp, Effects.PreservesOutside]
      exact AvxOperation.preservesOutside (address_size := .mk addr_sz) op p s _
        (fun s' hregs _ => by rw [hregs])
-/

/-- `written_regs` is sound for every `Instr`: `.regular` instructions are
covered by `Operation.written_regs_sound`, and `.avx` instructions never
touch any general-purpose register. -/
theorem written_regs_sound [Labels] (i : Instr) (p : Std.Rco Int64)
    (initial final : MachineData)
    (r : Reg64) (hr : (written_regs i).contains r = false)
    (final_pc arbitrary_pc : Int64)
    (hfinal : (i.interp initial p
                   (fun s' => .done (s', arbitrary_pc))
                   (fun pc s' => .done (s', pc))).Exists (final, final_pc)) :
    final.regs.get64 r = initial.regs.get64 r := by
  sorry
