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
choices reaches `final` -- think of it like a small-step `-->* final`
judgement, with `e` playing the role of "the current configuration"
(it already has the starting `MachineData` baked in from whoever called
`.interp` on it, so unlike a textbook `-->*` there's no separate initial
state to name). -/

/-- Reading a `RegOrMem` operand hands its continuation a state whose
`regs`/`status` are unchanged (only `dmem` may differ, if the read went to
an address outside the modeled memory: `nonmem_load` only ever changes
`dmem`, see `MachineData.load`). -/
theorem MachineData.load_reaches {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.load s addr w ret) final) :
    ∃ (a : w.type), Effects.Exists (ret a s) final := by
  simp only [MachineData.load, Effects.Exists] at hfinal
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | some i => rw [hl] at hfinal; exact ⟨_, hfinal⟩
  | none => rw [hl] at hfinal; exact hfinal.elim

theorem RegOrMem.interp_reaches {w : Width} [Labels] [AddressSize]
    (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | reg r => exact ⟨_, s, rfl, rfl, hfinal⟩
  | mem a =>
      simp only [RegOrMem.interp] at hfinal
      obtain ⟨v, hfinal⟩ := MachineData.load_reaches s _ ret final hfinal
      exact ⟨v, s, rfl, rfl, hfinal⟩

/-- Reading an `Operand` hands its continuation a state whose
`regs`/`status` are unchanged. -/
theorem Operand.interp_reaches {w : Width} [Labels] [AddressSize]
    (o : Operand w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | regOrMem rm => exact RegOrMem.interp_reaches rm s p ret final hfinal
  | imm v => exact ⟨_, s, rfl, rfl, hfinal⟩

/-- Reading a plain `Reg` (as opposed to a `RegOrMem`/`Operand`) never
touches memory, so it hands its continuation back the very same state. -/
theorem Reg.interp_reaches {w : Width} (reg : Reg w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (reg.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final :=
  ⟨_, s, rfl, rfl, hfinal⟩

/-- Reading a `RelRegOrMem` (the target of a `jmp`/`call`) hands its
continuation a state whose `regs`/`status` are unchanged. -/
theorem RelRegOrMem.interp_reaches [Labels] [AddressSize]
    (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64) (ret : BitVec 64 → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : BitVec 64) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | rel c => exact ⟨_, s, rfl, rfl, hfinal⟩
  | reg r => exact ⟨_, s, rfl, rfl, hfinal⟩
  | mem a =>
      simp only [RelRegOrMem.interp] at hfinal
      obtain ⟨v, hfinal⟩ := MachineData.load_reaches s _ ret final hfinal
      exact ⟨v, s, rfl, rfl, hfinal⟩

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

/-- `Reg64`'s derived `BEq` is decided pointwise, so a failed comparison
witnesses disequality -- proved once here by brute-force case split, since
that avoids relying on a `LawfulBEq Reg64` instance being available to
`simp`. -/
theorem Reg64.ne_of_beq_eq_false {a b : Reg64} (h : (a == b) = false) : a ≠ b := by
  cases a <;> cases b <;> first | decide | exact absurd h (by decide)

/-- Storing to memory hands its continuation a state whose `regs`/`status`
are unchanged (only `dmem` differs). -/
theorem MachineData.store_reaches {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (v : w.type) (ret : MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (s.store addr v ret) final) :
    ∃ s', s'.regs = s.regs ∧ s'.status = s.status ∧ Effects.Exists (ret s') final := by
  simp only [MachineData.store, Effects.Exists] at hfinal
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | some _ =>
      rw [hl] at hfinal
      exact ⟨{ s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }, rfl, rfl, hfinal⟩
  | none => rw [hl] at hfinal; exact hfinal.elim

/-- Writing a `Dst` never changes the flags, whether it lands in a register
or in memory. -/
theorem MachineData.set_reaches_status {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.set s d v p ret) final) :
    ∃ s', s'.status = s.status ∧ Effects.Exists (ret s') final := by
  cases d with
  | reg rd => exact ⟨_, MachineData.setReg_status s rd v, hfinal⟩
  | mem a =>
      simp only [MachineData.set] at hfinal
      obtain ⟨s', hregs, hstatus, hfinal⟩ := MachineData.store_reaches s _ v ret final hfinal
      exact ⟨s', hstatus, hfinal⟩

/-- Writing a `Dst` can only change `regs.get64 r` when the destination is a
register whose base is `r`. -/
theorem MachineData.set_get64_of_ne {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (r : Reg64) (hd : ∀ rd, d = .reg rd → r ≠ rd.base)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.set s d v p ret) final) :
    ∃ s', s'.regs.get64 r = s.regs.get64 r ∧ Effects.Exists (ret s') final := by
  cases d with
  | reg rd => exact ⟨_, MachineData.setReg_get64_of_ne s rd v (hd rd rfl), hfinal⟩
  | mem a =>
      simp only [MachineData.set] at hfinal
      obtain ⟨s', hregs, _, hfinal⟩ := MachineData.store_reaches s _ v ret final hfinal
      exact ⟨s', by rw [hregs], hfinal⟩

/-- Once execution reaches a `.done a`, `Effects.Exists` pins the final
state down exactly to `a`. -/
theorem Effects.exists_done {a final : MachineState} (h : Effects.Exists (.done a) final) :
    final = a := h.symm

/-- Reading an AVX memory operand never touches `regs`/`status` (only
`dmem` may differ, via an out-of-range access, and even then the failure
cases -- unaligned, not backed by `dmem` -- can't reach a `.done`). -/
theorem MachineData.loadAvx_reaches {w : AvxWidth} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (ret : w.type → MachineData → Effects) (checkAlign : Bool)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.loadAvx s addr w ret checkAlign) final) :
    ∃ (a : w.type), Effects.Exists (ret a s) final := by
  simp only [MachineData.loadAvx] at hfinal
  split at hfinal
  · exact hfinal.elim
  · simp only [Effects.Exists] at hfinal
    cases hl : Mem.loadInt s.dmem addr w.bytes with
    | some i => rw [hl] at hfinal; exact ⟨_, hfinal⟩
    | none => rw [hl] at hfinal; exact hfinal.elim

/-- Reading an `AvxRegOrMem` operand hands its continuation a state whose
`regs`/`status` are unchanged. -/
theorem AvxRegOrMem.interp_reaches {w : AvxWidth} [Labels] [AddressSize]
    (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (checkAlign : Bool) (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret checkAlign) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | avx r => exact ⟨_, s, rfl, rfl, hfinal⟩
  | mem a =>
      simp only [AvxRegOrMem.interp] at hfinal
      obtain ⟨v, hfinal⟩ := MachineData.loadAvx_reaches s _ ret checkAlign final hfinal
      exact ⟨v, s, rfl, rfl, hfinal⟩

/-- Storing to an AVX memory address never touches `regs`/`status` (only
`dmem` differs, mirroring `MachineData.store_reaches`). -/
theorem MachineData.storeAvx_reaches {w : AvxWidth} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (v : w.type) (ret : MachineData → Effects) (checkAlign : Bool)
    (final : MachineState) (hfinal : Effects.Exists (s.storeAvx addr v ret checkAlign) final) :
    ∃ s', s'.regs = s.regs ∧ s'.status = s.status ∧ Effects.Exists (ret s') final := by
  simp only [MachineData.storeAvx] at hfinal
  split at hfinal
  · exact hfinal.elim
  · simp only [Effects.Exists] at hfinal
    cases hl : Mem.loadInt s.dmem addr w.bytes with
    | some _ =>
        rw [hl] at hfinal
        exact ⟨{ s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }, rfl, rfl, hfinal⟩
    | none => rw [hl] at hfinal; exact hfinal.elim

/-- Writing an `AvxDst` (as a "new-style" register, via `setAvx`) never
changes `regs`/`status`, whether it lands in a `zmm` register or in
memory. -/
theorem MachineData.setAvx_reaches {w : AvxWidth} [Labels] [AddressSize]
    (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (checkAlign : Bool) (final : MachineState)
    (hfinal : Effects.Exists (MachineData.setAvx s d v p ret checkAlign) final) :
    ∃ s', s'.regs = s.regs ∧ s'.status = s.status ∧ Effects.Exists (ret s') final := by
  cases d with
  | avx r =>
      simp only [MachineData.setAvx] at hfinal
      exact ⟨s.setAvxReg r v, rfl, rfl, hfinal⟩
  | mem a =>
      simp only [MachineData.setAvx] at hfinal
      exact MachineData.storeAvx_reaches s _ v ret checkAlign final hfinal

/-- Writing an `AvxDst` (as a legacy SSE register, via `setAvxLegacy`)
never changes `regs`/`status`, whether it lands in a `zmm` register or
in memory. -/
theorem MachineData.setAvxLegacy_reaches {w : AvxWidth} [Labels] [AddressSize]
    (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (checkAlign : Bool) (final : MachineState)
    (hfinal : Effects.Exists (MachineData.setAvxLegacy s d v p ret checkAlign) final) :
    ∃ s', s'.regs = s.regs ∧ s'.status = s.status ∧ Effects.Exists (ret s') final := by
  cases d with
  | avx r =>
      simp only [MachineData.setAvxLegacy] at hfinal
      exact ⟨s.setAvxLegacyReg r v, rfl, rfl, hfinal⟩
  | mem a =>
      simp only [MachineData.setAvxLegacy] at hfinal
      exact MachineData.storeAvx_reaches s _ v ret checkAlign final hfinal

/-- No `AvxOperation` ever touches `regs`/`status`: each of the five AVX
instructions only reads/writes `zmm` registers or `dmem`. Constructors
with the same read/write shape (`subps`/`addps`, both a `checkAlign`d
read of `src`, a plain read of `dst`, then a `setAvxLegacy` on `dst`)
share one case, so a new AVX instruction only needs its own case here
if its shape doesn't already match one. Used to prove
`written_regs_sound`/`modifies_flags_sound`'s `.avx` cases, where
`written_regs`/`modifies_flags` unconditionally report `[]`/`false`. -/
theorem AvxOperation.interp_reaches [Labels] [address_size : AddressSize] {w : AvxWidth}
    (op : AvxOperation w) (p : Std.Rco Int64) (s : MachineData) (arbitrary_pc : Int64)
    (final : MachineState)
    (hfinal : Effects.Exists (AvxOperation.interp op p s (fun s' => .done (s', arbitrary_pc))) final) :
    final.1.regs = s.regs ∧ final.1.status = s.status := by
  cases op with
  | movups dst src =>
      simp only [AvxOperation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := AvxRegOrMem.interp_reaches src s p _ false final hfinal
      obtain ⟨s'', hregs', hstatus', hfinal⟩ := MachineData.setAvxLegacy_reaches s' dst a p _ false final hfinal
      rw [Effects.exists_done hfinal]
      exact ⟨hregs'.trans hregs, hstatus'.trans hstatus⟩
  | vmovups dst src =>
      simp only [AvxOperation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := AvxRegOrMem.interp_reaches src s p _ false final hfinal
      obtain ⟨s'', hregs', hstatus', hfinal⟩ := MachineData.setAvx_reaches s' dst a p _ false final hfinal
      rw [Effects.exists_done hfinal]
      exact ⟨hregs'.trans hregs, hstatus'.trans hstatus⟩
  | movaps dst src =>
      simp only [AvxOperation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := AvxRegOrMem.interp_reaches src s p _ true final hfinal
      obtain ⟨s'', hregs', hstatus', hfinal⟩ := MachineData.setAvxLegacy_reaches s' dst a p _ true final hfinal
      rw [Effects.exists_done hfinal]
      exact ⟨hregs'.trans hregs, hstatus'.trans hstatus⟩
  | subps dst src | addps dst src =>
      simp only [AvxOperation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := AvxRegOrMem.interp_reaches src s p _ true final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := AvxRegOrMem.interp_reaches dst s' p _ false final hfinal
      obtain ⟨s''', hregs'', hstatus'', hfinal⟩ := MachineData.setAvxLegacy_reaches s'' dst _ p _ false final hfinal
      rw [Effects.exists_done hfinal]
      exact ⟨hregs''.trans (hregs'.trans hregs), hstatus''.trans (hstatus'.trans hstatus)⟩

/-- `modifies_flags` is a sound over-approximation of `Operation.interp`:
running an operation it reports as not modifying the flags really does
leave `status` unchanged, for every state its execution can reach.
`next`/`jmp` are fixed to immediately finish (`Effects.done`), matching
how Kraken's own `step1` observes a single instruction's effect.

Only the constructors `modifies_flags` reports `false` for get their
own case; every other constructor -- i.e. every one `modifies_flags`
reports `true` for -- falls through to the final wildcard case, which
derives a contradiction from `h` without needing to know which
constructor `op` actually is. This means a newly-added constructor
that modifies the flags needs no change here at all; only one that
*doesn't* would need a new named case above the wildcard. -/
theorem Operation.modifies_flags_sound [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData) (arbitrary_pc : Int64)
    (h : modifies_flags (.regular address_size.address_size w op) = false)
    (final : MachineState)
    (hfinal : Effects.Exists
        (Operation.interp op p s (fun s' => .done (s', arbitrary_pc)) (fun pc s' => .done (s', pc)))
        final) :
    final.1.status = s.status := by
  cases op with
  | mov dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      obtain ⟨s'', hstatus', hfinal⟩ := MachineData.set_reaches_status dst s' a p _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'.trans hstatus
  | movsx dst src | movzx dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      obtain ⟨s'', hstatus', hfinal⟩ := MachineData.set_reaches_status dst s' _ p _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'.trans hstatus
  | push src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      obtain ⟨s'', hregs', hstatus', hfinal⟩ := MachineData.store_reaches _ _ a _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'.trans hstatus
  | pop dst =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, hfinal⟩ := MachineData.load_reaches s _ _ final hfinal
      obtain ⟨s'', hstatus', hfinal⟩ := MachineData.set_reaches_status dst _ a p _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'
  | setcc cc dst =>
      simp only [Operation.interp] at hfinal
      obtain ⟨s', hstatus', hfinal⟩ := MachineData.set_reaches_status dst s _ p _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'
  | cmovcc cc dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      split at hfinal <;> rw [Effects.exists_done hfinal] <;>
        exact (MachineData.setReg_status s' dst _).trans hstatus
  | lea dst src =>
      simp only [Operation.interp] at hfinal
      rw [Effects.exists_done hfinal]
      exact MachineData.setReg_status s dst _
  | not dst =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      obtain ⟨s'', hstatus', hfinal⟩ := MachineData.set_reaches_status dst s' _ p _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'.trans hstatus
  | bswap dst =>
      simp only [Operation.interp] at hfinal
      cases w with
      | W32 | W64 => rw [Effects.exists_done hfinal]; exact MachineData.setReg_status s dst _
      | W8 | W16 =>
          obtain ⟨v, hfinal⟩ := hfinal
          rw [Effects.exists_done hfinal]; exact MachineData.setReg_status s dst _
  | jcc cc l =>
      simp only [Operation.interp] at hfinal
      split at hfinal <;> rw [Effects.exists_done hfinal]
  | jmp tgt =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RelRegOrMem.interp_reaches tgt s p _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus
  | call tgt =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RelRegOrMem.interp_reaches tgt s p _ final hfinal
      obtain ⟨s'', hregs', hstatus', hfinal⟩ := MachineData.store_reaches _ _ _ _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'.trans hstatus
  | ret =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, hfinal⟩ := MachineData.load_reaches s _ _ final hfinal
      rw [Effects.exists_done hfinal]
  | nop n | nopalign n _ =>
      simp only [Operation.interp] at hfinal; rw [Effects.exists_done hfinal]
  -- Every other constructor is one `modifies_flags` already reports `true`
  -- for, contradicting `h`; this covers them without listing them (and
  -- automatically covers a newly-added flag-modifying instruction too).
  | _ => simp [modifies_flags] at h

/-- `written_regs` is a sound over-approximation of `Operation.interp`:
running an operation can only change `regs.get64 r` for a register `r`
it reports as written. Same setup as `modifies_flags_sound` (`next`/`jmp`
fixed to `Effects.done`).

Unlike `modifies_flags_sound`, there's no single fallback tactic that
covers every constructor `written_regs` doesn't single out, since each
one's proof depends on which registers/operands it actually reads and
writes. Constructors that read/write the same shape of operands (e.g.
`add`/`adc`/`sub`/`sbb`, or the shift family) share one case instead,
so a newly-added constructor with a shape already covered just joins
that case's pattern; only a genuinely new shape needs a new case. -/
theorem Operation.written_regs_sound [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData) (arbitrary_pc : Int64) (r : Reg64)
    (hr : (written_regs (.regular address_size.address_size w op)).contains r = false)
    (final : MachineState)
    (hfinal : Effects.Exists
        (Operation.interp op p s (fun s' => .done (s', arbitrary_pc)) (fun pc s' => .done (s', pc)))
        final) :
    final.1.regs.get64 r = s.regs.get64 r := by
  cases op with
  | mov dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst s' a p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs]
  | movsx dst src | movzx dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst s' _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs]
  | lea dst src =>
      simp only [Operation.interp] at hfinal
      rw [Effects.exists_done hfinal]
      exact MachineData.setReg_get64_of_ne s dst _ (Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr))
  | setcc cc dst =>
      simp only [Operation.interp] at hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst s _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      exact hget
  | cmovcc cc dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      have hne : r ≠ dst.base := Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      split at hfinal <;> rw [Effects.exists_done hfinal] <;>
        simp [MachineData.setReg_get64_of_ne s' dst _ hne, hregs]
  | add dst src | adc dst src | sub dst src | sbb dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := RegOrMem.interp_reaches dst s' p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs', hregs]
  | cmp a b =>
      simp only [Operation.interp] at hfinal
      obtain ⟨va, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches a s p _ final hfinal
      obtain ⟨vb, s'', hregs', hstatus', hfinal⟩ := Operand.interp_reaches b s' p _ final hfinal
      rw [Effects.exists_done hfinal]
      simp [hregs', hregs]
  | mul src | imul1 src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨b, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      have hr' : (r == Reg64.rax) = false ∧ (r == Reg64.rdx) = false := by simpa [written_regs] using hr
      have hrax : r ≠ Reg64.rax := Reg64.ne_of_beq_eq_false hr'.1
      have hrdx : r ≠ Reg64.rdx := Reg64.ne_of_beq_eq_false hr'.2
      obtain ⟨_, hfinal⟩ := hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      split at hfinal
      · rw [Effects.exists_done hfinal]
        simp [MachineData.setReg_get64_of_ne s' (.low .rax .W16) _ hrax, hregs]
      · rw [Effects.exists_done hfinal]
        simp [MachineData.setReg_get64_of_ne _ (.low .rdx w) _ hrdx,
          MachineData.setReg_get64_of_ne s' (.low .rax w) _ hrax, hregs]
  | imul dst src1 src2 =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src1 s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := Operand.interp_reaches src2 s' p _ final hfinal
      obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne _ s'' _ p _ r
        (by intro rd hrd
            cases dst with
            | some d => exact Reg64.ne_of_beq_eq_false (by simp_all [written_regs])
            | none => exact Reg64.ne_of_beq_eq_false (by simp_all [written_regs]))
        final hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs', hregs]
  | mulx hi lo src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      have hr' : (r == hi.base) = false ∧ (r == lo.base) = false := by simpa [written_regs] using hr
      have hhi : r ≠ hi.base := Reg64.ne_of_beq_eq_false hr'.1
      have hlo : r ≠ lo.base := Reg64.ne_of_beq_eq_false hr'.2
      rw [Effects.exists_done hfinal]
      simp [MachineData.setReg_get64_of_ne _ hi _ hhi, MachineData.setReg_get64_of_ne s' lo _ hlo, hregs]
  | test a b =>
      simp only [Operation.interp] at hfinal
      obtain ⟨va, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches a s p _ final hfinal
      obtain ⟨vb, s'', hregs', hstatus', hfinal⟩ := Operand.interp_reaches b s' p _ final hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      rw [Effects.exists_done hfinal]
      simp [hregs', hregs]
  | and dst src | or dst src | xor dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := Operand.interp_reaches src s' p _ final hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs', hregs]
  | not dst | inc dst | dec dst | neg dst =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs]
  | adcx dst src | adox dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := Reg.interp_reaches dst s' p _ final hfinal
      have hne : r ≠ dst.base := Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      rw [Effects.exists_done hfinal]
      simp [Reg64s.get64_set_of_ne dst _ hne, hregs', hregs]
  | shl dst c | shr dst c | sar dst c =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      split at hfinal
      · rw [Effects.exists_done hfinal]; simp [hregs]
      · all_goals (try obtain ⟨_, hfinal⟩ := hfinal)
        all_goals (try split at hfinal)
        all_goals (try obtain ⟨_, hfinal⟩ := hfinal)
        all_goals (try split at hfinal)
        all_goals (try obtain ⟨_, hfinal⟩ := hfinal)
        all_goals (obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal)
        all_goals (rw [Effects.exists_done hfinal]; simp [hget, hregs])
  | rol dst c | ror dst c | rcl dst c | rcr dst c =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      split at hfinal
      · rw [Effects.exists_done hfinal]; simp [hregs]
      · split at hfinal
        · obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
          rw [Effects.exists_done hfinal]; simp [hget, hregs]
        · obtain ⟨_, hfinal⟩ := hfinal
          obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
          rw [Effects.exists_done hfinal]; simp [hget, hregs]
  | shld dst src c | shrd dst src c =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := Reg.interp_reaches src s' p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      split at hfinal
      · rw [Effects.exists_done hfinal]; simp [hregs', hregs]
      · all_goals (try obtain ⟨_, hfinal⟩ := hfinal)
        all_goals (try split at hfinal)
        all_goals (try obtain ⟨_, hfinal⟩ := hfinal)
        all_goals (try split at hfinal)
        all_goals (try obtain ⟨_, hfinal⟩ := hfinal)
        all_goals (obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal)
        all_goals (rw [Effects.exists_done hfinal]; simp [hget, hregs', hregs])
  | bswap dst =>
      simp only [Operation.interp] at hfinal
      have hne : r ≠ dst.base := Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      cases w with
      | W32 | W64 => rw [Effects.exists_done hfinal]; exact MachineData.setReg_get64_of_ne s dst _ hne
      | W8 | W16 =>
          obtain ⟨v, hfinal⟩ := hfinal
          rw [Effects.exists_done hfinal]; exact MachineData.setReg_get64_of_ne s dst _ hne
  | push src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      have hne : r ≠ Reg64.rsp := Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hregs', hstatus', hfinal⟩ := MachineData.store_reaches _ _ a _ final hfinal
      rw [Effects.exists_done hfinal]
      simp [hregs', Reg64s.get64_set64_of_ne hne, hregs]
  | pop dst =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, hfinal⟩ := MachineData.load_reaches s _ _ final hfinal
      have hr' : (r == Reg64.rsp) = false ∧
          (match dst with | .reg r' => [r'.base] | .mem _ => ([] : List Reg64)).contains r = false := by
        simpa [written_regs] using hr
      have hnersp : r ≠ Reg64.rsp := Reg64.ne_of_beq_eq_false hr'.1
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa using hr'.2)
      obtain ⟨s', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ a p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, Reg64s.get64_set64_of_ne hnersp]
  | jcc cc l =>
      simp only [Operation.interp] at hfinal
      split at hfinal <;> rw [Effects.exists_done hfinal]
  | jmp tgt =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RelRegOrMem.interp_reaches tgt s p _ final hfinal
      rw [Effects.exists_done hfinal]
      simp [hregs]
  | call tgt =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RelRegOrMem.interp_reaches tgt s p _ final hfinal
      have hne : r ≠ Reg64.rsp := Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hregs', hstatus', hfinal⟩ := MachineData.store_reaches _ _ _ _ final hfinal
      rw [Effects.exists_done hfinal]
      simp [hregs', Reg64s.get64_set64_of_ne hne, hregs]
  | ret =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, hfinal⟩ := MachineData.load_reaches s _ _ final hfinal
      have hne : r ≠ Reg64.rsp := Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      rw [Effects.exists_done hfinal]
      simp [Reg64s.get64_set64_of_ne hne]
  | nop n | nopalign n _ =>
      simp only [Operation.interp] at hfinal; rw [Effects.exists_done hfinal]

/-- `modifies_flags` is sound for every `Instr`:
running an operation it reports as not modifying the flags really does
leave `status` unchanged, for every state its execution can reach.
`next`/`jmp` are fixed to immediately finish (`Effects.done`), matching
how Kraken's own `step1` observes a single instruction's effect. -/
theorem modifies_flags_sound [Labels] (i : Instr) (p : Std.Rco Int64)
    (initial final : MachineData) (hr : modifies_flags i = false)
    (final_pc arbitrary_pc : Int64)
    (hfinal : (i.interp initial p
                   (fun s' => .done (s', arbitrary_pc))
                   (fun pc s' => .done (s', pc))).Exists (final, final_pc)) :
    final.status = initial.status := by
  cases i with
  | regular addr_sz op_sz op =>
      simp only [Instr.interp, Effects.Exists] at hfinal
      exact Operation.modifies_flags_sound (address_size := .mk addr_sz) op p initial arbitrary_pc hr
        (final, final_pc) hfinal
  | avx addr_sz op_sz op =>
      simp only [Instr.interp, Effects.Exists] at hfinal
      exact (AvxOperation.interp_reaches (address_size := .mk addr_sz) op p initial arbitrary_pc
        (final, final_pc) hfinal).2

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
  cases i with
  | regular addr_sz op_sz op =>
      simp only [Instr.interp, Effects.Exists] at hfinal
      exact Operation.written_regs_sound (address_size := .mk addr_sz) op p initial arbitrary_pc r hr
        (final, final_pc) hfinal
  | avx addr_sz op_sz op =>
      simp only [Instr.interp, Effects.Exists] at hfinal
      have hregs : final.regs = initial.regs :=
        (AvxOperation.interp_reaches (address_size := .mk addr_sz) op p initial arbitrary_pc
          (final, final_pc) hfinal).1
      rw [hregs]
