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

/-- `modifies_flags` is a sound over-approximation of `Operation.interp`:
running an operation it reports as not modifying the flags really does
leave `status` unchanged, for every state its execution can reach.
`next`/`jmp` are fixed to immediately finish (`Effects.done`), matching
how Kraken's own `step1` observes a single instruction's effect. -/
theorem Operation.modifies_flags_sound [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData)
    (h : modifies_flags (.regular address_size.address_size w op) = false)
    (final : MachineState)
    (hfinal : Effects.Exists
        (Operation.interp op p s (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc)))
        final) :
    final.1.status = s.status := by
  cases op with
  | mov dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      obtain ⟨s'', hstatus', hfinal⟩ := MachineData.set_reaches_status dst s' a p _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'.trans hstatus
  | movsx dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      obtain ⟨s'', hstatus', hfinal⟩ := MachineData.set_reaches_status dst s' _ p _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'.trans hstatus
  | movzx dst src =>
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
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      obtain ⟨s'', hstatus', hfinal⟩ := MachineData.set_reaches_status dst s' _ p _ final hfinal
      rw [Effects.exists_done hfinal]
      exact hstatus'.trans hstatus
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
  | nop n => simp only [Operation.interp] at hfinal; rw [Effects.exists_done hfinal]
  | nopalign a b => simp only [Operation.interp] at hfinal; rw [Effects.exists_done hfinal]

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
  cases op with
  | mov dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst s' a p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs]
  | movsx dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst s' _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs]
  | movzx dst src =>
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
  | add dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := RegOrMem.interp_reaches dst s' p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs', hregs]
  | adc dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := RegOrMem.interp_reaches dst s' p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs', hregs]
  | sub dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := Operand.interp_reaches src s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := RegOrMem.interp_reaches dst s' p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs', hregs]
  | sbb dst src =>
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
  | mul src =>
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
  | imul1 src =>
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
  | and dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := Operand.interp_reaches src s' p _ final hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs', hregs]
  | or dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := Operand.interp_reaches src s' p _ final hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs', hregs]
  | xor dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := Operand.interp_reaches src s' p _ final hfinal
      obtain ⟨_, hfinal⟩ := hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s''', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs', hregs]
  | not dst =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst s' _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs]
  | inc dst =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs]
  | dec dst =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs]
  | neg dst =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches dst s p _ final hfinal
      have hne : ∀ rd, dst = .reg rd → r ≠ rd.base := fun rd hrd => by
        subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      obtain ⟨s'', hget, hfinal⟩ := MachineData.set_get64_of_ne dst _ _ p _ r hne final hfinal
      rw [Effects.exists_done hfinal]
      simp [hget, hregs]
  | adcx dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := Reg.interp_reaches dst s' p _ final hfinal
      have hne : r ≠ dst.base := Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      rw [Effects.exists_done hfinal]
      simp [Reg64s.get64_set_of_ne dst _ hne, hregs', hregs]
  | adox dst src =>
      simp only [Operation.interp] at hfinal
      obtain ⟨a, s', hregs, hstatus, hfinal⟩ := RegOrMem.interp_reaches src s p _ final hfinal
      obtain ⟨b, s'', hregs', hstatus', hfinal⟩ := Reg.interp_reaches dst s' p _ final hfinal
      have hne : r ≠ dst.base := Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr)
      rw [Effects.exists_done hfinal]
      simp [Reg64s.get64_set_of_ne dst _ hne, hregs', hregs]
  | shl dst c =>
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
  | shr dst c =>
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
  | sar dst c =>
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
  | rol dst c =>
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
  | ror dst c =>
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
  | rcl dst c =>
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
  | rcr dst c =>
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
  | shld dst src c =>
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
  | shrd dst src c =>
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
  | nop n => simp only [Operation.interp] at hfinal; rw [Effects.exists_done hfinal]
  | nopalign a b => simp only [Operation.interp] at hfinal; rw [Effects.exists_done hfinal]
