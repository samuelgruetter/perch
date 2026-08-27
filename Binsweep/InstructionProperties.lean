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
choices reaches `final` -- so `∀ final, Effects.Exists e final → post
final.1` reads as "every state `e` can reach satisfies `post`".

TODO (now): this is a work in progress switching from an earlier
`Effects.PreservesOutside` (a direct, universally-quantified "every
resolution reaches a state satisfying `post`" predicate) to the above
`Effects.Exists`-based phrasing throughout. Only the theorem *statements*
below have been adapted so far; every proof is a placeholder `sorry`. -/

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

/-- Loading from memory hands its continuation a state whose `regs`/`status`
are unchanged (only `dmem` may differ, if the address is outside the
modeled memory). -/
theorem MachineData.load_preservesOutside {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (ret : w.type → MachineData → Effects)
    (post : MachineData → Prop)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret a s') final → post final.1) :
    ∀ final, Effects.Exists (MachineData.load s addr w ret) final → post final.1 := by
  sorry

/-- Storing to memory hands its continuation a state whose `regs`/`status`
are unchanged (only `dmem` differs). -/
theorem MachineData.store_preservesOutside {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (v : w.type) (ret : MachineData → Effects)
    (post : MachineData → Prop)
    (h : ∀ s', s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret s') final → post final.1) :
    ∀ final, Effects.Exists (s.store addr v ret) final → post final.1 := by
  sorry

/-- Reading a `RegOrMem` operand hands its continuation a state whose
`regs`/`status` are unchanged (only `dmem` may differ, if the read went to
an address outside the modeled memory). -/
theorem RegOrMem.interp_preservesOutside {w : Width} [Labels] [AddressSize]
    (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret a s') final → post final.1) :
    ∀ final, Effects.Exists (o.interp s p ret) final → post final.1 := by
  sorry

/-- Reading an `Operand` hands its continuation a state whose
`regs`/`status` are unchanged. -/
theorem Operand.interp_preservesOutside {w : Width} [Labels] [AddressSize]
    (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret a s') final → post final.1) :
    ∀ final, Effects.Exists (o.interp s p ret) final → post final.1 := by
  sorry

/-- Reading a plain `Reg` (as opposed to a `RegOrMem`/`Operand`) never
touches memory, so it hands its continuation back the very same state. -/
theorem Reg.interp_preservesOutside {w : Width} (reg : Reg w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret a s') final → post final.1) :
    ∀ final, Effects.Exists (reg.interp s p ret) final → post final.1 := by
  sorry

/-- Reading a `RelRegOrMem` (the target of a `jmp`/`call`) hands its
continuation a state whose `regs`/`status` are unchanged. -/
theorem RelRegOrMem.interp_preservesOutside [Labels] [AddressSize]
    (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
    (ret : BitVec 64 → MachineData → Effects) (post : MachineData → Prop)
    (h : ∀ (a : BitVec 64) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret a s') final → post final.1) :
    ∀ final, Effects.Exists (o.interp s p ret) final → post final.1 := by
  sorry

/-- Writing a `Dst` never changes the flags, whether it lands in a register
or in memory. -/
theorem MachineData.set_status_preservesOutside {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (post : MachineData → Prop)
    (h : ∀ s', s'.status = s.status → ∀ final, Effects.Exists (ret s') final → post final.1) :
    ∀ final, Effects.Exists (MachineData.set s d v p ret) final → post final.1 := by
  sorry

/-- Writing a `Dst` can only change `regs.get64 r` when the destination is a
register whose base is `r`. -/
theorem MachineData.set_get64_of_ne {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (post : MachineData → Prop) (r : Reg64) (hd : ∀ rd, d = .reg rd → r ≠ rd.base)
    (h : ∀ s', s'.regs.get64 r = s.regs.get64 r →
      ∀ final, Effects.Exists (ret s') final → post final.1) :
    ∀ final, Effects.Exists (MachineData.set s d v p ret) final → post final.1 := by
  sorry

/-- AVX operations never touch the general-purpose registers or flags this
file reasons about (they only ever change `zmms`/`dmem`), so reading an AVX
operand hands its continuation a state whose `regs`/`status` are unchanged,
exactly like `RegOrMem.interp_preservesOutside`. Unlike GP memory reads, an
AVX read of unmapped memory is a hard `unimplemented` failure rather than a
resolvable choice, which `Effects.Exists` already treats as impossible
(no `final` it can reach). -/
theorem AvxRegOrMem.interp_preservesOutside {w : AvxWidth} [Labels] [AddressSize]
    (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop) (checkAlign : Bool)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret a s') final → post final.1) :
    ∀ final, Effects.Exists (o.interp s p ret checkAlign) final → post final.1 := by
  sorry

theorem AvxOperand.interp_preservesOutside {w : AvxWidth} [Labels] [AddressSize]
    (o : AvxOperand w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (post : MachineData → Prop) (checkAlign : Bool)
    (h : ∀ (a : w.type) (s' : MachineData), s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret a s') final → post final.1) :
    ∀ final, Effects.Exists (o.interp s p ret checkAlign) final → post final.1 := by
  sorry

/-- Writing an AVX `Dst` never touches `regs`/`status` at all: it only ever
changes `zmms` (register destination) or `dmem` (memory destination, or a
hard `unimplemented` failure on unmapped memory). -/
theorem MachineData.setAvx_preservesOutside {w : AvxWidth} [Labels] [AddressSize]
    (d : AvxDst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (post : MachineData → Prop) (checkAlign : Bool)
    (h : ∀ s', s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret s') final → post final.1) :
    ∀ final, Effects.Exists (MachineData.setAvx s d v p ret checkAlign) final → post final.1 := by
  sorry

theorem MachineData.setAvxLegacy_preservesOutside {w : AvxWidth} [Labels] [AddressSize]
    (d : AvxDst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (post : MachineData → Prop) (checkAlign : Bool)
    (h : ∀ s', s'.regs = s.regs → s'.status = s.status →
      ∀ final, Effects.Exists (ret s') final → post final.1) :
    ∀ final, Effects.Exists (MachineData.setAvxLegacy s d v p ret checkAlign) final → post final.1 := by
  sorry

/-- `AvxOperation.interp` never touches `regs`/`status`. -/
theorem AvxOperation.preservesOutside [Labels] [address_size : AddressSize] {w : AvxWidth}
    (op : AvxOperation w) (p : Std.Rco Int64) (s : MachineData) (post : MachineData → Prop)
    (hpost : ∀ s' : MachineData, s'.regs = s.regs → s'.status = s.status → post s') :
    ∀ final, Effects.Exists
      (AvxOperation.interp op p s (fun s' => .done (s', (0 : Int64)))) final → post final.1 := by
  sorry

/-- `Reg64`'s derived `BEq` is decided pointwise, so a failed comparison
witnesses disequality -- proved once here by brute-force case split, since
that avoids relying on a `LawfulBEq Reg64` instance being available to
`simp`. -/
theorem Reg64.ne_of_beq_eq_false {a b : Reg64} (h : (a == b) = false) : a ≠ b := by
  cases a <;> cases b <;> first | decide | exact absurd h (by decide)

/-- `modifies_flags` is a sound over-approximation of `Operation.interp`:
running an operation it reports as not modifying the flags really does
leave `status` unchanged, for every state its execution can reach.
`next`/`jmp` are fixed to immediately finish (`Effects.done`), matching
how Kraken's own `step1` observes a single instruction's effect. -/
theorem Operation.modifies_flags_sound [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData)
    (h : modifies_flags (.regular address_size.address_size w op) = false) :
    ∀ final, Effects.Exists
        (Operation.interp op p s (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc)))
        final →
      final.1.status = s.status := by
  sorry

/-- `written_regs` is a sound over-approximation of `Operation.interp`:
running an operation can only change `regs.get64 r` for a register `r`
it reports as written. Same setup as `modifies_flags_sound` (`next`/`jmp`
fixed to `Effects.done`). -/
theorem Operation.written_regs_sound [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData) (r : Reg64)
    (hr : (written_regs (.regular address_size.address_size w op)).contains r = false) :
    ∀ final, Effects.Exists
        (Operation.interp op p s (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc)))
        final →
      final.1.regs.get64 r = s.regs.get64 r := by
  sorry

/-- `modifies_flags` is sound for every `Instr`: `.regular` instructions are
covered by `Operation.modifies_flags_sound`, and `.avx` instructions never
touch the flags at all. -/
theorem Instr.modifies_flags_sound [Labels] (i : Instr) (p : Std.Rco Int64) (s : MachineData)
    (h : modifies_flags i = false) :
    ∀ final, Effects.Exists
        (i.interp s p (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc))) final →
      final.1.status = s.status := by
  sorry

/-- `written_regs` is sound for every `Instr`: `.regular` instructions are
covered by `Operation.written_regs_sound`, and `.avx` instructions never
touch any general-purpose register. -/
theorem Instr.written_regs_sound [Labels] (i : Instr) (p : Std.Rco Int64) (s : MachineData)
    (r : Reg64) (hr : (written_regs i).contains r = false) :
    ∀ final, Effects.Exists
        (i.interp s p (fun s' => .done (s', (0 : Int64))) (fun pc s' => .done (s', pc))) final →
      final.1.regs.get64 r = s.regs.get64 r := by
  sorry
