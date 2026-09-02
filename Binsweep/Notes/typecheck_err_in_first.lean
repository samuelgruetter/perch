import Binsweep.InstructionProperties

inductive Shape
  | square (side : Nat)
  | circle (radius : Nat)

def Shape.thing : Shape → Type
  | .square _ => Nat
  | .circle _ => Bool

theorem reads_nat (n : Nat) (hn : n = n) : ∃ m, m = n := ⟨n, hn⟩
theorem reads_bool (b : Bool) (hb : b = b) : ∃ m, m = b := ⟨b, hb⟩

axiom foo {α} : α → α
axiom elim_foo {α} (x : α) : foo x = x

-- Example 1: typecheck error inside branch of `first` gets discarded, as expected

example (sh : Shape) (w : sh.thing) (hn : w = foo w) : ∃ y : sh.thing, y = w := by
  cases sh <;>
    first
    | (rw [elim_foo] at hn
       -- if we're in the .circle case, the line below does not typecheck,
       -- but, as expected, this error gets discarded by the surrounding `first`,
       -- and we fall through into the next case
       obtain ⟨m, hn⟩ := reads_nat (hn := hn)
       exact ⟨m, hn⟩)
 -- .circle case:
 -- | (rw [elim_foo] at hn
 --    obtain ⟨m, hn⟩ := reads_bool (hb := hn)
 --    exact ⟨m, hn⟩)
    | dbg_trace "fell through into sorry case" <;> sorry


-- Example 2: seems to be "the same" setup, but typecheck error inside branch of `first`
-- fails the whole `first`. Unexpected!

example [Labels] [address_size : AddressSize] {w : Width}
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData) (arbitrary_pc : Int64) (r : Reg64)
    (hr : (written_regs (.regular address_size.address_size w op)).contains r = false)
    (final : MachineState)
    (hfinal : Effects.Exists
        (Operation.interp op p s (fun s' => .done (s', arbitrary_pc)) (fun pc s' => .done (s', pc)))
        final) :
    final.1.regs.get64 r = s.regs.get64 r := by
  cases op <;>
    first
    | (--trace_state
       --simp only [Operation.interp] at hfinal
       --trace_state
       obtain ⟨a, s', hregs, hstatus, hfinal⟩ :=
         RegOrMem.interp_reaches (final := final) (hfinal := hfinal) (s := s) (p := p) (o := _) (ret := _)
         --                                                  ^^^^^^ type error
       sorry)
    -- The correct, fully-proven recipe for `mov` (and only `mov`).
    | (simp only [Operation.interp] at hfinal
       obtain ⟨a, s', hregs, hstatus, hfinal⟩ :=
         Operand.interp_reaches (final := final) (hfinal := hfinal) (s := s) (p := p) (o := _) (ret := _)
       obtain ⟨s'', hget, hfinal⟩ :=
         MachineData.set_get64_of_ne (final := final) (hfinal := hfinal) (s := _) (p := p) (d := _) (v := _)
           (r := r) (ret := _)
           (hd := fun rd hrd => by subst hrd; exact Reg64.ne_of_beq_eq_false (by simpa [written_regs] using hr))
       rw [Effects.exists_done hfinal]
       simp [hget, hregs])
    | sorry
