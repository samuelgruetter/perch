-- Minimized, self-contained re-derivation of Kraken/Binsweep's `Operation`,
-- `MachineData`, `Effects`, etc., cut down to the bare minimum needed to
-- reproduce the "undiscarded typecheck error in `first`" phenomenon from
-- Example 2 below. No imports needed.

inductive Reg64 | rax deriving BEq, DecidableEq

structure Reg64s where
  rax : UInt64 := 0

def Reg64s.get (s : Reg64s) (r : Reg64) : UInt64 := match r with | .rax => s.rax

structure MachineData where
  regs : Reg64s := {}

inductive Effects
  | done (a : MachineData)

def Effects.Exists (es : Effects) (final : MachineData) : Prop :=
  match es with
  | .done result => result = final

inductive RegOrMem | reg (r : Reg64)

inductive Operation | not (_ : RegOrMem)

def RegOrMem.interp
  (o : RegOrMem) (s : MachineData)
  (ret : UInt64 → MachineData → Effects) :=
  match o with
  | .reg r => ret (s.regs.get r) s

def Operation.interp
  (i : Operation) (s : MachineData) (next : MachineData → Effects) : Effects :=
  match i with
  | .not dst => dst.interp s (fun _ s => next s)

theorem RegOrMem.interp_reaches
    (o : RegOrMem) (s : MachineData) (ret : UInt64 → MachineData → Effects)
    (final : MachineData) (hfinal : Effects.Exists (o.interp s ret) final) :
    ∃ (a : UInt64) (s' : MachineData), s'.regs = s.regs ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | reg r => exact ⟨_, s, rfl, hfinal⟩


-- Example 1: typecheck error inside branch of `first` gets discarded, as expected

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

example (op : Operation) (s : MachineData)
    (final : MachineData)
    (hfinal : Effects.Exists (Operation.interp op s (fun s' => .done s')) final) :
    True := by
  cases op <;>
    first
    | (obtain ⟨a, s', hregs, hfinal⟩ :=
         RegOrMem.interp_reaches (final := final) (hfinal := hfinal) (s := s) (o := _) (ret := _)
         --                                                  ^^^^^^ type error
       sorry)
    | sorry
