-- Common definitions shared by Example 1 and Example 2 below.

structure MachineData where
  reg : UInt64 := 0

inductive Effects
  | done (a : MachineData)

def Effects.Exists (es : Effects) (final : MachineData) : Prop :=
  match es with
  | .done result => result = final

inductive RegOrMem | reg

def RegOrMem.interp
  (o : RegOrMem) (s : MachineData)
  (ret : UInt64 → MachineData → Effects) :=
  match o with
  | .reg => ret s.reg s

theorem RegOrMem.interp_reaches
    (o : RegOrMem) (s : MachineData) (ret : UInt64 → MachineData → Effects)
    (final : MachineData) (hfinal : Effects.Exists (o.interp s ret) final) :
    ∃ (a : UInt64) (s' : MachineData), s' = s ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | reg => exact ⟨_, s, rfl, hfinal⟩

-- The one thing that differs between Example 1 and Example 2 below: whether
-- the body of the function producing `hfinal`'s type contains a `match`.
-- Both compute the exact same `Effects` value
-- (`RegOrMem.reg.interp s (fun _ s => next s)`) -- `interp_with_match` just
-- reaches it through a single-armed, otherwise-trivial `match`.

def interp_no_match (s : MachineData) (next : MachineData → Effects) : Effects :=
  RegOrMem.reg.interp s (fun _ s => next s)

inductive Trivial | mk

def interp_with_match (i : Trivial) (s : MachineData) (next : MachineData → Effects) : Effects :=
  match i with
  | .mk => RegOrMem.reg.interp s (fun _ s => next s)


-- Example 1: typecheck error inside branch of `first` gets discarded, as expected
--
-- `hfinal`'s type is headed by `interp_no_match`, whose body has no `match`.
-- Applying `RegOrMem.interp_reaches` with `_` placeholders for its first
-- four arguments now unifies immediately against `hfinal`'s type -- the
-- first `first` alternative succeeds outright, so, unlike Example 2 below,
-- there's no error here for `first` to discard in the first place.

example (s : MachineData) (final : MachineData)
    (hfinal : Effects.Exists (interp_no_match s (fun s' => .done s')) final) :
    True := by
  first
    | (dbg_trace "no match: unifies immediately, nothing to discard"
       obtain ⟨a, s', hregs, hfinal⟩ := RegOrMem.interp_reaches _ _ _ _ hfinal
       sorry)
    | dbg_trace "fell through into sorry case" <;> sorry


-- Example 2: seems to be "the same" setup, but typecheck error inside branch of `first`
-- fails the whole `first`. Unexpected!
--
-- `hfinal`'s type is headed by `interp_with_match` instead -- computing the
-- exact same `Effects` value as Example 1's `interp_no_match`, just behind
-- one extra (single-armed) `match`. That's enough to make the very same
-- `RegOrMem.interp_reaches` application fail to unify, and, unlike an
-- ordinary typecheck error, that failure isn't discarded by `first`.

example (s : MachineData) (final : MachineData)
    (hfinal : Effects.Exists (interp_with_match .mk s (fun s' => .done s')) final) :
    True := by
  first
    | (obtain ⟨a, s', hregs, hfinal⟩ :=
         RegOrMem.interp_reaches _ _ _ _ hfinal
         --                                   ^^^^^^ type error
       sorry)
    | dbg_trace "fell through into sorry case" <;> sorry
