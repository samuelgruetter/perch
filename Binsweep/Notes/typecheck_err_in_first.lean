/-
I am trying to use `first` to write a proof script to apply to a big
case distinction, where each of the many cases can be solved by one
of a small number of recipes.
For this to work, I need the following to hold:

> If one branch of `first` produces a typing error, the next branch is tried.

This holds in Example 1, but not in Example 2 (which fails with a type mismatch
error).

Actual behavior of Example 2: It prints

```
reached the tactic after the error
```

Desired behavior of Example 2: It should print the same as Example 1, i.e.

```
fell through into sorry case
declaration uses `sorry`
```

Lean version: leanprover/lean4:nightly-2026-08-02

Full context and minimization history: https://github.com/samuelgruetter/perch/commits/typecheck-err-in-first/
-/
-- Example 1: typecheck error inside branch of `first` gets discarded, as expected

example : True := by
  first
    | (have x := (True.intro : Nat)
       dbg_trace "reached the tactic after the error"
       trivial)
    | dbg_trace "fell through into sorry case" <;> sorry


-- Example 2: seems to be "the same" setup, but typecheck error inside branch
-- of `first` fails the whole `first`. Unexpected!

example : True := by
  first
    | (obtain x := (True.intro : Nat)
       dbg_trace "reached the tactic after the error"
       trivial)
    | dbg_trace "fell through into sorry case" <;> sorry


-- Additional analysis:

-- The recovery in Example 2 is visible without any `first` at all: the tactic
-- after the failing `obtain` runs, and `x` is in context with a placeholder
-- type `?m...` rather than the `Nat` that was asked for.

example : True := by
  obtain x := (True.intro : Nat)
  trace_state
  trivial


-- Examples 3 and 4: `obtain` does not always recover, and it is not obvious
-- when it does. Both pass an argument of the wrong type to a function whose
-- expected type shares its head symbol with the argument's actual type (`Eq`
-- resp. `List`) and still contains unassigned metavariables -- yet Example 3
-- fails (so `first` discards it, like `have` above) while Example 4 recovers
-- (so the error escapes `first`, like Example 2 above). So neither "the heads
-- differ" nor "there are metavariables in the way" explains which happens; I
-- have not pinned down what does.

def usesEq {a b : Nat} (_h : a = b) : Nat := 0

-- Example 3: `obtain` fails here, so `first` discards the error, as expected

example (s : String) (hs : s = s) : True := by
  first
    | (obtain x := usesEq hs
       dbg_trace "reached the tactic after the error"
       trivial)
    | dbg_trace "fell through into sorry case" <;> sorry

def usesFin {a : Nat} (_l : List (Fin a)) : Nat := 0

-- Example 4: `obtain` recovers here, so the error escapes `first`

example (l : List String) : True := by
  first
    | (obtain x := usesFin l
       dbg_trace "reached the tactic after the error"
       trivial)
    | dbg_trace "fell through into sorry case" <;> sorry
