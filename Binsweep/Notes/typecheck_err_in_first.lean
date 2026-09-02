-- Examples 1 and 2 run the very same ill-typed term, `(True.intro : Nat)`,
-- inside the first alternative of the very same `first`. They differ in
-- exactly one token: the tactic used to bind it, `have` vs `obtain`.
--
-- `have` fails, so `first` discards the error and moves on to the next
-- alternative, as expected (Example 1).
--
-- `obtain` does not fail. It recovers from the error, binding `x` to a
-- placeholder, and carries on -- so `first` commits to the alternative that
-- just went wrong, never tries the next one, and the error is still reported
-- and fails the build (Example 2). Unexpected!
--
-- Each alternative below traces where it got to, which is what shows the
-- difference is "did the tactic fail?" rather than anything about the error
-- itself. Running `lake build` prints, from Example 1 and Example 2:
--
--   fell through into sorry case            <- Example 1: `have` failed
--   reached the tactic after the error      <- Example 2: `obtain` did not
--
-- Note the two are exclusive: Example 1 never reaches the tactic after the
-- error, and Example 2 never falls through.

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
