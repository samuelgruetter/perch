-- Both examples below run the very same ill-typed term, `(True.intro : Nat)`,
-- inside the first alternative of the very same `first`. They differ in
-- exactly one token: the tactic used to bind it, `have` vs `obtain`.
--
-- `have` throws the typechecking error, so `first` catches it and moves on to
-- the next alternative, as expected (Example 1).
--
-- `obtain` instead *logs* the error and reports success, so `first` commits to
-- the alternative that just failed. The next alternative is never tried, yet
-- the logged error still fails the build (Example 2). Unexpected!
--
-- No definitions of our own are needed to trigger this; the ill-typed term can
-- be anything. `obtain`'s payload doesn't have to be destructured either -- the
-- plain name pattern `obtain x :=` used below is enough.

-- Example 1: typecheck error inside branch of `first` gets discarded, as expected

example : True := by
  first
    | (have x := (True.intro : Nat)
       trivial)
    | dbg_trace "fell through into sorry case" <;> sorry


-- Example 2: seems to be "the same" setup, but typecheck error inside branch
-- of `first` fails the whole `first`. Unexpected!

example : True := by
  first
    | (obtain x := (True.intro : Nat)
       trivial)
    | dbg_trace "fell through into sorry case" <;> sorry


-- Note: `obtain` does not *always* swallow the error this way, which is why
-- earlier versions of this file had an Example 1 that used `obtain` and still
-- got discarded correctly. When the argument's actual type and its expected
-- type share a head symbol and the expected one still has unassigned
-- metavariables (e.g. passing `hs : s = s` for `s : String` where `?a = ?b`
-- over `Nat` is expected), the mismatch is thrown and `first` discards it as
-- in Example 1. It is the mismatches that `obtain` reports as success --
-- like the one above -- that escape `first`.
