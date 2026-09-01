/-!
# `sorry` inside one `first` alternative disables backtracking entirely

Discovered while trying to finish `Operation.written_regs_sound`'s
`imul` case with a bare `cases op <;> first | recipe1 | recipe2 | ...`
proof (see `b12.md`'s outcome): dropping a `sorry` into *one*
alternative of a `first` combinator, when that alternative's earlier
steps fail with a genuine type error for some other goal, does not
make `first` backtrack to the next alternative for that goal the way
it normally would. Instead the type error is reported directly and
**no later alternative is ever tried, for any goal** handled by that
same `cases ... <;> first ...` -- not just the one whose own attempt
at the sorry'd alternative happens to reach the `sorry`.

This file is intentionally **not** imported from `Binsweep.lean`, so
none of the code below (all of it kept inside doc comments, since none
of it is meant to compile) is part of `lake build`. The point of this
note is to document the failure, not to demonstrate it live; if you
want to see it for yourself, copy the fenced blocks below out to a
scratch `.lean` file (with `import Binsweep.InstructionProperties` at
the top) and run `lake env lean` on it.

## A working baseline

`Operation.modifies_flags_sound` in `Binsweep/InstructionProperties.lean`
already does exactly this shape of proof across all 43 `Operation`
constructors -- a bare `cases op <;> first | recipe1 | recipe2 | ...`
with no constructor names anywhere -- and `lake build` proves it
compiles cleanly with zero `sorry`s. Whichever recipe doesn't apply to
a given goal fails with a type mismatch there, `first` discards it,
and the next one is tried, exactly as you'd expect. The same shape
also works fine in isolation, e.g. on a two-constructor toy type with
no Kraken/Binsweep dependencies at all:

```
inductive Shape
  | square (side : Nat)
  | circle (radius : Nat)

def Shape.thing : Shape → Type
  | .square _ => Nat
  | .circle _ => Bool

theorem reads_nat (n : Nat) (_ : n = n) : ∃ m, m = n := ⟨n, rfl⟩

example (sh : Shape) (w : sh.thing) (h : w = w) : (1 : Nat) = 1 := by
  cases sh <;>
    first
    -- Only applies to `square`, where `w : Nat`; for `circle`,
    -- `w : Bool` and the `reads_nat _ h` call fails outright.
    | (obtain ⟨m, hm⟩ := reads_nat _ h
       rfl)
    | rfl
```

This one *does* type-check as written (both branches close: `square`
via the first recipe, `circle` by falling through to the second).
Interestingly, replacing rfl in the first branch with `sorry` still
does *not* reproduce the bug here -- backtracking still finds the
second `rfl` for `circle`. Whatever triggers the corruption below
needs more going on than a single non-dependent lemma application;
every reproduction found involved a chain of `obtain`s against named
arguments (`(final := final) (hfinal := hfinal) (x := _) ...`, see
`b12.md`'s outcome for why that shape is used at all) feeding into
each other, plus a return type that isn't trivially provable
(`True`/`rfl` goals didn't reproduce it either -- only a real
`final.1.status = s.status`-shaped conclusion did). That suggests the
underlying issue is Lean deferring some part of elaborating the
`obtain` chain until the whole `first`-branch's proof term is
otherwise complete, at which point it's too late for `first` to
backtrack -- but this is a guess, not something traced into Lean's
elaborator.

## The bug, illustrated

Take a proof shape like `Operation.modifies_flags_sound`'s, but make
one recipe genuinely incomplete (`sorry` after its own `obtain`
succeeds) instead of fully proving it, and put a fully-correct,
unrelated second recipe after it:

```
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
    -- Pretend this is the recipe for `imul`: it obtains successfully
    -- for `imul`'s own goal (closing it via the `sorry`), but for
    -- every *other* goal the `RegOrMem.interp_reaches` call below
    -- fails with a genuine type mismatch, exactly as it should.
    | (simp only [Operation.interp] at hfinal
       obtain ⟨a, s', hregs, hstatus, hfinal⟩ :=
         RegOrMem.interp_reaches (final := final) (hfinal := hfinal) (s := s) (p := p) (o := _) (ret := _)
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
```

Running that produces, for `mov`'s own goal (and every other
constructor `RegOrMem.interp_reaches` doesn't apply to):

```
error: Application type mismatch: The argument
  hfinal
has type
  (src.interp s p fun val s => s.set dst val p fun s' => Effects.done (s', arbitrary_pc)).Exists final
but is expected to have type
  (RegOrMem.interp ?m s p ?m).Exists final
in the application
  RegOrMem.interp_reaches ?m s p ?m final hfinal
```

even though the *second* recipe is exactly the proof that closes
`mov`'s goal correctly (it's the real, committed recipe for `mov` from
`Operation.modifies_flags_sound`, and it type-checks completely on its
own, outside this `first`). `first` never even tries it: as soon as
one branch anywhere in the combinator contains a `sorry`, none of
`first`'s branches backtrack past a genuine failure for *any* goal
being handled by that `cases ... <;> first ...` -- whether or not that
goal's own attempt ever reaches the `sorry`.

## An attempted fix: `axiom TODO : False` + `cases TODO`

The natural workaround is to replace the bare `sorry` with something
that isn't literally the `sorry` elaborator hook -- e.g. an opaque
`False` axiom, discharged via `cases`:

```
axiom TODO : False

-- ... same proof as above, but the first recipe ends in `cases TODO`
-- instead of `sorry`.
```

This does **not** fix it. Swapping `sorry` for `cases TODO` in the
example above still leaves the second recipe untried for every wrong
goal (`RegOrMem.interp_reaches` fails exactly as before, and `first`
still doesn't move on) -- and it also makes elaboration noticeably
slower (well over a minute rather than a few seconds for the same
43-case `cases op`, presumably because `cases TODO` re-elaborates a
fresh `False.elim`-shaped proof term per goal where `sorry` reuses a
single `sorryAx` application). So the axiom trick doesn't help here;
this is left as a documented dead end rather than a working recipe.

## Takeaway

Don't leave a `sorry` inside one alternative of a `first` that's
shared across many goals via `cases ... <;> first ...` (or any other
`<;>`-driven fan-out): if even one of those goals' attempts at that
alternative fails *before* reaching the `sorry`, the entire `first`
stops backtracking for every goal, not just that one. A `sorry`
belongs either in its own theorem (not sharing a `first` with anything
that needs to keep working), or nowhere in the file until every
alternative it shares a `first` with is fully proven. -/
