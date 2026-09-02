-- A tiny "database of persons" domain, used to illustrate an elaboration
-- quirk: a typecheck error inside one branch of `first` sometimes gets
-- discarded, as expected (Example 1), but an error produced the exact
-- same way -- applying a lemma to a hypothesis via `_` placeholders --
-- sometimes escapes `first` entirely instead (Example 2). Unexpected!

-- Example 1: typecheck error inside branch of `first` gets discarded, as expected

inductive Field | age | name

def Field.type : Field → Type
  | .age => Nat
  | .name => String

theorem reads_age (n : Nat) (h : n = n) : ∃ m, m = n := ⟨n, h⟩

example (f : Field) (v : f.type) (hv : v = v) : ∃ y : f.type, y = v := by
  cases f <;>
    first
    | (obtain ⟨m, hm⟩ := reads_age (h := hv)
       exact ⟨m, hm⟩)
    -- .name case: `hv : v = v` for `v : String`, but `reads_age` only
    -- accepts `n = n` for `n : Nat` -- a typecheck error, but one `first`
    -- discards cleanly, falling through to the line below.
    | dbg_trace "fell through into sorry case" <;> sorry


-- Example 2: seems to be "the same" setup, but typecheck error inside branch
-- of `first` fails the whole `first`. Unexpected!

structure Database where
  age : Nat := 0

inductive Outcome
  | done (db : Database)

def Holds (o : Outcome) (final : Database) : Prop :=
  match o with
  | .done result => result = final

inductive Column | age

def Column.interp
    (c : Column) (db : Database) (ret : Nat → Database → Outcome) : Outcome :=
  match c with
  | .age => ret db.age db

theorem Column.interp_reaches
    (c : Column) (db : Database) (ret : Nat → Database → Outcome)
    (final : Database) (h : Holds (c.interp db ret) final) :
    ∃ (a : Nat) (db' : Database), db' = db ∧
      Holds (ret a db') final := by
  cases c with
  | age => exact ⟨_, db, rfl, h⟩

-- The one supported "command": look up the age column. Applying
-- `Column.interp_reaches` to `h` below requires unifying against
-- `lookup.interp db ret`, which only reduces through this `match`.
inductive Command | lookup

def lookup (c : Command) (db : Database) (next : Database → Outcome) : Outcome :=
  match c with
  | .lookup => Column.age.interp db (fun _ db => next db)

example (db : Database) (final : Database)
    (h : Holds (lookup .lookup db (fun db' => .done db')) final) : True := by
  first
    | (obtain ⟨a, db', hdb, h⟩ :=
         Column.interp_reaches _ _ _ _ h
         --                              ^^^^^^ type error
       sorry)
    | dbg_trace "fell through into sorry case" <;> sorry
