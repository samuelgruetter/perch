import Kraken.X64.Syntax
import Kraken.X64.Semantics
import Binsweep.InterpEffects

-- Some of these extra instructions might eventually make it into
-- the main Kraken repo, but probably not all: For instance,
-- forcing all Kraken users to thread MPK-related state through
-- their proofs does not seem appropriate.

inductive ExtraInstr
  | int (_ : UInt8)
  | endbr32 -- encoded as "F3 0F 1E FB" (LSB first), not used by Binsweep
  | endbr64 -- encoded as "F3 0F 1E FA" (LSB first), used by Binsweep
  -- TODO (later): add wrpkru and rdpkru

def ExtraInstr.interp [Labels]
  (i : ExtraInstr) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (_jmp : Int64 → MachineData → Effects) : Effects :=
  require_exec_access p (fun _unit =>
    match i with
    -- Effects.unimplemented is good enough for now to say that our
    -- statement tells us what happens if no interrupt is hit
    | .int  _ => Effects.unimplemented "INT not implemented"
    -- We model a machine where IBT (indirect branch tracking) is NOT active,
    -- i.e. ENDBR is treated as a NOP, because we want to show that the
    -- software-based CFI works even if hardware does not support IBT
    | .endbr32 => next s
    | .endbr64 => next s
  )

-- similar to Kraken's Directive, but for binaries instead of assembly,
-- and also allowing ExtraInstr
inductive Command
  | instr (_ : Instr)
  | extra (_ : ExtraInstr)

def Command.interp [Labels]
  (c : Command) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match c with
  | .instr i => i.interp s p next jmp
  | .extra i => i.interp s p next jmp

def Commands.interp [Labels]
  (cs : List (Command × Nat)) (s : MachineData) (pc : Int64)
  (ret : Int64 → MachineData → Effects) : Effects :=
  match cs with
  | [] => ret pc s
  | (c, sz) :: ds =>
    c.interp s (.mk pc (pc+.ofNat sz)) (jmp:=ret) (next := (fun s =>
    interp ds s (pc+.ofNat sz) ret))

abbrev Binary := Kraken.Executable Command

def Binary.step (b : Binary) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let : Labels := { label _l := -1 } -- dummy address because we're not using labels
  Commands.interp (b.directivesAtAddress s.2) s.1 s.2 (fun pc s => ret (s, pc))

def Binary.stepN (n : Nat) (b : Binary) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  match n with
  | 0 => ret s
  | m + 1 => Binary.step b s (fun s' => Binary.stepN m b s' ret)

def Binary.step_star (b : Binary) (initial final : MachineState) : Prop :=
  ∃ n, (Binary.stepN n b initial Effects.done).Exists final

-- Snippets copied/adapted from https://github.com/AeneasVerif/kraken/pull/156:

-- How one instruction transfers control: fall through, or jump to `target`.
inductive Ctrl : Type
  | next
  | jmp (target : Int64)
  deriving Repr, BEq, DecidableEq

-- How control leaves a list of directives. -/
inductive BlockExit : Type
  | fallthrough (next : Int64)
  | jump (target : Int64)
  deriving Repr, BEq, DecidableEq

-- With #156, signature of of Instr.interp becomes:
-- def Instr.interp [Labels] (i : Instr) (s : MachineData) (p : Std.Rco Int64) : Effects (MachineData × Ctrl)

/-
Statement in pseudocode:

forall insts s s', exec s insts s' /\ policy insts = true ->
s'.halted = true \/ fetch(s'.pc) = endbr

More precise statement but in English:

if we start at a pc that points to an endbr according to layout
and end at a pc that points to an indirect jump,
and we run one more instruction (ie the indirect jump),
then the pc now points to an endbr instruction

-/
