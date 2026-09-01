import Kraken.X64.Syntax

-- Some of these extra instructions might eventually make it into
-- the main Kraken repo, but probably not all: For instance,
-- forcing all Kraken users to thread MPK-related state through
-- their proofs does not seem appropriate.

inductive ExtraInstr
  | int (_ : UInt8)
  | endbr32 -- encoded as "F3 0F 1E FB" (LSB first), not used by Binsweep
  | endbr64 -- encoded as "F3 0F 1E FA" (LSB first), used by Binsweep
  -- TODO (later): add wrpkru and rdpkru

-- similar to Kraken's Directive, but for binaries instead of assembly,
-- and also allowing ExtraInstr
inductive Command
  | instr (_ : Instr)
  | extra (_ : ExtraInstr)

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
