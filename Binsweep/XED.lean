-- Gemini-generated sketch to represent Intel XED data types.
-- TODO Connect this to the actual XED C implementation,
-- and/or use https://github.com/AeneasVerif/kraken

-- Basic x86 registers and widths
inductive Reg where
  | rax | rbx | rcx | rdx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving BEq, Repr, DecidableEq, Inhabited

inductive RegWidth where
  | w8 | w16 | w32 | w64
  deriving BEq, Repr, DecidableEq, Inhabited

-- Memory displacement and base/index modes
structure MemOp where
  base     : Option Reg
  index    : Option Reg
  scale    : Nat         -- 1, 2, 4, or 8
  disp     : Int
  segment  : Option Reg
  deriving BEq, Repr, Inhabited

-- Operand variants (matching XED operand actions/types)
inductive Operand where
  | reg (r : Reg) (width : RegWidth)
  | mem (m : MemOp) (width : RegWidth)
  | imm (val : UInt64) (width : RegWidth)
  | rel (offset : Int)
  deriving BEq, Repr, Inhabited

-- Selected XED instruction classes (ICLASS)
inductive InstClass where
  | ADD | SUB | MOV | XOR | NOP | JMP | CALL | RET | LEA
  deriving BEq, Repr, DecidableEq, Inhabited

-- Parsed prefixes (REX, VEX, EVEX, REP, etc.)
structure Prefixes where
  lock : Bool := false
  rep  : Bool := false
  repne: Bool := false
  rexW : Bool := false
  deriving BEq, Repr, Inhabited

-- The translated `xed_decoded_inst_t` structure
structure XEDDecodedInst where
  iclass   : InstClass
  operands : List Operand
  prefixes : Prefixes
  length   : Nat          -- Length in bytes (1 to 15)
  eosz     : RegWidth     -- Effective operand size
  easz     : RegWidth     -- Effective address size
  deriving BEq, Repr, Inhabited
