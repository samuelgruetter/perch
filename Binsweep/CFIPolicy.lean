import Binsweep.XED

/-!
Implements the CFI policy described in sections 3.3 and 4.3 of the
Binsweep paper (https://dl.acm.org/doi/10.1145/3689938.3694778),
in functional style rather than as a state machine.
-/

def MAGIC: UInt32 := 0x05E1F00D

abbrev InstructionId := Nat

abbrev RegisterName := Reg
abbrev RegisterNameOrMemoryAddr := Operand

structure InstrNode where
  instr: XEDDecodedInst
  predecessors: List InstructionId
  deriving Inhabited

abbrev Graph := List InstrNode

def acceptable_instr (_instr: XEDDecodedInst) : Bool :=
  -- TODO check that the instruction uses no forbidden prefix or segment override
  true

-- TODO in general, what register widths are used/acceptable?

def get_acceptable_instr (g : Graph) (idx : InstructionId)
  (check : XEDDecodedInst → List InstructionId → Bool) : Bool :=
  match g[idx]? with
  | .some (InstrNode.mk instr predecessors) =>
      acceptable_instr instr && check instr predecessors
  | .none => false

-- non-empty forall
def neForall {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  !xs.isEmpty && xs.all p

def deref_reg (r : Reg) : Operand :=
  Operand.mem {
    base    := some r
    index   := none
    scale   := 0
    disp    := 0
    segment := none
  } RegWidth.w64

def find_target_origin (g : Graph) (idx : InstructionId)
  (target : RegisterName) (target_read_src : RegisterNameOrMemoryAddr) : Bool :=
  get_acceptable_instr g idx fun instr _predecessors =>
    (instr.iclass == .LEA && instr.operands == [.reg target .w32, target_read_src]) ||
    (instr.iclass == .MOV && instr.operands == [target_read_src, deref_reg target]) ||
    (instr.iclass == .MOV && instr.operands == [deref_reg target, target_read_src])

def find_target_read (g : Graph) (idx : InstructionId)
  (target: RegisterName)(check_register: RegisterName) : Bool :=
  get_acceptable_instr g idx fun instr predecessors =>
    if instr.iclass == .MOV && instr.operands == [.reg check_register .w32, .mem target .w32] then true else true
    /-
    else if g[i].mnemonic = MOV && g[i].target_register = check_register g[i].source_operand.is_memory() then
        NEForall j in g[i].predecessors, find_target_origin g j target g[i].source_operand
    else
        (g[i] is allowed and does not modify target or check_register &&
         NEForall j in g[i].predecessors, find_target_read g j target check_register)

/-

def find_add(g: Graph)(i: InstructionId)(target: RegisterName) :=
    acceptable_instr g[i] &&
    if g[i].mnemonic = ADD && g[i].register_width = 32 && g[i].source_operand == MAGIC then
        let check_register := g[i].target_register in
        NEForall j in g[i].predecessors, find_target_read g j target check_register
    else if g[i] copies another register into target then
        NEForall j in g[i].predecessors, find_add g j g[i].source_operand
    else
        (g[i] is allowed and does not modify target and does not modify condition flags &&
         NEForall j in g[i].predecessors, find_add g j target)


def find_branch(g: Graph)(i: InstructionId)(target: RegisterName) :=
    acceptable_instr g[i] &&
    if g[i].mnemonic is JZ or JNZ && its failure path reaches INT3 then
        NEForall j in g[i].predecessors, find_add g j target
    else if instruction copies another register into target then
        NEForall j in g[i].predecessors, find_branch g g[i].source_operand
    else
        (g[i] is allowed and does not modify target &&
        NEForall j in g[i].predecessors, find_branch g target)

def cfi_check (g: Graph) (i: InstructionId) :=
    acceptable_instr g[i] &&
    g[i].mnemonic is CALL or JMP &&
    g[i].register_width = 64 &&
    NEForall j in g[i].predecessors, find_branch g j g[i].target_register



### Termination

Some of the above functions call themselves recursively, so the check might run into an infinite recursion if the control-flow graph contains a cycle. Therefore, binsweep uses a hard iteration cutoff at 48 instructions. So, when implementing the recursive functions in Lean, we will add an argument (fuel: Nat) to each function, which decreases by 1 in each recursive call, and we reject if the fuel reaches 0.
-/
