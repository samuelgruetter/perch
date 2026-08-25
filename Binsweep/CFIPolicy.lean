import Kraken.X64.Syntax

/-!
Implements the CFI policy described in sections 3.3 and 4.3 of the
Binsweep paper (https://dl.acm.org/doi/10.1145/3689938.3694778),
in functional style rather than as a state machine.
-/

def MAGIC: UInt32 := 0x05E1F00D

abbrev InstrId := Nat

structure InstrNode where
  instr: Instr
  predecessors: List InstrId

abbrev Graph := List InstrNode

def acceptable_instr (_instr: Instr) : Bool :=
  -- TODO (later) check that the instruction uses no forbidden prefix or segment override
  true

-- TODO (later) in general, what register widths are used/acceptable?

def get_acceptable_instr (g : Graph) (idx : InstrId)
  (check : Instr → List InstrId → Bool) : Bool :=
  match g[idx]? with
  | .some (InstrNode.mk instr predecessors) =>
      acceptable_instr instr && check instr predecessors
  | .none => false

-- non-empty forall
def neForall {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  !xs.isEmpty && xs.all p

-- TODO (now) termination: Some of the functions call themselves recursively, so the check might run into an infinite recursion if the control-flow graph contains a cycle. Therefore, binsweep uses a hard iteration cutoff at 48 instructions. So, when implementing the recursive functions in Lean, we will add an argument (fuel: Nat) to each function, which decreases by 1 in each recursive call, and we reject if the fuel reaches 0.

def find_target_origin (g : Graph) (idx : InstrId)
  (target : Reg .W32) (target_read_src : Operand .W32) : Bool :=
  get_acceptable_instr g idx fun instr _predecessors =>
    (instr.iclass == .LEA && instr.operands == [.reg target .W32, target_read_src]) ||
    (instr.iclass == .MOV && instr.operands == [target_read_src, deref_reg target]) ||
    (instr.iclass == .MOV && instr.operands == [deref_reg target, target_read_src])

def find_target_read (g : Graph) (idx : InstrId)
  (target: Reg)(check_register: Reg) : Bool :=
  get_acceptable_instr g idx fun instr predecessors =>
    instr.iclass == .MOV && instr.operands == [.reg check_register .W32, deref_reg target] ||
    if instr.iclass = MOV &&
        match instr.operands with
        | [.reg tgt .W32, src] => check_register g[i].source_operand.is_memory() then
        NEForall j in g[i].predecessors, find_target_origin g j target g[i].source_operand
    else
        (g[i] is allowed and does not modify target or check_register &&
         NEForall j in g[i].predecessors, find_target_read g j target check_register)

def find_add(g: Graph)(i: InstrId)(target: Reg) :=
    acceptable_instr g[i] &&
    if instr.iclass = ADD && g[i].register_width = 32 && g[i].source_operand == MAGIC then
        let check_register := g[i].target_register in
        NEForall j in g[i].predecessors, find_target_read g j target check_register
    else if g[i] copies another register into target then
        NEForall j in g[i].predecessors, find_add g j g[i].source_operand
    else
        (g[i] is allowed and does not modify target and does not modify condition flags &&
         NEForall j in g[i].predecessors, find_add g j target)

def find_branch(g: Graph)(i: InstrId)(target: Reg) :=
    acceptable_instr g[i] &&
    if instr.iclass is JZ or JNZ && its failure path reaches INT3 then
        NEForall j in g[i].predecessors, find_add g j target
    else if instruction copies another register into target then
        NEForall j in g[i].predecessors, find_branch g g[i].source_operand
    else
        (g[i] is allowed and does not modify target &&
        NEForall j in g[i].predecessors, find_branch g target)

def cfi_check (g: Graph) (i: InstrId) :=
    acceptable_instr g[i] &&
    instr.iclass is CALL or JMP &&
    g[i].register_width = 64 &&
    NEForall j in g[i].predecessors, find_branch g j g[i].target_register
