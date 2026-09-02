-- Inlined copy of the pieces of Kraken.X64.Syntax / Kraken.X64.Semantics /
-- Kraken.Mem / Kraken.ToBytes / Binsweep.InterpEffects / Binsweep.InstructionProperties
-- that Example 2 below needs, so that this file has no imports at all.
-- Irrelevant machinery (AVX execution, the Directive/Layout/Executable
-- layer, Mem's internal hashmap representation, the many `written_regs`/
-- `modifies_flags` soundness proofs not exercised by Example 2, ...) has
-- been dropped or replaced by a trivial stand-in, since none of that
-- affects the typechecking behavior under investigation.

inductive Width | W8 | W16 | W32 | W64 deriving BEq, DecidableEq

namespace Width
@[reducible] def bits : Width → Nat | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64
@[reducible] def bytes : Width → Nat | W8 => 1 | W16 => 2 | W32 => 4 | W64 => 8
abbrev bytesv (w : Width) {n} : BitVec n := BitVec.ofNat n w.bytes
abbrev type (w : Width) : Type := BitVec w.bits
instance {w : Width} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end Width

inductive AvxWidth | W128 | W256 | W512

namespace AvxWidth
@[reducible] def bits : AvxWidth → Nat | W128 => 128 | W256 => 256 | W512 => 512
abbrev type (w : AvxWidth) : Type := BitVec w.bits
end AvxWidth

inductive RegMm
  | mm0  | mm1  | mm2  | mm3
  | mm4  | mm5  | mm6  | mm7
  | mm8  | mm9  | mm10 | mm11
  | mm12 | mm13 | mm14 | mm15
  | mm16 | mm17 | mm18 | mm19
  | mm20 | mm21 | mm22 | mm23
  | mm24 | mm25 | mm26 | mm27
  | mm28 | mm29 | mm30 | mm31

inductive Reg64
  | rax | rbx | rcx | rdx
  | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11
  | r12 | r13 | r14 | r15
  deriving BEq, DecidableEq

inductive Reg : Width → Type
  | low (_ : Reg64) (w : Width) : Reg w
  | ah : Reg .W8 | bh : Reg .W8 | ch : Reg .W8| dh : Reg .W8

namespace Reg
def base {w} (r : Reg w) : Reg64 := match r with
  | .low r _ => r
  | .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

def offset {w} (r : Reg w) : Nat := match r with
  | .low _ _ => 0
  | .ah | .bh | .ch | .dh => 8
end Reg

inductive AvxReg : AvxWidth → Type
  | xmm (_ : RegMm) : AvxReg AvxWidth.W128
  | ymm (_ : RegMm) : AvxReg AvxWidth.W256
  | zmm (_ : RegMm) : AvxReg AvxWidth.W512

abbrev Label := String

inductive ConstExpr
  | label (_ : Label)
  | int64 (_ : Int64)
  | before_current_instruction | after_current_instruction
  | add (_ _ : ConstExpr) | sub (_ _ : ConstExpr)

inductive RegOrRip where | reg (_ : Reg64) | rip : RegOrRip

structure AddrIndex where
  reg : Reg64
  scale: Width

structure AddrExpr where
  base : Option RegOrRip
  idx : Option AddrIndex
  disp : ConstExpr := .int64 0

class AddressSize where address_size : Width
export AddressSize (address_size)

inductive RegOrMem w | reg (r : Reg w) | mem (_ : AddrExpr)
abbrev Dst := RegOrMem

inductive AvxRegOrMem (w : AvxWidth) | avx (r : AvxReg w) | mem (_ : AddrExpr)
abbrev AvxDst := AvxRegOrMem

inductive Operand w | regOrMem (_ : RegOrMem w) | imm (v : ConstExpr)

inductive CondCode | z | nz | c | nc | a | be | l | le
abbrev CondCode.e := CondCode.z
abbrev CondCode.ne := CondCode.nz
abbrev CondCode.b := CondCode.c
abbrev CondCode.ae := CondCode.nc

inductive ShiftCountExpr | cl | imm8 (v : ConstExpr)

inductive RelRegOrMem | rel (_ : ConstExpr) | reg (r : Reg .W64) | mem (_ : AddrExpr)

inductive Operation (w : Width)
  -- Data movement
  | mov (_ : Dst w) (src : Operand w)
  | movsx {w'} (_ : Dst w) (src : RegOrMem w')
  | movzx {w'} (_ : Dst w) (src : RegOrMem w')
  | push (src : Operand w)
  | pop  (_ : Dst w)
  | setcc (_ : CondCode) (_ : Dst w)
  | cmovcc (_ : CondCode) (_ : Reg w) (src : RegOrMem w)
  -- Arithmetic
  | lea (_ : Reg w) (src : AddrExpr)
  | add  (_ : Dst w) (src : Operand w)
  | adc  (_ : Dst w) (src : Operand w)
  | adcx (_ : Reg w) (src : RegOrMem w)
  | adox (dst : Reg w) (src : RegOrMem w)
  | inc  (_ : RegOrMem w)
  | dec  (_ : RegOrMem w)
  | neg  (_ : RegOrMem w)
  | sub  (_ : Dst w) (src : Operand w)
  | sbb  (_ : Dst w) (src : Operand w)
  | cmp  (a : RegOrMem w) (b : Operand w)
  | mul  (src : RegOrMem w)
  | mulx (hi lo : Reg w) (src : RegOrMem w)
  | imul1 (src : RegOrMem w)
  | imul (_ : Option (Dst w)) (src1 : RegOrMem w) (src2 : Operand w)
  -- Bitwise
  | test (a : RegOrMem w) (b : Operand w)
  | and  (_ : Dst w) (src : Operand w)
  | not  (_ : Dst w)
  | or   (_ : Dst w) (src : Operand w)
  | xor  (_ : Dst w) (src : Operand w)
  | shl  (_ : Dst w) (_ : ShiftCountExpr)
  | shr  (_ : Dst w) (_ : ShiftCountExpr)
  | sar  (_ : Dst w) (_ : ShiftCountExpr)
  | shld (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr)
  | shrd (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr)
  | rol  (_ : Dst w) (_ : ShiftCountExpr)
  | ror  (_ : Dst w) (_ : ShiftCountExpr)
  | rcl  (_ : Dst w) (_ : ShiftCountExpr)
  | rcr  (_ : Dst w) (_ : ShiftCountExpr)
  | bswap  (dst : Reg w)
  -- Control flow
  | jcc (cc : CondCode) (target : Label)
  | jmp (target : RelRegOrMem)
  | call (target : RelRegOrMem)
  | ret
  | nop (length : Nat)
  | nopalign (alignment : Nat) (pad : Option Nat)

-- The non-v* variants take SSE registers only. AVX execution isn't
-- exercised by Example 2, so `AvxOperation`/`Instr` only need to exist as
-- types (for `written_regs`'s `.avx` case below), not to have an `.interp`.
inductive AvxOperation (w : AvxWidth)
  | movups (_ : AvxDst w) (src : AvxRegOrMem w)
  | vmovups (_ : AvxDst w) (src : AvxRegOrMem w)
  | movaps (_ : AvxDst w) (src : AvxRegOrMem w)
  | subps (_ : AvxDst w) (src : AvxRegOrMem w)
  | addps (_ : AvxDst w) (src : AvxRegOrMem w)

inductive Instr
  | regular (address_size : Width) (operation_size : Width) (operation : Operation operation_size)
  | avx (address_size : Width) (operation_size : AvxWidth) (operation : AvxOperation operation_size)

/-- The base registers written by `instr` (copied from
`Binsweep.InstructionProperties`). -/
def written_regs (instr : Instr) : List Reg64 :=
  match instr with
  | .avx .. => []
  | .regular _ _ op =>
    match op with
    | .mov dst _ | .add dst _ | .adc dst _ | .sub dst _ | .sbb dst _
    | .and dst _ | .or dst _ | .xor dst _ | .not dst
    | .shl dst _ | .shr dst _ | .sar dst _
    | .rol dst _ | .ror dst _ | .rcl dst _ | .rcr dst _
    | .shld dst _ _ | .shrd dst _ _
    | .inc dst | .dec dst | .neg dst
    | .movsx dst _ | .movzx dst _ =>
        match dst with | .reg r => [r.base] | .mem _ => []
    | .setcc _ dst =>
        match dst with | .reg r => [r.base] | .mem _ => []
    | .imul (some dst) _ _ =>
        match dst with | .reg r => [r.base] | .mem _ => []
    | .imul none src1 _ =>
        match src1 with | .reg r => [r.base] | .mem _ => []
    | .lea r _ | .cmovcc _ r _ | .bswap r | .adcx r _ | .adox r _ =>
        [r.base]
    | .mulx hi lo _ => [hi.base, lo.base]
    | .mul _ | .imul1 _ => [.rax, .rdx]
    | .pop dst =>
        .rsp :: match dst with | .reg r => [r.base] | .mem _ => []
    | .push _ | .call _ | .ret => [.rsp]
    | .test _ _ | .cmp _ _ | .jcc _ _ | .jmp _ | .nop _ | .nopalign _ _ => []

-- A drastically simplified stand-in for `Kraken.Mem`'s `ExtHashMap`-backed
-- memory (only `loadInt`/`storeInt`/`∅` are used below, and their actual
-- contents never matter for the typechecking bug being investigated).
abbrev Mem (w : Nat) : Type := List (BitVec w × UInt8)
instance {w} : EmptyCollection (Mem w) where emptyCollection := []
def Mem.get? {w} (m : Mem w) (a : BitVec w) : Option UInt8 :=
  (m.find? (fun p => p.1 == a)).map Prod.snd
def List.allSome {α} (l : List (Option α)) : Option (List α) := l.mapM id
def Mem.loadBytes {w} (m : Mem w) (a : BitVec w) (n : Nat) : Option (List UInt8) :=
  ((List.range n).map (fun i => m.get? (a + .ofNat _ i))).allSome

abbrev Int.take (v : Int) (w : Nat) : Int := v % (2 : Int) ^ w
def Int.ofBytes (bs : List UInt8) : Int :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0
def Int.toBytes (n : Nat) (v : Int) : List UInt8 :=
  match n with
  | 0 => []
  | n' + 1 => ((v.take 8).toNat.toUInt8) :: Int.toBytes n' (v / 256)

def Mem.loadInt {w} (m : Mem w) (a : BitVec w) (n : Nat) : Option Int :=
  (Mem.loadBytes m a n).map Int.ofBytes
def List.At {w} (bs : List UInt8) (a : BitVec w) : List (BitVec w × UInt8) :=
  bs.mapIdx (fun i b => (a + .ofNat w i, b))
def Mem.storeBytes {w} (m : Mem w) (a : BitVec w) (bs : List UInt8) : Mem w :=
  bs.At a ++ m
def Mem.storeInt {w} (m : Mem w) (a : BitVec w) (n : Nat) (v : Int) : Mem w :=
  Mem.storeBytes m a (Int.toBytes n v)

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat
instance : Coe UInt64 (BitVec 64) := ⟨UInt64.toBitVec⟩

namespace BitVec
def unsigned {w} (x : BitVec w) : Int := x.toNat
def signed {w} (x : BitVec w) : Int := x.toInt
def take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
def drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)
end BitVec
def BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth _

structure Reg64s where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0

def Reg64s.get64 (s : Reg64s) (r : Reg64) : Width.W64.type := UInt64.toBitVec (match r with
  | .rax => s.rax | .rbx => s.rbx | .rcx => s.rcx | .rdx => s.rdx
  | .rsi => s.rsi | .rdi => s.rdi | .rsp => s.rsp | .rbp => s.rbp
  | .r8  => s.r8  | .r9  => s.r9  | .r10 => s.r10 | .r11 => s.r11
  | .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15)

def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : Width.W64.type) : Reg64s :=
  let  v := UInt64.ofBitVec v
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
  | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
  | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
  | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
  | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  ((s.get64 r.base).drop r.offset).take w.bits

def Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.set64 r v
  | .low r .W32 => s.set64 r (v.zeroExtend _)
  | .low r w => s.set64 r ((s.get64 r).replaceLow v)
  | .ah | .bh | .ch | .dh => let old := s.get64 r.base;
    s.set64 r.base (old.replaceLow (BitVec.append v (s.get (.low r.base .W8))))

-- The AVX register file's contents are never touched by Example 2 (only
-- non-AVX `Operation.interp` is exercised), so a field-less stand-in
-- suffices to give `MachineData` its `zmms` field a type.
structure RegZmms

def BitVec.toAddressSize [address_size: AddressSize] (w: BitVec 64): BitVec address_size.address_size.bits :=
  w.take address_size.address_size.bits

structure StatusFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool

abbrev DataMem := Mem 64
structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  zmms : RegZmms := {}
  status : StatusFlags := .mk false false false false false false
  dmem : DataMem := ∅

-- We only allow nondeterministic choices for a fixed set of types.
class inductive NondetSupportingType : Type -> Type
  | bitvec (w : Width) : NondetSupportingType w.type
  | avx_bitvec (aw : AvxWidth) : NondetSupportingType aw.type
  | bool : NondetSupportingType Bool
  | statusFlags : NondetSupportingType StatusFlags

instance (w : Width) : NondetSupportingType w.type := .bitvec w
instance (w : AvxWidth) : NondetSupportingType w.type := .avx_bitvec w
instance : NondetSupportingType Bool := .bool
instance : NondetSupportingType StatusFlags := .statusFlags

inductive Effects
  | done (a : MachineData × Int64)
  | unimplemented (msg : String)
  | gp_unaligned (addr : BitVec 64) (w : Nat)
  | nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : Width) (ret : w.type → DataMem → Effects)
  | nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : Width} (v : w.type) (ret: DataMem → Effects)
  | undefined {α : Type} [NondetSupportingType α] (ret : α → Effects)
  | require_read_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects)
  | require_write_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects)
  | require_exec_access (p: Std.Rco Int64) (ok : Unit → Effects)
export Effects (unimplemented nonmem_load nonmem_store undefined require_read_access require_write_access require_exec_access)

def MachineData.load
  (s : MachineData) (addr : BitVec 64) (w : Width)
  (ret : w.type → MachineData → Effects): Effects :=
  require_read_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i => ret (.ofInt _ i) s
    | .none => nonmem_load s.dmem addr w (fun v dmem => ret v { s with dmem }))

def MachineData.store (s : MachineData) (addr : BitVec 64) {w : Width} (v : w.type) (ret: MachineData → Effects) : Effects :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
    | .none => nonmem_store s.dmem addr v (fun dmem' => ret { s with dmem := dmem' }))

class Labels where label : Label → Int64
export Labels (label)

def ConstExpr.interp [Labels] : ConstExpr → Std.Rco _root_.Int64 → _root_.Int64
  | .label l, _ => Labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p

def AddrExpr.interp [Labels] [address_size : AddressSize] (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) :=
  let base := match a.base with
              | .some (.reg r) => (s.get64 r).toAddressSize.signed
              | .some .rip => p.upper.toInt
              | .none => 0
  let idx := match a.idx with
             | .some ⟨r, c⟩ => (s.get64 r).toAddressSize.signed * c.bytes
             | .none => 0
  BitVec.ofInt address_size.address_size.bits (base + idx + (a.disp.interp p).toInt)

def Reg.interp {w} (r : Reg w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.get r) s

def RegOrMem.interp {w} [Labels] [AddressSize]
  (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
match o with
  | .reg r => ret (s.regs.get r) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) w ret

def MachineData.setReg (s : MachineData) {w} (r : Reg w) (v : w.type) : MachineData :=
  { s with regs := s.regs.set r v }

def MachineData.set {w} [Labels] [AddressSize] (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) : Effects :=
  match d with
  | .reg r => ret (s.setReg r v)
  | .mem a => s.store ((a.interp s.regs p).zeroExtend _) v ret

def Operand.interp {w} [Labels] [AddressSize]
  (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
  match o with
  | regOrMem rm => rm.interp s p ret
  | .imm v => ret ((v.interp p).toBitVec.truncate _) s

def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .z  => s.zf | .nz => !s.zf | .c  => s.cf | .nc => !s.cf
  | .a  => !s.cf && !s.zf | .be => s.cf || s.zf
  | .l => s.sf != s.of | .le => (s.sf != s.of) || s.zf

def ShiftCountExpr.interp [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) := match c with
  | .cl => s.regs.rcx.toBitVec.take 8
  | .imm8 v => (v.interp p).toBitVec.take _
def ShiftCountExpr.interpMasked [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) (w : Width) : Nat :=
  (c.interp s p).toNat &&& match w with | .W64 => 0x3f | _ => 0x1f

def RelRegOrMem.interp [Labels] [AddressSize]
  (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
  (ret : BitVec 64 → MachineData → Effects) :=
  match o with
  | .rel c => ret (p.upper + c.interp p).toBitVec s
  | .reg r => ret (s.regs.get r) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) .W64 ret

structure StatusFlags.from_result.Remaining where
  cf : Bool
  af : Bool
  of : Bool

namespace BitVec
def cpopNatRec_ {w} (x : BitVec w) (pos acc : Nat) : Nat :=
  match pos with
  | 0 => acc
  | n + 1 => x.cpopNatRec_ n (acc + (x.getLsbD n).toNat)

def cpop_ {w} (x : BitVec w) : BitVec w := BitVec.ofNat w (cpopNatRec_ x w 0)
end BitVec

def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { pf := (result.take 8).cpop_ % 2 == BitVec.zero _
    zf := result == BitVec.zero _
    sf := result.msb, cf := f.cf, af := f.af, of := f.of }

set_option maxHeartbeats 1000000
def Operation.interp [Labels] [address_size : AddressSize]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match (generalizing := false) (motive := Operation w → Effects) i with
  | .mov dst src => src.interp s p (fun val s => s.set dst val p next)
  | .movsx dst src => src.interp s p (fun val s => s.set dst (val.signExtend _) p next)
  | .movzx dst src => src.interp s p (fun val s => s.set dst (val.zeroExtend _) p next)
  | .push src =>
    src.interp s p (fun v s =>
    let rsp := s.regs.get64 .rsp - w.bytesv
    { s with regs := s.regs.set64 .rsp rsp }.store rsp v next)
  | .pop dst =>
    let rsp := s.regs.get64 .rsp
    s.load rsp w (fun val s =>
    let s := { s with regs := s.regs.set64 .rsp (rsp + w.bytesv) }
    s.set dst val p next)
  | .setcc cc dst =>
    s.set dst (cc.interp s.status) p next
  | .cmovcc cc dst src =>
    src.interp s p (fun src s =>
    let v := if cc.interp s.status then src else s.regs.get dst
    next (s.setReg dst v))
-- Arithmetic
  | .lea dst src => next (s.setReg dst ((src.interp s.regs p).zeroExtend _))
  | .add dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b
    let status := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := v.signed != a.signed + b.signed }
    { s with status }.set dst v p next))
  | .adc dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := a + b + c
    let status := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned + c
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
      of := v.signed != a.signed + b.signed + c }
    { s with status }.set dst v p next))
  | .adcx dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.cf
    let cf := v.unsigned != a.unsigned + b.unsigned + s.status.cf
    next { s with regs := s.regs.set dst v, status := { s.status with cf := cf }}))
  | .adox dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.of
    let of := v.unsigned != a.unsigned + b.unsigned + s.status.of
    next { s with regs := s.regs.set dst v, status := { s.status with of := of }}))
  | .inc dst =>
    dst.interp s p (fun a s =>
    let v := a + 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
      of := v.signed != a.signed + 1 }
    { s with status }.set dst v p next)
  | .dec dst =>
    dst.interp s p (fun a s =>
    let v := a - 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
      of := v.signed != a.signed - 1 }
    { s with status }.set dst v p next)
  | .neg dst =>
    dst.interp s p (fun b s =>
    let v := -b
    let status := .from_result v {
      cf := b != 0
      af := (b.take 4) != 0,
      of := v.signed != - b.signed }
    { s with status }.set dst v p next)
  | .sub dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := b - a
    let status := .from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
      of := v.signed != b.signed - a.signed }
    { s with status }.set dst v p next))
  | .sbb dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := b - a - c
    let status := .from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned - c
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - c,
      of := v.signed != b.signed - a.signed - c }
    { s with status }.set dst v p next))
  | .cmp a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    let v := a - b
    let status := .from_result v {
      cf := v.unsigned != a.unsigned - b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := v.signed != a.signed - b.signed }
    next { s with status }))
  | .mul src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a * b
    let vn := a.unsigned * b.unsigned
    let s := if w == .W8
      then s.setReg (.low .rax .W16) (.ofInt _ vn)
      else (s.setReg (.low .rax w) v).setReg (.low .rdx w) (.ofInt _ (vn >>> w.bits))
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := v.unsigned != vn, pf, af, zf, sf, of := v.unsigned != vn }})))))
  | .mulx r_hi r_lo src1 =>
    src1.interp s p (fun a s =>
    let b := s.regs.get (.low .rdx w)
    let v := a.unsigned * b.unsigned
    let s := s.setReg r_lo (.ofInt _ v)
    let s := s.setReg r_hi (.ofInt _ (v >>> w.bits))
    next s)
  | .imul1 src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a.toInt * b.toInt
    let s := if w == .W8 then
      s.setReg (.low .rax .W16) (BitVec.ofInt 16 v)
    else
      let result := BitVec.ofInt (w.bits * 2) v
      let low := result.take w.bits
      let high := (result.drop w.bits).setWidth _
      (s.setReg (.low .rax w) low).setReg (.low .rdx w) high
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    let low := BitVec.ofInt w.bits v
    let cf := v != low.toInt
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))
  | .imul dst src1 src2 =>
    src1.interp s p (fun a s =>
    src2.interp s p (fun b s =>
    let v := a * b
    s.set (match (generalizing := false) (motive := Option (RegOrMem w) → RegOrMem w)
             dst with | .some dst => dst | _ => src1) v p (fun s =>
    let cf := v.signed != a.signed * b.signed
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))))
-- Bitwise
  | .test a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    let v := a &&& b
    undefined (fun af =>
    let status := .from_result v { cf := false, af, of := false}
    next { s with status})))
  | .and dst src | .or dst src | .xor dst src =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let v := match i with | .and _ _ => a &&& b | .or _ _ => a ||| b | _ => a ^^^ b
    undefined (fun af =>
    let status := .from_result v { cf := false, of := false, af }
    { s with status }.set dst v p next)))
  | .not dst =>
    dst.interp s p (fun a s =>
    let v := ~~~a
    s.set dst v p next)
  | .shl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a <<< count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a <<< (count-1)).msb else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.ushiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof a.msb else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .sar dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.sshiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof false else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shrd dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := (((b.append a) >>> count).take w.bits).setWidth _
    (λ setstatus => if count >= w.bits then undefined setstatus else
      let cf := a.getLsbD (count-1)
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    { s with status }.set dst v p next)))
  | .shld dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := (((a.append b) <<< count).drop w.bits).setWidth _
    (λ setstatus => if count >= w.bits then undefined setstatus else
      let cf := (a <<< (count-1)).msb
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    { s with status }.set dst v p next)))
  | .rol dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.rotateLeft count
    let cf := v.getLsbD 0
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .ror dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.rotateRight count
    let cf := v.msb
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateRight count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateLeft count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .bswap dst =>
    let a := s.regs.get dst
    match (generalizing := false) (motive := Width → Effects) w with
    | .W32 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24
      next (s.setReg dst (v.setWidth _))
    | .W64 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
            ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56
      next (s.setReg dst (v.setWidth _))
    | _ => undefined (fun v => next (s.setReg dst v))
  | .jcc cc l =>
    if cc.interp s.status
    then jmp (label l) s
    else next s
  | .jmp tgt =>
    tgt.interp s p (fun a s =>
    jmp (.ofBitVec a) s)
  | .call tgt =>
    tgt.interp s p (fun a s =>
    let rsp := s.regs.get64 .rsp - Width.W64.bytesv
    { s with regs := s.regs.set64 .rsp rsp }.store rsp (w:=.W64) p.upper.toBitVec (jmp (.ofBitVec a)))
  | .ret =>
    let rsp := s.regs.get64 .rsp
    s.load rsp .W64 (fun ra s =>
    jmp (.ofBitVec ra) { s with regs := s.regs.set64 .rsp (rsp + 8) })
  | nop _ | nopalign _ _ => next s

def Effects.Exists (es : Effects) (final : MachineData × Int64) : Prop :=
  match es with
  | .done result => result = final
  | .unimplemented .. => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∃ v : α, (cont v).Exists final
  | .require_read_access _ _ ok => (ok ()).Exists final
  | .require_write_access _ _ ok => (ok ()).Exists final
  | .require_exec_access _ ok => (ok ()).Exists final

abbrev MachineState := MachineData × Int64

-- The following theorems (copied from `Binsweep.InstructionProperties`)
-- are the exact chain that Example 2's first `first`-branch is trying
-- (and failing) to apply.

theorem MachineData.load_reaches {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.load s addr w ret) final) :
    ∃ (a : w.type), Effects.Exists (ret a s) final := by
  simp only [MachineData.load, Effects.Exists] at hfinal
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | some i => rw [hl] at hfinal; exact ⟨_, hfinal⟩
  | none => rw [hl] at hfinal; exact hfinal.elim

theorem RegOrMem.interp_reaches {w : Width} [Labels] [AddressSize]
    (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | reg r => exact ⟨_, s, rfl, rfl, hfinal⟩
  | mem a =>
      simp only [RegOrMem.interp] at hfinal
      obtain ⟨v, hfinal⟩ := MachineData.load_reaches s _ ret final hfinal
      exact ⟨v, s, rfl, rfl, hfinal⟩

theorem Operand.interp_reaches {w : Width} [Labels] [AddressSize]
    (o : Operand w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧ s'.status = s.status ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | regOrMem rm => exact RegOrMem.interp_reaches rm s p ret final hfinal
  | imm v => exact ⟨_, s, rfl, rfl, hfinal⟩

theorem Reg64s.get64_set64_of_ne {regs : Reg64s} {r r' : Reg64} (h : r' ≠ r) (v : UInt64) :
    (regs.set64 r v).get64 r' = regs.get64 r' := by
  cases r <;> cases r' <;> simp_all [Reg64s.set64, Reg64s.get64]

theorem Reg64s.get64_set_of_ne {w : Width} {regs : Reg64s} (rd : Reg w) (v : w.type) {r : Reg64}
    (h : r ≠ rd.base) : (regs.set rd v).get64 r = regs.get64 r := by
  cases rd with
  | low r64 _ =>
      simp only [Reg.base] at h
      cases w <;> simp only [Reg64s.set] <;> exact Reg64s.get64_set64_of_ne h _
  | ah => exact Reg64s.get64_set64_of_ne h _
  | bh => exact Reg64s.get64_set64_of_ne h _
  | ch => exact Reg64s.get64_set64_of_ne h _
  | dh => exact Reg64s.get64_set64_of_ne h _

theorem MachineData.setReg_get64_of_ne {w : Width} (s : MachineData) (rd : Reg w) (v : w.type)
    {r : Reg64} (h : r ≠ rd.base) : (s.setReg rd v).regs.get64 r = s.regs.get64 r :=
  Reg64s.get64_set_of_ne rd v h

theorem Reg64.ne_of_beq_eq_false {a b : Reg64} (h : (a == b) = false) : a ≠ b := by
  cases a <;> cases b <;> first | decide | exact absurd h (by decide)

theorem MachineData.store_reaches {w : Width} [Labels] [AddressSize]
    (s : MachineData) (addr : BitVec 64) (v : w.type) (ret : MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (s.store addr v ret) final) :
    ∃ s', s'.regs = s.regs ∧ s'.status = s.status ∧ Effects.Exists (ret s') final := by
  simp only [MachineData.store, Effects.Exists] at hfinal
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | some _ =>
      rw [hl] at hfinal
      exact ⟨{ s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }, rfl, rfl, hfinal⟩
  | none => rw [hl] at hfinal; exact hfinal.elim

theorem MachineData.set_get64_of_ne {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (r : Reg64) (hd : ∀ rd, d = .reg rd → r ≠ rd.base)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.set s d v p ret) final) :
    ∃ s', s'.regs.get64 r = s.regs.get64 r ∧ Effects.Exists (ret s') final := by
  cases d with
  | reg rd => exact ⟨_, MachineData.setReg_get64_of_ne s rd v (hd rd rfl), hfinal⟩
  | mem a =>
      simp only [MachineData.set] at hfinal
      obtain ⟨s', hregs, _, hfinal⟩ := MachineData.store_reaches s _ v ret final hfinal
      exact ⟨s', by rw [hregs], hfinal⟩

theorem Effects.exists_done {a final : MachineState} (h : Effects.Exists (.done a) final) :
    final = a := h.symm


-- Example 1: typecheck error inside branch of `first` gets discarded, as expected

inductive Shape
  | square (side : Nat)
  | circle (radius : Nat)

def Shape.thing : Shape → Type
  | .square _ => Nat
  | .circle _ => Bool

theorem reads_nat (n : Nat) (hn : n = n) : ∃ m, m = n := ⟨n, hn⟩
theorem reads_bool (b : Bool) (hb : b = b) : ∃ m, m = b := ⟨b, hb⟩

axiom foo {α} : α → α
axiom elim_foo {α} (x : α) : foo x = x

example (sh : Shape) (w : sh.thing) (hn : w = foo w) : ∃ y : sh.thing, y = w := by
  cases sh <;>
    first
    | (rw [elim_foo] at hn
       -- if we're in the .circle case, the line below does not typecheck,
       -- but, as expected, this error gets discarded by the surrounding `first`,
       -- and we fall through into the next case
       obtain ⟨m, hn⟩ := reads_nat (hn := hn)
       exact ⟨m, hn⟩)
 -- .circle case:
 -- | (rw [elim_foo] at hn
 --    obtain ⟨m, hn⟩ := reads_bool (hb := hn)
 --    exact ⟨m, hn⟩)
    | dbg_trace "fell through into sorry case" <;> sorry


-- Example 2: seems to be "the same" setup, but typecheck error inside branch of `first`
-- fails the whole `first`. Unexpected!

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
    | (--trace_state
       --simp only [Operation.interp] at hfinal
       --trace_state
       obtain ⟨a, s', hregs, hstatus, hfinal⟩ :=
         RegOrMem.interp_reaches (final := final) (hfinal := hfinal) (s := s) (p := p) (o := _) (ret := _)
         --                                                  ^^^^^^ type error
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
    | sorry
