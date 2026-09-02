-- Minimized, self-contained re-derivation of Kraken/Binsweep's `Operation`,
-- `MachineData`, `Effects`, etc., cut down to the bare minimum needed to
-- reproduce the "undiscarded typecheck error in `first`" phenomenon from
-- Example 2 below. No imports needed.

inductive Width | W8 | W16 | W32 | W64 deriving BEq, DecidableEq

namespace Width
@[reducible] def bits : Width → Nat | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64
abbrev type (w : Width) : Type := BitVec w.bits
end Width

inductive Reg64 | rax | rbx deriving BEq, DecidableEq

inductive Reg : Width → Type
  | low (_ : Reg64) (w : Width) : Reg w

namespace Reg
def base {w} (r : Reg w) : Reg64 := match r with | .low r _ => r
end Reg

class AddressSize where address_size : Width
class Labels where label : String → Int64

inductive RegOrMem (w : Width) | reg (r : Reg w)
abbrev Dst := RegOrMem

inductive Operand (w : Width) | regOrMem (_ : RegOrMem w)

inductive Operation (w : Width)
  | mov (_ : Dst w) (src : Operand w)
  | not (_ : Dst w)

inductive Instr
  | regular (address_size : Width) (operation_size : Width) (operation : Operation operation_size)

def written_regs (instr : Instr) : List Reg64 :=
  match instr with
  | .regular _ _ op =>
    match op with
    | .mov dst _ | .not dst => match dst with | .reg r => [r.base]

instance : Coe UInt64 (BitVec 64) := ⟨UInt64.toBitVec⟩

namespace BitVec
def take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
def drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)
end BitVec
def BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth _

structure Reg64s where
  rax : UInt64 := 0
  rbx : UInt64 := 0

def Reg64s.get64 (s : Reg64s) (r : Reg64) : Width.W64.type := UInt64.toBitVec (match r with
  | .rax => s.rax | .rbx => s.rbx)

def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : Width.W64.type) : Reg64s :=
  let v := UInt64.ofBitVec v
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }

def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  (s.get64 r.base).take w.bits

def Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.set64 r v
  | .low r .W32 => s.set64 r (v.zeroExtend _)
  | .low r w => s.set64 r ((s.get64 r).replaceLow v)

structure MachineData where
  regs : Reg64s := {}

inductive Effects
  | done (a : MachineData × Int64)

def Effects.Exists (es : Effects) (final : MachineData × Int64) : Prop :=
  match es with
  | .done result => result = final

abbrev MachineState := MachineData × Int64

def RegOrMem.interp {w} [Labels] [AddressSize]
  (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
  match o with
  | .reg r => ret (s.regs.get r) s

def MachineData.setReg (s : MachineData) {w} (r : Reg w) (v : w.type) : MachineData :=
  { s with regs := s.regs.set r v }

def MachineData.set {w} [Labels] [AddressSize] (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) : Effects :=
  match d with
  | .reg r => ret (s.setReg r v)

def Operand.interp {w} [Labels] [AddressSize]
  (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
  match o with
  | regOrMem rm => rm.interp s p ret

def Operation.interp [Labels] [address_size : AddressSize]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match i with
  | .mov dst src => src.interp s p (fun val s => s.set dst val p next)
  | .not dst => dst.interp s p (fun a s => let v := ~~~a; s.set dst v p next)

theorem RegOrMem.interp_reaches {w : Width} [Labels] [AddressSize]
    (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | reg r => exact ⟨_, s, rfl, hfinal⟩

theorem Operand.interp_reaches {w : Width} [Labels] [AddressSize]
    (o : Operand w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (final : MachineState) (hfinal : Effects.Exists (o.interp s p ret) final) :
    ∃ (a : w.type) (s' : MachineData), s'.regs = s.regs ∧
      Effects.Exists (ret a s') final := by
  cases o with
  | regOrMem rm => exact RegOrMem.interp_reaches rm s p ret final hfinal

theorem Reg64s.get64_set64_of_ne {regs : Reg64s} {r r' : Reg64} (h : r' ≠ r) (v : UInt64) :
    (regs.set64 r v).get64 r' = regs.get64 r' := by
  cases r <;> cases r' <;> simp_all [Reg64s.set64, Reg64s.get64]

theorem Reg64s.get64_set_of_ne {w : Width} {regs : Reg64s} (rd : Reg w) (v : w.type) {r : Reg64}
    (h : r ≠ rd.base) : (regs.set rd v).get64 r = regs.get64 r := by
  cases rd with
  | low r64 _ =>
      simp only [Reg.base] at h
      cases w <;> simp only [Reg64s.set] <;> exact Reg64s.get64_set64_of_ne h _

theorem MachineData.setReg_get64_of_ne {w : Width} (s : MachineData) (rd : Reg w) (v : w.type)
    {r : Reg64} (h : r ≠ rd.base) : (s.setReg rd v).regs.get64 r = s.regs.get64 r :=
  Reg64s.get64_set_of_ne rd v h

theorem Reg64.ne_of_beq_eq_false {a b : Reg64} (h : (a == b) = false) : a ≠ b := by
  cases a <;> cases b <;> first | decide | exact absurd h (by decide)

theorem MachineData.set_get64_of_ne {w : Width} [Labels] [AddressSize]
    (d : Dst w) (s : MachineData) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects)
    (r : Reg64) (hd : ∀ rd, d = .reg rd → r ≠ rd.base)
    (final : MachineState) (hfinal : Effects.Exists (MachineData.set s d v p ret) final) :
    ∃ s', s'.regs.get64 r = s.regs.get64 r ∧ Effects.Exists (ret s') final := by
  cases d with
  | reg rd => exact ⟨_, MachineData.setReg_get64_of_ne s rd v (hd rd rfl), hfinal⟩

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
