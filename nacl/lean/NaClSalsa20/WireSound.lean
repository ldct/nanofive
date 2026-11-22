import NaClSalsa20.Wire
import TweetNaCl.ForHumans.Salsa20Spec

/-!
# Soundness of the wire normal forms

`Describes val n w x` says that wire `w` gives the low `n` bits of `x`, when atom `a` has the
value `val a`. Each wire operation is sound for the corresponding `BitVec` operation, and an
atom checked by `Arena.mk` has the value its row prescribes (`Arena.mk_sound`).
-/
namespace NaClSalsa20.Wire
open TinyFive

attribute [-simp] BitVec.getLsbD_eq_getElem

section Sem
variable (val : Id → BitVec 32)

def xorAll : List Term → Bool
  | [] => false
  | t :: ts => (val t.1).getLsbD t.2 ^^ xorAll ts

def Bit.eval (b : Bit) : Bool := b.flip ^^ xorAll val b.terms

/-- `w` gives the low `n` bits of `x`. -/
def Describes (n : Nat) (w : Wire) {k : Nat} (x : BitVec k) : Prop :=
  ∀ i, i < n → x.getLsbD i = (bit w i).eval val

def ofBits (n : Nat) (f : Nat → Bool) : BitVec n :=
  (BitVec.ofBoolListLE ((List.range n).map f)).cast (by simp)

def eval (w : Wire) : BitVec 32 := ofBits 32 fun i => (bit w i).eval val

end Sem

variable {val : Id → BitVec 32}

theorem getLsbD_ofBits (n : Nat) (f : Nat → Bool) (i : Nat) :
    (ofBits n f).getLsbD i = (decide (i < n) && f i) := by
  by_cases h : i < n <;> simp [ofBits, List.getD_eq_getElem?_getD, h]

theorem describes_eval (w : Wire) : Describes val 32 w (eval val w) := by
  intro i hi
  simp [eval, getLsbD_ofBits, hi]

theorem eq_eval {w : Wire} {x : BitVec 32} (h : Describes val 32 w x) : x = eval val w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [h i hi, describes_eval w i hi]

theorem Describes.of_bits {n : Nat} {w : Wire} {k k' : Nat} {x : BitVec k} {y : BitVec k'}
    (h : Describes val n w x) (hb : ∀ i, i < n → y.getLsbD i = x.getLsbD i) :
    Describes val n w y := fun i hi => (hb i hi).trans (h i hi)

theorem describes_setWidth {w : Wire} {k : Nat} {x : BitVec k} :
    Describes val 32 w (x.setWidth 32) ↔ Describes val 32 w x := by
  constructor <;> intro h <;> refine h.of_bits fun i hi => ?_ <;> simp [hi]

theorem describes_signExtend {w : Wire} {x : BitVec 32} :
    Describes val 32 w (x.signExtend 64) ↔ Describes val 32 w x := by
  constructor <;> intro h <;> refine h.of_bits fun i hi => ?_ <;>
    simp [BitVec.getLsbD_signExtend, hi, show i < 64 by omega]

theorem xorAll_merge (a b : List Term) :
    xorAll val (merge a b) = (xorAll val a ^^ xorAll val b) := by
  fun_induction merge a b with
  | case1 => simp [xorAll]
  | case2 l hl =>
    cases l with
    | nil => contradiction
    | cons => simp [xorAll]
  | case3 ts t us ih =>
    simp only [xorAll, ih]
    cases (val t.1).getLsbD t.2 <;> simp
  | case4 t ts u us h1 h2 ih =>
    simp only [xorAll, ih, Bool.xor_assoc]
  | case5 t ts u us h1 h2 ih =>
    simp only [xorAll, ih]
    cases (val u.1).getLsbD u.2 <;> cases xorAll val us <;> cases (val t.1).getLsbD t.2 <;>
      cases xorAll val ts <;> rfl

theorem Bit.eval_xor (a b : Bit) : (a.xor b).eval val = (a.eval val ^^ b.eval val) := by
  simp only [Bit.xor, Bit.eval, xorAll_merge]
  cases a.flip <;> cases b.flip <;> cases xorAll val a.terms <;> cases xorAll val b.terms <;> rfl

@[simp] theorem Bit.eval_zero : Bit.zero.eval val = false := rfl

theorem Bit.eval_const (b : Bool) : (Bit.mk b []).eval val = b := by simp [Bit.eval, xorAll]

theorem Bit.eval_of_terms {b : Bit} (h : b.terms = []) : b.eval val = b.flip := by
  simp [Bit.eval, h, xorAll]

theorem Bit.or_eval {a b c : Bit} (h : a.or b = some c) : c.eval val = (a.eval val || b.eval val) := by
  unfold Bit.or at h
  split at h
  next ha =>
    cases h
    rw [Bit.eval_of_terms (b := a) ha]
    cases a.flip <;> simp [Bit.eval_const]
  split at h
  next hb =>
    cases h
    rw [Bit.eval_of_terms (b := b) hb]
    cases b.flip <;> simp [Bit.eval_const]
  contradiction

theorem Bit.and_eval {a b c : Bit} (h : a.and b = some c) :
    c.eval val = (a.eval val && b.eval val) := by
  unfold Bit.and at h
  split at h
  next ha =>
    cases h
    rw [Bit.eval_of_terms (b := a) ha]
    cases a.flip <;> simp
  split at h
  next hb =>
    cases h
    rw [Bit.eval_of_terms (b := b) hb]
    cases b.flip <;> simp
  contradiction

theorem bit_gen {f : Nat → Bit} {i : Nat} (hi : i < 32) : bit (gen f) i = f i := by
  simp [bit, gen, List.getD_eq_getElem?_getD, hi]

theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r →
      r.length = l.length ∧ ∀ i (h : i < l.length), f l[i] = r[i]?
  | [], r, h => by simp at h; subst h; simp
  | x :: xs, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨hl, hi⟩ := mapM_some hys
    refine ⟨by simp [hl], fun i h => ?_⟩
    cases i with
    | zero => simpa using hy
    | succ i => simpa using hi i (by simpa using h)

theorem bit_genM {f : Nat → Option Bit} {w : Wire} (h : genM f = some w) {i : Nat}
    (hi : i < 32) : f i = some (bit w i) := by
  obtain ⟨hl, he⟩ := mapM_some h
  have := he i (by simpa using hi)
  simp only [List.getElem_range] at this
  rw [this, bit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hl; omega)]
  rfl

theorem bit_mem_or_zero (w : Wire) (i : Nat) : bit w i ∈ w ∨ bit w i = Bit.zero := by
  simp only [bit, List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · simp [List.getElem?_eq_getElem h, List.getElem_mem]
  · rw [List.getElem?_eq_none (by omega)]; simp

section Ops
variable {x y : BitVec 32} {a b w : Wire}

theorem xor_sound (ha : Describes val 32 a x) (hb : Describes val 32 b y) :
    Describes val 32 (xor a b) (x ^^^ y) := by
  intro i hi
  simp [xor, bit_gen hi, Bit.eval_xor, ha i hi, hb i hi]

theorem or_sound (h : or a b = some w) (ha : Describes val 32 a x) (hb : Describes val 32 b y) :
    Describes val 32 w (x ||| y) := by
  intro i hi
  rw [BitVec.getLsbD_or, ha i hi, hb i hi, (Bit.or_eval (bit_genM h hi))]

theorem and_sound (h : and a b = some w) (ha : Describes val 32 a x) (hb : Describes val 32 b y) :
    Describes val 32 w (x &&& y) := by
  intro i hi
  rw [BitVec.getLsbD_and, ha i hi, hb i hi, (Bit.and_eval (bit_genM h hi))]

theorem shl_sound (k : Nat) (ha : Describes val 32 a x) : Describes val 32 (shl k a) (x <<< k) := by
  intro i hi
  rw [BitVec.getLsbD_shiftLeft, shl, bit_gen hi]
  by_cases hk : i < k
  · simp [hk]
  · simp [hk, hi, ha (i - k) (by omega)]

theorem shr_sound (k : Nat) (ha : Describes val 32 a x) : Describes val 32 (shr k a) (x >>> k) := by
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, shr, bit_gen hi]
  by_cases hk : i + k < 32
  · simp [hk, ha (i + k) hk, Nat.add_comm k i]
  · simp [hk, BitVec.getLsbD_of_ge x (k + i) (by omega)]

theorem sar_sound (k : Nat) (ha : Describes val 32 a x) :
    Describes val 32 (sar k a) (x.sshiftRight k) := by
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, sar, bit_gen hi]
  by_cases hk : i + k < 32
  · simp [hk, show ¬ 32 ≤ i by omega, ha (i + k) hk, Nat.add_comm k i]
  · simp [show ¬ k + i < 32 by omega, show ¬ 32 ≤ i by omega, hk,
      BitVec.msb_eq_getLsbD_last, ha 31 (by omega)]

theorem rotl_sound (k : Nat) (ha : Describes val 32 a x) :
    Describes val 32 (rotl a k) (x.rotateLeft k) := by
  intro i hi
  rw [BitVec.getLsbD_rotateLeft, rotl, bit_gen hi]
  have hk : k % 32 < 32 := Nat.mod_lt _ (by omega)
  by_cases h : i < k % 32
  · simp only [h, ite_true]
    rw [ha _ (by omega)]
    congr 2
    omega
  · simp only [h, ite_false, hi, decide_true, Bool.true_and]
    rw [ha _ (by omega)]
    congr 2
    omega

theorem const_sound (v : BitVec 32) : Describes val 32 (const v) v := by
  intro i hi
  simp [const, bit_gen hi, Bit.eval_const]

theorem toConst_sound {c : BitVec 32} (h : toConst w = some c) (hw : Describes val 32 w x) :
    x = c := by
  unfold toConst at h
  split at h
  next ht =>
    cases h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hti := List.all_eq_true.mp ht i (by simpa using hi)
    rw [hw i hi, Bit.eval_of_terms (by simpa using hti)]
    simp [List.getD_eq_getElem?_getD, hi]
  next => contradiction

theorem atom_sound {n : Nat} (id : Id) : Describes val n (atom n id) (val id) := by
  intro i hi
  simp [atom, bit, List.getD_eq_getElem?_getD, hi, Bit.eval, xorAll]

/-- A byte of a wire describes the corresponding byte of the value. -/
theorem byte_sound {k j : Nat} {X : BitVec j} {z : BitVec 8} (hk : k < 4)
    (hx : Describes val 32 w X) (hz : ∀ i, i < 8 → z.getLsbD i = X.getLsbD (8 * k + i)) :
    Describes val 8 (byte w k) z := by
  intro i hi
  rw [hz i hi, hx _ (by omega)]
  simp [byte, bit, List.getD_eq_getElem?_getD, hi]

theorem pack_sound {b0 b1 b2 b3 : Wire} {y0 y1 y2 y3 : BitVec 8}
    (h0 : Describes val 8 b0 y0) (h1 : Describes val 8 b1 y1) (h2 : Describes val 8 b2 y2)
    (h3 : Describes val 8 b3 y3) :
    Describes val 32 (pack b0 b1 b2 b3) (TweetNaCl.Salsa20Spec.loadLE #v[y0, y1, y2, y3]) := by
  intro i hi
  simp only [pack, bit_gen hi, TweetNaCl.Salsa20Spec.loadLE, BitVec.getLsbD_append]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32)) with
    h | h | h | h
  · simp [h, show i / 8 = 0 by omega, Nat.mod_eq_of_lt h, h0 i h]
  · simp [show ¬ i < 8 by omega, show i - 8 < 8 by omega, show i / 8 = 1 by omega,
      h1 (i - 8) (by omega), show i % 8 = i - 8 by omega]
  · simp [show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show i - 8 - 8 < 8 by omega,
      show i / 8 = 2 by omega, h2 (i - 8 - 8) (by omega), show i % 8 = i - 8 - 8 by omega]
  · simp [show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show i / 8 = 3 by omega, h3 (i - 8 - 8 - 8) (by omega), show i % 8 = i - 8 - 8 - 8 by omega]

end Ops

/-! ## The arena -/

def Node.eval (env : Nat → BitVec 8) (val : Id → BitVec 32) : Node → BitVec 32
  | .leaf a => (env a).setWidth 32
  | .add a b => Wire.eval val a + Wire.eval val b

namespace Arena

/-- The value of each atom. Unchecked rows evaluate arbitrarily; `mk_sound` covers checked rows. -/
def eval (arena : Arena) (env : Nat → BitVec 8) (id : Id) : BitVec 32 :=
  match arena.nodes[id]? with
  | some (.leaf a) => (env a).setWidth 32
  | some (.add a b) =>
    Wire.eval (fun j => if _h : j < id then arena.eval env j else 0) a +
      Wire.eval (fun j => if _h : j < id then arena.eval env j else 0) b
  | none => 0
termination_by id
decreasing_by all_goals exact _h

theorem eval_congr {val val' : Id → BitVec 32} {w : Wire}
    (h : ∀ b ∈ w, ∀ t ∈ b.terms, val t.1 = val' t.1) : Wire.eval val w = Wire.eval val' w := by
  have hx : ∀ ts : List Term, (∀ t ∈ ts, val t.1 = val' t.1) → xorAll val ts = xorAll val' ts := by
    intro ts
    induction ts with
    | nil => intro; rfl
    | cons t ts ih =>
      intro ht
      simp only [xorAll, ht t List.mem_cons_self, ih fun u hu => ht u (List.mem_cons_of_mem _ hu)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Wire.eval, getLsbD_ofBits, Bit.eval]
  rcases bit_mem_or_zero w i with hm | hz
  · rw [hx _ (h _ hm)]
  · rw [hz]; rfl

theorem mk_sound {arena : Arena} {node : Node} {id : Id} (env : Nat → BitVec 8)
    (h : arena.mk node = some id) : arena.eval env id = node.eval env (arena.eval env) := by
  unfold mk at h
  cases hi : arena.index[node]? with
  | none => simp [hi] at h
  | some i =>
    simp only [hi, bind, Option.bind] at h
    split at h
    next hc =>
      cases h
      obtain ⟨hn, hb⟩ := hc
      rw [eval, hn]
      cases node with
      | leaf a => rfl
      | add a b =>
        simp only [Node.Before, Bool.and_eq_true, Below, List.all_eq_true, decide_eq_true_eq] at hb
        simp only [Node.eval]
        congr 1 <;> apply eval_congr <;> intro c hc t ht
        · simp [hb.1 c hc t ht]
        · simp [hb.2 c hc t ht]
    next => contradiction

end Arena

section Add
variable {arena : Arena} {env : Nat → BitVec 8} {a b w : Wire} {x y : BitVec 32}

theorem add_sound (h : Wire.add arena.mk a b = some w)
    (ha : Describes (arena.eval env) 32 a x) (hb : Describes (arena.eval env) 32 b y) :
    Describes (arena.eval env) 32 w (x + y) := by
  unfold Wire.add at h
  split at h
  next cx cy hx hy =>
    cases h
    rw [toConst_sound hx ha, toConst_sound hy hb]
    exact const_sound _
  next hx _ =>
    cases h
    rw [toConst_sound hx ha, BitVec.zero_add]
    exact hb
  next hy _ =>
    cases h
    rw [toConst_sound hy hb, BitVec.add_zero]
    exact ha
  next =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨id, hid, rfl⟩ := h
    have he := Arena.mk_sound env hid
    have hv : arena.eval env id = x + y := by
      rw [he]
      split <;> simp only [Node.eval, ← eq_eval ha, ← eq_eval hb, BitVec.add_comm]
    rw [← hv]
    exact atom_sound id

theorem op32_sound {op : AluOp} (h : op32 arena.mk op a b = some (some w))
    (ha : Describes (arena.eval env) 32 a x) (hb : Describes (arena.eval env) 32 b y) :
    Describes (arena.eval env) 32 w (alu op x y) := by
  cases op <;> simp only [op32, pure, bind, Option.bind_eq_some_iff, Option.some.injEq,
    Option.map_eq_some_iff, reduceCtorEq] at h
  case add =>
    obtain ⟨w', hw, rfl⟩ := h
    exact add_sound hw ha hb
  case xor => cases h; exact xor_sound ha hb
  case or => exact or_sound h ha hb
  case and => exact and_sound h ha hb
  case sll =>
    obtain ⟨k, hk, rfl⟩ := h
    rw [alu, toConst_sound hk hb]
    exact shl_sound _ ha
  case srl =>
    obtain ⟨k, hk, rfl⟩ := h
    rw [alu, toConst_sound hk hb]
    exact shr_sound _ ha
  case sra =>
    obtain ⟨k, hk, rfl⟩ := h
    rw [alu, toConst_sound hk hb]
    exact sar_sound _ ha

theorem op64_sound {op : AluOp} {X Y : BitVec 64} (h : op64 arena.mk op a b = some (some w))
    (ha : Describes (arena.eval env) 32 a X) (hb : Describes (arena.eval env) 32 b Y) :
    Describes (arena.eval env) 32 w (alu op X Y) := by
  have ha' := describes_setWidth.mpr ha
  have hb' := describes_setWidth.mpr hb
  cases op <;> simp only [op64, pure, Option.some.injEq, Option.map_eq_some_iff, reduceCtorEq] at h
  case add =>
    refine describes_setWidth.mp ?_
    simpa [alu, BitVec.setWidth_add] using op32_sound (op := .add) h ha' hb'
  case xor =>
    refine describes_setWidth.mp ?_
    simpa [alu] using op32_sound (op := .xor) h ha' hb'
  case or =>
    refine describes_setWidth.mp ?_
    simpa [alu] using op32_sound (op := .or) h ha' hb'
  case and =>
    refine describes_setWidth.mp ?_
    simpa [alu] using op32_sound (op := .and) h ha' hb'
  case sll =>
    obtain ⟨k, hk, rfl⟩ := h
    have hy := toConst_sound hk hb'
    have hm : Y.toNat % 64 = k.toNat % 64 := by
      rw [← hy, BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (by decide)]
    intro i hi
    rw [alu, hm, BitVec.getLsbD_shiftLeft, shl, bit_gen hi]
    by_cases hk : i < k.toNat % 64
    · simp [hk]
    · simp [hk, show i < 64 by omega, ha (i - k.toNat % 64) (by omega)]

end Add
end NaClSalsa20.Wire
