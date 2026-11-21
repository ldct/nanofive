import Init.Data.BitVec.Lemmas
import Init.Omega
import TweetNaCl.ForHumans.Salsa20Spec

/-!
The algebra of the RV64 `core` quarter-round (ELF addresses `0x1dc`–`0x23c`).
In the upstream C, `u32` is `unsigned long` and is therefore 64 bits on
this target. `L32` masks the right-shift input but does not truncate the
left shift. The proof below allows arbitrary high halves in every input.
It relates the instruction pattern to word arithmetic, not execution of
the surrounding loads, stores, or loops.
-/

namespace TweetNaCl.Salsa20LowWords

def low32 (x : BitVec 64) : BitVec 32 := x.setWidth 32

theorem low32_add (x y : BitVec 64) : low32 (x + y) = low32 x + low32 y :=
  BitVec.setWidth_add x y (by decide)

theorem low32_xor (x y : BitVec 64) : low32 (x ^^^ y) = low32 x ^^^ low32 y :=
  BitVec.setWidth_xor

theorem low32_sub (x y : BitVec 64) : low32 (x - y) = low32 x - low32 y := by
  rw [BitVec.eq_sub_iff_add_eq, ← low32_add, BitVec.sub_add_cancel]

/-- RV64 `srliw` at the in-range immediates used below: shift the low word
logically, then sign-extend that word back to XLEN. -/
def srliw (x : BitVec 64) (imm : Nat) : BitVec 64 :=
  ((low32 x) >>> imm).signExtend 64

/-- `srliw`, `slli`, `or`: the lowering used for rotations by 7 and 9. -/
def rotate64Word (x : BitVec 64) (n : Nat) : BitVec 64 :=
  srliw x (32 - n) ||| (x <<< n)

/-- `srli`, `and`, `slli`, `or`: the lowering used for rotations by 13 and 18. -/
def rotate64Masked (x : BitVec 64) (n : Nat) (mask : BitVec 64) : BitVec 64 :=
  ((x >>> (32 - n)) &&& mask) ||| (x <<< n)

theorem low32_rotate64Word (x : BitVec 64) (n : Nat) (hn : n < 32) :
    low32 (rotate64Word x n) = (low32 x).rotateLeft n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateLeft_of_le hn]
  simp only [low32, rotate64Word, srliw, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_signExtend, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi,
    show i < 64 by omega, decide_true, Bool.true_and, ite_true]
  by_cases hir : i < n
  · simp [hir]
  · simp [hir, show ¬ (32 - n + i < 32) by omega, show i - n < 32 by omega]

theorem low32_rotate64Masked (x : BitVec 64) (n : Nat) (hn : n < 32) :
    low32 (rotate64Masked x n (BitVec.ofNat 64 (2 ^ n - 1))) = (low32 x).rotateLeft n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateLeft_of_le hn]
  simp only [low32, rotate64Masked, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hi,
    show i < 64 by omega, decide_true, Bool.true_and]
  by_cases hir : i < n
  · simp [hir, show 32 - n + i < 32 by omega]
  · simp [hir, show i - n < 32 by omega]

theorem low32_rotate7 (x : BitVec 64) :
    low32 (rotate64Word x 7) = (low32 x).rotateLeft 7 :=
  low32_rotate64Word x 7 (by decide)

theorem low32_rotate9 (x : BitVec 64) :
    low32 (rotate64Word x 9) = (low32 x).rotateLeft 9 :=
  low32_rotate64Word x 9 (by decide)

theorem low32_rotate13 (x : BitVec 64) :
    low32 (rotate64Masked x 13 0x1fff) = (low32 x).rotateLeft 13 :=
  low32_rotate64Masked x 13 (by decide)

theorem low32_rotate18 (x : BitVec 64) :
    low32 (rotate64Masked x 18 0x3ffff) = (low32 x).rotateLeft 18 :=
  low32_rotate64Masked x 18 (by decide)

/-- The ELF's four updates, in the order in which they are computed.
The tuple is returned in scratch-slot order (`t[0]` through `t[3]`). -/
def quarterRound64 (a b c d : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let b' := rotate64Word (a + d) 7 ^^^ b
  let c' := rotate64Word (a + b') 9 ^^^ c
  let d' := rotate64Masked (b' + c') 13 0x1fff ^^^ d
  let a' := rotate64Masked (c' + d') 18 0x3ffff ^^^ a
  (a', b', c', d')

/-- Project each scratch slot onto its low word. -/
def low32Quarter (x : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  (low32 x.1, low32 x.2.1, low32 x.2.2.1, low32 x.2.2.2)

/-- The four low words of the RV64 computation agree with the Salsa20 spec,
regardless of the input high words. -/
theorem quarterRound64_low32 (a b c d : BitVec 64) :
    low32Quarter (quarterRound64 a b c d) =
      Salsa20Spec.quarterRound (low32 a) (low32 b) (low32 c) (low32 d) := by
  simp only [quarterRound64, low32Quarter, Salsa20Spec.quarterRound, low32_add, low32_xor,
    low32_rotate7, low32_rotate9, low32_rotate13, low32_rotate18,
    BitVec.add_comm, BitVec.xor_comm]

/-- Little-endian assembly of four zero-extended `lbu` results. -/
def loadLE64 (b0 b1 b2 b3 : BitVec 8) : BitVec 64 :=
  ((b3.setWidth 64 <<< 24) |||
    ((b2.setWidth 64 <<< 16) ||| ((b1.setWidth 64 <<< 8) ||| b0.setWidth 64)))

theorem loadLE64_eq_setWidth (b0 b1 b2 b3 : BitVec 8) :
    loadLE64 b0 b1 b2 b3 = (b3 ++ b2 ++ b1 ++ b0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [loadLE64, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp only [Nat.sub_sub, Nat.reduceAdd, decide_true, Bool.true_and,
    show i - 8 < 64 by omega, show i - 16 < 64 by omega, show i - 24 < 64 by omega]
  by_cases h8 : i < 8
  · simp [h8, show i < 16 by omega, show i < 24 by omega]
  by_cases h16 : i < 16
  · simp [h8, h16, show i < 24 by omega, show i - 8 < 8 by omega,
      BitVec.getLsbD_of_ge b0 i (by omega)]
  by_cases h24 : i < 24
  · simp [h8, h16, h24, show ¬ (i - 8 < 8) by omega, show i - 16 < 8 by omega,
      BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i - 8) (by omega)]
  · simp [h8, h16, h24, show ¬ (i - 8 < 8) by omega, show ¬ (i - 16 < 8) by omega,
      BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i - 8) (by omega),
      BitVec.getLsbD_of_ge b2 (i - 16) (by omega)]

theorem low32_loadLE64 (b0 b1 b2 b3 : BitVec 8) :
    low32 (loadLE64 b0 b1 b2 b3) = b3 ++ b2 ++ b1 ++ b0 := by
  rw [loadLE64_eq_setWidth, low32, BitVec.setWidth_setWidth_of_le _ (by decide),
    BitVec.setWidth_eq]

theorem low32_loadLE64_eq_loadLE (b : Salsa20Spec.Bytes 4) :
    low32 (loadLE64 b[0] b[1] b[2] b[3]) = Salsa20Spec.loadLE b :=
  low32_loadLE64 b[0] b[1] b[2] b[3]

/-- An `sb` in the four-byte output loop sees only the low word. -/
theorem storeByte64_eq_storeByte32 (x : BitVec 64) {i : Nat} (hi : i < 4) :
    (x >>> (8 * i)).setWidth 8 = ((low32 x) >>> (8 * i)).setWidth 8 := by
  simp only [BitVec.setWidth_ushiftRight_eq_extractLsb, low32]
  rw [BitVec.extractLsb'_setWidth_of_le (by omega)]

theorem storeByte64_eq_storeLE (x : BitVec 64) (i : Fin 4) :
    (x >>> (8 * i.val)).setWidth 8 = (Salsa20Spec.storeLE (low32 x))[i] := by
  rw [storeByte64_eq_storeByte32 x i.isLt, BitVec.setWidth_ushiftRight_eq_extractLsb]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    simp only [Fin.ext_iff]
    change i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3
    omega
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

end TweetNaCl.Salsa20LowWords
