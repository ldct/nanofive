import TinyFive.Machine
import TinyFive.SieveMemory

/-!
# 64-bit slots in byte memory

`readBytes` and `writeBytes` at eight bytes, as `ld` and `sd` use them: a store succeeds inside
memory, reads back what it wrote, preserves the size and the code prefix, and leaves every
disjoint slot alone.
-/
namespace TinyFive.LucyMemory

open SieveMemory

private theorem append_setWidth {k : Nat} (v : BitVec k) (n : Nat) :
    (((v >>> 8).setWidth (8 * n) ++ v.setWidth 8).cast (by omega) : BitVec (8 * (n + 1))) =
      v.setWidth (8 * (n + 1)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [h, hi, show i - 8 < 8 * n by omega, show 8 + (i - 8) = i by omega]

/-- An in-bounds store of `n` bytes succeeds, keeps the size, changes only its own bytes and reads
back as the low `8 * n` bits of the value. -/
theorem writeBytes_spec {k : Nat} (n : Nat) (mem : Array (BitVec 8)) (addr : Nat) (v : BitVec k)
    (h : addr + n ≤ mem.size) :
    ∃ mem', writeBytes mem addr v n = some mem' ∧ mem'.size = mem.size ∧
      (∀ i, i < addr ∨ addr + n ≤ i → mem'[i]? = mem[i]?) ∧
      readBytes mem' addr n = some (v.setWidth (8 * n)) := by
  induction n generalizing mem addr v with
  | zero =>
    refine ⟨mem, rfl, rfl, fun _ _ => rfl, ?_⟩
    simp only [readBytes]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_one]
  | succ n ih =>
    have hlt : addr < mem.size := by omega
    obtain ⟨mem', hw, hs, hf, hr⟩ := ih (mem.setIfInBounds addr (v.setWidth 8)) (addr + 1)
      (v >>> 8) (by rw [Array.size_setIfInBounds]; omega)
    refine ⟨mem', ?_, ?_, ?_, ?_⟩
    · simp only [writeBytes, hlt, ite_true]
      exact hw
    · rw [hs, Array.size_setIfInBounds]
    · intro i hi
      rw [hf i (by omega), Array.getElem?_setIfInBounds_ne (by omega)]
    · have hlo : mem'[addr]? = some (v.setWidth 8) := by
        rw [hf addr (by omega), Array.getElem?_setIfInBounds_self_of_lt hlt]
      simp only [readBytes, hlo, hr, bind, Option.bind]
      congr 1
      exact append_setWidth v n

/-- A doubleword store above the code boundary and inside memory. -/
theorem store64 {image mem : Array (BitVec 8)} {boundary cap : Nat}
    (hl : Layout image boundary cap mem) (a : Nat) (v : BitVec 64)
    (hlo : boundary ≤ a) (hhi : a + 8 ≤ cap) :
    ∃ mem', writeBytes mem a v 8 = some mem' ∧ Layout image boundary cap mem' ∧
      readBytes mem' a 8 = some v ∧
      ∀ b, b + 8 ≤ a ∨ a + 8 ≤ b → readBytes mem' b 8 = readBytes mem b 8 := by
  obtain ⟨mem', hw, hs, hf, hr⟩ := writeBytes_spec 8 mem a v (by rw [hl.size_eq]; exact hhi)
  refine ⟨mem', hw, ⟨by rw [hs, hl.size_eq], ?_⟩, ?_, ?_⟩
  · intro i hi
    rw [hf i (by omega)]
    exact hl.code_eq i hi
  · rw [hr]
    simp
  · intro b hb
    apply readBytes_congr
    intro i h1 h2
    exact hf i (by omega)

end TinyFive.LucyMemory
