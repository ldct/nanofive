import GrumpyBinary.Memset

/-! Arrays in memory: `n` little-endian words of 1, 4 or 8 bytes from `base`, read through
`readBytes` exactly as `lbu`, `lw` and `ld` read them, and how stores (as `wr` layers) and
`memset` change them. -/
namespace TinyFive.GrumpyBinary
open SieveMemory

local notation "bv" => BitVec.ofNat 64

/-- Bytes: `lbu` at `base + i` gives `f i`. -/
def Arr8 (mem : Array (BitVec 8)) (base n : Nat) (f : Nat → Nat) : Prop :=
  ∀ i, i < n → readBytes mem (base + i) 1 = some (BitVec.ofNat 8 (f i))

/-- 32-bit words: `lw` at `base + i * 4` gives `f i`. -/
def Arr32 (mem : Array (BitVec 8)) (base n : Nat) (f : Nat → Nat) : Prop :=
  ∀ i, i < n → readBytes mem (base + i * 4) 4 = some (BitVec.ofNat 32 (f i))

/-- 64-bit words: `ld` at `base + i * 8` gives `f i`. -/
def Arr64 (mem : Array (BitVec 8)) (base n : Nat) (f : Nat → Nat) : Prop :=
  ∀ i, i < n → readBytes mem (base + i * 8) 8 = some (bv (f i))

/-- `f` with entry `i` replaced by `z`. -/
def upd (f : Nat → Nat) (i z : Nat) : Nat → Nat := fun j => if j = i then z else f j

@[simp] theorem upd_same (f : Nat → Nat) (i z : Nat) : upd f i z i = z := by simp [upd]
theorem upd_other (f : Nat → Nat) (i z j : Nat) (h : j ≠ i) : upd f i z j = f j := by
  simp [upd, h]

theorem setWidth_ofNat_le (w k a : Nat) (h : k ≤ w) :
    (BitVec.ofNat w a).setWidth k = BitVec.ofNat k a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : 2 ^ k ∣ 2 ^ w := Nat.pow_dvd_pow 2 h
  exact Nat.mod_mod_of_dvd a h1

/-- `lbu`: a byte read zero-extends. -/
theorem zext8 (a : Nat) (h : a < 256) : (BitVec.ofNat 8 a).setWidth 64 = bv a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-! ## Frames: the bytes of an array did not change. -/

theorem Arr8.congr {mem mem' : Array (BitVec 8)} {base n : Nat} {f : Nat → Nat}
    (h : Arr8 mem base n f) (hf : ∀ j, base ≤ j → j < base + n → mem'[j]? = mem[j]?) :
    Arr8 mem' base n f := by
  intro i hi
  rw [readBytes_congr mem' mem _ _ (fun j h1 h2 => hf j (by omega) (by omega))]
  exact h i hi

theorem Arr32.congr {mem mem' : Array (BitVec 8)} {base n : Nat} {f : Nat → Nat}
    (h : Arr32 mem base n f) (hf : ∀ j, base ≤ j → j < base + n * 4 → mem'[j]? = mem[j]?) :
    Arr32 mem' base n f := by
  intro i hi
  rw [readBytes_congr mem' mem _ _ (fun j h1 h2 => hf j (by omega) (by
    have : (i + 1) * 4 ≤ n * 4 := Nat.mul_le_mul_right 4 hi
    rw [Nat.add_mul] at this; omega))]
  exact h i hi

theorem Arr64.congr {mem mem' : Array (BitVec 8)} {base n : Nat} {f : Nat → Nat}
    (h : Arr64 mem base n f) (hf : ∀ j, base ≤ j → j < base + n * 8 → mem'[j]? = mem[j]?) :
    Arr64 mem' base n f := by
  intro i hi
  rw [readBytes_congr mem' mem _ _ (fun j h1 h2 => hf j (by omega) (by
    have : (i + 1) * 8 ≤ n * 8 := Nat.mul_le_mul_right 8 hi
    rw [Nat.add_mul] at this; omega))]
  exact h i hi

theorem Arr8.ext {mem : Array (BitVec 8)} {base n : Nat} {f g : Nat → Nat}
    (h : Arr8 mem base n f) (hfg : ∀ i, i < n → f i = g i) : Arr8 mem base n g :=
  fun i hi => by rw [← hfg i hi]; exact h i hi

theorem Arr32.ext {mem : Array (BitVec 8)} {base n : Nat} {f g : Nat → Nat}
    (h : Arr32 mem base n f) (hfg : ∀ i, i < n → f i = g i) : Arr32 mem base n g :=
  fun i hi => by rw [← hfg i hi]; exact h i hi

theorem Arr64.ext {mem : Array (BitVec 8)} {base n : Nat} {f g : Nat → Nat}
    (h : Arr64 mem base n f) (hfg : ∀ i, i < n → f i = g i) : Arr64 mem base n g :=
  fun i hi => by rw [← hfg i hi]; exact h i hi

/-- A store elsewhere leaves an array alone. -/
theorem wr_frame (mem : Array (BitVec 8)) (a : Nat) {k : Nat} (v : BitVec k) (m lo hi : Nat)
    (h : a + m ≤ mem.size) (hd : hi ≤ a ∨ a + m ≤ lo) :
    ∀ j, lo ≤ j → j < hi → (wr mem a v m)[j]? = mem[j]? :=
  fun j h1 h2 => wr_get mem a v m h j (by omega)

/-! ## Stores into an array. -/

theorem Arr8.wr {mem : Array (BitVec 8)} {base n : Nat} {f : Nat → Nat}
    (h : Arr8 mem base n f) (hs : base + n ≤ mem.size) (i z : Nat) (hi : i < n) :
    Arr8 (wr mem (base + i) (bv z) 1) base n (upd f i z) := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    rw [read_wr_same _ _ _ _ (by omega), upd_same]
    congr 1
    exact setWidth_ofNat_le 64 8 z (by omega)
  · rw [read_wr_other _ _ _ _ _ _ (by omega) (by omega), upd_other f i z j hji]
    exact h j hj

theorem Arr32.wr {mem : Array (BitVec 8)} {base n : Nat} {f : Nat → Nat}
    (h : Arr32 mem base n f) (hs : base + n * 4 ≤ mem.size) (i z : Nat) (hi : i < n) :
    Arr32 (wr mem (base + i * 4) (bv z) 4) base n (upd f i z) := by
  have hi4 : (i + 1) * 4 ≤ n * 4 := Nat.mul_le_mul_right 4 hi
  rw [Nat.add_mul] at hi4
  intro j hj
  have hj4 : (j + 1) * 4 ≤ n * 4 := Nat.mul_le_mul_right 4 hj
  rw [Nat.add_mul] at hj4
  by_cases hji : j = i
  · subst hji
    rw [read_wr_same _ _ _ _ (by omega), upd_same]
    congr 1
    exact setWidth_ofNat_le 64 32 z (by omega)
  · rw [read_wr_other _ _ _ _ _ _ (by omega) (by omega), upd_other f i z j hji]
    exact h j hj

theorem Arr64.wr {mem : Array (BitVec 8)} {base n : Nat} {f : Nat → Nat}
    (h : Arr64 mem base n f) (hs : base + n * 8 ≤ mem.size) (i z : Nat) (hi : i < n) :
    Arr64 (wr mem (base + i * 8) (bv z) 8) base n (upd f i z) := by
  have hi8 : (i + 1) * 8 ≤ n * 8 := Nat.mul_le_mul_right 8 hi
  rw [Nat.add_mul] at hi8
  intro j hj
  have hj8 : (j + 1) * 8 ≤ n * 8 := Nat.mul_le_mul_right 8 hj
  rw [Nat.add_mul] at hj8
  by_cases hji : j = i
  · subst hji
    rw [read_wr_same _ _ _ _ (by omega), upd_same]
    rfl
  · rw [read_wr_other _ _ _ _ _ _ (by omega) (by omega), upd_other f i z j hji]
    exact h j hj

/-! ## Zeroed memory. -/

theorem readBytes_zero (mem : Array (BitVec 8)) (a n : Nat)
    (h : ∀ j, a ≤ j → j < a + n → mem[j]? = some 0) : readBytes mem a n = some 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [readBytes, h a (by omega) (by omega), ih (a + 1) (fun j h1 h2 => h j (by omega) (by omega))]
    show some _ = some _
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp; exact BitVec.toNat_zero

theorem Zeroed.arr8 {mem mem' : Array (BitVec 8)} {d n : Nat} (hz : Zeroed mem mem' d n) :
    Arr8 mem' d n (fun _ => 0) := by
  intro i hi
  rw [readBytes_zero _ _ _ (fun j h1 h2 => hz.zero j (by omega) (by omega))]; rfl

theorem Zeroed.arr32 {mem mem' : Array (BitVec 8)} {d n : Nat} (hz : Zeroed mem mem' d (4 * n)) :
    Arr32 mem' d n (fun _ => 0) := by
  intro i hi
  have : (i + 1) * 4 ≤ n * 4 := Nat.mul_le_mul_right 4 hi
  rw [Nat.add_mul] at this
  rw [readBytes_zero _ _ _ (fun j h1 h2 => hz.zero j (by omega) (by omega))]; rfl

theorem Zeroed.arr64 {mem mem' : Array (BitVec 8)} {d n : Nat} (hz : Zeroed mem mem' d (8 * n)) :
    Arr64 mem' d n (fun _ => 0) := by
  intro i hi
  have : (i + 1) * 8 ≤ n * 8 := Nat.mul_le_mul_right 8 hi
  rw [Nat.add_mul] at this
  rw [readBytes_zero _ _ _ (fun j h1 h2 => hz.zero j (by omega) (by omega))]; rfl

theorem readBytes_some (mem : Array (BitVec 8)) (a n : Nat) (h : a + n ≤ mem.size) :
    ∃ w, readBytes mem a n = some w := by
  induction n generalizing a with
  | zero => exact ⟨_, rfl⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih (a + 1) (by omega)
    refine ⟨(w ++ mem[a]'(by omega)).cast (by omega), ?_⟩
    simp only [readBytes, hw, Array.getElem?_eq_getElem (show a < mem.size by omega)]
    rfl

end TinyFive.GrumpyBinary
