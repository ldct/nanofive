import ZjyBinary.Calc
import GrumpyBinary.FinishRun

/-! The finish of `pi` at 956: `z = large[0] + 1 + (V + 2C - 2)(V - 1)/2`, minus the other
large counts, plus the triple correction; `z` stays in `a0` and is returned at 620. It is the
same computation as grumpygordon's finish, so the values are grumpygordon's `tri`, `sumR` and
`triLoop`. -/
namespace TinyFive.ZjyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64
local notation "iv" => BitVec.ofInt 64

theorem add_int_nat (a : Int) (b : Nat) : alu .add (iv a) (bv b) = iv (a + b) := by
  simp only [alu]; rw [BitVec.ofInt_add, BitVec.ofInt_natCast]

theorem ofNat32_m2' (a : Nat) (h : 2 ≤ a) :
    BitVec.ofNat 32 (a + 4294967294) = BitVec.ofNat 32 (a - 2) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- 956 → 1008: `z = (V + 2C - 2)(V - 1)/2 + large[0] + 1`. -/
theorem fin_pro (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (Cb s pc L0 : Nat)
    (hmem : Prefix image mem 1480)
    (h2 : x.get 2 = bv 4194096) (h18 : x.get 18 = bv Cb)
    (sV : readBytes mem 4194124 4 = some (BitVec.ofNat 32 s))
    (sC : readBytes mem 4194120 4 = some (BitVec.ofNat 32 pc))
    (hs1 : 1 ≤ s) (hs : s < 200000) (hpc : pc < 200000) (hCb : Cb + 8 ≤ 4194304)
    (hL : readBytes mem Cb 8 = some (bv L0)) (hL0 : L0 < 2 ^ 40) :
    ∃ y, run 13 ⟨x, bv 956, mem, [], out, .running⟩ = ⟨y, bv 1008, mem, [], out, .running⟩ ∧
      y.get 10 = bv (tri s pc + (L0 + 1)) ∧ y.get 15 = bv 0 ∧ y.get 13 = bv s ∧ y.get 12 = bv pc ∧
      (∀ r : Reg, r ∉ ([10, 12, 13, 14, 15] : List Reg) → y.get r = x.get r) := by
  have := ofNat32_m2'
  rcases Nat.lt_or_ge (s + 2 * pc) 2 with hlt | hge
  · obtain rfl : s = 1 := by omega
    obtain rfl : pc = 0 := by omega
    have h1 : BitVec.signExtend 64 4294967295#32 = 18446744073709551615#64 := by decide
    have h7 : tri 1 0 = 0 := rfl
    rw [h7]
    exact ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
      by simp [Regs.get_set], by frame_tac⟩
  · have hb : (s + 2 * pc - 2) * (s - 1) < 2 ^ 63 := by
      have := Nat.mul_le_mul (show s + 2 * pc - 2 ≤ 600000 by omega) (show s - 1 ≤ 200000 by omega)
      omega
    have hd := alu_div ((s + pc + pc - 2) * (s - 1)) 2 (by rw [show s + pc + pc = s + 2 * pc by omega]; exact hb)
      (by decide) (by decide)
    have ht : tri s pc = (s + pc + pc - 2) * (s - 1) / 2 := by
      simp only [tri, show s + pc + pc = s + 2 * pc by omega]
    have := Nat.div_le_self ((s + pc + pc - 2) * (s - 1)) 2
    rw [ht]
    exact ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
      by simp [Regs.get_set], by frame_tac⟩

/-! ## Subtracting the large counts (loop at 1008) -/

theorem fin_loop1_step (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (Cb s k lk : Nat) (Z : Int)
    (hmem : Prefix image mem 1480)
    (h10 : x.get 10 = iv Z) (h15 : x.get 15 = bv k) (h13 : x.get 13 = bv s) (h18 : x.get 18 = bv Cb)
    (hk : k + 1 < s) (hs : s < 200000) (hC : 1480 ≤ Cb) (hCs : Cb + s * 8 ≤ 4194304)
    (hL : readBytes mem (Cb + (k + 1) * 8) 8 = some (bv lk)) :
    ∃ y, run 8 ⟨x, bv 1008, mem, [], out, .running⟩ = ⟨y, bv 1008, mem, [], out, .running⟩ ∧
      y.get 15 = bv (k + 1) ∧ y.get 10 = iv (Z - lk) ∧
      (∀ r : Reg, r ∉ ([10, 14, 15] : List Reg) → y.get r = x.get r) := by
  have := sub_int
  exact ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

theorem fin_loop1_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s k : Nat)
    (hmem : Prefix image mem 1480)
    (h15 : x.get 15 = bv k) (h13 : x.get 13 = bv s) (hk : s ≤ k + 1) (hk' : k < s) (hs : s < 200000) :
    ∃ y, run 3 ⟨x, bv 1008, mem, [], out, .running⟩ = ⟨y, bv 1020, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([14, 15] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by frame_tac⟩

theorem fin_loop1 (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (Cb s k : Nat)
    (f : Nat → Nat) (Z : Int) (hmem : Prefix image mem 1480)
    (h10 : x.get 10 = iv Z) (h15 : x.get 15 = bv k) (h13 : x.get 13 = bv s) (h18 : x.get 18 = bv Cb)
    (hk : k + 1 ≤ s) (hs : s < 200000) (hC : 1480 ≤ Cb) (hCs : Cb + s * 8 ≤ 4194304)
    (hla : ∀ j, 1 ≤ j → j < s → readBytes mem (Cb + j * 8) 8 = some (bv (f j))) :
    ∃ n y, run n ⟨x, bv 1008, mem, [], out, .running⟩ = ⟨y, bv 1020, mem, [], out, .running⟩ ∧
      y.get 10 = iv (Z - sumR f (k + 1) s) ∧
      (∀ r : Reg, r ∉ ([10, 14, 15] : List Reg) → y.get r = x.get r) := by
  by_cases hks : k + 1 < s
  · obtain ⟨y1, hr1, hy15, hy10, g1⟩ := fin_loop1_step x mem out Cb s k (f (k + 1)) Z hmem h10 h15
      h13 h18 hks hs hC hCs (hla (k + 1) (by omega) hks)
    obtain ⟨n, y, hr, hy, g⟩ := fin_loop1 y1 mem out Cb s (k + 1) f (Z - f (k + 1)) hmem hy10 hy15
      (by rw [g1 13 (by decide), h13]) (by rw [g1 18 (by decide), h18]) (by omega) hs hC hCs hla
    refine ⟨8 + n, y, by rw [run_add, hr1, hr], ?_, ?_⟩
    · rw [hy, sumR_succ f (k + 1) s hks]; congr 1; push_cast; omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [hr]), g1 r (by simp [hr])]
  · obtain ⟨y, hr, g⟩ := fin_loop1_exit x mem out s k hmem h15 h13 (by omega) (by omega) hs
    refine ⟨3, y, hr, ?_, ?_⟩
    · rw [sumR_self f (k + 1) s (by omega), g 10 (by decide), h10]; simp
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact g r (by simp [hr])
termination_by s - k

/-! ## The triple correction (loops at 1032 and 1100) -/

theorem tri_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N pc : Nat)
    (hmem : Prefix image mem 1480) (h2 : x.get 2 = bv 4194096) (h12 : x.get 12 = bv pc)
    (sn : readBytes mem 4194104 8 = some (bv N)) :
    ∃ y, run 3 ⟨x, bv 1020, mem, [], out, .running⟩ = ⟨y, bv 1032, mem, [], out, .running⟩ ∧
      y.get 28 = bv N ∧ y.get 6 = bv pc ∧ y.get 11 = bv 1 ∧
      (∀ r : Reg, r ∉ ([6, 11, 28] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

theorem tri_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s : Nat)
    (hmem : Prefix image mem 1480) (h11 : x.get 11 = bv s) (h13 : x.get 13 = bv s) (hs : s < 200000) :
    ∃ y, run 2 ⟨x, bv 1032, mem, [], out, .running⟩ = ⟨y, bv 620, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([17] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by frame_tac⟩

/-- Row `l` stops the loop: `e = small[half(N/q/q)] - C < l + 1`; `pi` returns. -/
theorem tri_break (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B N s pc l q m : Nat)
    (hmem : Prefix image mem 1480)
    (h11 : x.get 11 = bv l) (h13 : x.get 13 = bv s) (h28 : x.get 28 = bv N) (h9 : x.get 9 = bv B)
    (h8 : x.get 8 = bv A) (h12 : x.get 12 = bv pc)
    (hl : l < s) (hs : s < 200000) (hN : N < 2 ^ 40) (hpc : pc < 200000)
    (hA : 1480 ≤ A) (hB : B + s * 4 ≤ 4194304) (hA2 : A + (N / q / q - 1) / 2 * 4 + 4 ≤ 4194304)
    (hq2 : 1 ≤ q) (hq : q < 2 ^ 20) (hm : m < 2 ^ 20) (h1 : 1 ≤ N / q / q)
    (hrq : readBytes mem (B + l * 4) 4 = some (BitVec.ofNat 32 q))
    (hrm : readBytes mem (A + (N / q / q - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 m))
    (hbrk : m < pc + l + 1) :
    ∃ y, run 15 ⟨x, bv 1032, mem, [], out, .running⟩ = ⟨y, bv 620, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([14, 15, 17, 29, 30] : List Reg) → y.get r = x.get r) := by
  have := Nat.div_le_self N q
  have := Nat.div_le_self (N / q) q
  have := sext_sub32 m pc (by omega) (by omega)
  have := slt_nat_int l ((m : Int) - pc) (by omega) (by omega) (by omega)
  have hc : (m : Int) - pc ≤ l := by omega
  have : alu .add (iv ((m : Int) - pc)) 0#64 = iv ((m : Int) - pc) := by simp [alu]
  exact ⟨_, by zexec; rfl, by frame_tac⟩

/-- Row `l` runs: `e = small[half(N/q/q)] - C ≥ l + 1`. -/
theorem tri_cont (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B N s pc l q m : Nat)
    (hmem : Prefix image mem 1480)
    (h11 : x.get 11 = bv l) (h13 : x.get 13 = bv s) (h28 : x.get 28 = bv N) (h9 : x.get 9 = bv B)
    (h8 : x.get 8 = bv A) (h12 : x.get 12 = bv pc)
    (hl : l < s) (hs : s < 200000) (hN : N < 2 ^ 40) (hpc : pc < 200000)
    (hA : 1480 ≤ A) (hB : B + s * 4 ≤ 4194304) (hA2 : A + (N / q / q - 1) / 2 * 4 + 4 ≤ 4194304)
    (hq2 : 1 ≤ q) (hq : q < 2 ^ 20) (hm : m < 2 ^ 20) (h1 : 1 ≤ N / q / q)
    (hrq : readBytes mem (B + l * 4) 4 = some (BitVec.ofNat 32 q))
    (hrm : readBytes mem (A + (N / q / q - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 m))
    (hcont : pc + l + 1 ≤ m) :
    ∃ y, run 17 ⟨x, bv 1032, mem, [], out, .running⟩ = ⟨y, bv 1100, mem, [], out, .running⟩ ∧
      y.get 29 = bv (N / q) ∧ y.get 16 = bv (l + 1) ∧ y.get 11 = bv (l + 1) ∧
      y.get 14 = bv (m - pc) ∧ y.get 30 = bv (m - pc) ∧ y.get 17 = bv l ∧
      (∀ r : Reg, r ∉ ([11, 14, 15, 16, 17, 29, 30] : List Reg) → y.get r = x.get r) := by
  have := Nat.div_le_self N q
  have := Nat.div_le_self (N / q) q
  exact ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

/-- One term of the inner sum: `z += small[half(y / rough[k])]`. -/
theorem inner_step (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B M k e r v : Nat) (Z : Int)
    (hmem : Prefix image mem 1480)
    (h16 : x.get 16 = bv k) (h10 : x.get 10 = iv Z) (h30 : x.get 30 = bv e) (h29 : x.get 29 = bv M)
    (h9 : x.get 9 = bv B) (h8 : x.get 8 = bv A)
    (hke : k ≤ e) (he : e < 200000) (hM : M < 2 ^ 40)
    (hA : 1480 ≤ A) (hB' : B + k * 4 + 4 ≤ 4194304)
    (hA2 : A + (M / r - 1) / 2 * 4 + 4 ≤ 4194304)
    (hr2 : 1 ≤ r) (hr : r < 2 ^ 20) (hv : v < 2 ^ 20) (h1 : 1 ≤ M / r)
    (hrq : readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 r))
    (hrm : readBytes mem (A + (M / r - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 v)) :
    ∃ y, run 14 ⟨x, bv 1100, mem, [], out, .running⟩ = ⟨y, bv 1100, mem, [], out, .running⟩ ∧
      y.get 16 = bv (k + 1) ∧ y.get 10 = iv (Z + v) ∧
      (∀ r : Reg, r ∉ ([10, 15, 16] : List Reg) → y.get r = x.get r) := by
  have := Nat.div_le_self M r
  have := add_int_nat
  exact ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

/-- The inner sum is done (`k = e + 1`): subtract `(e - l)(C + l - 1)` and go to row `l + 1`. -/
theorem inner_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (l a6 e : Nat) (Z : Int)
    (hmem : Prefix image mem 1480)
    (h16 : x.get 16 = bv (e + 1)) (h30 : x.get 30 = bv e) (h14 : x.get 14 = bv e)
    (h17 : x.get 17 = bv l) (h6 : x.get 6 = bv a6) (h10 : x.get 10 = iv Z)
    (hle : l + 1 ≤ e) (he : e < 200000) (ha6 : a6 < 400000) :
    ∃ y, run 7 ⟨x, bv 1100, mem, [], out, .running⟩ = ⟨y, bv 1032, mem, [], out, .running⟩ ∧
      y.get 6 = bv (a6 + 1) ∧ y.get 10 = iv (Z - ((e - l) * a6 : Nat)) ∧
      (∀ r : Reg, r ∉ ([6, 10, 14, 15] : List Reg) → y.get r = x.get r) := by
  have := sub_int
  have : (e - l) * a6 < 200000 * 400000 := Nat.mul_lt_mul'' (by omega) ha6
  exact ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

theorem inner_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B M k e : Nat) (Z : Int)
    (sm q : Nat → Nat)
    (hmem : Prefix image mem 1480)
    (h16 : x.get 16 = bv k) (h10 : x.get 10 = iv Z) (h30 : x.get 30 = bv e) (h29 : x.get 29 = bv M)
    (h9 : x.get 9 = bv B) (h8 : x.get 8 = bv A)
    (hk : k ≤ e + 1) (he : e < 200000) (hM : M < 2 ^ 40) (hA : 1480 ≤ A)
    (hro : ∀ j, k ≤ j → j ≤ e →
      readBytes mem (B + j * 4) 4 = some (BitVec.ofNat 32 (q j)) ∧ B + j * 4 + 4 ≤ 4194304 ∧
      1 ≤ q j ∧ q j < 2 ^ 20 ∧ 1 ≤ M / q j ∧ A + (M / q j - 1) / 2 * 4 + 4 ≤ 4194304 ∧
      readBytes mem (A + (M / q j - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 (smd sm (M / q j))) ∧
      smd sm (M / q j) < 2 ^ 20) :
    ∃ n y, run n ⟨x, bv 1100, mem, [], out, .running⟩ = ⟨y, bv 1100, mem, [], out, .running⟩ ∧
      y.get 16 = bv (e + 1) ∧ y.get 10 = iv (Z + sumR (fun j => smd sm (M / q j)) k (e + 1)) ∧
      (∀ r : Reg, r ∉ ([10, 15, 16] : List Reg) → y.get r = x.get r) := by
  by_cases hke : k ≤ e
  · obtain ⟨hr1, hb1, hq1, hq2, hd1, ha1, hr2, hv⟩ := hro k (by omega) hke
    obtain ⟨y1, hrun1, hy16, hy10, g1⟩ := inner_step x mem out A B M k e (q k) (smd sm (M / q k)) Z
      hmem h16 h10 h30 h29 h9 h8 hke he hM hA hb1 ha1 hq1 hq2 hv hd1 hr1 hr2
    obtain ⟨n, y, hrun, hy16', hy10', g⟩ := inner_loop y1 mem out A B M (k + 1) e
      (Z + smd sm (M / q k)) sm q hmem hy16 hy10 (by rw [g1 30 (by decide), h30])
      (by rw [g1 29 (by decide), h29]) (by rw [g1 9 (by decide), h9]) (by rw [g1 8 (by decide), h8])
      (by omega) he hM hA (fun j h1 h2 => hro j (by omega) h2)
    refine ⟨14 + n, y, by rw [run_add, hrun1, hrun], hy16', ?_, ?_⟩
    · rw [hy10', sumR_succ _ k (e + 1) (by omega)]; congr 1; push_cast; omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [hr]), g1 r (by simp [hr])]
  · obtain rfl : k = e + 1 := by omega
    refine ⟨0, x, rfl, h16, by rw [sumR_self _ _ _ (by omega)]; simpa using h10, fun _ _ => rfl⟩
termination_by e + 1 - k

/-- What the triple loop at 1032 needs, on the arrays it reads. `D` bounds the arguments of
`small`. -/
structure ZFH (mem : Array (BitVec 8)) (A B N s pc D : Nat) (sm q : Nat → Nat) : Prop where
  hs : s < 200000
  hpc : pc < 200000
  hN : N < 2 ^ 40
  hA : 1480 ≤ A
  hB : B + s * 4 ≤ 4194304
  pre : Prefix image mem 1480
  ro : ∀ k, 1 ≤ k → k < s →
    readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 (q k)) ∧ 1 ≤ q k ∧ q k < 2 ^ 20
  smr : ∀ d, 1 ≤ d → d ≤ D →
    readBytes mem (A + (d - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 (smd sm d)) ∧
      A + (d - 1) / 2 * 4 + 4 ≤ 4194304 ∧ smd sm d < 2 ^ 20
  dl : ∀ l, 1 ≤ l → l < s → 1 ≤ N / q l / q l ∧ N / q l / q l ≤ D
  dk : ∀ l k, 1 ≤ l → l < k → k < s → 1 ≤ N / q l / q k ∧ N / q l / q k ≤ D
  el : ∀ l, 1 ≤ l → l < s → smd sm (N / q l / q l) < pc + s

/-- The triple loop at 1032, from row `l` to `pi`'s return at 620. -/
theorem tri_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B N s pc D l : Nat)
    (sm q : Nat → Nat) (Z : Int) (h : ZFH mem A B N s pc D sm q)
    (h11 : x.get 11 = bv l) (h13 : x.get 13 = bv s) (h28 : x.get 28 = bv N) (h9 : x.get 9 = bv B)
    (h8 : x.get 8 = bv A) (h12 : x.get 12 = bv pc) (h6 : x.get 6 = bv (pc + l - 1))
    (h10 : x.get 10 = iv Z) (hl1 : 1 ≤ l) (hl : l ≤ s) :
    ∃ n y, run n ⟨x, bv 1032, mem, [], out, .running⟩ = ⟨y, bv 620, mem, [], out, .running⟩ ∧
      y.get 10 = iv (Z + triLoop sm q N s pc l) ∧
      (∀ r : Reg, r ∉ ([6, 10, 11, 14, 15, 16, 17, 29, 30] : List Reg) → y.get r = x.get r) := by
  have hs := h.hs
  have hpc := h.hpc
  have hN := h.hN
  have hA := h.hA
  have hB := h.hB
  by_cases hls : l < s
  · obtain ⟨hrq, hq1, hq2⟩ := h.ro l hl1 hls
    obtain ⟨hd1, hd2⟩ := h.dl l hl1 hls
    obtain ⟨hrm, hma, hm⟩ := h.smr _ hd1 hd2
    have hel := h.el l hl1 hls
    by_cases hbrk : smd sm (N / q l / q l) < pc + l + 1
    · obtain ⟨y, hr, g⟩ := tri_break x mem out A B N s pc l (q l) (smd sm (N / q l / q l)) h.pre
        h11 h13 h28 h9 h8 h12 hls hs hN hpc hA (by omega) (by omega) hq1 hq2 hm hd1 hrq hrm hbrk
      refine ⟨15, y, hr, ?_, ?_⟩
      · rw [g 10 (by decide), h10, triLoop, if_pos hls, if_pos hbrk]; simp
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact g r (by simp [hr])
    · have hcont : pc + l + 1 ≤ smd sm (N / q l / q l) := by omega
      obtain ⟨y1, hr1, y29, y16, y11, y14, y30, y17, g1⟩ := tri_cont x mem out A B N s pc l (q l)
        (smd sm (N / q l / q l)) h.pre h11 h13 h28 h9 h8 h12 hls hs hN hpc hA (by omega) (by omega)
        hq1 hq2 hm hd1 hrq hrm hcont
      have hND : N / q l < 2 ^ 40 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hN
      obtain ⟨n2, y2, hr2, z16, z10, g2⟩ := inner_loop y1 mem out A B (N / q l) (l + 1)
        (smd sm (N / q l / q l) - pc) Z sm q h.pre y16 (by rw [g1 10 (by decide), h10]) y30 y29
        (by rw [g1 9 (by decide), h9]) (by rw [g1 8 (by decide), h8]) (by omega) (by omega) hND hA
        (fun j h1 h2 => by
          obtain ⟨r1, a1, b1⟩ := h.ro j (by omega) (by omega)
          obtain ⟨e1, e2⟩ := h.dk l j hl1 (by omega) (by omega)
          obtain ⟨r2, a2, b2⟩ := h.smr _ e1 e2
          exact ⟨r1, by omega, a1, b1, e1, by omega, r2, b2⟩)
      obtain ⟨y3, hr3, z6, z10', g3⟩ := inner_exit y2 mem out l (pc + l - 1)
        (smd sm (N / q l / q l) - pc)
        (Z + sumR (fun j => smd sm (N / q l / q j)) (l + 1) (smd sm (N / q l / q l) - pc + 1))
        h.pre z16 (by rw [g2 30 (by decide), y30]) (by rw [g2 14 (by decide), y14])
        (by rw [g2 17 (by decide), y17]) (by rw [g2 6 (by decide), g1 6 (by decide), h6]) z10
        (by omega) (by omega) (by omega)
      have f3 : ∀ r : Reg, r ∉ ([6, 10, 11, 14, 15, 16, 17, 29, 30] : List Reg) → y3.get r = x.get r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [g3 r (by simp [hr]), g2 r (by simp [hr]), g1 r (by simp [hr])]
      obtain ⟨n4, y4, hr4, z4, g4⟩ := tri_loop y3 mem out A B N s pc D (l + 1) sm q _ h
        (by rw [g3 11 (by decide), g2 11 (by decide), y11])
        (by rw [f3 13 (by decide), h13]) (by rw [f3 28 (by decide), h28]) (by rw [f3 9 (by decide), h9])
        (by rw [f3 8 (by decide), h8]) (by rw [f3 12 (by decide), h12]) (by rw [z6]; congr 1; omega)
        z10' (by omega) (by omega)
      refine ⟨17 + n2 + 7 + n4, y4, by rw [run_add, run_add, run_add, hr1, hr2, hr3, hr4], ?_, ?_⟩
      · rw [z4]; congr 1
        rw [triLoop.eq_1 sm q N s pc l, if_pos hls, if_neg hbrk]; push_cast; omega
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [g4 r (by simp [hr]), f3 r (by simp [hr])]
  · obtain rfl : l = s := by omega
    obtain ⟨y, hr, g⟩ := tri_exit x mem out l h.pre h11 h13 hs
    refine ⟨2, y, hr, ?_, ?_⟩
    · rw [g 10 (by decide), h10, triLoop, if_neg hls]; simp
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact g r (by simp [hr])
termination_by s - l

end TinyFive.ZjyBinary
