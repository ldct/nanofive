import LphaBinary.Round
import LphaBinary.NoWrap
import LphaBinary.PiBound
import GrumpyBinary.FinishRun
/-! The finish of `prime_count` from 552: `ret = 1 + larges[0] - larges[1..s)`, the triangular term,
and the triple loop at 680, all in 32-bit arithmetic, then the return to the driver at 684. The
running total is a sign-extended `uint32_t`, tracked as `sx Z` for an integer `Z`. -/
namespace TinyFive.LphaBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary
local notation "bv" => BitVec.ofNat 64

/-- A sign-extended 32-bit value. -/
abbrev sx (z : Int) : BitVec 64 := (BitVec.ofInt 32 z).signExtend 64

theorem fin_pro (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (L0 : Nat)
    (hmem : Prefix image mem 1536) (h2 : x.get 2 = bv 715648) (h11 : x.get 11 = bv LB)
    (hL : readBytes mem LB 4 = some (BitVec.ofNat 32 L0)) :
    ∃ y, run 9 ⟨x, bv 552, mem, [], out, .running⟩ = ⟨y, bv 588, mem, [], out, .running⟩ ∧
      y.get 10 = bv 1 ∧ y.get 15 = sx ((L0 + 1 : Nat) : Int) ∧
      (∀ r : Reg, r ∉ ([10, 15] : List Reg) → y.get r = x.get r) := by
  have e1 : alu .add (3478512#64) (BitVec.signExtend 64 4292435968#32) = 947184#64 := by decide
  have e2 : alu .add (947184#64) 715680#64 = 1662864#64 := by decide
  exact ⟨_, by lexec; rfl, by rg, by rg, by frame_tac⟩

theorem sub32_nat (Z : Int) (L : Nat) :
    alu .sub (BitVec.ofInt 32 Z) (BitVec.ofNat 32 L) = BitVec.ofInt 32 (Z - L) := by
  simp only [alu]
  rw [show Z - (L : Int) = Z + -(L : Int) by omega, BitVec.ofInt_add, BitVec.ofInt_neg,
    BitVec.ofInt_natCast, BitVec.sub_eq_add_neg]

theorem lsub_step (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s k Lk : Nat) (Z : Int)
    (hmem : Prefix image mem 1536) (h10 : x.get 10 = bv k) (h11 : x.get 11 = bv (1664364 + k * 4))
    (h15 : x.get 15 = sx Z) (h8 : x.get 8 = bv s) (hk : k < s) (hs : s < 200000)
    (hL : readBytes mem (LB + k * 4) 4 = some (BitVec.ofNat 32 Lk)) :
    ∃ y, run 6 ⟨x, bv 588, mem, [], out, .running⟩ = ⟨y, bv 588, mem, [], out, .running⟩ ∧
      y.get 10 = bv (k + 1) ∧ y.get 11 = bv (1664364 + (k + 1) * 4) ∧ y.get 15 = sx (Z - Lk) ∧
      (∀ r : Reg, r ∉ ([0, 10, 11, 15, 16] : List Reg) → y.get r = x.get r) := by
  have := sub32_nat
  exact ⟨_, by lexec; rfl, by rg, by rg, by rg, by frame_tac⟩

theorem add32_nn (A B : Nat) :
    alu .add (BitVec.ofNat 32 A) (BitVec.ofNat 32 B) = BitVec.ofNat 32 (A + B) := by
  simp only [alu]; rw [BitVec.ofNat_add]

theorem add32_ni (C : Nat) (Z : Int) :
    alu .add (BitVec.ofNat 32 C) (BitVec.ofInt 32 Z) = BitVec.ofInt 32 (C + Z) := by
  simp only [alu]; rw [BitVec.ofInt_add, BitVec.ofInt_natCast]

theorem setWidth_bv32 (X : Nat) : BitVec.setWidth 32 (bv X) = BitVec.ofNat 32 X := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd X (by decide)

theorem srl1 (X : Nat) (h : X < 2 ^ 64) : alu .srl (bv X) 1#64 = bv (X / 2) := by
  simp only [alu]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show X / 2 < 2 ^ 64 by omega)]

theorem lsub_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s pc : Nat) (Z : Int)
    (hmem : Prefix image mem 1536) (h10 : x.get 10 = bv s) (h11 : x.get 11 = bv (1664364 + s * 4))
    (h15 : x.get 15 = sx Z) (h8 : x.get 8 = bv s) (h14 : x.get 14 = bv pc) (h2 : x.get 2 = bv 715648)
    (hs1 : 1 ≤ s) (hs : s < 200000) (hpc : pc < 200000) :
    ∃ y, run 23 ⟨x, bv 588, mem, [], out, .running⟩ = ⟨y, bv 680, mem, [], out, .running⟩ ∧
      y.get 10 = sx (((pc + 4294967295) * (s - 1) + (s - 1) * s / 2 : Nat) + Z) ∧
      y.get 16 = bv 1 ∧ y.get 30 = (BitVec.ofNat 32 (pc + 4294967294)).signExtend 64 ∧
      y.get 6 = bv 1032080 ∧ y.get 17 = bv IB ∧
      (∀ r : Reg, r ∉ ([6, 10, 11, 15, 16, 17, 30] : List Reg) → y.get r = x.get r) := by
  have := add32_nn
  have := add32_ni
  have := setWidth_bv32
  have hb : (s - 1) * s < 2 ^ 64 := by
    have := Nat.mul_le_mul (show s - 1 ≤ 200000 by omega) (show s ≤ 200000 by omega); omega
  have := srl1 _ hb
  have e1 : alu .add (3478512#64) (BitVec.signExtend 64 4291805184#32) = 316400#64 := by decide
  have e2 : alu .add (316400#64) 715680#64 = 1032080#64 := by decide
  have e3 : alu .add (BitVec.signExtend 64 4293701632#32) 752#64 = 18446744073708286704#64 := by decide
  have e4 : alu .add (3478512#64) 18446744073708286704#64 = 2213600#64 := by decide
  have e5 : alu .add (2213600#64) 715680#64 = 2929280#64 := by decide
  exact ⟨_, by lexec; rfl, by rg, by rg, by rg, by rg, by rg, by frame_tac⟩


theorem ofInt32_congr (a b : Int) (h : a % 4294967296 = b % 4294967296) :
    BitVec.ofInt 32 a = BitVec.ofInt 32 b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  show (a % ((2 ^ 32 : Nat) : Int)).toNat = (b % ((2 ^ 32 : Nat) : Int)).toNat
  rw [show ((2 ^ 32 : Nat) : Int) = 4294967296 from rfl, h]

/-! ## Subtracting the large counts (loop at 588) -/

theorem lsub_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s k : Nat) (f : Nat → Nat)
    (Z : Int) (hmem : Prefix image mem 1536) (h10 : x.get 10 = bv k)
    (h11 : x.get 11 = bv (1664364 + k * 4)) (h15 : x.get 15 = sx Z) (h8 : x.get 8 = bv s)
    (hk1 : 1 ≤ k) (hk : k ≤ s) (hs : s < 200000)
    (hla : ∀ j, k ≤ j → j < s → readBytes mem (LB + j * 4) 4 = some (BitVec.ofNat 32 (f j))) :
    ∃ n y, run n ⟨x, bv 588, mem, [], out, .running⟩ = ⟨y, bv 588, mem, [], out, .running⟩ ∧
      y.get 10 = bv s ∧ y.get 11 = bv (1664364 + s * 4) ∧ y.get 15 = sx (Z - sumR f k s) ∧
      (∀ r : Reg, r ∉ ([0, 10, 11, 15, 16] : List Reg) → y.get r = x.get r) := by
  by_cases hks : k < s
  · obtain ⟨y1, hr1, y10, y11, y15, g1⟩ := lsub_step x mem out s k (f k) Z hmem h10 h11 h15 h8 hks hs
      (hla k (Nat.le_refl k) hks)
    obtain ⟨n, y, hr, z10, z11, z15, g⟩ := lsub_loop y1 mem out s (k + 1) f (Z - f k) hmem y10 y11 y15
      (by rw [g1 8 (by decide), h8]) (by omega) (by omega) hs (fun j h1 h2 => hla j (by omega) h2)
    refine ⟨6 + n, y, by rw [run_add, hr1, hr], z10, z11, ?_, ?_⟩
    · rw [z15, sumR_succ f k s hks, show Z - (f k : Int) - (sumR f (k + 1) s : Int) =
        Z - ((f k + sumR f (k + 1) s : Nat) : Int) by push_cast; omega]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [hr]), g1 r (by simp [hr])]
  · obtain rfl : k = s := by omega
    refine ⟨0, x, rfl, h10, h11, by rw [sumR_self f k k (Nat.le_refl k)]; simpa using h15,
      fun _ _ => rfl⟩
termination_by s - k

/-- The triangular term, modulo `2^32`. -/
theorem tri_cong (s pc : Nat) (hs : 1 ≤ s) :
    ((((pc + 4294967295) * (s - 1) + (s - 1) * s / 2 : Nat) : Int)) % 4294967296 =
      ((tri s pc : Nat) : Int) % 4294967296 := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel, tri]
  have hev : (u * (u + 1)) % 2 = 0 := by
    rw [Nat.mul_mod]; rcases Nat.mod_two_eq_zero_or_one u with h | h <;>
      simp [h, Nat.add_mod]
  have hc : (u + 1) * u = u * (u + 1) := Nat.mul_comm _ _
  rcases Nat.eq_zero_or_pos pc with h0 | hpc
  · subst h0
    have e1 : (4294967295 + 0) * u = 4294967296 * u - u := by omega
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simp
    · have e2 : u + 1 + 2 * 0 - 2 = u - 1 := by omega
      have e3 : (u - 1) * u + 2 * u = u * (u + 1) := by
        rw [show u + 1 = (u - 1) + 2 by omega, Nat.mul_add, Nat.mul_comm u (u - 1)]; omega
      rw [e1, e2]
      omega
  · have e1 : (pc + 4294967295) * u = (pc - 1) * u + 4294967296 * u := by
      rw [show pc + 4294967295 = (pc - 1) + 4294967296 by omega, Nat.add_mul, Nat.mul_comm 4294967296 u]
    have e2 : (u + 1 + 2 * pc - 2) * u = u * (u + 1) + 2 * ((pc - 1) * u) := by
      rw [show u + 1 + 2 * pc - 2 = (u + 1) + 2 * (pc - 1) by omega, Nat.add_mul, Nat.mul_assoc, hc]
    rw [e1, e2]
    omega

theorem lsub_run (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s pc L0 : Nat)
    (f : Nat → Nat) (hmem : Prefix image mem 1536) (h2 : x.get 2 = bv 715648)
    (h11 : x.get 11 = bv LB) (h8 : x.get 8 = bv s) (h14 : x.get 14 = bv pc)
    (hs1 : 1 ≤ s) (hs : s < 200000) (hpc : pc < 200000)
    (hL : readBytes mem LB 4 = some (BitVec.ofNat 32 L0))
    (hla : ∀ j, 1 ≤ j → j < s → readBytes mem (LB + j * 4) 4 = some (BitVec.ofNat 32 (f j))) :
    ∃ n y, run n ⟨x, bv 552, mem, [], out, .running⟩ = ⟨y, bv 680, mem, [], out, .running⟩ ∧
      y.get 10 = sx (((L0 + 1 : Nat) : Int) - sumR f 1 s + tri s pc) ∧
      y.get 16 = bv 1 ∧ y.get 30 = (BitVec.ofNat 32 (pc + 4294967294)).signExtend 64 ∧
      y.get 6 = bv 1032080 ∧ y.get 17 = bv IB ∧
      (∀ r : Reg, r ∉ ([0, 6, 10, 11, 15, 16, 17, 30] : List Reg) → y.get r = x.get r) := by
  obtain ⟨y1, hr1, y10, y15, g1⟩ := fin_pro x mem out L0 hmem h2 h11 hL
  obtain ⟨n2, y2, hr2, z10, z11, z15, g2⟩ := lsub_loop y1 mem out s 1 f _ hmem y10
    (by rw [g1 11 (by decide), h11]) y15 (by rw [g1 8 (by decide), h8]) (Nat.le_refl 1) hs1 hs hla
  have f2 : ∀ r : Reg, r ∉ ([0, 10, 11, 15, 16] : List Reg) → y2.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g2 r (by simp [hr]), g1 r (by simp [hr])]
  obtain ⟨y3, hr3, w10, w16, w30, w6, w17, g3⟩ := lsub_exit y2 mem out s pc _ hmem z10 z11 z15
    (by rw [f2 8 (by decide), h8]) (by rw [f2 14 (by decide), h14]) (by rw [f2 2 (by decide), h2])
    hs1 hs hpc
  refine ⟨9 + n2 + 23, y3, by rw [run_add, run_add, hr1, hr2, hr3], ?_, w16, w30, w6, w17, ?_⟩
  · rw [w10]
    exact congrArg (BitVec.signExtend 64) (ofInt32_congr _ _ (by have := tri_cong s pc hs1; omega))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3 r (by simp [hr]), f2 r (by simp [hr])]

/-! ## The triple loop (680, inner loop at 1444) -/

theorem ltri_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s : Nat)
    (hmem : Prefix image mem 1536) (h16 : x.get 16 = bv s) (h8 : x.get 8 = bv s) (hs : s < 200000) :
    run 1 ⟨x, bv 680, mem, [], out, .running⟩ = ⟨x, bv 684, mem, [], out, .running⟩ := by
  lexec

/-- Row `l` ends the loop: `k2_max = smalls[half(N/q/q)] - pc ≤ l`. -/
theorem ltri_break (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s pc l q D m : Nat)
    (hmem : Prefix image mem 1536) (h16 : x.get 16 = bv l) (h12 : x.get 12 = bv (2296820 + l * 4))
    (h13 : x.get 13 = bv (2929272 + l * 8)) (h8 : x.get 8 = bv s) (h14 : x.get 14 = bv pc)
    (h6 : x.get 6 = bv 1032080)
    (hl : l < s) (hs : s < 200000) (hpc : pc < 200000) (hq1 : 1 ≤ q) (hq : q < 316228)
    (hD : D < 100000000000) (hd1 : 1 ≤ D / q) (hm : m < 200000) (hpm : pc ≤ m) (hbrk : m - pc ≤ l)
    (hrq : readBytes mem (RB + l * 4) 4 = some (BitVec.ofNat 32 q))
    (hrD : readBytes mem (IB + l * 8) 8 = some (bv D))
    (hrm : readBytes mem (SB + (D / q - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 m)) :
    ∃ y, run 13 ⟨x, bv 680, mem, [], out, .running⟩ = ⟨y, bv 684, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([11, 15, 31] : List Reg) → y.get r = x.get r) := by
  have := Nat.div_le_self D q
  exact ⟨_, by lexec; rfl, by frame_tac⟩

/-- Row `l` goes on: `k2_max = smalls[half(N/q/q)] - pc > l`. -/
theorem ltri_cont (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s pc l q D m : Nat)
    (hmem : Prefix image mem 1536) (h16 : x.get 16 = bv l) (h12 : x.get 12 = bv (2296820 + l * 4))
    (h13 : x.get 13 = bv (2929272 + l * 8)) (h8 : x.get 8 = bv s) (h14 : x.get 14 = bv pc)
    (h6 : x.get 6 = bv 1032080)
    (hl : l < s) (hs : s < 200000) (hpc : pc < 200000) (hq1 : 1 ≤ q) (hq : q < 316228)
    (hD : D < 100000000000) (hd1 : 1 ≤ D / q) (hm : m < 200000) (hcont : pc + l + 1 ≤ m)
    (hrq : readBytes mem (RB + l * 4) 4 = some (BitVec.ofNat 32 q))
    (hrD : readBytes mem (IB + l * 8) 8 = some (bv D))
    (hrm : readBytes mem (SB + (D / q - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 m)) :
    ∃ y, run 15 ⟨x, bv 680, mem, [], out, .running⟩ = ⟨y, bv 1444, mem, [], out, .running⟩ ∧
      y.get 31 = bv q ∧ y.get 11 = bv (m - pc) ∧ y.get 28 = bv (l + 1) ∧ y.get 29 = bv (l + 1) ∧
      (∀ r : Reg, r ∉ ([11, 15, 28, 29, 31] : List Reg) → y.get r = x.get r) := by
  have := Nat.div_le_self D q
  exact ⟨_, by lexec; rfl, by rg, by rg, by rg, by rg, by frame_tac⟩

/-- One term of the inner sum: `ret += smalls[half(invs[k] / q)]`. -/
theorem linner_step (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (k e q Dk v : Nat) (T : Int)
    (hmem : Prefix image mem 1536) (h28 : x.get 28 = bv k) (h11 : x.get 11 = bv e)
    (h31 : x.get 31 = bv q) (h17 : x.get 17 = bv IB) (h6 : x.get 6 = bv 1032080)
    (h10 : x.get 10 = sx T)
    (hke : k ≤ e) (he : e < 200000) (hq1 : 1 ≤ q) (hq : q < 316228) (hD : Dk < 100000000000)
    (hd1 : 1 ≤ Dk / q) (hv : v < 200000)
    (hrD : readBytes mem (IB + k * 8) 8 = some (bv Dk))
    (hrm : readBytes mem (SB + (Dk / q - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 v)) :
    ∃ y, run 13 ⟨x, bv 1444, mem, [], out, .running⟩ = ⟨y, bv 1444, mem, [], out, .running⟩ ∧
      y.get 28 = bv (k + 1) ∧ y.get 10 = sx (v + T) ∧
      (∀ r : Reg, r ∉ ([0, 10, 15, 28] : List Reg) → y.get r = x.get r) := by
  have := Nat.div_le_self Dk q
  have := add32_ni
  exact ⟨_, by lexec; rfl, by rg, by rg, by frame_tac⟩

/-- The inner sum is done (`k = e + 1`): `ret -= (e - l)(pc + l - 1)`, next row. -/
theorem linner_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (l e pc : Nat) (T : Int)
    (hmem : Prefix image mem 1536) (h28 : x.get 28 = bv (e + 1)) (h11 : x.get 11 = bv e)
    (h16 : x.get 16 = bv l) (h29 : x.get 29 = bv (l + 1))
    (h30 : x.get 30 = (BitVec.ofNat 32 (pc + 4294967294)).signExtend 64)
    (h12 : x.get 12 = bv (2296820 + l * 4)) (h13 : x.get 13 = bv (2929272 + l * 8))
    (h10 : x.get 10 = sx T) (hl1 : 1 ≤ l) (hle : l + 1 ≤ e) (he : e < 200000) (hpc : pc < 200000) :
    ∃ y, run 9 ⟨x, bv 1444, mem, [], out, .running⟩ = ⟨y, bv 680, mem, [], out, .running⟩ ∧
      y.get 16 = bv (l + 1) ∧ y.get 12 = bv (2296820 + (l + 1) * 4) ∧
      y.get 13 = bv (2929272 + (l + 1) * 8) ∧
      y.get 10 = sx (T - (((e - l) * (pc + l - 1) : Nat) : Int)) ∧
      (∀ r : Reg, r ∉ ([0, 10, 11, 12, 13, 15, 16] : List Reg) → y.get r = x.get r) := by
  have := sub32_nat
  have hc : BitVec.ofInt 32 (T - ((pc : Int) + 4294967294 + ((l : Int) + 1)) * ((e - l : Nat) : Int)) =
      BitVec.ofInt 32 (T - (((e - l) * (pc + l - 1) : Nat) : Int)) := by
    apply ofInt32_congr
    have e1 : (((e - l) * (pc + l - 1) : Nat) : Int) = ((pc + l - 1 : Nat) : Int) * ((e - l : Nat) : Int) := by
      rw [Nat.mul_comm]; exact Int.natCast_mul _ _
    have e2 : ((pc : Int) + 4294967294 + ((l : Int) + 1)) = ((pc + l - 1 : Nat) : Int) + 4294967296 := by
      omega
    rw [e1, e2, Int.add_mul]
    omega
  exact ⟨_, by lexec; rfl, by rg, by rg, by rg, by rg, by frame_tac⟩

/-- `N / x / y = N / y / x`. -/
theorem div_div_swap (N x y : Nat) : N / x / y = N / y / x := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem linner_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N Q k e : Nat)
    (sm q : Nat → Nat) (T : Int)
    (hmem : Prefix image mem 1536) (h28 : x.get 28 = bv k) (h11 : x.get 11 = bv e)
    (h31 : x.get 31 = bv Q) (h17 : x.get 17 = bv IB) (h6 : x.get 6 = bv 1032080)
    (h10 : x.get 10 = sx T)
    (hk : k ≤ e + 1) (he : e < 200000) (hQ1 : 1 ≤ Q) (hQ : Q < 316228) (hN : N < 100000000000)
    (hro : ∀ j, k ≤ j → j ≤ e →
      readBytes mem (IB + j * 8) 8 = some (bv (N / q j)) ∧ 1 ≤ N / q j / Q ∧
      readBytes mem (SB + (N / q j / Q - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 (smd sm (N / q j / Q))) ∧
      smd sm (N / q j / Q) < 200000) :
    ∃ n y, run n ⟨x, bv 1444, mem, [], out, .running⟩ = ⟨y, bv 1444, mem, [], out, .running⟩ ∧
      y.get 28 = bv (e + 1) ∧
      y.get 10 = sx (T + (sumR (fun j => smd sm (N / q j / Q)) k (e + 1) : Nat)) ∧
      (∀ r : Reg, r ∉ ([0, 10, 15, 28] : List Reg) → y.get r = x.get r) := by
  by_cases hke : k ≤ e
  · obtain ⟨hr1, hd1, hr2, hv⟩ := hro k (Nat.le_refl k) hke
    obtain ⟨y1, hrun1, y28, y10, g1⟩ := linner_step x mem out k e Q (N / q k) (smd sm (N / q k / Q)) T
      hmem h28 h11 h31 h17 h6 h10 hke he hQ1 hQ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hN) hd1 hv
      hr1 hr2
    obtain ⟨n, y, hrun, z28, z10, g⟩ := linner_loop y1 mem out N Q (k + 1) e sm q _ hmem y28
      (by rw [g1 11 (by decide), h11]) (by rw [g1 31 (by decide), h31])
      (by rw [g1 17 (by decide), h17]) (by rw [g1 6 (by decide), h6]) y10 (by omega) he hQ1 hQ hN
      (fun j h1 h2 => hro j (by omega) h2)
    refine ⟨13 + n, y, by rw [run_add, hrun1, hrun], z28, ?_, ?_⟩
    · rw [z10, sumR_succ _ k (e + 1) (by omega)]; exact congrArg sx (by push_cast; omega)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [hr]), g1 r (by simp [hr])]
  · obtain rfl : k = e + 1 := by omega
    exact ⟨0, x, rfl, h28, by rw [sumR_self _ _ _ (Nat.le_refl _)]; simpa using h10, fun _ _ => rfl⟩
termination_by e + 1 - k

/-- What the triple loop needs, on the tables it reads. -/
structure LH (mem : Array (BitVec 8)) (N s pc D : Nat) (sm q : Nat → Nat) : Prop where
  hs : s < 200000
  hpc : pc < 200000
  hN : N < 100000000000
  pre : Prefix image mem 1536
  ro : ∀ k, 1 ≤ k → k < s →
    readBytes mem (RB + k * 4) 4 = some (BitVec.ofNat 32 (q k)) ∧ 1 ≤ q k ∧ q k < 316228
  iv : ∀ k, 1 ≤ k → k < s → readBytes mem (IB + k * 8) 8 = some (bv (N / q k))
  smr : ∀ d, 1 ≤ d → d ≤ D →
    readBytes mem (SB + (d - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 (smd sm d)) ∧ smd sm d < 200000
  dl : ∀ l, 1 ≤ l → l < s → 1 ≤ N / q l / q l ∧ N / q l / q l ≤ D
  dk : ∀ l k, 1 ≤ l → l < k → k < s → 1 ≤ N / q l / q k ∧ N / q l / q k ≤ D
  el : ∀ l, 1 ≤ l → l < s → smd sm (N / q l / q l) < pc + s
  lo : ∀ l, 1 ≤ l → l < s → (l = 1 ∨ pc + l ≤ smd sm (N / q (l - 1) / q (l - 1))) →
    pc ≤ smd sm (N / q l / q l)

theorem ltri_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N s pc D l : Nat)
    (sm q : Nat → Nat) (Z : Int) (h : LH mem N s pc D sm q)
    (h16 : x.get 16 = bv l) (h12 : x.get 12 = bv (2296820 + l * 4))
    (h13 : x.get 13 = bv (2929272 + l * 8)) (h8 : x.get 8 = bv s) (h14 : x.get 14 = bv pc)
    (h6 : x.get 6 = bv 1032080) (h17 : x.get 17 = bv IB)
    (h30 : x.get 30 = (BitVec.ofNat 32 (pc + 4294967294)).signExtend 64) (h10 : x.get 10 = sx Z)
    (hl1 : 1 ≤ l) (hl : l ≤ s) (hv : l = 1 ∨ pc + l ≤ smd sm (N / q (l - 1) / q (l - 1))) :
    ∃ n y, run n ⟨x, bv 680, mem, [], out, .running⟩ = ⟨y, bv 684, mem, [], out, .running⟩ ∧
      y.get 10 = sx (Z + triLoop sm q N s pc l) ∧
      (∀ r : Reg, r ∉ ([0, 10, 11, 12, 13, 15, 16, 28, 29, 31] : List Reg) → y.get r = x.get r) := by
  have hs := h.hs
  have hpc := h.hpc
  have hN := h.hN
  by_cases hls : l < s
  · obtain ⟨hrq, hq1, hq2⟩ := h.ro l hl1 hls
    have hrD := h.iv l hl1 hls
    obtain ⟨hd1, hd2⟩ := h.dl l hl1 hls
    obtain ⟨hrm, hm⟩ := h.smr _ hd1 hd2
    have hel := h.el l hl1 hls
    have hlo := h.lo l hl1 hls hv
    have hND : N / q l < 100000000000 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hN
    by_cases hbrk : smd sm (N / q l / q l) < pc + l + 1
    · obtain ⟨y, hr, g⟩ := ltri_break x mem out s pc l (q l) (N / q l) (smd sm (N / q l / q l)) h.pre
        h16 h12 h13 h8 h14 h6 hls hs hpc hq1 hq2 hND hd1 hm hlo (by omega) hrq hrD hrm
      refine ⟨13, y, hr, ?_, ?_⟩
      · rw [triLoop, if_pos hls, if_pos hbrk, g 10 (by decide), h10, Int.add_zero]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact g r (by simp [hr])
    · have hcont : pc + l + 1 ≤ smd sm (N / q l / q l) := by omega
      obtain ⟨y1, hr1, y31, y11, y28, y29, g1⟩ := ltri_cont x mem out s pc l (q l) (N / q l)
        (smd sm (N / q l / q l)) h.pre h16 h12 h13 h8 h14 h6 hls hs hpc hq1 hq2 hND hd1 hm hcont
        hrq hrD hrm
      obtain ⟨n2, y2, hr2, z28, z10, g2⟩ := linner_loop y1 mem out N (q l) (l + 1)
        (smd sm (N / q l / q l) - pc) sm q Z h.pre y28 y11 y31 (by rw [g1 17 (by decide), h17])
        (by rw [g1 6 (by decide), h6]) (by rw [g1 10 (by decide), h10]) (by omega) (by omega) hq1 hq2 hN
        (fun j h1 h2 => by
          have hjs : j < s := by omega
          have hr1 := h.iv j (by omega) hjs
          obtain ⟨e1, e2⟩ := h.dk l j hl1 (by omega) hjs
          rw [div_div_swap N (q j) (q l)]
          obtain ⟨r2, b2⟩ := h.smr _ e1 e2
          exact ⟨hr1, e1, r2, b2⟩)
      have f2 : ∀ r : Reg, r ∉ ([0, 10, 11, 15, 28, 29, 31] : List Reg) → y2.get r = x.get r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [g2 r (by simp [hr]), g1 r (by simp [hr])]
      obtain ⟨y3, hr3, w16, w12, w13, w10, g3⟩ := linner_exit y2 mem out l
        (smd sm (N / q l / q l) - pc) pc _ h.pre (by rw [z28])
        (by rw [g2 11 (by decide), y11]) (by rw [f2 16 (by decide), h16])
        (by rw [g2 29 (by decide), y29]) (by rw [f2 30 (by decide), h30])
        (by rw [f2 12 (by decide), h12]) (by rw [f2 13 (by decide), h13]) z10 hl1 (by omega)
        (by omega) hpc
      have f3 : ∀ r : Reg, r ∉ ([0, 10, 11, 12, 13, 15, 16, 28, 29, 31] : List Reg) →
          y3.get r = x.get r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [g3 r (by simp [hr]), f2 r (by simp [hr])]
      obtain ⟨n4, y4, hr4, u10, g4⟩ := ltri_loop y3 mem out N s pc D (l + 1) sm q _ h w16 w12 w13
        (by rw [f3 8 (by decide), h8]) (by rw [f3 14 (by decide), h14]) (by rw [f3 6 (by decide), h6])
        (by rw [f3 17 (by decide), h17]) (by rw [f3 30 (by decide), h30]) w10 (by omega) (by omega)
        (Or.inr (by rw [Nat.add_sub_cancel]; omega))
      refine ⟨15 + n2 + 9 + n4, y4, by rw [run_add, run_add, run_add, hr1, hr2, hr3, hr4], ?_, ?_⟩
      · have hsw : sumR (fun j => smd sm (N / q j / q l)) (l + 1) (smd sm (N / q l / q l) - pc + 1) =
            sumR (fun k => smd sm (N / q l / q k)) (l + 1) (smd sm (N / q l / q l) - pc + 1) := by
          simp only [div_div_swap N _ (q l)]
        rw [u10]
        exact congrArg sx (by rw [triLoop.eq_1 sm q N s pc l, if_pos hls, if_neg hbrk, ← hsw]; omega)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [g4 r (by simp [hr]), f3 r (by simp [hr])]
  · obtain rfl : l = s := by omega
    refine ⟨1, x, ltri_exit x mem out l h.pre h16 h8 hs, ?_, fun _ _ => rfl⟩
    rw [triLoop, if_neg hls, h10, Int.add_zero]
termination_by s - l

theorem zext_sx (R : Nat) (hR : R < 4294967296) :
    alu .srl (alu .sll (sx (R : Int)) 32#64) 32#64 = bv R := by
  have h1 : sx (R : Int) = (BitVec.ofNat 32 R).signExtend 64 := by
    show (BitVec.ofInt 32 (R : Int)).signExtend 64 = _; rw [BitVec.ofInt_natCast]
  have h2 := congrArg BitVec.toNat (sext_low32 (BitVec.ofNat 32 R))
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h2
  rw [h1]
  apply BitVec.eq_of_toNat_eq
  simp only [alu, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show (2 : Nat) ^ (32 % 2 ^ 64 % 64) = 4294967296 from rfl]
  generalize ((BitVec.ofNat 32 R).signExtend 64).toNat = X at h2 ⊢
  omega

/-! ## The return, and the driver's printing -/

/-- `return ret` at 684, then the driver zero-extends it, prints it and a newline, and exits. -/
theorem lfin_ret (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (R : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h2 : x.get 2 = bv 715648) (h10 : x.get 10 = sx (R : Int)) (hR : R < 4294967296)
    (hra : readBytes mem 4194296 8 = some (bv 8)) :
    is_exited_with_output (run 26 ⟨x, bv 684, mem, [], out, .running⟩) (out ++ toString R ++ "\n") := by
  obtain ⟨w1, hw1⟩ := readBytes_some mem 4194288 8 (by omega)
  obtain ⟨w2, hw2⟩ := readBytes_some mem 4194280 8 (by omega)
  obtain ⟨w3, hw3⟩ := readBytes_some mem 4194272 8 (by omega)
  obtain ⟨w4, hw4⟩ := readBytes_some mem 4194264 8 (by omega)
  obtain ⟨w5, hw5⟩ := readBytes_some mem 4194256 8 (by omega)
  obtain ⟨w6, hw6⟩ := readBytes_some mem 4194248 8 (by omega)
  obtain ⟨w7, hw7⟩ := readBytes_some mem 4194240 8 (by omega)
  obtain ⟨w8, hw8⟩ := readBytes_some mem 4194232 8 (by omega)
  obtain ⟨w9, hw9⟩ := readBytes_some mem 4194224 8 (by omega)
  obtain ⟨w10, hw10⟩ := readBytes_some mem 4194216 8 (by omega)
  obtain ⟨w11, hw11⟩ := readBytes_some mem 4194208 8 (by omega)
  obtain ⟨w12, hw12⟩ := readBytes_some mem 4194200 8 (by omega)
  have := out_eq out R (by omega)
  have := zext_sx R hR
  lexec
  exact ⟨rfl, rfl⟩

theorem isqrt_two : isqrt 2 = 1 := by
  obtain ⟨h1, h2⟩ := isqrt_spec 2
  rcases Nat.lt_or_ge (isqrt 2) 2 with h | h
  · rcases Nat.eq_zero_or_pos (isqrt 2) with h0 | h0
    · rw [h0] at h2; omega
    · omega
  · have := Nat.mul_le_mul h h; omega

/-- The finish's table facts, from the sieve invariant at the cutoff. -/
theorem inv_LH {N a : Nat} {x : Regs 64} {mem : Array (BitVec 8)} (h : Inv N a x mem) (hc : Cut N a) :
    LH mem N (RL N a).length (C a (a - 1)) (isqrt N) (fun i => C a (2 * i + 1)) (qq N a) := by
  have hvb := inv_vb h
  have hv1 : 1 ≤ isqrt N := le_isqrt (by have := hc.hN3; omega)
  have hlen := RL_len N a h.hp3 hv1
  have ha564 : a ≤ 564 := by
    apply Decidable.byContradiction; intro hc'
    have := h.hpr 563 (by decide) (by omega) prime_563'
    have := h.hN
    omega
  have hpc : C a (a - 1) ≤ a - 1 := C_le a _
  exact {
    hs := by omega
    hpc := by omega
    hN := h.hN
    pre := h.pre
    ro := fun k hk1 hk => by
      obtain ⟨hak, hkv, _⟩ := hc.qq_range k hk1 hk
      exact ⟨h.ro k hk, by have := hc.ha; omega, by omega⟩
    iv := fun k _ hk => h.iv k hk
    smr := fun d hd1 hdv => by
      refine ⟨h.sm ((d - 1) / 2) (by omega), ?_⟩
      rw [smd_C a d hc.ha hd1]
      have := C_le_half a d hc.ha
      omega
    dl := fun l hl1 hl => by
      obtain ⟨hal, hlv, _⟩ := hc.qq_range l hl1 hl
      exact hc.div2 _ _ hal hal hlv hlv
    dk := fun l k hl1 hlk hk => by
      obtain ⟨hal, hlv, _⟩ := hc.qq_range l hl1 (by omega)
      obtain ⟨hak, hkv, _⟩ := hc.qq_range k (by omega) hk
      exact hc.div2 _ _ hal hak hlv hkv
    el := fun l hl1 hl => by
      obtain ⟨hal, hlv, _⟩ := hc.qq_range l hl1 hl
      obtain ⟨hX1, hXv⟩ := hc.div2 _ _ hal hal hlv hlv
      rw [smd_C a _ hc.ha hX1]
      have := C_mono a hXv
      have := C_isqrt N a hc.ha (by omega)
      omega
    lo := fun l hl1 hl hv => by
      obtain ⟨hal, hlv, _⟩ := hc.qq_range l hl1 hl
      obtain ⟨hX1, _⟩ := hc.div2 _ _ hal hal hlv hlv
      rw [smd_C a _ hc.ha hX1]
      apply nowrap hc h.hpr l hl1 hl
      rcases hv with h1 | h2
      · exact Or.inl h1
      · by_cases hl' : l = 1
        · exact Or.inl hl'
        · obtain ⟨hal', hlv', _⟩ := hc.qq_range (l - 1) (by omega) (by omega)
          obtain ⟨hY1, _⟩ := hc.div2 _ _ hal' hal' hlv' hlv'
          rw [smd_C a _ hc.ha hY1] at h2
          exact Or.inr h2 }

/-- From the end of the sieve at the cutoff stage `a` (552) to the exit, having printed `π(N)`. -/
theorem lfinish_run (N a : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h : Inv N a x mem) (hcut : isqrt N < a * a) :
    ∃ n, is_exited_with_output (run n ⟨x, bv 552, mem, [], out, .running⟩)
      (out ++ toString (countPrimes N) ++ "\n") := by
  have ha3 := h.hp3
  have hvb := inv_vb h
  have hv1 : 1 ≤ isqrt N := le_isqrt (by have := h.hN2; omega)
  have hlen := RL_len N a h.hp3 hv1
  have hs1 : 1 ≤ (RL N a).length := by simp [RL]
  have ha564 : a ≤ 564 := by
    apply Decidable.byContradiction; intro hc'
    have := h.hpr 563 (by decide) (by omega) prime_563'
    have := h.hN
    omega
  have hpc : C a (a - 1) ≤ a - 1 := C_le a _
  have hL0 : readBytes mem LB 4 = some (BitVec.ofNat 32 (C a N)) := by
    have := h.la 0 hs1; simpa using this
  obtain ⟨n1, y1, hr1, y10, y16, y30, y6, y17, g1⟩ := lsub_run x mem out (RL N a).length (C a (a - 1))
    (C a N) (fun k => C a (N / qq N a k)) h.pre h.x2 h.x11 h.x8 h.x14 hs1 (by omega) (by omega) hL0
    (fun j _ hj => h.la j hj)
  have hR := LphaBinary.PiBound.countPrimes_lt N h.hN
  -- the value
  have hval : ((C a N + 1 : Nat) : Int) - (sumR (fun k => C a (N / qq N a k)) 1 (RL N a).length : Nat) +
      (tri (RL N a).length (C a (a - 1)) : Nat) +
      triLoop (fun i => C a (2 * i + 1)) (qq N a) N (RL N a).length (C a (a - 1)) 1 =
      countPrimes N := by
    rcases Nat.lt_or_ge N 3 with hN2 | hN3
    · obtain rfl : N = 2 := by have := h.hN2; omega
      have hv := isqrt_two
      have hrl : RL 2 a = [1] := by
        simp only [RL, roughList, hv]
        rw [show 1 + 1 - a = 0 by omega]; rfl
      have hC : C a 2 = 0 := by
        simp only [C, count]
        have h1 : ¬ Alive a 1 := fun h => by have := h.1; omega
        have h2 : ¬ Alive a 2 := fun h => by have := h.1; omega
        simp [h1, h2]
      rw [hrl, hC]
      simp [sumR, tri, triLoop]
      decide
    · have hc : Cut N a := ⟨hN3, h.hN, h.hp3, by
        have := Nat.mul_le_mul (show isqrt N + 1 ≤ a * a by omega) (show isqrt N + 1 ≤ a * a by omega)
        have := (isqrt_spec N).2
        omega⟩
      have := finish_value hc
      have h0 : qq N a 0 = 1 := rfl
      rw [h0, Nat.div_one] at this
      push_cast at this ⊢
      omega
  -- the triple loop, and the return
  have f1 : ∀ r : Reg, r ∉ ([0, 6, 10, 11, 15, 16, 17, 30] : List Reg) → y1.get r = x.get r := g1
  have hfin : ∃ n2 y2, run n2 ⟨y1, bv 680, mem, [], out, .running⟩ = ⟨y2, bv 684, mem, [], out, .running⟩ ∧
      y2.get 10 = sx (countPrimes N) ∧ y2.get 2 = bv 715648 := by
    rcases Nat.lt_or_ge N 3 with hN2 | hN3
    · obtain rfl : N = 2 := by have := h.hN2; omega
      have hrl : (RL 2 a).length = 1 := by
        have hv := isqrt_two
        simp only [RL, roughList, hv]
        rw [show 1 + 1 - a = 0 by omega]; rfl
      refine ⟨1, y1, ltri_exit y1 mem out 1 h.pre (by rw [y16]) (by rw [f1 8 (by decide), h.x8, hrl]) (by omega),
        ?_, by rw [f1 2 (by decide), h.x2]⟩
      rw [y10, ← hval]
      have hT : triLoop (fun i => C a (2 * i + 1)) (qq 2 a) 2 (RL 2 a).length (C a (a - 1)) 1 = 0 := by
        rw [triLoop, if_neg (by omega)]
      rw [hT, Int.add_zero]
    · have hc : Cut N a := ⟨hN3, h.hN, h.hp3, by
        have := Nat.mul_le_mul (show isqrt N + 1 ≤ a * a by omega) (show isqrt N + 1 ≤ a * a by omega)
        have := (isqrt_spec N).2
        omega⟩
      obtain ⟨n2, y2, hr2, z10, g2⟩ := ltri_loop y1 mem out N (RL N a).length (C a (a - 1)) (isqrt N) 1
        (fun i => C a (2 * i + 1)) (qq N a) _ (inv_LH h hc) y16 (by rw [f1 12 (by decide), h.x12])
        (by rw [f1 13 (by decide), h.x13]) (by rw [f1 8 (by decide), h.x8])
        (by rw [f1 14 (by decide), h.x14]) y6 y17 y30 y10 (Nat.le_refl 1) hs1 (Or.inl rfl)
      refine ⟨n2, y2, hr2, by rw [z10, hval], ?_⟩
      rw [g2 2 (by decide), f1 2 (by decide), h.x2]
  obtain ⟨n2, y2, hr2, z10, z2⟩ := hfin
  have hret := lfin_ret y2 mem out (countPrimes N) h.pre h.size z2 z10 hR h.ra
  exact ⟨n1 + n2 + 26, by rw [run_add, run_add, hr1, hr2]; exact hret⟩

end TinyFive.LphaBinary
