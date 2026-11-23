import GrumpyBinary.Outer

/-! The finish of `prime_pi` at 396: the triangular term, the subtraction of the large counts, and
the triple correction loops. The running total `larges[0]` is a signed 64-bit value; it is
tracked as `BitVec.ofInt 64 z`, so no step needs a bound on it. -/
namespace TinyFive.GrumpyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory

local notation "bv" => BitVec.ofNat 64
local notation "iv" => BitVec.ofInt 64

/-! ## Registers and signed arithmetic -/

theorem Regs.set_set' (x : Regs 64) (r : Reg) (a b : BitVec 64) : (x.set r a).set r b = x.set r b := by
  simp [Regs.set]

theorem Regs.set_comm' (x : Regs 64) (i j : Reg) (a b : BitVec 64) (h : i < j) :
    (x.set j a).set i b = (x.set i b).set j a := by
  simp only [Regs.set]; congr 1; exact Vector.set_comm _ _ (Fin.val_ne_of_ne (Fin.ne_of_lt h)).symm

/-- Sort the writes of a register file by register, keeping only the last write to each. -/
macro "regs_tac" : tactic => `(tactic| simp (disch := decide) only [Regs.set_set', Regs.set_comm'])

theorem sub_int (a : Int) (b : Nat) : alu .sub (iv a) (bv b) = iv (a - b) := by
  simp only [alu]
  rw [show a - (b : Int) = a + -(b : Int) by omega, BitVec.ofInt_add, BitVec.ofInt_neg,
    BitVec.ofInt_natCast, BitVec.sub_eq_add_neg]

theorem sub_nat_int (a b : Nat) : alu .sub (bv a) (bv b) = iv ((a : Int) - b) := by
  rw [← BitVec.ofInt_natCast 64 a]; exact sub_int a b

theorem add_int (a b : Int) : alu .add (iv a) (iv b) = iv (a + b) := by
  simp only [alu]; rw [BitVec.ofInt_add]

theorem iv_nat (a : Nat) : iv (a : Int) = bv a := BitVec.ofInt_natCast 64 a

/-- `subw` of two small non-negative `int`s, sign-extended. -/
theorem sext_sub32 (a b : Nat) (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) :
    (alu .sub (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)).signExtend 64 = iv ((a : Int) - b) := by
  have h1 : (BitVec.ofNat 32 a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_msb (msb_bv32 a (by omega))]; simp; omega
  have h2 : (BitVec.ofNat 32 b).toInt = b := by
    rw [BitVec.toInt_eq_toNat_of_msb (msb_bv32 b (by omega))]; simp; omega
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  simp only [alu, BitVec.toInt_sub, h1, h2, BitVec.toInt_ofInt]
  simp only [Int.bmod_def]
  split <;> split <;> omega

theorem slt_nat_int (l : Nat) (z : Int) (hl : l < 2 ^ 62) (hz : -2 ^ 62 < z) (hz' : z < 2 ^ 62) :
    (bv l).slt (iv z) = decide ((l : Int) < z) := by
  have h1 : (bv l).toInt = l := by
    rw [BitVec.toInt_eq_toNat_of_msb (msb_bv l (by omega))]; simp; omega
  rw [BitVec.slt_eq_decide, BitVec.toInt_ofInt, h1]
  simp only [Int.bmod_def]
  congr 1; apply propext; split <;> omega

theorem sext_m1 (pc : Nat) (h : 1 ≤ pc) :
    BitVec.ofNat 32 (pc + 4294967295) = BitVec.ofNat 32 (pc - 1) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem add_m2 (s : Nat) : alu .add 4294967294#32 (BitVec.ofNat 32 (s + 2)) = BitVec.ofNat 32 s := by
  apply BitVec.eq_of_toNat_eq; simp only [alu, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-! ## Sums -/

/-- `f k + ... + f (s-1)`. -/
def sumR (f : Nat → Nat) (k s : Nat) : Nat := ((List.range' k (s - k)).map f).sum

theorem sumR_succ (f : Nat → Nat) (k s : Nat) (h : k < s) : sumR f k s = f k + sumR f (k + 1) s := by
  simp only [sumR]; rw [show s - k = (s - (k + 1)) + 1 by omega, List.range'_succ]; simp

theorem sumR_self (f : Nat → Nat) (k s : Nat) (h : s ≤ k) : sumR f k s = 0 := by
  simp [sumR, show s - k = 0 by omega]

/-! ## The triangular term (396 → 444) -/

/-- `(s + 2(pc-1))(s-1)/2`, which is never negative. -/
def tri (s pc : Nat) : Nat := (s + 2 * pc - 2) * (s - 1) / 2

theorem fin_pro (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (Cb s pc L0 : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h14 : x.get 14 = bv pc) (h9 : x.get 9 = bv s) (h8 : x.get 8 = bv Cb)
    (hs1 : 1 ≤ s) (hs : s < 200000) (hpc : pc < 200000) (hCb : Cb + 8 ≤ 4194304)
    (hL : readBytes mem Cb 8 = some (bv L0)) :
    ∃ y, run 12 ⟨x, bv 396, mem, [], out, .running⟩ =
      ⟨y, bv 444, wr mem Cb (bv (tri s pc + L0)) 8, [], out, .running⟩ ∧
      y.get 13 = bv 1 ∧ y.get 15 = bv (tri s pc + L0) ∧
      (∀ r : Reg, r ∉ ([13, 15] : List Reg) → y.get r = x.get r) := by
  refine ⟨(x.set 13 (bv 1)).set 15 (bv (tri s pc + L0)), ?_, by simp [Regs.get_set],
    by simp [Regs.get_set], by frame_tac⟩
  have hsm : s - 1 < 200000 := by omega
  rcases Nat.eq_zero_or_pos pc with h0 | hpc1
  · subst h0
    have h1 : BitVec.signExtend 64 4294967295#32 = 18446744073709551615#64 := by decide
    have h2 : BitVec.setWidth 32 18446744073709551615#64 = 4294967295#32 := by decide
    have h3 : alu .sll 4294967295#32 1#32 = 4294967294#32 := by decide
    have h4 : BitVec.signExtend 64 4294967294#32 = 18446744073709551614#64 := by decide
    have h5 : BitVec.setWidth 32 18446744073709551614#64 = 4294967294#32 := by decide
    rcases Nat.lt_or_ge s 2 with hs2 | hs2
    · obtain rfl : s = 1 := by omega
      have h6 : alu .add 4294967294#32 (BitVec.ofNat 32 1) = 4294967295#32 := by decide
      have h7 : tri 1 0 = 0 := rfl
      rw [h7]
      gexec <;> regs_tac
    · obtain ⟨s, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
      have h6 := add_m2 s
      have ht : tri (s + 2) 0 = s * (s + 1) / 2 := by simp [tri]
      have hb : s * (s + 1) < 2 ^ 63 := by
        have := Nat.mul_le_mul (show s ≤ 200000 by omega) (show s + 1 ≤ 200000 by omega); omega
      have hd := alu_div (s * (s + 1)) 2 hb (by decide) (by decide)
      rw [ht]
      gexec <;> regs_tac
  · have := sext_m1 pc hpc1
    have ht : tri s pc = ((pc - 1) * 2 + s) * (s - 1) / 2 := by
      simp only [tri]; congr 2; omega
    have hb : ((pc - 1) * 2 + s) * (s - 1) < 2 ^ 63 := by
      have := Nat.mul_le_mul (show (pc - 1) * 2 + s ≤ 600000 by omega) (show s - 1 ≤ 200000 by omega); omega
    have hd := alu_div (((pc - 1) * 2 + s) * (s - 1)) 2 hb (by decide) (by decide)
    rw [ht]
    gexec <;> regs_tac

/-! ## Subtracting the large counts (loop at 444) -/

theorem fin_loop1_step (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (Cb s k lk : Nat) (Z : Int)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = iv Z) (h13 : x.get 13 = bv k) (h9 : x.get 9 = bv s) (h8 : x.get 8 = bv Cb)
    (hk : k < s) (hs : s < 200000) (hC : 1248 ≤ Cb) (hCs : Cb + s * 8 ≤ 4194304)
    (hL : readBytes mem (Cb + k * 8) 8 = some (bv lk)) :
    ∃ y, run 9 ⟨x, bv 444, mem, [], out, .running⟩ =
      ⟨y, bv 444, wr mem Cb (iv (Z - lk)) 8, [], out, .running⟩ ∧
      y.get 13 = bv (k + 1) ∧ y.get 15 = iv (Z - lk) ∧
      (∀ r : Reg, r ∉ ([12, 13, 15] : List Reg) → y.get r = x.get r) := by
  refine ⟨(((x.set 0 1024#64).set 12 (bv lk)).set 13 (bv (k + 1))).set 15 (iv (Z - lk)), ?_,
    by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  have := sub_int
  have hL' : readBytes mem (k * 8 + Cb) 8 = some (bv lk) := by rw [Nat.add_comm]; exact hL
  gexec
  regs_tac

theorem fin_loop1_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s pc : Nat)
    (hmem : Prefix image mem 1236)
    (h13 : x.get 13 = bv s) (h9 : x.get 9 = bv s) (h14 : x.get 14 = bv pc) (hs : s < 200000) :
    ∃ y, run 4 ⟨x, bv 444, mem, [], out, .running⟩ = ⟨y, bv 460, mem, [], out, .running⟩ ∧
      y.get 12 = bv 1 ∧ y.get 16 = bv pc ∧
      (∀ r : Reg, r ∉ ([12, 16] : List Reg) → y.get r = x.get r) := by
  refine ⟨(x.set 12 (bv 1)).set 16 (bv pc), ?_, by simp [Regs.get_set], by simp [Regs.get_set],
    by frame_tac⟩
  gexec
  regs_tac

theorem fin_loop1 (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (Cb s k pc : Nat)
    (f : Nat → Nat) (Z : Int)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = iv Z) (h13 : x.get 13 = bv k) (h9 : x.get 9 = bv s) (h8 : x.get 8 = bv Cb)
    (h14 : x.get 14 = bv pc)
    (hk1 : 1 ≤ k) (hk : k ≤ s) (hs : s < 200000) (hC : 1248 ≤ Cb) (hCs : Cb + s * 8 ≤ 4194304)
    (hla : ∀ j, 1 ≤ j → j < s → readBytes mem (Cb + j * 8) 8 = some (bv (f j)))
    (hZ : readBytes mem Cb 8 = some (iv Z)) :
    ∃ n y mem', run n ⟨x, bv 444, mem, [], out, .running⟩ = ⟨y, bv 460, mem', [], out, .running⟩ ∧
      Same mem mem' Cb (Cb + 8) ∧ readBytes mem' Cb 8 = some (iv (Z - sumR f k s)) ∧
      y.get 12 = bv 1 ∧ y.get 16 = bv pc ∧
      (∀ r : Reg, r ∉ ([12, 13, 15, 16] : List Reg) → y.get r = x.get r) := by
  by_cases hks : k < s
  · obtain ⟨y1, hr1, hy13, hy15, g1⟩ := fin_loop1_step x mem out Cb s k (f k) Z hmem hsz h15 h13 h9 h8
      hks hs hC hCs (hla k hk1 hks)
    have hsame : Same mem (wr mem Cb (iv (Z - f k)) 8) Cb (Cb + 8) :=
      Same.wr _ _ _ _ _ _ (by omega) (by omega) (by omega)
    obtain ⟨n, y, mem', hr, hs', hZ', hy12, hy16, g⟩ := fin_loop1 y1 _ out Cb s (k + 1) pc f (Z - f k)
      (hsame.prefix hmem (by omega)) (by simp [hsz]) hy15 hy13
      (by rw [g1 9 (by decide), h9]) (by rw [g1 8 (by decide), h8]) (by rw [g1 14 (by decide), h14])
      (by omega) (by omega) hs hC hCs
      (fun j hj1 hj => hsame.read (hla j hj1 hj) (by omega))
      (by rw [read_wr_same _ _ _ _ (by omega)]; simp)
    refine ⟨9 + n, y, mem', by rw [run_add, hr1, hr], hsame.trans hs', ?_, hy12, hy16, ?_⟩
    · rw [hZ', sumR_succ f k s hks]; congr 2; push_cast; omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [hr]), g1 r (by simp [hr])]
  · obtain rfl : k = s := by omega
    obtain ⟨y, hr, hy12, hy16, g⟩ := fin_loop1_exit x mem out k pc hmem h13 h9 h14 hs
    refine ⟨4, y, mem, hr, Same.refl _ _ _, ?_, hy12, hy16, ?_⟩
    · rw [sumR_self f k k (by omega)]; simpa using hZ
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact g r (by simp [hr])
termination_by s - k

/-! ## The triple correction (loops at 460 and 1088) -/

theorem tri_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s : Nat)
    (hmem : Prefix image mem 1236) (h12 : x.get 12 = bv s) (h9 : x.get 9 = bv s) (hs : s < 200000) :
    ∃ y, run 2 ⟨x, bv 460, mem, [], out, .running⟩ = ⟨y, bv 468, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([17] : List Reg) → y.get r = x.get r) := by
  refine ⟨x.set 17 (bv s), ?_, by frame_tac⟩
  gexec

/-- Row `l` stops the loop: `e = smalls[half(N/q/q)] - pc < l + 1`. -/
theorem tri_break (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B N s pc l q m : Nat)
    (hmem : Prefix image mem 1236)
    (h12 : x.get 12 = bv l) (h9 : x.get 9 = bv s) (h19 : x.get 19 = bv N) (h21 : x.get 21 = bv B)
    (h20 : x.get 20 = bv A) (h14 : x.get 14 = bv pc)
    (hl : l < s) (hs : s < 200000) (hN : N < 2 ^ 40) (hpc : pc < 200000)
    (hA : 1248 ≤ A) (hB : B + s * 4 ≤ 4194304) (hA2 : A + (N / q / q - 1) / 2 * 4 + 4 ≤ 4194304)
    (hq2 : 1 ≤ q) (hq : q < 2 ^ 20) (hm : m < 2 ^ 20) (h1 : 1 ≤ N / q / q)
    (hrq : readBytes mem (B + l * 4) 4 = some (BitVec.ofNat 32 q))
    (hrm : readBytes mem (A + (N / q / q - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 m))
    (hbrk : m < pc + l + 1) :
    ∃ y, run 15 ⟨x, bv 460, mem, [], out, .running⟩ = ⟨y, bv 468, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([6, 13, 15, 17, 28] : List Reg) → y.get r = x.get r) := by
  refine ⟨((((x.set 6 (bv (N / q))).set 13 (iv ((m : Int) - pc))).set 15
    (bv (A + (N / q / q - 1) / 2 * 4))).set 17 (bv l)).set 28 (iv ((m : Int) - pc)), ?_, by frame_tac⟩
  have := Nat.div_le_self N q
  have := Nat.div_le_self (N / q) q
  have := sext_sub32 m pc (by omega) (by omega)
  have := slt_nat_int l ((m : Int) - pc) (by omega) (by omega) (by omega)
  have hc : (m : Int) - pc ≤ l := by omega
  have : alu .add (iv ((m : Int) - pc)) 0#64 = iv ((m : Int) - pc) := by simp [alu]
  gexec
  regs_tac

/-- Row `l` runs: `e = smalls[half(N/q/q)] - pc ≥ l + 1`. -/
theorem tri_cont (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B N s pc l q m : Nat)
    (hmem : Prefix image mem 1236)
    (h12 : x.get 12 = bv l) (h9 : x.get 9 = bv s) (h19 : x.get 19 = bv N) (h21 : x.get 21 = bv B)
    (h20 : x.get 20 = bv A) (h14 : x.get 14 = bv pc)
    (hl : l < s) (hs : s < 200000) (hN : N < 2 ^ 40) (hpc : pc < 200000)
    (hA : 1248 ≤ A) (hB : B + s * 4 ≤ 4194304) (hA2 : A + (N / q / q - 1) / 2 * 4 + 4 ≤ 4194304)
    (hq2 : 1 ≤ q) (hq : q < 2 ^ 20) (hm : m < 2 ^ 20) (h1 : 1 ≤ N / q / q)
    (hrq : readBytes mem (B + l * 4) 4 = some (BitVec.ofNat 32 q))
    (hrm : readBytes mem (A + (N / q / q - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 m))
    (hcont : pc + l + 1 ≤ m) :
    ∃ y, run 18 ⟨x, bv 460, mem, [], out, .running⟩ = ⟨y, bv 1088, mem, [], out, .running⟩ ∧
      y.get 6 = bv (N / q) ∧ y.get 10 = bv (l + 1) ∧ y.get 11 = bv 0 ∧ y.get 12 = bv (l + 1) ∧
      y.get 13 = bv (m - pc) ∧ y.get 17 = bv l ∧ y.get 28 = bv (m - pc) ∧
      (∀ r : Reg, r ∉ ([6, 10, 11, 12, 13, 15, 17, 28] : List Reg) → y.get r = x.get r) := by
  refine ⟨(((((((x.set 6 (bv (N / q))).set 10 (bv (l + 1))).set 11 (bv 0)).set 12 (bv (l + 1))).set 13
    (bv (m - pc))).set 15 (bv (A + (N / q / q - 1) / 2 * 4))).set 17 (bv l)).set 28 (bv (m - pc)), ?_,
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  have := Nat.div_le_self N q
  have := Nat.div_le_self (N / q) q
  gexec
  regs_tac

/-- One term of the inner sum: `t += smalls[half(M / roughs[k])]`. -/
theorem inner_step (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B M k t e r v : Nat)
    (hmem : Prefix image mem 1236)
    (h10 : x.get 10 = bv k) (h11 : x.get 11 = bv t) (h28 : x.get 28 = bv e) (h6 : x.get 6 = bv M)
    (h21 : x.get 21 = bv B) (h20 : x.get 20 = bv A)
    (hke : k ≤ e) (he : e < 200000) (hM : M < 2 ^ 40)
    (hA : 1248 ≤ A) (hB' : B + k * 4 + 4 ≤ 4194304)
    (hA2 : A + (M / r - 1) / 2 * 4 + 4 ≤ 4194304)
    (hr2 : 1 ≤ r) (hr : r < 2 ^ 20) (hv : v < 2 ^ 20) (h1 : 1 ≤ M / r)
    (hrq : readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 r))
    (hrm : readBytes mem (A + (M / r - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 v)) :
    ∃ y, run 14 ⟨x, bv 1088, mem, [], out, .running⟩ = ⟨y, bv 1088, mem, [], out, .running⟩ ∧
      y.get 10 = bv (k + 1) ∧ y.get 11 = bv (t + v) ∧
      (∀ r : Reg, r ∉ ([0, 10, 11, 15] : List Reg) → y.get r = x.get r) := by
  refine ⟨(((x.set 0 1176#64).set 10 (bv (k + 1))).set 11 (bv (t + v))).set 15 (bv v), ?_,
    by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  have := Nat.div_le_self M r
  gexec
  regs_tac

/-- The inner sum is done (`k = e + 1`): add `t - (e - l)(pc + l - 1)` to `larges[0]`. -/
theorem inner_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (Cb l a6 t e : Nat) (Z : Int)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h10 : x.get 10 = bv (e + 1)) (h11 : x.get 11 = bv t) (h28 : x.get 28 = bv e) (h13 : x.get 13 = bv e)
    (h17 : x.get 17 = bv l) (h16 : x.get 16 = bv a6) (h8 : x.get 8 = bv Cb)
    (hle : l + 1 ≤ e) (he : e < 200000)
    (hC : 1248 ≤ Cb) (hC' : Cb + 8 ≤ 4194304)
    (hZ : readBytes mem Cb 8 = some (iv Z)) :
    ∃ y, run 10 ⟨x, bv 1088, mem, [], out, .running⟩ =
      ⟨y, bv 460, wr mem Cb (iv (Z + ((t : Int) - ((e - l) * a6 : Nat)))) 8, [], out, .running⟩ ∧
      y.get 16 = bv (a6 + 1) ∧
      (∀ r : Reg, r ∉ ([0, 11, 13, 15, 16] : List Reg) → y.get r = x.get r) := by
  refine ⟨((((x.set 0 1128#64).set 11 (iv ((t : Int) - ((e - l) * a6 : Nat)))).set 13
    (bv ((e - l) * a6))).set 15 (iv (Z + ((t : Int) - ((e - l) * a6 : Nat))))).set 16 (bv (a6 + 1)), ?_,
    by simp [Regs.get_set], by frame_tac⟩
  have := sub_nat_int
  have := add_int
  gexec
  regs_tac

/-- `smalls[half(d)]`. -/
def smd (sm : Nat → Nat) (d : Nat) : Nat := sm ((d - 1) / 2)

theorem inner_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B M k t e : Nat)
    (sm q : Nat → Nat)
    (hmem : Prefix image mem 1236)
    (h10 : x.get 10 = bv k) (h11 : x.get 11 = bv t) (h28 : x.get 28 = bv e) (h6 : x.get 6 = bv M)
    (h21 : x.get 21 = bv B) (h20 : x.get 20 = bv A)
    (hk : k ≤ e + 1) (he : e < 200000) (hM : M < 2 ^ 40) (hA : 1248 ≤ A)
    (hro : ∀ j, k ≤ j → j ≤ e →
      readBytes mem (B + j * 4) 4 = some (BitVec.ofNat 32 (q j)) ∧ B + j * 4 + 4 ≤ 4194304 ∧
      1 ≤ q j ∧ q j < 2 ^ 20 ∧ 1 ≤ M / q j ∧ A + (M / q j - 1) / 2 * 4 + 4 ≤ 4194304 ∧
      readBytes mem (A + (M / q j - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 (smd sm (M / q j))) ∧
      smd sm (M / q j) < 2 ^ 20) :
    ∃ n y, run n ⟨x, bv 1088, mem, [], out, .running⟩ = ⟨y, bv 1088, mem, [], out, .running⟩ ∧
      y.get 10 = bv (e + 1) ∧ y.get 11 = bv (t + sumR (fun j => smd sm (M / q j)) k (e + 1)) ∧
      (∀ r : Reg, r ∉ ([0, 10, 11, 15] : List Reg) → y.get r = x.get r) := by
  by_cases hke : k ≤ e
  · obtain ⟨hr1, hb1, hq1, hq2, hd1, ha1, hr2, hv⟩ := hro k (by omega) hke
    obtain ⟨y1, hrun1, hy10, hy11, g1⟩ := inner_step x mem out A B M k t e (q k) (smd sm (M / q k))
      hmem h10 h11 h28 h6 h21 h20 hke he hM hA hb1 ha1 hq1 hq2 hv hd1 hr1 hr2
    obtain ⟨n, y, hrun, hy10', hy11', g⟩ := inner_loop y1 mem out A B M (k + 1) (t + smd sm (M / q k)) e
      sm q hmem hy10 hy11 (by rw [g1 28 (by decide), h28]) (by rw [g1 6 (by decide), h6])
      (by rw [g1 21 (by decide), h21]) (by rw [g1 20 (by decide), h20]) (by omega) he hM hA
      (fun j h1 h2 => hro j (by omega) h2)
    refine ⟨14 + n, y, by rw [run_add, hrun1, hrun], hy10', ?_, ?_⟩
    · rw [hy11', sumR_succ _ k (e + 1) (by omega), Nat.add_assoc]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [hr]), g1 r (by simp [hr])]
  · obtain rfl : k = e + 1 := by omega
    refine ⟨0, x, rfl, h10, by rw [sumR_self _ _ _ (by omega)]; simpa using h11, fun _ _ => rfl⟩
termination_by e + 1 - k

/-- What the triple loop at 460 needs, on the arrays it reads. `D` bounds the arguments of
`smalls`. -/
structure FH (mem : Array (BitVec 8)) (A B Cb N s pc D : Nat) (sm q : Nat → Nat) : Prop where
  hs : s < 200000
  hpc : pc < 200000
  hN : N < 2 ^ 40
  hA : 1248 ≤ A
  hB : B + s * 4 ≤ Cb
  hCb : 1248 ≤ Cb
  hC : Cb + 8 ≤ 4194304
  size : mem.size = 4194304
  pre : Prefix image mem 1236
  ro : ∀ k, 1 ≤ k → k < s →
    readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 (q k)) ∧ 1 ≤ q k ∧ q k < 2 ^ 20
  smr : ∀ d, 1 ≤ d → d ≤ D →
    readBytes mem (A + (d - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 (smd sm d)) ∧
      A + (d - 1) / 2 * 4 + 4 ≤ B ∧ smd sm d < 2 ^ 20
  dl : ∀ l, 1 ≤ l → l < s → 1 ≤ N / q l / q l ∧ N / q l / q l ≤ D
  dk : ∀ l k, 1 ≤ l → l < k → k < s → 1 ≤ N / q l / q k ∧ N / q l / q k ≤ D
  el : ∀ l, 1 ≤ l → l < s → smd sm (N / q l / q l) < pc + s

theorem FH.same {mem mem' : Array (BitVec 8)} {A B Cb N s pc D : Nat} {sm q : Nat → Nat}
    (h : FH mem A B Cb N s pc D sm q) (hs : Same mem mem' Cb (Cb + 8)) :
    FH mem' A B Cb N s pc D sm q where
  hs := h.hs
  hpc := h.hpc
  hN := h.hN
  hA := h.hA
  hB := h.hB
  hCb := h.hCb
  hC := h.hC
  size := by rw [hs.size_eq, h.size]
  pre := hs.prefix h.pre (by have := h.hCb; omega)
  ro k h1 h2 := by
    obtain ⟨r, a, b⟩ := h.ro k h1 h2
    exact ⟨hs.read r (by have := h.hB; omega), a, b⟩
  smr d h1 h2 := by
    obtain ⟨r, a, b⟩ := h.smr d h1 h2
    exact ⟨hs.read r (by have := h.hB; omega), a, b⟩
  dl := h.dl
  dk := h.dk
  el := h.el

/-- The value the triple loop adds to `larges[0]`, from row `l` on, as the binary computes it. -/
def triLoop (sm q : Nat → Nat) (N s pc : Nat) (l : Nat) : Int :=
  if l < s then
    if smd sm (N / q l / q l) < pc + l + 1 then 0
    else ((sumR (fun k => smd sm (N / q l / q k)) (l + 1) (smd sm (N / q l / q l) - pc + 1) : Int)
          - (((smd sm (N / q l / q l) - pc - l) * (pc + l - 1) : Nat) : Int))
         + triLoop sm q N s pc (l + 1)
  else 0
termination_by s - l

theorem tri_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B Cb N s pc D l : Nat)
    (sm q : Nat → Nat) (Z : Int) (h : FH mem A B Cb N s pc D sm q)
    (h12 : x.get 12 = bv l) (h9 : x.get 9 = bv s) (h19 : x.get 19 = bv N) (h21 : x.get 21 = bv B)
    (h20 : x.get 20 = bv A) (h14 : x.get 14 = bv pc) (h8 : x.get 8 = bv Cb)
    (h16 : x.get 16 = bv (pc + l - 1)) (hl1 : 1 ≤ l) (hl : l ≤ s)
    (hZ : readBytes mem Cb 8 = some (iv Z)) :
    ∃ n y mem', run n ⟨x, bv 460, mem, [], out, .running⟩ = ⟨y, bv 468, mem', [], out, .running⟩ ∧
      Same mem mem' Cb (Cb + 8) ∧ readBytes mem' Cb 8 = some (iv (Z + triLoop sm q N s pc l)) ∧
      (∀ r : Reg, r ∉ ([0, 6, 10, 11, 12, 13, 15, 16, 17, 28] : List Reg) → y.get r = x.get r) := by
  have hs := h.hs
  have hpc := h.hpc
  have hN := h.hN
  have hA := h.hA
  have hB := h.hB
  have hC := h.hC
  have hCb := h.hCb
  by_cases hls : l < s
  · obtain ⟨hrq, hq1, hq2⟩ := h.ro l hl1 hls
    obtain ⟨hd1, hd2⟩ := h.dl l hl1 hls
    obtain ⟨hrm, hma, hm⟩ := h.smr _ hd1 hd2
    have hel := h.el l hl1 hls
    by_cases hbrk : smd sm (N / q l / q l) < pc + l + 1
    · obtain ⟨y, hr, g⟩ := tri_break x mem out A B N s pc l (q l) (smd sm (N / q l / q l)) h.pre
        h12 h9 h19 h21 h20 h14 hls hs hN hpc hA (by omega) (by omega) hq1 hq2 hm hd1 hrq hrm hbrk
      refine ⟨15, y, mem, hr, Same.refl _ _ _, ?_, ?_⟩
      · rw [triLoop, if_pos hls, if_pos hbrk]; simpa using hZ
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact g r (by simp [hr])
    · have hcont : pc + l + 1 ≤ smd sm (N / q l / q l) := by omega
      obtain ⟨y1, hr1, y6, y10, y11, y12, y13, y17, y28, g1⟩ := tri_cont x mem out A B N s pc l (q l)
        (smd sm (N / q l / q l)) h.pre h12 h9 h19 h21 h20 h14 hls hs hN hpc hA (by omega) (by omega)
        hq1 hq2 hm hd1 hrq hrm hcont
      have hND : N / q l < 2 ^ 40 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hN
      obtain ⟨n2, y2, hr2, z10, z11, g2⟩ := inner_loop y1 mem out A B (N / q l) (l + 1) 0
        (smd sm (N / q l / q l) - pc) sm q h.pre y10 y11 y28 y6 (by rw [g1 21 (by decide), h21])
        (by rw [g1 20 (by decide), h20]) (by omega) (by omega) hND hA
        (fun j h1 h2 => by
          obtain ⟨r1, a1, b1⟩ := h.ro j (by omega) (by omega)
          obtain ⟨e1, e2⟩ := h.dk l j hl1 (by omega) (by omega)
          obtain ⟨r2, a2, b2⟩ := h.smr _ e1 e2
          exact ⟨r1, by omega, a1, b1, e1, by omega, r2, b2⟩)
      have hsz := h.size
      obtain ⟨y3, hr3, z16, g3⟩ := inner_exit y2 mem out Cb l (pc + l - 1)
        (0 + sumR (fun j => smd sm (N / q l / q j)) (l + 1) (smd sm (N / q l / q l) - pc + 1))
        (smd sm (N / q l / q l) - pc) Z h.pre hsz z10 z11 (by rw [g2 28 (by decide), y28])
        (by rw [g2 13 (by decide), y13]) (by rw [g2 17 (by decide), y17])
        (by rw [g2 16 (by decide), g1 16 (by decide), h16])
        (by rw [g2 8 (by decide), g1 8 (by decide), h8]) (by omega) (by omega) (by omega) (by omega) hZ
      have hsame : Same mem (wr mem Cb (iv (Z + ((↑(0 + sumR (fun j => smd sm (N / q l / q j)) (l + 1)
          (smd sm (N / q l / q l) - pc + 1)) : Int) - (((smd sm (N / q l / q l) - pc - l) *
          (pc + l - 1) : Nat) : Int)))) 8) Cb (Cb + 8) :=
        Same.wr _ _ _ _ _ _ (by omega) (by omega) (by omega)
      have f3 : ∀ r : Reg, r ∉ ([0, 6, 10, 11, 12, 13, 15, 16, 17, 28] : List Reg) → y3.get r = x.get r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [g3 r (by simp [hr]), g2 r (by simp [hr]), g1 r (by simp [hr])]
      obtain ⟨n4, y4, mem4, hr4, hs4, hZ4, g4⟩ := tri_loop y3 _ out A B Cb N s pc D (l + 1) sm q
        (Z + ((↑(0 + sumR (fun j => smd sm (N / q l / q j)) (l + 1)
          (smd sm (N / q l / q l) - pc + 1)) : Int) - (((smd sm (N / q l / q l) - pc - l) *
          (pc + l - 1) : Nat) : Int)))
        (h.same hsame)
        (by rw [g3 12 (by decide), g2 12 (by decide), y12])
        (by rw [f3 9 (by decide), h9]) (by rw [f3 19 (by decide), h19]) (by rw [f3 21 (by decide), h21])
        (by rw [f3 20 (by decide), h20]) (by rw [f3 14 (by decide), h14]) (by rw [f3 8 (by decide), h8])
        (by rw [z16]; congr 1; omega) (by omega) (by omega)
        (by rw [read_wr_same _ _ _ _ (by omega)]; simp)
      refine ⟨18 + n2 + 10 + n4, y4, mem4, by rw [run_add, run_add, run_add, hr1, hr2, hr3, hr4],
        hsame.trans hs4, ?_, ?_⟩
      · rw [hZ4]; congr 2
        rw [triLoop.eq_1 sm q N s pc l, if_pos hls, if_neg hbrk, Nat.zero_add, Int.add_assoc]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [g4 r (by simp [hr]), f3 r (by simp [hr])]
  · obtain rfl : l = s := by omega
    obtain ⟨y, hr, g⟩ := tri_exit x mem out l h.pre h12 h9 hs
    refine ⟨2, y, mem, hr, Same.refl _ _ _, ?_, ?_⟩
    · rw [triLoop, if_neg hls]; simpa using hZ
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact g r (by simp [hr])
termination_by s - l

end TinyFive.GrumpyBinary
