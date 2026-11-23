import GrumpyBinary.FinishRun

/-! From the entry at 0 to the head of the outer loop (388) with the stage-3 invariant: the
call to `prime_pi`, the register saves, `isqrt`, the three tables and the skip bitmap. -/
namespace TinyFive.GrumpyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory

local notation "bv" => BitVec.ofNat 64

/-- The stack after `prime_pi`'s prologue: the saved registers (all zero) and `ra = 8`. -/
def stk (mem : Array (BitVec 8)) : Array (BitVec 8) :=
  wr (wr (wr (wr (wr (wr (wr (wr (wr (wr (wr mem 4194264 (0 : BitVec 64) 8) 4194296 (bv 8) 8)
    4194288 (0 : BitVec 64) 8) 4194280 (0 : BitVec 64) 8) 4194272 (0 : BitVec 64) 8)
    4194256 (0 : BitVec 64) 8) 4194248 (0 : BitVec 64) 8) 4194240 (0 : BitVec 64) 8)
    4194232 (0 : BitVec 64) 8) 4194224 (0 : BitVec 64) 8) 4194216 (0 : BitVec 64) 8

theorem Same.wr' {m1 m2 : Array (BitVec 8)} {lo hi : Nat} (h : Same m1 m2 lo hi) (a : Nat) {k : Nat}
    (v : BitVec k) (n : Nat) (hs : a + n ≤ m2.size) (h1 : lo ≤ a) (h2 : a + n ≤ hi) :
    Same m1 (GrumpyBinary.wr m2 a v n) lo hi :=
  h.trans (Same.wr m2 a v n lo hi hs h1 h2)

theorem stk_same (mem : Array (BitVec 8)) (hsz : mem.size = 4194304) :
    Same mem (stk mem) 4194216 4194304 := by
  refine ⟨by simp [stk, wr_size, hsz], fun j hj => ?_⟩
  unfold stk
  repeat rw [wr_get _ _ _ _ (by simp only [wr_size, hsz]; omega) j (by omega)]

theorem stk_ra (mem : Array (BitVec 8)) (hsz : mem.size = 4194304) :
    readBytes (stk mem) 4194296 8 = some (bv 8) := by
  unfold stk
  repeat rw [read_wr_other _ _ _ _ _ _ (by simp only [wr_size, hsz]; omega) (by omega)]
  rw [read_wr_same _ _ _ _ (by simp only [wr_size, hsz]; omega)]
  rfl

theorem Zeroed.same {mem mem' : Array (BitVec 8)} {d n : Nat} (h : Zeroed mem mem' d n) :
    Same mem mem' d (d + n) := ⟨h.size_eq, h.frame⟩

/-- 0 → 192: the call, the prologue, and the first Newton step `(N + 1) / 2`. -/
theorem setup_entry (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv N) (hN : 3 ≤ N)
    (hN' : N < 100000000000) :
    ∃ y, run 23 ⟨x, 0, mem, [], out, .running⟩ = ⟨y, bv 192, stk mem, [], out, .running⟩ ∧
      y.get 2 = bv 4194192 ∧ y.get 15 = bv ((N + 1) / 2) ∧ y.get 19 = bv N ∧ y.get 22 = bv N ∧
      (∀ r : Reg, r ∉ ([1, 2, 10, 15, 19, 22] : List Reg) → y.get r = 0) := by
  refine ⟨(((((x.set 1 (bv 8)).set 2 (bv 4194192)).set 10 (bv 1)).set 15 (bv ((N + 1) / 2))).set 19
    (bv N)).set 22 (bv N), ?_, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], ?_⟩
  · have h1 := hx 1 (by decide)
    have h2 := hx 2 (by decide)
    have h8 := hx 8 (by decide)
    have h9 := hx 9 (by decide)
    have h18 := hx 18 (by decide)
    have h19 := hx 19 (by decide)
    have h20 := hx 20 (by decide)
    have h21 := hx 21 (by decide)
    have h22 := hx 22 (by decide)
    have h23 := hx 23 (by decide)
    have h24 := hx 24 (by decide)
    have h25 := hx 25 (by decide)
    have h15 := hx 15 (by decide)
    simp only [stk]
    gexec
    regs_tac
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hr
    simp only [Regs.get_set]
    simp [Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5, Ne.symm a6, hx r a3]

/-- 196 → 1184: `s = (v + 1) / 2`, and the call constructing `smalls`. -/
theorem setup_c (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v : Nat)
    (hmem : Prefix image mem 1236) (h22 : x.get 22 = bv v) (h2 : x.get 2 = bv 4194192)
    (hv : v < 316228) :
    ∃ y, run 8 ⟨x, bv 196, mem, [], out, .running⟩ = ⟨y, bv 1184, mem, [], out, .running⟩ ∧
      y.get 1 = bv 228 ∧ y.get 9 = bv ((v + 1) / 2) ∧ y.get 10 = bv 4194192 ∧
      y.get 11 = bv ((v + 1) / 2) ∧ y.get 18 = bv v ∧ y.get 23 = bv (v + 1) ∧
      (∀ r : Reg, r ∉ ([1, 9, 10, 11, 15, 18, 23] : List Reg) → y.get r = x.get r) := by
  refine ⟨((((((x.set 1 (bv 228)).set 9 (bv ((v + 1) / 2))).set 10 (bv 4194192)).set 11
    (bv ((v + 1) / 2))).set 15 (bv 2)).set 18 (bv v)).set 23 (bv (v + 1)), ?_,
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec
  regs_tac

/-- 228 → 236: `s4 = smalls.data`, `i = 1`. -/
theorem setup_d (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1236) (h2 : x.get 2 = bv 4194192)
    (hr : readBytes mem 4194192 8 = some (bv 1248)) :
    ∃ y, run 2 ⟨x, bv 228, mem, [], out, .running⟩ = ⟨y, bv 236, mem, [], out, .running⟩ ∧
      y.get 15 = bv 1 ∧ y.get 20 = bv 1248 ∧
      (∀ r : Reg, r ∉ ([15, 20] : List Reg) → y.get r = x.get r) := by
  refine ⟨(x.set 15 (bv 1)).set 20 (bv 1248), ?_, by simp [Regs.get_set], by simp [Regs.get_set],
    by frame_tac⟩
  gexec
  regs_tac

/-- 244 → 1184: the call constructing `roughs`. -/
theorem setup_e (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s : Nat)
    (hmem : Prefix image mem 1236) (h2 : x.get 2 = bv 4194192) (h9 : x.get 9 = bv s) :
    ∃ y, run 4 ⟨x, bv 244, mem, [], out, .running⟩ = ⟨y, bv 1184, mem, [], out, .running⟩ ∧
      y.get 1 = bv 260 ∧ y.get 10 = bv 4194200 ∧ y.get 11 = bv s ∧
      (∀ r : Reg, r ∉ ([1, 10, 11] : List Reg) → y.get r = x.get r) := by
  refine ⟨((x.set 1 (bv 260)).set 10 (bv 4194200)).set 11 (bv s), ?_, by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec
  regs_tac

/-- 260 → 268: `s5 = roughs.data`, `i = 0`. -/
theorem setup_f (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (B : Nat)
    (hmem : Prefix image mem 1236) (h2 : x.get 2 = bv 4194192)
    (hr : readBytes mem 4194200 8 = some (bv B)) :
    ∃ y, run 2 ⟨x, bv 260, mem, [], out, .running⟩ = ⟨y, bv 268, mem, [], out, .running⟩ ∧
      y.get 15 = bv 0 ∧ y.get 21 = bv B ∧
      (∀ r : Reg, r ∉ ([15, 21] : List Reg) → y.get r = x.get r) := by
  refine ⟨(x.set 15 (bv 0)).set 21 (bv B), ?_, by simp [Regs.get_set], by simp [Regs.get_set],
    by frame_tac⟩
  gexec
  regs_tac

/-- 276 → 36: allocate `larges` (8-aligned, not yet recorded in the heap cursor) and call
`memset` on it. -/
theorem setup_g (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s H : Nat)
    (hmem : Prefix image mem 1236) (h9 : x.get 9 = bv s) (hs : s < 200000) (hH : H < 3000000)
    (hr : readBytes mem 1240 8 = some (bv H)) :
    ∃ y, run 11 ⟨x, bv 276, mem, [], out, .running⟩ = ⟨y, bv 36, mem, [], out, .running⟩ ∧
      y.get 1 = bv 320 ∧ y.get 8 = bv ((H + 7) / 8 * 8) ∧ y.get 10 = bv ((H + 7) / 8 * 8) ∧
      y.get 11 = bv 0 ∧ y.get 12 = bv (s * 8) ∧ y.get 24 = bv (s * 8) ∧ y.get 25 = bv 1240 ∧
      (∀ r : Reg, r ∉ ([1, 8, 10, 11, 12, 24, 25] : List Reg) → y.get r = x.get r) := by
  refine ⟨((((((x.set 1 (bv 320)).set 8 (bv ((H + 7) / 8 * 8))).set 10 (bv ((H + 7) / 8 * 8))).set 11
    (bv 0)).set 12 (bv (s * 8))).set 24 (bv (s * 8))).set 25 (bv 1240), ?_,
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec
  regs_tac

/-- 320 → 328: `i = 0`, `a2 = 2`. -/
theorem setup_h (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1236) :
    ∃ y, run 2 ⟨x, bv 320, mem, [], out, .running⟩ = ⟨y, bv 328, mem, [], out, .running⟩ ∧
      y.get 12 = bv 2 ∧ y.get 14 = bv 0 ∧
      (∀ r : Reg, r ∉ ([12, 14] : List Reg) → y.get r = x.get r) := by
  refine ⟨(x.set 12 (bv 2)).set 14 (bv 0), ?_, by simp [Regs.get_set], by simp [Regs.get_set],
    by frame_tac⟩
  gexec
  regs_tac

/-- 336 → 36: `skip` after `larges`, recorded in the heap cursor, and `memset` on it. -/
theorem setup_i (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (C8 S8 v : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h8 : x.get 8 = bv C8) (h24 : x.get 24 = bv S8) (h23 : x.get 23 = bv (v + 1))
    (h22 : x.get 22 = bv v) (h25 : x.get 25 = bv 1240)
    (hv1 : 1 ≤ v) (hv : v < 316228) (hC : C8 + S8 + v + 1 < 3000000) :
    ∃ y, run 9 ⟨x, bv 336, mem, [], out, .running⟩ =
        ⟨y, bv 36, wr mem 1240 (bv (C8 + S8 + (v + 1))) 8, [], out, .running⟩ ∧
      y.get 1 = bv 372 ∧ y.get 10 = bv (C8 + S8) ∧ y.get 11 = bv 0 ∧ y.get 12 = bv (v + 1) ∧
      y.get 22 = bv (v - 1) ∧ y.get 24 = bv (C8 + S8) ∧
      (∀ r : Reg, r ∉ ([1, 10, 11, 12, 15, 22, 24] : List Reg) → y.get r = x.get r) := by
  refine ⟨((((((x.set 1 (bv 372)).set 10 (bv (C8 + S8))).set 11 (bv 0)).set 12 (bv (v + 1))).set 15
    (bv (C8 + S8 + (v + 1)))).set 22 (bv (v - 1))).set 24 (bv (C8 + S8)), ?_,
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec
  regs_tac

/-- 372 → 388: `(v - 1) / 2`, `p = 3`, `pc = 0`, `a0 = 1`. -/
theorem setup_j (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v : Nat)
    (hmem : Prefix image mem 1236) (h22 : x.get 22 = bv (v - 1)) (hv : v < 316228) :
    ∃ y, run 4 ⟨x, bv 372, mem, [], out, .running⟩ = ⟨y, bv 388, mem, [], out, .running⟩ ∧
      y.get 10 = bv 1 ∧ y.get 12 = bv 3 ∧ y.get 14 = bv 0 ∧ y.get 22 = bv ((v - 1) / 2) ∧
      (∀ r : Reg, r ∉ ([10, 12, 14, 22] : List Reg) → y.get r = x.get r) := by
  refine ⟨(((x.set 10 (bv 1)).set 12 (bv 3)).set 14 (bv 0)).set 22 (bv ((v - 1) / 2)), ?_,
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by frame_tac⟩
  gexec
  regs_tac

/-- `N ≤ 1`: `prime_pi` returns 0 at once. -/
theorem small01 (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h10 : x.get 10 = bv N) (hN : N ≤ 1) :
    is_exited_with_output (run 13 ⟨x, 0, mem, [], out, .running⟩) (out ++ toString 0 ++ "\n") := by
  have := out_eq out 0 (by decide)
  gexec
  exact ⟨rfl, rfl⟩

/-- `N = 2`: `prime_pi` returns 1 after its prologue. -/
theorem small2 (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv 2) :
    is_exited_with_output (run 40 ⟨x, 0, mem, [], out, .running⟩) (out ++ toString 1 ++ "\n") := by
  have := out_eq out 1 (by decide)
  have h1 := hx 1 (by decide)
  have h2 := hx 2 (by decide)
  have h8 := hx 8 (by decide)
  have h9 := hx 9 (by decide)
  have h18 := hx 18 (by decide)
  have h19 := hx 19 (by decide)
  have h20 := hx 20 (by decide)
  have h21 := hx 21 (by decide)
  have h22 := hx 22 (by decide)
  have h23 := hx 23 (by decide)
  have h24 := hx 24 (by decide)
  have h25 := hx 25 (by decide)
  gexec
  exact ⟨rfl, rfl⟩

/-! ## Stage 3 -/

theorem RL3_len (N : Nat) (hv : 1 ≤ isqrt N) : (RL N 3).length = (isqrt N + 1) / 2 := by
  have := interval_length 3 (isqrt N + 1 - 3) (Nat.le_refl 3)
  rw [C_init, C_init] at this
  simp only [RL, List.length_cons]
  unfold roughList
  rcases Nat.lt_or_ge (isqrt N) 2 with h | h
  · rw [show isqrt N + 1 - 3 = 0 by omega]; simp; omega
  · rw [show 3 - 1 + (isqrt N + 1 - 3) = isqrt N by omega] at this; omega

theorem RL3_get (N k : Nat) (hk : k < (isqrt N + 1) / 2) : (RL N 3).getD k 0 = 2 * k + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rfl
  have hal : Alive 3 (2 * k + 1) := by
    have hs := C_succ 3 (2 * k)
    rw [C_init, C_init] at hs
    by_cases ha : Alive 3 (2 * k + 1)
    · exact ha
    · rw [if_neg ha] at hs; omega
  have hm : 2 * k + 1 ∈ roughList 3 (isqrt N) := mem_rough.mpr ⟨by omega, by omega, hal⟩
  have hr := rough_rank (Nat.le_refl 3) hm
  rw [C_init, show 3 - 1 = 2 by rfl, C_init] at hr
  rw [show (2 * k + 1 - 1) / 2 - (2 - 1) / 2 = k by omega] at hr
  simp only [RL]
  rw [List.getD_eq_getElem?_getD, hr]
  rfl

theorem not_skip3 (i : Nat) : ¬ SkipMarked 3 i := fun ⟨q, h1, h2, _⟩ => by omega

theorem run_seq {a b : Nat} {m m1 m2 : Machine 64} (h1 : run a m = m1) (h2 : run b m1 = m2) :
    run (a + b) m = m2 := by rw [run_add, h1, h2]

theorem rd_wr {m : Array (BitVec 8)} {b n : Nat} {w : BitVec (8 * n)} (hr : readBytes m b n = some w)
    (a : Nat) {j : Nat} (v : BitVec j) (k : Nat) (hs : a + k ≤ m.size) (hd : b + n ≤ a ∨ a + k ≤ b) :
    readBytes (wr m a v k) b n = some w := by
  rw [read_wr_other _ _ _ _ _ _ hs hd]; exact hr

theorem Same.ofwr (m : Array (BitVec 8)) (a : Nat) {j : Nat} (v : BitVec j) (k : Nat)
    (hs : a + k ≤ m.size) : Same m (GrumpyBinary.wr m a v k) a (a + k) :=
  Same.wr m a v k a (a + k) hs (Nat.le_refl _) (Nat.le_refl _)

/-- From the entry at 0 to the outer loop at 388 with the stage-3 invariant, for `3 ≤ N`. -/
theorem setup_run (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (hheap : readBytes mem 1240 8 = some (bv 1248))
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv N) (hN3 : 3 ≤ N)
    (hN : N < 100000000000) :
    ∃ n y mem', run n ⟨x, 0, mem, [], out, .running⟩ = ⟨y, bv 388, mem', [], out, .running⟩ ∧
      Inv N 3 y mem' := by
  have hv := isqrt_spec N
  have hvb : isqrt N < 316228 := r_lt_of_sq hv.1 hN
  have hv1 : 1 ≤ isqrt N := le_isqrt (by omega)
  have hvN : isqrt N ≤ N := Nat.le_trans (Nat.le_mul_self _) hv.1
  have hlay := layout ((isqrt N + 1) / 2)
  have hLD : LD ((isqrt N + 1) / 2) = LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 := rfl
  have hLB : LB ((isqrt N + 1) / 2) = (1248 + 4 * ((isqrt N + 1) / 2) + 7) / 8 * 8 := rfl
  have hLC : LC ((isqrt N + 1) / 2) = (LB ((isqrt N + 1) / 2) + 4 * ((isqrt N + 1) / 2) + 7) / 8 * 8 := rfl
  -- 0 → 192
  obtain ⟨y0, r0, y0_2, y0_15, y0_19, y0_22, g0⟩ := setup_entry x mem out N hmem hsz hx h10 hN3 hN
  have hS1 := stk_same mem hsz
  have pre1 := hS1.prefix hmem (by omega)
  have sz1 : (stk mem).size = 4194304 := by rw [hS1.size_eq, hsz]
  -- isqrt
  obtain ⟨n1, y1, r1, y1_22, g1⟩ := newton_loop N (by omega) hN N y0 (stk mem) out pre1 y0_19 y0_22
    (by rw [y0_15, Nat.div_self (by omega)]) hvN (Nat.le_refl N)
  -- smalls
  obtain ⟨y2, r2, y2_1, y2_9, y2_10, y2_11, y2_18, y2_23, g2⟩ := setup_c y1 (stk mem) out (isqrt N) pre1
    y1_22 (by rw [g1 2 (by decide), y0_2]) hvb
  have heap1 : readBytes (stk mem) 1240 8 = some (bv 1248) := hS1.read hheap (by omega)
  obtain ⟨x3, m2, r3, pre2, z2, x3_10, g3⟩ := vec_ctor y2 (stk mem) out 4194192 ((isqrt N + 1) / 2) 1248 228
    pre1 sz1 y2_10 y2_11 y2_1 (by decide) (by decide) heap1 (Nat.le_refl _) (by omega) (by omega)
  have e1 : (1248 + 7) / 8 * 8 = 1248 := rfl
  rw [e1, show heapAddr = 1240 from rfl] at z2
  rw [e1] at x3_10
  have sz2 : m2.size = 4194304 := by rw [z2.size_eq]; simp [sz1]
  have x3_2 : x3.get 2 = bv 4194192 := by rw [g3 2 (by decide), g2 2 (by decide), g1 2 (by decide), y0_2]
  have rd2 : readBytes m2 4194192 8 = some (bv 1248) := by
    rw [readBytes_congr m2 _ 4194192 8 (fun j h1 h2 => z2.frame j (by omega)),
      read_wr_other _ _ _ _ _ _ (by simp [sz1]) (by omega), read_wr_same _ _ _ _ (by simp [sz1])]
    simp
  obtain ⟨y4, r4, y4_15, y4_20, g4⟩ := setup_d x3 m2 out pre2 x3_2 rd2
  obtain ⟨n5, y5, m3, r5, S5, sm3, g5⟩ := smalls_loop y4 m2 out 1248 ((isqrt N + 1) / 2) 1 pre2 sz2 y4_15
    (by rw [g4 9 (by decide), g3 9 (by decide), y2_9]) y4_20 (by omega) (by omega) (by omega) (by omega)
    ((z2.arr32).ext (fun i hi => by simp; omega))
  have pre3 := S5.prefix pre2 (by omega)
  have sz3 : m3.size = 4194304 := by rw [S5.size_eq, sz2]
  -- roughs
  have y5_2 : y5.get 2 = bv 4194192 := by rw [g5 2 (by decide), g4 2 (by decide), x3_2]
  have y5_9 : y5.get 9 = bv ((isqrt N + 1) / 2) := by
    rw [g5 9 (by decide), g4 9 (by decide), g3 9 (by decide), y2_9]
  obtain ⟨y6, r6, y6_1, y6_10, y6_11, g6⟩ := setup_e y5 m3 out _ pre3 y5_2 y5_9
  have heap3 : readBytes m3 1240 8 = some (bv (1248 + 4 * ((isqrt N + 1) / 2))) := by
    rw [S5.read (show readBytes m2 1240 8 = _ from ?_) (by omega)]
    rw [readBytes_congr m2 _ 1240 8 (fun j h1 h2 => z2.frame j (by omega)),
      read_wr_same _ _ _ _ (by simp [sz1])]
    simp
  obtain ⟨x7, m4, r7, pre4, z4, x7_10, g7⟩ := vec_ctor y6 m3 out 4194200 ((isqrt N + 1) / 2)
    (1248 + 4 * ((isqrt N + 1) / 2)) 260 pre3 sz3 y6_10 y6_11 y6_1 (by decide) (by decide) heap3
    (by omega) (by omega) (by omega)
  rw [← hLB, show heapAddr = 1240 from rfl] at z4
  rw [← hLB] at x7_10
  have sz4 : m4.size = 4194304 := by rw [z4.size_eq]; simp [sz3]
  have x7_2 : x7.get 2 = bv 4194192 := by rw [g7 2 (by decide), g6 2 (by decide), y5_2]
  have rd4 : readBytes m4 4194200 8 = some (bv (LB ((isqrt N + 1) / 2))) := by
    rw [readBytes_congr m4 _ 4194200 8 (fun j h1 h2 => z4.frame j (by omega)),
      read_wr_other _ _ _ _ _ _ (by simp [sz3]) (by omega), read_wr_same _ _ _ _ (by simp [sz3])]
    simp
  obtain ⟨y8, r8, y8_15, y8_21, g8⟩ := setup_f x7 m4 out _ pre4 x7_2 rd4
  have y8_9 : y8.get 9 = bv ((isqrt N + 1) / 2) := by
    rw [g8 9 (by decide), g7 9 (by decide), g6 9 (by decide), y5_9]
  obtain ⟨n9, y9, m5, r9, S9, ro5, g9⟩ := roughs_loop y8 m4 out (LB ((isqrt N + 1) / 2)) ((isqrt N + 1) / 2) 0
    pre4 sz4 y8_15 y8_9 y8_21 (by omega) (by omega) (by omega) (by omega)
    ((z4.arr32).ext (fun i hi => by simp))
  have pre5 := S9.prefix pre4 (by omega)
  have sz5 : m5.size = 4194304 := by rw [S9.size_eq, sz4]
  -- larges
  have heap5 : readBytes m5 1240 8 = some (bv (LB ((isqrt N + 1) / 2) + 4 * ((isqrt N + 1) / 2))) := by
    rw [S9.read (show readBytes m4 1240 8 = _ from ?_) (by omega)]
    rw [readBytes_congr m4 _ 1240 8 (fun j h1 h2 => z4.frame j (by omega)),
      read_wr_same _ _ _ _ (by simp [sz3])]
    simp
  obtain ⟨y10, r10, y10_1, y10_8, y10_10, y10_11, y10_12, y10_24, y10_25, g10⟩ := setup_g y9 m5 out
    ((isqrt N + 1) / 2) _ pre5 (by rw [g9 9 (by decide), y8_9]) (by omega) (by omega) heap5
  rw [← hLC] at y10_8 y10_10
  obtain ⟨x11, m6, r11, pre6, z6, g11⟩ := memset y10 m5 out (LC ((isqrt N + 1) / 2))
    ((isqrt N + 1) / 2 * 8) 320 pre5 sz5 y10_10 y10_12 y10_11 y10_1 (by decide) (by decide) (by omega)
    (by omega)
  have sz6 : m6.size = 4194304 := by rw [z6.size_eq, sz5]
  obtain ⟨y12, r12, y12_12, y12_14, g12⟩ := setup_h x11 m6 out pre6
  have y12_9 : y12.get 9 = bv ((isqrt N + 1) / 2) := by
    rw [g12 9 (by decide), g11 9 (by decide), g10 9 (by decide), g9 9 (by decide), y8_9]
  have y12_8 : y12.get 8 = bv (LC ((isqrt N + 1) / 2)) := by
    rw [g12 8 (by decide), g11 8 (by decide), y10_8]
  have y12_19 : y12.get 19 = bv N := by
    rw [g12 19 (by decide), g11 19 (by decide), g10 19 (by decide), g9 19 (by decide), g8 19 (by decide),
      g7 19 (by decide), g6 19 (by decide), g5 19 (by decide), g4 19 (by decide), g3 19 (by decide),
      g2 19 (by decide), g1 19 (by decide), y0_19]
  obtain ⟨n13, y13, m7, r13, S13, la7, g13⟩ := larges_loop y12 m6 out N (LC ((isqrt N + 1) / 2))
    ((isqrt N + 1) / 2) 0 pre6 sz6 y12_14 y12_9 y12_8 y12_19 y12_12 (by omega) (by omega) (by omega) hN
    (by omega) ((Zeroed.arr64 (n := (isqrt N + 1) / 2) (by rw [Nat.mul_comm]; exact z6)).ext
      (fun i hi => by simp))
  have pre7 := S13.prefix pre6 (by omega)
  have sz7 : m7.size = 4194304 := by rw [S13.size_eq, sz6]
  -- skip
  have y13_22 : y13.get 22 = bv (isqrt N) := by
    rw [g13 22 (by decide), g12 22 (by decide), g11 22 (by decide), g10 22 (by decide),
      g9 22 (by decide), g8 22 (by decide), g7 22 (by decide), g6 22 (by decide), g5 22 (by decide),
      g4 22 (by decide), g3 22 (by decide), g2 22 (by decide), y1_22]
  obtain ⟨y14, r14, y14_1, y14_10, y14_11, y14_12, y14_22, y14_24, g14⟩ := setup_i y13 m7 out
    (LC ((isqrt N + 1) / 2)) ((isqrt N + 1) / 2 * 8) (isqrt N) pre7 sz7
    (by rw [g13 8 (by decide), y12_8])
    (by rw [g13 24 (by decide), g12 24 (by decide), g11 24 (by decide), y10_24])
    (by rw [g13 23 (by decide), g12 23 (by decide), g11 23 (by decide), g10 23 (by decide),
      g9 23 (by decide), g8 23 (by decide), g7 23 (by decide), g6 23 (by decide), g5 23 (by decide),
      g4 23 (by decide), g3 23 (by decide), y2_23])
    y13_22
    (by rw [g13 25 (by decide), g12 25 (by decide), g11 25 (by decide), y10_25]) hv1 hvb (by omega)
  rw [← hLD] at y14_10 y14_24
  have szC : (wr m7 1240 (bv (LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 + (isqrt N + 1))) 8).size =
      4194304 := by simp [sz7]
  have preC := prefix_wr 1240 (bv (LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 + (isqrt N + 1))) 8
    pre7 (by omega) (by omega)
  obtain ⟨x15, m8, r15, pre8, z8, g15⟩ := memset y14 _ out (LD ((isqrt N + 1) / 2)) (isqrt N + 1) 372
    preC szC y14_10 y14_12 y14_11 y14_1 (by decide) (by decide) (by omega) (by omega)
  obtain ⟨y16, r16, y16_10, y16_12, y16_14, y16_22, g16⟩ := setup_j x15 m8 out (isqrt N) pre8
    (by rw [g15 22 (by decide), y14_22]) hvb
  -- the memory
  have hs0 : (RL N 3).length = (isqrt N + 1) / 2 := RL3_len N hv1
  have ra8 : readBytes m8 4194296 8 = some (bv 8) := by
    have a1 := stk_ra mem hsz
    have a2 := rd_wr (rd_wr a1 4194192 (bv 1248) 8 (by simp [sz1]) (by omega)) 1240
      (bv (1248 + 4 * ((isqrt N + 1) / 2))) 8 (by simp [sz1]) (by omega)
    have a3 := z2.same.read a2 (by omega)
    have a4 := S5.read a3 (by omega)
    have a5 := rd_wr (rd_wr a4 4194200 (bv (LB ((isqrt N + 1) / 2))) 8 (by simp [sz3]) (by omega)) 1240
      (bv (LB ((isqrt N + 1) / 2) + 4 * ((isqrt N + 1) / 2))) 8 (by simp [sz3]) (by omega)
    have a6 := z4.same.read a5 (by omega)
    have a7 := S9.read a6 (by omega)
    have a8 := z6.same.read a7 (by omega)
    have a9 := S13.read a8 (by omega)
    have a10 := rd_wr a9 1240 (bv (LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 + (isqrt N + 1))) 8
      (by simp [sz7]) (by omega)
    exact z8.same.read a10 (by omega)
  have sm8 : Arr32 m8 1248 ((isqrt N + 1) / 2) (fun i => C 3 (2 * i + 1)) := by
    have b1 := sm3.ext (g := fun i => C 3 (2 * i + 1)) (fun i _ => by rw [C_init]; omega)
    have b2a := (Same.ofwr m3 4194200 (bv (LB ((isqrt N + 1) / 2))) 8 (by simp [sz3])).arr32 b1 (by omega)
    have b2 := (Same.ofwr (wr m3 4194200 (bv (LB ((isqrt N + 1) / 2))) 8) 1240
      (bv (LB ((isqrt N + 1) / 2) + 4 * ((isqrt N + 1) / 2))) 8 (by simp [sz3])).arr32 b2a (by omega)
    have b3 := z4.same.arr32 b2 (by omega)
    have b4 := S9.arr32 b3 (by omega)
    have b5 := z6.same.arr32 b4 (by omega)
    have b6 := S13.arr32 b5 (by omega)
    have b7 := (Same.ofwr m7 1240 (bv (LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 + (isqrt N + 1))) 8
      (by simp [sz7])).arr32 b6 (by omega)
    exact z8.same.arr32 b7 (by omega)
  have ro8 : Arr32 m8 (LB ((isqrt N + 1) / 2)) (RL N 3).length (fun k => (RL N 3).getD k 0) := by
    rw [hs0]
    have b1 := ro5.ext (g := fun k => (RL N 3).getD k 0)
      (fun i hi => by rw [RL3_get N i hi]; omega)
    have b2 := z6.same.arr32 b1 (by omega)
    have b3 := S13.arr32 b2 (by omega)
    have b4 := (Same.ofwr m7 1240 (bv (LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 + (isqrt N + 1))) 8
      (by simp [sz7])).arr32 b3 (by omega)
    exact z8.same.arr32 b4 (by omega)
  have la8 : Arr64 m8 (LC ((isqrt N + 1) / 2)) (RL N 3).length
      (fun k => C 3 (N / (RL N 3).getD k 0)) := by
    rw [hs0]
    have b1 := la7.ext (g := fun k => C 3 (N / (RL N 3).getD k 0))
      (fun i hi => by rw [RL3_get N i hi, C_init, Nat.mul_comm 2 i])
    have b2 := (Same.ofwr m7 1240 (bv (LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 + (isqrt N + 1))) 8
      (by simp [sz7])).arr64 b1 (by omega)
    exact z8.same.arr64 b2 (by omega)
  have sk8 : Arr8 m8 (LD ((isqrt N + 1) / 2)) (isqrt N + 1)
      (fun i => if SkipMarked 3 i then 1 else 0) :=
    z8.arr8.ext (fun i _ => by rw [if_neg (not_skip3 i)])
  -- the registers
  have f16 : ∀ r : Reg, r ∉ ([10, 12, 14, 22] : List Reg) → r ∉ ([12, 15] : List Reg) →
      y16.get r = y14.get r := by
    intro r h1 h2; rw [g16 r h1, g15 r h2]
  refine ⟨_, y16, m8, run_seq r0 (run_seq r1 (run_seq r2 (run_seq r3 (run_seq r4 (run_seq r5
    (run_seq r6 (run_seq r7 (run_seq r8 (run_seq r9 (run_seq r10 (run_seq r11 (run_seq r12 (run_seq r13
    (run_seq r14 (run_seq r15 r16))))))))))))))), ?_⟩
  · exact {
      hN3 := hN3
      hN := hN
      hp3 := Nat.le_refl 3
      hpo := rfl
      hpr := fun r h1 h2 => by omega
      x8 := by rw [f16 8 (by decide) (by decide), g14 8 (by decide), g13 8 (by decide), y12_8]
      x9 := by rw [hs0, f16 9 (by decide) (by decide), g14 9 (by decide), g13 9 (by decide), y12_9]
      x18 := by
        rw [f16 18 (by decide) (by decide), g14 18 (by decide), g13 18 (by decide), g12 18 (by decide),
          g11 18 (by decide), g10 18 (by decide), g9 18 (by decide), g8 18 (by decide), g7 18 (by decide),
          g6 18 (by decide), g5 18 (by decide), g4 18 (by decide), g3 18 (by decide), y2_18]
      x19 := by rw [f16 19 (by decide) (by decide), g14 19 (by decide), g13 19 (by decide), y12_19]
      x20 := by
        rw [f16 20 (by decide) (by decide), g14 20 (by decide), g13 20 (by decide), g12 20 (by decide),
          g11 20 (by decide), g10 20 (by decide), g9 20 (by decide), g8 20 (by decide), g7 20 (by decide),
          g6 20 (by decide), g5 20 (by decide), y4_20]
      x21 := by
        rw [f16 21 (by decide) (by decide), g14 21 (by decide), g13 21 (by decide), g12 21 (by decide),
          g11 21 (by decide), g10 21 (by decide), g9 21 (by decide), y8_21]
      x22 := y16_22
      x23 := by
        rw [f16 23 (by decide) (by decide), g14 23 (by decide), g13 23 (by decide), g12 23 (by decide),
          g11 23 (by decide), g10 23 (by decide), g9 23 (by decide), g8 23 (by decide), g7 23 (by decide),
          g6 23 (by decide), g5 23 (by decide), g4 23 (by decide), g3 23 (by decide), y2_23]
      x24 := by rw [f16 24 (by decide) (by decide), y14_24]
      x25 := by
        rw [f16 25 (by decide) (by decide), g14 25 (by decide), g13 25 (by decide), g12 25 (by decide),
          g11 25 (by decide), y10_25]
      x12 := y16_12
      x14 := by rw [y16_14, C_init]
      x10 := y16_10
      x2 := by
        rw [f16 2 (by decide) (by decide), g14 2 (by decide), g13 2 (by decide), g12 2 (by decide),
          g11 2 (by decide), g10 2 (by decide), g9 2 (by decide), g8 2 (by decide), x7_2]
      size := by rw [z8.size_eq]; simp [sz7]
      pre := pre8
      ra := ra8
      sm := sm8
      ro := ro8
      la := la8
      sk := sk8 }

end TinyFive.GrumpyBinary
