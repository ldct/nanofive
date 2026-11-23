import LphaBinary.Memset
import ZjyBinary.Setup

/-! From the entry at 0 to the head of `prime_count`'s sieve loop (544): the call, the
prologue, `v = isqrt N`, zeroing `smooth`, and the loop filling `smalls`, `roughs`, `invs`
and `larges`. The stack frame is fixed: `sp = 715648`, `smooth` at 715680, `smalls` at
1031912, `larges` at 1664368, `roughs` at 2296824 and `invs` at 2929280. -/
namespace TinyFive.LphaBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

set_option linter.unusedVariables false

/-- A register value after symbolic execution, with constant address arithmetic. -/
macro "rg" : tactic => `(tactic| ((simp [Regs.get_set]) <;> first | rfl | decide | assumption | (congr 1 <;> omega)))

/-- `smooth`, `smalls`, `larges`, `roughs`, `invs`. -/
notation "SM" => (715680 : Nat)
notation "SB" => (1031912 : Nat)
notation "LB" => (1664368 : Nat)
notation "RB" => (2296824 : Nat)
notation "IB" => (2929280 : Nat)

/-- 0 → 160: the call, the prologue (saving `ra = 8` and eleven zero registers), and the first
Newton step `(N + 1) / 2`, for `2 ≤ N`. -/
theorem setup_entry (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv N) (hN : 2 ≤ N)
    (hN' : N < 100000000000) :
    ∃ y mem', run 24 ⟨x, 0, mem, [], out, .running⟩ = ⟨y, bv 160, mem', [], out, .running⟩ ∧
      Same mem mem' 4194192 4194304 ∧ mem'.size = 4194304 ∧
      readBytes mem' 4194296 8 = some (bv 8) ∧ y.get 2 = bv 715648 ∧ y.get 18 = bv N ∧
      y.get 9 = bv N ∧ y.get 15 = bv ((N + 1) / 2) := by
  have h1 := hx 1 (by decide)
  have h2 := hx 2 (by decide)
  refine ⟨_, _, by lexec; exact ⟨rfl, rfl⟩, by same_tac, by simp only [wr_size]; omega, by rd_tac,
    by simp [Regs.get_set, sp_down], by simp [Regs.get_set, h10], by simp [Regs.get_set, h10],
    by simp [Regs.get_set, h10]⟩

/-- 0 → 1528 → 8 for `N ≤ 1`: `prime_count` returns 0 at once; then the driver prints it. -/
theorem small01 (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv N) (hN : N ≤ 1) :
    is_exited_with_output (run 15 ⟨x, 0, mem, [], out, .running⟩) (out ++ toString 0 ++ "\n") := by
  have := out_eq out 0 (by decide)
  lexec
  exact ⟨rfl, rfl⟩

/-- The Newton loop at 160 (body at 752) for `isqrt N`, with `N` in `s2`, `x` in `s1`, `y` in `a5`. -/
theorem newton (N : Nat) (hN : 1 ≤ N) (hN' : N < 100000000000) (X : Nat) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1536) (hn : x.get 18 = bv N) (hx : x.get 9 = bv X)
    (h15 : x.get 15 = bv ((X + N / X) / 2)) (hX : isqrt N ≤ X) (hXN : X ≤ N) :
    ∃ k y, run k ⟨x, bv 160, mem, [], out, .running⟩ = ⟨y, bv 164, mem, [], out, .running⟩ ∧
      y.get 9 = bv (isqrt N) ∧
      (∀ i : Reg, i ∉ ([9, 14, 15] : List Reg) → y.get i = x.get i) := by
  have hX1 : 1 ≤ isqrt N := le_isqrt (by omega)
  have hY := newton_ge N X (by omega)
  have hdX := Nat.div_le_self N X
  by_cases hlt : (X + N / X) / 2 < X
  · have hdY := Nat.div_le_self N ((X + N / X) / 2)
    obtain ⟨y, hr, hyX, hy15, hfy⟩ : ∃ y, run 6 ⟨x, bv 160, mem, [], out, .running⟩ =
        ⟨y, bv 160, mem, [], out, .running⟩ ∧ y.get 9 = bv ((X + N / X) / 2) ∧
        y.get 15 = bv (((X + N / X) / 2 + N / ((X + N / X) / 2)) / 2) ∧
        (∀ i : Reg, i ∉ ([9, 14, 15] : List Reg) → y.get i = x.get i) :=
      ⟨_, by lexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set]; (try congr 1); try omega,
        by frame_tac⟩
    obtain ⟨k, z, hr2, hzX, hfz⟩ := newton N hN hN' ((X + N / X) / 2) y mem out hmem
      (by rw [hfy 18 (by decide), hn]) hyX hy15 hY (by omega)
    exact ⟨6 + k, z, by rw [run_add, hr, hr2], hzX, fun i hi => by rw [hfz i hi, hfy i hi]⟩
  · have hXX : X * X ≤ N := by
      have : X ≤ N / X := by omega
      exact (Nat.le_div_iff_mul_le (by omega)).mp this
    have hXe : X = isqrt N := Nat.le_antisymm (le_isqrt hXX) hX
    refine ⟨1, x, ?_, by rw [hx, hXe], fun _ _ => rfl⟩
    clear hXe
    lexec
termination_by X
decreasing_by omega

/-- 164 → 44: `memset(smooth, 0, 316228)`, returning to 212. -/
theorem seg_ms (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1536) (h2 : x.get 2 = bv 715648) :
    ∃ y, run 12 ⟨x, bv 164, mem, [], out, .running⟩ = ⟨y, bv 44, mem, [], out, .running⟩ ∧
      y.get 1 = bv 212 ∧ y.get 10 = bv SM ∧ y.get 11 = bv 0 ∧ y.get 12 = bv 316228 ∧
      y.get 19 = bv 3477504 ∧
      (∀ r : Reg, r ∉ ([1, 10, 11, 12, 14, 15, 19] : List Reg) → y.get r = x.get r) :=
  ⟨_, by lexec; rfl, by rg, by rg, by rg,
    by rg, by rg, by frame_tac⟩

/-- 212 → 336: the table pointers, `s = (v + 1) / 2`, `i = 0`. -/
theorem seg_ptr (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v : Nat)
    (hmem : Prefix image mem 1536) (h2 : x.get 2 = bv 715648) (h19 : x.get 19 = bv 3477504)
    (h9 : x.get 9 = bv v) (hv : v < 316228) :
    ∃ y, run 31 ⟨x, bv 212, mem, [], out, .running⟩ = ⟨y, bv 336, mem, [], out, .running⟩ ∧
      y.get 8 = bv ((v + 1) / 2) ∧ y.get 10 = bv 0 ∧ y.get 15 = bv SB ∧ y.get 28 = bv RB ∧
      y.get 6 = bv IB ∧ y.get 17 = bv LB ∧ y.get 16 = bv (2 * 0 + 1) ∧ y.get 11 = bv LB ∧
      y.get 12 = bv RB ∧ y.get 13 = bv IB ∧
      (∀ r : Reg, r ∉ ([6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 28] : List Reg) → y.get r = x.get r) :=
  ⟨_, by lexec; rfl, by rg, by rg, by rg,
    by rg, by rg, by rg, by rg,
    by rg, by rg, by rg, by frame_tac⟩

theorem _root_.TinyFive.GrumpyBinary.Same.lpre {mem mem' : Array (BitVec 8)} {lo hi : Nat}
    (h : Same mem mem' lo hi) (hp : Prefix image mem 1536) (hlo : 1536 ≤ lo) :
    Prefix image mem' 1536 :=
  fun i hi => by rw [h.frame i (by omega)]; exact hp i hi

/-- One pass of the table loop at 336 (body at 772): `smalls[i]`, `roughs[i]`, `invs[i]` and
`larges[i]`. -/
theorem init_step (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N s i : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h10 : x.get 10 = bv i) (h8 : x.get 8 = bv s) (h15 : x.get 15 = bv (SB + i * 4))
    (h28 : x.get 28 = bv (RB + i * 4)) (h16 : x.get 16 = bv (2 * i + 1))
    (h6 : x.get 6 = bv (IB + i * 8)) (h17 : x.get 17 = bv (LB + i * 4)) (h18 : x.get 18 = bv N)
    (hi : i < s) (hs : s ≤ 158114) (hN : N < 100000000000) (hsN : 2 * s ≤ N + 1) :
    ∃ y, run 15 ⟨x, bv 336, mem, [], out, .running⟩ = ⟨y, bv 336,
      wr (wr (wr (wr mem (SB + i * 4) (bv i) 4) (RB + i * 4) (bv (2 * i + 1)) 4) (IB + i * 8)
        (bv (N / (2 * i + 1))) 8) (LB + i * 4) (bv ((N / (2 * i + 1) - 1) / 2)) 4, [], out, .running⟩ ∧
      y.get 10 = bv (i + 1) ∧ y.get 15 = bv (SB + (i + 1) * 4) ∧ y.get 28 = bv (RB + (i + 1) * 4) ∧
      y.get 16 = bv (2 * (i + 1) + 1) ∧ y.get 6 = bv (IB + (i + 1) * 8) ∧
      y.get 17 = bv (LB + (i + 1) * 4) ∧
      (∀ r : Reg, r ∉ ([6, 10, 14, 15, 16, 17, 28] : List Reg) → y.get r = x.get r) := by
  have hd1 : 1 ≤ N / (2 * i + 1) := Nat.div_pos (by omega) (by omega)
  have hd2 := Nat.div_le_self N (2 * i + 1)
  exact ⟨_, by lexec; rfl, by rg, by rg, by rg, by rg, by rg, by rg, by frame_tac⟩

/-- The table loop from `i` to `s`, ending at 340. -/
theorem init_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N s i : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h10 : x.get 10 = bv i) (h8 : x.get 8 = bv s) (h15 : x.get 15 = bv (SB + i * 4))
    (h28 : x.get 28 = bv (RB + i * 4)) (h16 : x.get 16 = bv (2 * i + 1))
    (h6 : x.get 6 = bv (IB + i * 8)) (h17 : x.get 17 = bv (LB + i * 4)) (h18 : x.get 18 = bv N)
    (his : i ≤ s) (hs : s ≤ 158114) (hN : N < 100000000000) (hsN : 2 * s ≤ N + 1)
    (hsm : Arr32 mem SB s (fun j => if j < i then j else 0))
    (hro : Arr32 mem RB s (fun j => if j < i then 2 * j + 1 else 0))
    (hiv : Arr64 mem IB s (fun j => if j < i then N / (2 * j + 1) else 0))
    (hla : Arr32 mem LB s (fun j => if j < i then (N / (2 * j + 1) - 1) / 2 else 0)) :
    ∃ k y mem', run k ⟨x, bv 336, mem, [], out, .running⟩ = ⟨y, bv 340, mem', [], out, .running⟩ ∧
      Same mem mem' SB 4194192 ∧ Arr32 mem' SB s (fun j => j) ∧
      Arr32 mem' RB s (fun j => 2 * j + 1) ∧ Arr64 mem' IB s (fun j => N / (2 * j + 1)) ∧
      Arr32 mem' LB s (fun j => (N / (2 * j + 1) - 1) / 2) ∧
      (∀ r : Reg, r ∉ ([6, 10, 14, 15, 16, 17, 28] : List Reg) → y.get r = x.get r) := by
  by_cases hi : i < s
  · obtain ⟨y, hr, y10, y15, y28, y16, y6, y17, fy⟩ :=
      init_step x mem out N s i hmem hsz h10 h8 h15 h28 h16 h6 h17 h18 hi hs hN hsN
    have S1 := Same.ofwr mem (SB + i * 4) (bv i) 4 (by omega)
    have S2 := Same.ofwr (wr mem (SB + i * 4) (bv i) 4) (RB + i * 4) (bv (2 * i + 1)) 4
      (by simp only [wr_size]; omega)
    have S3 := Same.ofwr (wr (wr mem (SB + i * 4) (bv i) 4) (RB + i * 4) (bv (2 * i + 1)) 4)
      (IB + i * 8) (bv (N / (2 * i + 1))) 8 (by simp only [wr_size]; omega)
    have S4 := Same.ofwr (wr (wr (wr mem (SB + i * 4) (bv i) 4) (RB + i * 4) (bv (2 * i + 1)) 4)
      (IB + i * 8) (bv (N / (2 * i + 1))) 8) (LB + i * 4) (bv ((N / (2 * i + 1) - 1) / 2)) 4
      (by simp only [wr_size]; omega)
    have sm1 := (hsm.wr (by omega) i i hi).ext (g := fun j => if j < i + 1 then j else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    have sm4 := S4.arr32 (S3.arr32 (S2.arr32 sm1 (by omega)) (by omega)) (by omega)
    have ro2 := ((S1.arr32 hro (by omega)).wr (by simp only [wr_size]; omega) i (2 * i + 1) hi).ext
      (g := fun j => if j < i + 1 then 2 * j + 1 else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    have ro4 := S4.arr32 (S3.arr32 ro2 (by omega)) (by omega)
    have iv3 := ((S2.arr64 (S1.arr64 hiv (by omega)) (by omega)).wr (by simp only [wr_size]; omega)
      i (N / (2 * i + 1)) hi).ext (g := fun j => if j < i + 1 then N / (2 * j + 1) else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    have iv4 := S4.arr64 iv3 (by omega)
    have la4 := ((S3.arr32 (S2.arr32 (S1.arr32 hla (by omega)) (by omega)) (by omega)).wr
      (by simp only [wr_size]; omega) i ((N / (2 * i + 1) - 1) / 2) hi).ext
      (g := fun j => if j < i + 1 then (N / (2 * j + 1) - 1) / 2 else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    have S := (S1.wid SB 4194192 (by omega) (by omega)).trans
      ((S2.wid SB 4194192 (by omega) (by omega)).trans
        ((S3.wid SB 4194192 (by omega) (by omega)).trans (S4.wid SB 4194192 (by omega) (by omega))))
    obtain ⟨k, z, mem', hr2, S', sm', ro', iv', la', fz⟩ := init_loop y _ out N s (i + 1)
      (S.lpre hmem (by omega)) (by rw [S.size_eq, hsz]) y10 (by rw [fy 8 (by decide), h8]) y15 y28
      y16 y6 y17 (by rw [fy 18 (by decide), h18]) hi hs hN hsN sm4 ro4 iv4 la4
    exact ⟨15 + k, z, mem', by rw [run_add, hr, hr2], S.trans S', sm', ro', iv', la',
      fun r hr => by rw [fz r hr, fy r hr]⟩
  · have hie : i = s := by omega
    subst hie
    refine ⟨1, x, mem, by lexec, Same.refl _ _ _, hsm.ext (fun j hj => by simp [hj]),
      hro.ext (fun j hj => by simp [hj]), hiv.ext (fun j hj => by simp [hj]),
      hla.ext (fun j hj => by simp [hj]), fun _ _ => rfl⟩
termination_by s - i

/-- 340 → 544: the pointers of the sieve loop, the spills at `0..24(sp)`, `p = 3`, `pc = 0`. -/
theorem seg_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304) (h2 : x.get 2 = bv 715648)
    (h9 : x.get 9 = bv v) (hv : 1 ≤ v) (hv' : v < 316228) :
    ∃ y mem', run 51 ⟨x, bv 340, mem, [], out, .running⟩ = ⟨y, bv 544, mem', [], out, .running⟩ ∧
      Same mem mem' 715648 715680 ∧ mem'.size = 4194304 ∧
      readBytes mem' 715648 8 = some (bv SM) ∧ readBytes mem' 715656 8 = some (bv RB) ∧
      readBytes mem' 715664 8 = some (bv IB) ∧ readBytes mem' 715672 8 = some (bv LB) ∧
      y.get 7 = bv (SM + 1008) ∧ y.get 28 = bv (LB - 1504) ∧ y.get 29 = bv (SB + 168) ∧
      y.get 31 = bv SB ∧ y.get 27 = bv ((v - 1) / 2) ∧ y.get 15 = bv 3 ∧ y.get 14 = bv 0 ∧
      y.get 10 = bv SM ∧
      (∀ r : Reg, r ∉ ([5, 6, 7, 10, 14, 15, 16, 17, 27, 28, 29, 30, 31] : List Reg) → y.get r = x.get r) :=
  ⟨_, _, by lexec; exact ⟨rfl, rfl⟩, by same_tac, by simp only [wr_size]; omega, by rd_tac, by rd_tac, by rd_tac, by rd_tac, by rg, by rg, by rg, by rg, by rg, by rg, by rg, by rg, by frame_tac⟩

/-- The state at the head of the sieve loop (544) before stage `p`. -/
structure Inv (N p : Nat) (x : Regs 64) (mem : Array (BitVec 8)) : Prop where
  hN2 : 2 ≤ N
  hN : N < 100000000000
  hp3 : 3 ≤ p
  hpo : p % 2 = 1
  hpr : ∀ r, 3 ≤ r → r < p → Prime r → r * r * (r * r) ≤ N
  x15 : x.get 15 = bv p
  x14 : x.get 14 = bv (C p (p - 1))
  x10 : x.get 10 = bv (SM + p - 3)
  x9 : x.get 9 = bv (isqrt N)
  x8 : x.get 8 = bv (RL N p).length
  x27 : x.get 27 = bv ((isqrt N - 1) / 2)
  x7 : x.get 7 = bv (SM + 1008)
  x28 : x.get 28 = bv (LB - 1504)
  x29 : x.get 29 = bv (SB + 168)
  x31 : x.get 31 = bv SB
  x11 : x.get 11 = bv LB
  x12 : x.get 12 = bv RB
  x13 : x.get 13 = bv IB
  x2 : x.get 2 = bv 715648
  size : mem.size = 4194304
  pre : Prefix image mem 1536
  ra : readBytes mem 4194296 8 = some (bv 8)
  s0 : readBytes mem 715648 8 = some (bv SM)
  s8 : readBytes mem 715656 8 = some (bv RB)
  s16 : readBytes mem 715664 8 = some (bv IB)
  s24 : readBytes mem 715672 8 = some (bv LB)
  sm : Arr32 mem SB ((isqrt N + 1) / 2) (fun i => C p (2 * i + 1))
  ro : Arr32 mem RB (RL N p).length (fun k => (RL N p).getD k 0)
  iv : Arr64 mem IB (RL N p).length (fun k => N / (RL N p).getD k 0)
  la : Arr32 mem LB (RL N p).length (fun k => C p (N / (RL N p).getD k 0))
  sk : Arr8 mem SM (isqrt N + 1) (fun i => if SkipMarked p i then 1 else 0)

/-- From the entry at 0 to the sieve loop at 544 with the stage-3 invariant, for `2 ≤ N`. -/
theorem setup_run (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (hz : ∀ i, 1536 ≤ i → i < 4194304 → mem[i]? = some 0)
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv N) (hN : 2 ≤ N)
    (hN' : N < 100000000000) :
    ∃ n y mem', run n ⟨x, 0, mem, [], out, .running⟩ = ⟨y, bv 544, mem', [], out, .running⟩ ∧
      Inv N 3 y mem' := by
  have hv := isqrt_spec N
  have hvb : isqrt N < 316228 := r_lt_of_sq hv.1 hN'
  have hv1 : 1 ≤ isqrt N := le_isqrt (by omega)
  have hvN : isqrt N ≤ N := Nat.le_trans (Nat.le_mul_self _) hv.1
  have hs2 : 2 * ((isqrt N + 1) / 2) ≤ N + 1 := by omega
  obtain ⟨y0, m0, r0, S0, sz0, ra0, y0_2, y0_18, y0_9, y0_15⟩ :=
    setup_entry x mem out N hmem hsz hx h10 hN hN'
  have pre0 : Prefix image m0 1536 := S0.lpre hmem (by omega)
  obtain ⟨n1, y1, r1, y1_9, g1⟩ := newton N (by omega) hN' N y0 m0 out pre0 y0_18 y0_9
    (by rw [y0_15, Nat.div_self (by omega)]) hvN (Nat.le_refl N)
  obtain ⟨y2, r2, y2_1, y2_10, y2_11, y2_12, y2_19, g2⟩ := seg_ms y1 m0 out pre0
    (by rw [g1 2 (by decide), y0_2])
  obtain ⟨y3, m1, r3, pre1, Z1, g3⟩ := memset y2 m0 out SM 316228 212 pre0 sz0 y2_10 y2_12 y2_11
    y2_1 (by decide) (by decide) (by decide) (by decide)
  have sz1 : m1.size = 4194304 := by rw [Z1.size_eq, sz0]
  have S1 := Z1.same
  have zero1 : ∀ i, SB ≤ i → i < 4194192 → m1[i]? = some 0 := fun i h1 h2 => by
    rw [S1.frame i (by omega), S0.frame i (by omega)]; exact hz i (by omega) (by omega)
  obtain ⟨y4, r4, y4_8, y4_10, y4_15, y4_28, y4_6, y4_17, y4_16, y4_11, y4_12, y4_13, g4⟩ :=
    seg_ptr y3 m1 out (isqrt N) pre1
    (by rw [g3 2 (by decide), g2 2 (by decide), g1 2 (by decide), y0_2])
    (by rw [g3 19 (by decide), y2_19]) (by rw [g3 9 (by decide), g2 9 (by decide), y1_9]) hvb
  have arr32 : ∀ B, SB ≤ B → B + 158114 * 4 ≤ 4194192 → Arr32 m1 B ((isqrt N + 1) / 2) (fun _ => 0) :=
    fun B h1 h2 i hi => by
      rw [readBytes_zero _ _ _ (fun j hj1 hj2 => zero1 j (by omega) (by omega))]; rfl
  have arr64 : Arr64 m1 IB ((isqrt N + 1) / 2) (fun _ => 0) := fun i hi => by
    rw [readBytes_zero _ _ _ (fun j hj1 hj2 => zero1 j (by omega) (by omega))]; rfl
  obtain ⟨n5, y5, m2, r5, S2, sm2, ro2, iv2, la2, g5⟩ := init_loop y4 m1 out N ((isqrt N + 1) / 2) 0
    pre1 sz1 y4_10 y4_8 (by rw [y4_15]) (by rw [y4_28]) y4_16 (by rw [y4_6]) (by rw [y4_17])
    (by rw [g4 18 (by decide), g3 18 (by decide), g2 18 (by decide), g1 18 (by decide), y0_18])
    (Nat.zero_le _) (by omega) hN' hs2
    ((arr32 SB (by omega) (by omega)).ext (fun j _ => by simp))
    ((arr32 RB (by omega) (by omega)).ext (fun j _ => by simp))
    (arr64.ext (fun j _ => by simp)) ((arr32 LB (by omega) (by omega)).ext (fun j _ => by simp))
  have pre2 : Prefix image m2 1536 := S2.lpre pre1 (by omega)
  have sz2 : m2.size = 4194304 := by rw [S2.size_eq, sz1]
  obtain ⟨y6, m3, r6, S3, sz3, rd0, rd8, rd16, rd24, y6_7, y6_28, y6_29, y6_31, y6_27, y6_15, y6_14,
    y6_10, g6⟩ := seg_exit y5 m2 out (isqrt N) pre2 sz2
    (by rw [g5 2 (by decide), g4 2 (by decide), g3 2 (by decide), g2 2 (by decide),
      g1 2 (by decide), y0_2])
    (by rw [g5 9 (by decide), g4 9 (by decide), g3 9 (by decide), g2 9 (by decide), y1_9]) hv1 hvb
  have hlen := RL3_len N hv1
  refine ⟨24 + (n1 + (12 + ((4 * 316228 + 4) + (31 + (n5 + 51))))), y6, m3, ?_, ?_⟩
  · rw [run_add, r0, run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, r6]
  refine ⟨hN, hN', Nat.le_refl 3, rfl, fun r h1 h2 _ => absurd h2 (by omega), y6_15,
    by rw [y6_14]; rfl, by rw [y6_10], ?_, ?_, y6_27, y6_7, y6_28, y6_29, y6_31, ?_, ?_, ?_, ?_,
    sz3, S3.lpre pre2 (by omega), ?_, rd0, rd8, rd16, rd24, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g6 9 (by decide), g5 9 (by decide), g4 9 (by decide), g3 9 (by decide), g2 9 (by decide), y1_9]
  · rw [g6 8 (by decide), g5 8 (by decide), y4_8, hlen]
  · rw [g6 11 (by decide), g5 11 (by decide), y4_11]
  · rw [g6 12 (by decide), g5 12 (by decide), y4_12]
  · rw [g6 13 (by decide), g5 13 (by decide), y4_13]
  · rw [g6 2 (by decide), g5 2 (by decide), g4 2 (by decide), g3 2 (by decide), g2 2 (by decide),
      g1 2 (by decide), y0_2]
  · exact S3.read (S2.read (S1.read ra0 (by omega)) (by omega)) (by omega)
  · exact (S3.arr32 sm2 (by omega)).ext (fun i _ => by rw [C_init]; omega)
  · rw [hlen]
    exact (S3.arr32 ro2 (by omega)).ext (fun k hk => by rw [RL3_get N k hk])
  · rw [hlen]
    exact (S3.arr64 iv2 (by omega)).ext (fun k hk => by rw [RL3_get N k hk])
  · rw [hlen]
    exact (S3.arr32 la2 (by omega)).ext (fun k hk => by rw [RL3_get N k hk, C_init])
  · have := Z1.arr8
    refine fun i hi => ?_
    rw [S3.read (S2.read (this i (by omega)) (by omega)) (by omega)]
    simp [not_skip3]

end TinyFive.LphaBinary
