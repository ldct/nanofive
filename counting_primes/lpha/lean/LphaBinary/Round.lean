import LphaBinary.Update
import LphaBinary.Bertrand

/-! One pass of the sieve loop at 544, from the invariant at stage `p` to the one at `p + 2`, and
the whole loop: it ends at 552 at the first odd `a` with `v < a²`. -/
namespace TinyFive.LphaBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

set_option linter.unusedVariables false

/-- 1008 → 1028: `j = ((v / p) - 1) | 1`, `i = (v - 1) / 2`, `s0 = p * j`. -/
theorem upd_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p : Nat)
    (hmem : Prefix image mem 1536)
    (h9 : x.get 9 = bv v) (h15 : x.get 15 = bv p) (h27 : x.get 27 = bv ((v - 1) / 2))
    (hpv : p ≤ v) (hv : v < 316228) (hp3 : 3 ≤ p) :
    ∃ y, run 5 ⟨x, bv 1008, mem, [], out, .running⟩ = ⟨y, bv 1028, mem, [], out, .running⟩ ∧
      y.get 17 = bv ((v / p - 1) / 2 * 2 + 1) ∧ y.get 8 = bv (p * ((v / p - 1) / 2 * 2 + 1)) ∧
      y.get 5 = bv ((v - 1) / 2) ∧
      (∀ r : Reg, r ∉ ([5, 8, 17] : List Reg) → y.get r = x.get r) := by
  have : 1 ≤ v / p := Nat.div_pos hpv (by omega)
  have := Nat.div_le_self v p
  have hj : (v / p - 1) / 2 * 2 + 1 ≤ v := by omega
  have : p * ((v / p - 1) / 2 * 2 + 1) < 1000000000000 := by
    have := Nat.mul_le_mul (show p ≤ 316228 by omega) (show (v / p - 1) / 2 * 2 + 1 ≤ 316228 by omega)
    omega
  exact ⟨_, by lexec; rfl, by rg, by rg, by rg, by frame_tac⟩

/-- 1032 → 544: `pc++`, `s = ns`, `p += 2`. -/
theorem round_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (pc ns p : Nat)
    (hmem : Prefix image mem 1536)
    (h14 : x.get 14 = bv pc) (h16 : x.get 16 = bv ns) (h15 : x.get 15 = bv p)
    (h10 : x.get 10 = bv (SM + p - 3))
    (hpc : pc < 1000) (hp : 3 ≤ p) (hp' : p < 1000) :
    ∃ y, run 5 ⟨x, bv 1032, mem, [], out, .running⟩ = ⟨y, bv 544, mem, [], out, .running⟩ ∧
      y.get 14 = bv (pc + 1) ∧ y.get 8 = bv ns ∧ y.get 15 = bv (p + 2) ∧
      y.get 10 = bv (SM + (p + 2) - 3) ∧
      (∀ r : Reg, r ∉ ([8, 10, 14, 15] : List Reg) → y.get r = x.get r) :=
  ⟨_, by lexec; rfl, by rg, by rg, by rg, by rg, by frame_tac⟩

/-- `Inv` survives register changes outside the ones it constrains, given the new `p`-dependent
registers. -/
theorem Inv.frame' {N p : Nat} {x y : Regs 64} {mem : Array (BitVec 8)} (h : Inv N p x mem)
    (hf : ∀ r : Reg, r ∉ ([5, 6, 8, 10, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 30] :
      List Reg) → y.get r = x.get r) :
    y.get 9 = bv (isqrt N) ∧ y.get 27 = bv ((isqrt N - 1) / 2) ∧ y.get 7 = bv (SM + 1008) ∧
    y.get 28 = bv (LB - 1504) ∧ y.get 29 = bv (SB + 168) ∧ y.get 31 = bv SB ∧
    y.get 11 = bv LB ∧ y.get 12 = bv RB ∧ y.get 13 = bv IB ∧ y.get 2 = bv 715648 :=
  ⟨by rw [hf 9 (by decide), h.x9], by rw [hf 27 (by decide), h.x27], by rw [hf 7 (by decide), h.x7],
   by rw [hf 28 (by decide), h.x28], by rw [hf 29 (by decide), h.x29], by rw [hf 31 (by decide), h.x31],
   by rw [hf 11 (by decide), h.x11], by rw [hf 12 (by decide), h.x12], by rw [hf 13 (by decide), h.x13],
   by rw [hf 2 (by decide), h.x2]⟩

theorem inv_vb {N p : Nat} {x : Regs 64} {mem : Array (BitVec 8)} (h : Inv N p x mem) :
    isqrt N < 316228 := r_lt_of_sq (isqrt_spec N).1 h.hN

/-- A marked (composite) `p` with `p² ≤ v`. -/
theorem round_skip (N p : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h : Inv N p x mem) (hpp : p * p ≤ isqrt N) (hn : ¬ Prime p) :
    ∃ n y, run n ⟨x, bv 544, mem, [], out, .running⟩ = ⟨y, bv 544, mem, [], out, .running⟩ ∧
      Inv N (p + 2) y mem := by
  have hvb := inv_vb h
  have hpv : p ≤ isqrt N := Nat.le_trans (Nat.le_mul_of_pos_right p (by have := h.hp3; omega)) hpp
  have hsk := h.sk p (by omega)
  simp only [(skip_self_iff p h.hp3 h.hpo).mpr hn, ite_true] at hsk
  obtain ⟨y, hr, hy15, hy10, g⟩ := round_skip_run x mem out (isqrt N) p h.pre h.size h.x15 h.x10 h.x9
    hpp hvb h.hp3 hsk
  have hRL := RL_skip N p h.hp3 h.hpo hn
  refine ⟨7, y, hr, ⟨h.hN2, h.hN, by have := h.hp3; omega, by have := h.hpo; omega, ?_, hy15,
    by rw [g 14 (by decide), h.x14, C_pc_skip p h.hp3 h.hpo hn], hy10,
    by rw [g 9 (by decide), h.x9], by rw [g 8 (by decide), h.x8, hRL],
    by rw [g 27 (by decide), h.x27], by rw [g 7 (by decide), h.x7], by rw [g 28 (by decide), h.x28],
    by rw [g 29 (by decide), h.x29], by rw [g 31 (by decide), h.x31], by rw [g 11 (by decide), h.x11],
    by rw [g 12 (by decide), h.x12], by rw [g 13 (by decide), h.x13], by rw [g 2 (by decide), h.x2],
    h.size, h.pre, h.ra, h.s0, h.s8, h.s16, h.s24, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r h3 hr hpr
    by_cases hrp : r < p
    · exact h.hpr r h3 hrp hpr
    · by_cases hre : r = p
      · subst hre; exact absurd hpr hn
      · exact absurd hpr (by rw [show r = p + 1 by omega]; exact not_prime_even p h.hp3 h.hpo)
  · exact h.sm.ext (fun i _ => by rw [C_skip2 p h.hp3 h.hpo hn])
  · rw [hRL]; exact h.ro
  · rw [hRL]; exact h.iv
  · rw [hRL]; exact h.la.ext (fun i _ => by rw [C_skip2 p h.hp3 h.hpo hn])
  · exact h.sk.ext (fun i _ => by
      simp only [show SkipMarked (p + 2) i ↔ SkipMarked p i from
        skip_step_composite p i h.hp3 h.hpo hn])

/-- The break of the first compaction loop exists: a prime in `(v / 2, v]`. -/
theorem brk_exists (N p : Nat) (hp3 : 3 ≤ p) (hpo : p % 2 = 1) (hpp : p * p ≤ isqrt N)
    (hv : isqrt N < 316228) :
    ∃ j d, 0 ≤ j ∧ (RL N p)[j]? = some d ∧ (fun d => d % p != 0) d = true ∧ isqrt N < d * p := by
  have h9 : 9 ≤ isqrt N := Nat.le_trans (Nat.mul_le_mul hp3 hp3) hpp
  obtain ⟨q, hq, hq1, hq2⟩ := bertrand (isqrt N / 2) (by omega) (by omega)
  have hq2' : 2 ≤ q := hq.1
  have hqp : p < q := by
    have := Nat.mul_le_mul_right p hp3
    omega
  have hal : Alive p q := ⟨by omega, fun ⟨d, hd2, hdp, hdq, hdvd⟩ =>
    ((prime_iff_no_proper_divisor q).mp hq).2 d hd2 hdq hdvd⟩
  have hmem : q ∈ RL N p := List.mem_cons_of_mem _ (mem_rough.mpr ⟨by omega, by omega, hal⟩)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  refine ⟨j, q, Nat.zero_le _, hj, ?_, ?_⟩
  · have : q % p ≠ 0 := fun h0 =>
      ((prime_iff_no_proper_divisor q).mp hq).2 p (by omega) hqp (Nat.dvd_of_mod_eq_zero h0)
    simp [this]
  · have := Nat.mul_le_mul_left q hp3
    omega

/-- An unmarked (prime) `p` with `p² ≤ v`: one sieve round, back at 544 with `p + 2`. -/
theorem round_prime (N p : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h : Inv N p x mem) (hprime : Prime p) (hpp : p * p ≤ isqrt N) :
    ∃ n y mem', run n ⟨x, bv 544, mem, [], out, .running⟩ = ⟨y, bv 544, mem', [], out, .running⟩ ∧
      Inv N (p + 2) y mem' := by
  have hvb := inv_vb h
  have hp3 := h.hp3
  have hpo := h.hpo
  have hp563 := p_le_563 hpp hvb
  have hpv : p ≤ isqrt N := Nat.le_trans (Nat.le_mul_of_pos_right p (by omega)) hpp
  have hLlen := RL_len N p hp3 (by omega)
  have hpc : C p (p - 1) ≤ p := Nat.le_trans (C_le p _) (by omega)
  have hsz := h.size
  -- 544 → 852
  have hsk := h.sk p (by omega)
  dsimp only at hsk
  rw [if_neg (show ¬ SkipMarked p p from fun hs => (skip_self_iff p hp3 hpo).mp hs hprime)] at hsk
  obtain ⟨y1, hr1, hy16, hy24, hy6, g1⟩ := LphaBinary.round_enter x mem out (isqrt N) p h.pre h.size
    h.x15 h.x10 h.x9 hpp hvb hp3 hsk
  -- the marking loop
  have hsk1 := h.sk.wr (by rw [hsz]; omega) p 1 (by omega)
  have hpre1 := prefix_wr (SM + p) (bv 1) 1 h.pre (by rw [hsz]; omega) (by omega)
  obtain ⟨n2, y2, mem2, hr2, hsame2, hsk2, g2⟩ := LphaBinary.mark_loop y1 _ out (isqrt N) p (p * p)
    (upd (fun i => if SkipMarked p i then 1 else 0) p 1) hpre1 (by simp [hsz]) hy16 hy24 hy6
    (by rw [g1 2 (by decide), h.x2]) (by rw [g1 9 (by decide), h.x9])
    (by rw [read_wr_other _ _ _ _ _ _ (by omega) (by omega)]; exact h.s0) hvb hpo hpv
    (Nat.dvd_mul_right p p) (odd_mul hpo hpo) (Nat.le_refl _) hpp
    (hsk1.ext (fun i _ => by
      have : ¬ (p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < p * p) := fun h' => by omega
      simp only [this, ite_false]))
  have hskF : Arr8 mem2 SM (isqrt N + 1) (fun i => if SkipMarked (p + 2) i then 1 else 0) :=
    hsk2.ext (fun i _ => by
      have e := skip_step_prime p i hp3 hpo hprime
      by_cases h1 : p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1
      · rw [if_pos h1, if_pos (e.mpr (Or.inr (Or.inr h1)))]
      · rw [if_neg h1]
        by_cases h2 : i = p
        · subst h2; rw [upd_same, if_pos (e.mpr (Or.inr (Or.inl rfl)))]
        · rw [upd_other _ _ _ _ h2]
          by_cases h3 : SkipMarked p i
          · rw [if_pos h3, if_pos (e.mpr (Or.inl h3))]
          · rw [if_neg h3, if_neg (fun h4 => by
              rcases e.mp h4 with h5 | h5 | h5
              · exact h3 h5
              · exact h2 h5
              · exact h1 h5)])
  have hs1 : Same mem mem2 SM (SM + (isqrt N + 1)) :=
    (Same.wr mem _ (bv 1) 1 SM (SM + (isqrt N + 1)) (by rw [hsz]; omega) (by omega) (by omega)).trans
      ⟨hsame2.size_eq, hsame2.frame⟩
  have hpre2 : Prefix image mem2 1536 := hs1.lpre h.pre (by omega)
  have hsz2 : mem2.size = 4194304 := by rw [hs1.size_eq, hsz]
  -- 872 → 932
  have f2 : ∀ r : Reg, r ∉ ([6, 16, 17, 24] : List Reg) → y2.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g2 r (by simp [hr]), g1 r (by simp [hr])]
  obtain ⟨y3, hr3, hy21, hy20, hy19, hy17, hy16', hy22, hy23, g3⟩ := LphaBinary.compact_enter y2 mem2
    out hpre2 (by rw [f2 2 (by decide), h.x2]) (by rw [f2 11 (by decide), h.x11])
    (by rw [f2 12 (by decide), h.x12]) (by rw [f2 13 (by decide), h.x13])
  have f3 : ∀ r : Reg, r ∉ ([5, 6, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 30] : List Reg) →
      y3.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3 r (by simp [hr]), f2 r (by simp [hr])]
  have hcm := cmath N p h.hN hp3 hprime hpp
  have hrf : RF y3 (isqrt N) p (C p (p - 1)) (RL N p).length :=
    ⟨by rw [f3 7 (by decide), h.x7], by rw [f3 28 (by decide), h.x28], by rw [f3 29 (by decide), h.x29],
     by rw [f3 9 (by decide), h.x9], by rw [f3 15 (by decide), h.x15], by rw [f3 14 (by decide), h.x14],
     by rw [f3 8 (by decide), h.x8], by rw [f3 2 (by decide), h.x2]⟩
  have hs1' := fun {f : Nat → Nat} {n : Nat} (hh : Arr32 mem LB n f) (hn : n ≤ 158114 * 3) =>
    hs1.arr32 hh (by omega)
  obtain ⟨n4, y4, mem4, hr4, hsame4, ha4, hy4_16, g4⟩ := compact1 (RL N p) (fun d => d % p != 0)
    (fun d => C p (N / d)) (fun d => C (p + 1) (N / d)) (fun d => C p (N / d / p))
    (fun i => C p (2 * i + 1)) (fun i => if SkipMarked (p + 2) i then 1 else 0) N (isqrt N) p
    (C p (p - 1)) ⟨hcm, hLlen, hvb, hp563, h.hN, by omega⟩ y3 mem2 out 0 0 hrf hy17 hy16' hy21 hy20 hy19
    hy22 hy23 (by simp)
    ⟨hsz2, hpre2, hs1.read h.s8 (by omega), hs1.read h.s16 (by omega), hs1.read h.s24 (by omega),
     hs1.arr32 h.sm (by omega), hskF, fun k => (RL N p).getD k 0, fun k => C p (N / (RL N p).getD k 0),
     fun k => N / (RL N p).getD k 0, hs1.arr32 h.ro (by omega), hs1.arr32 h.la (by omega),
     hs1.arr64 h.iv (by omega), fun j d hj => by simp at hj,
     fun j d _ hj => by simp [List.getD_eq_getElem?_getD, hj]⟩
    (brk_exists N p hp3 hpo hpp hvb)
  have hdone := ha4.done
  have hpre4 : Prefix image mem4 1536 := ha4.pre
  have hsz4 : mem4.size = 4194304 := ha4.size
  have f4 : ∀ r : Reg, r ∉ ([5, 6, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 30] : List Reg) →
      y4.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g4 r (by simp [hr]), f3 r (by simp [hr])]
  -- the smalls update
  have hvp1 : 1 ≤ isqrt N / p := Nat.div_pos hpv (by omega)
  have hJv : ((isqrt N / p - 1) / 2 * 2 + 1) * p ≤ isqrt N :=
    Nat.le_trans (Nat.mul_le_mul_right p (show (isqrt N / p - 1) / 2 * 2 + 1 ≤ isqrt N / p by omega))
      (Nat.div_mul_le_self _ _)
  have hJ2 : isqrt N + 1 ≤ ((isqrt N / p - 1) / 2 * 2 + 1 + 2) * p := by
    have h1 : isqrt N < (isqrt N / p + 1) * p := by
      rw [Nat.mul_comm]; exact Nat.lt_mul_div_succ _ (by omega)
    have h2 := Nat.mul_le_mul_right p (show isqrt N / p + 1 ≤ (isqrt N / p - 1) / 2 * 2 + 1 + 2 by omega)
    omega
  obtain ⟨y5, hr5, hy5_17, hy5_8, hy5_5, g5⟩ := upd_enter y4 mem4 out (isqrt N) p hpre4
    (by rw [f4 9 (by decide), h.x9]) (by rw [f4 15 (by decide), h.x15])
    (by rw [f4 27 (by decide), h.x27]) hpv hvb hp3
  have hsm4 : Arr32 mem4 SB ((isqrt N + 1) / 2) (fun i => C p (2 * i + 1)) := ha4.sm
  obtain ⟨n6, y6, mem6, hr6, hsame6, hsm6, g6⟩ := upd_loop y5 mem4 out (isqrt N)
    ((isqrt N + 1) / 2) p (C p (p - 1)) (fun i => C p (2 * i + 1)) (fun i => C (p + 1) (2 * i + 1))
    ((isqrt N / p - 1) / 2 * 2 + 1) ((isqrt N - 1) / 2) hpre4 hsz4 hy5_17 hy5_8 hy5_5
    (by rw [g5 15 (by decide), f4 15 (by decide), h.x15])
    (by rw [g5 24 (by decide), g4 24 (by decide), g3 24 (by decide), g2 24 (by decide), hy24])
    (by rw [g5 29 (by decide), f4 29 (by decide), h.x29]) (by rw [g5 31 (by decide), f4 31 (by decide), h.x31])
    (by rw [g5 14 (by decide), f4 14 (by decide), h.x14]) rfl hvb hp3 hpv hpo
    (by omega) hJv (by
      have : (isqrt N + 1) / 2 ≤ ((isqrt N / p - 1) / 2 * 2 + 1 + 2) * p / 2 := Nat.div_le_div_right hJ2
      omega) (by omega)
    (upd_math N p hp3 hprime hpo _) (fun u _ hu => upd_math0 p hp3 hpo u hu)
    (fun u _ => by have := C_le p (2 * u + 1); omega)
    (hsm4.ext (fun u hu => by simp [show ¬ (isqrt N - 1) / 2 < u by omega]))
  have hpre6 : Prefix image mem6 1536 := hsame6.lpre hpre4 (by omega)
  have f6 : ∀ r : Reg, r ∉ ([5, 6, 8, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 30] : List Reg) →
      y6.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g6 r (by simp [hr]), g5 r (by simp [hr]), f4 r (by simp [hr])]
  have hRL := RL_prime N p hp3 hpo hpv
  obtain ⟨y7, hr7, hy7_14, hy7_8, hy7_15, hy7_10, g7⟩ := LphaBinary.round_exit y6 mem6 out (C p (p - 1))
    ((RL N p).filter (fun d => d % p != 0)).length p hpre6
    (by rw [f6 14 (by decide), h.x14]) (by rw [g6 16 (by decide), g5 16 (by decide), hy4_16])
    (by rw [f6 15 (by decide), h.x15]) (by rw [f6 10 (by decide), h.x10]) (by omega) hp3 (by omega)
  have f7 : ∀ r : Reg, r ∉ ([5, 6, 8, 10, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 30] :
      List Reg) → y7.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g7 r (by simp [hr]), f6 r (by simp [hr])]
  obtain ⟨x9, x27, x7, x28, x29, x31, x11, x12, x13, x2⟩ := h.frame' f7
  obtain ⟨hdR, hdL, hdI⟩ := hdone
  rw [hRL] at hdR hdL hdI hy7_8
  have hlen2 := RL_len N (p + 2) (by omega) (by omega)
  have S46 : Same mem4 mem6 SB (SB + (isqrt N + 1) / 2 * 4) := hsame6
  refine ⟨8 + (n2 + (15 + (n4 + (5 + (n6 + 5))))), y7, mem6, ?_, ?_⟩
  · rw [run_add, hr1, run_add, hr2, run_add, hr3, run_add, hr4, run_add, hr5, run_add, hr6, hr7]
  refine ⟨h.hN2, h.hN, by omega, by omega, ?_, hy7_15,
    by rw [hy7_14, C_pc_prime p hp3 hpo hprime], hy7_10, x9, hy7_8, x27, x7, x28, x29, x31, x11, x12,
    x13, x2, by rw [hsame6.size_eq, hsz4], hpre6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h3 hr hpr
    by_cases hrp : r < p
    · exact h.hpr r h3 hrp hpr
    · by_cases hre : r = p
      · subst hre
        exact Nat.le_trans (Nat.mul_le_mul hpp hpp) (isqrt_spec N).1
      · exact absurd hpr (by rw [show r = p + 1 by omega]; exact not_prime_even p hp3 hpo)
  · exact hsame6.read (hsame4.read (hs1.read h.ra (by omega)) (by omega)) (by omega)
  · exact hsame6.read (hsame4.read (hs1.read h.s0 (by omega)) (by omega)) (by omega)
  · exact hsame6.read ha4.s8 (by omega)
  · exact hsame6.read ha4.s16 (by omega)
  · exact hsame6.read ha4.s24 (by omega)
  · exact hsm6.ext (fun i _ => by
      rw [show p + 2 = (p + 1) + 1 by omega, C_composite (p + 1) (by omega) (not_prime_even p hp3 hpo)])
  · exact hsame6.arr32 hdR (by omega)
  · exact hsame6.arr64 hdI (by omega)
  · exact (hsame6.arr32 hdL (by omega)).ext (fun i _ => by
      rw [show p + 2 = (p + 1) + 1 by omega, C_composite (p + 1) (by omega) (not_prime_even p hp3 hpo)])
  · exact hsame6.arr8 (hsame4.arr8 hskF (by omega)) (by omega)

theorem prime_563' : Prime 563 := by decide +kernel

/-- From any stage, the sieve loop reaches 552 at a stage `a` with `v < a²`. -/
theorem outer_loop (N p : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h : Inv N p x mem) :
    ∃ n a y mem', run n ⟨x, bv 544, mem, [], out, .running⟩ = ⟨y, bv 552, mem', [], out, .running⟩ ∧
      Inv N a y mem' ∧ isqrt N < a * a := by
  have hvb := inv_vb h
  have hp3 := h.hp3
  have hp564 : p ≤ 564 := by
    apply Decidable.byContradiction; intro hc
    have h1 := h.hpr 563 (by decide) (by omega) prime_563'
    have := (isqrt_spec N).1
    have := h.hN
    omega
  by_cases hpp : p * p ≤ isqrt N
  · by_cases hprime : Prime p
    · obtain ⟨n1, y1, mem1, hr1, h1⟩ := round_prime N p x mem out h hprime hpp
      obtain ⟨n2, a, y2, mem2, hr2, h2, hc⟩ := outer_loop N (p + 2) y1 mem1 out h1
      exact ⟨n1 + n2, a, y2, mem2, by rw [run_add, hr1, hr2], h2, hc⟩
    · obtain ⟨n1, y1, hr1, h1⟩ := LphaBinary.round_skip N p x mem out h hpp hprime
      obtain ⟨n2, a, y2, mem2, hr2, h2, hc⟩ := outer_loop N (p + 2) y1 mem out h1
      exact ⟨n1 + n2, a, y2, mem2, by rw [run_add, hr1, hr2], h2, hc⟩
  · obtain ⟨y, hr, hy16, hf⟩ := LphaBinary.outer_exit x mem out (isqrt N) p h.pre h.x15 h.x9
      (by omega) (by omega)
    have g : ∀ r : Reg, r ≠ 16 → y.get r = x.get r := fun r hr => hf r (by simp [hr])
    refine ⟨2, p, y, mem, hr, ?_, by omega⟩
    exact { h with
      x15 := by rw [g 15 (by decide), h.x15], x14 := by rw [g 14 (by decide), h.x14]
      x10 := by rw [g 10 (by decide), h.x10], x9 := by rw [g 9 (by decide), h.x9]
      x8 := by rw [g 8 (by decide), h.x8], x27 := by rw [g 27 (by decide), h.x27]
      x7 := by rw [g 7 (by decide), h.x7], x28 := by rw [g 28 (by decide), h.x28]
      x29 := by rw [g 29 (by decide), h.x29], x31 := by rw [g 31 (by decide), h.x31]
      x11 := by rw [g 11 (by decide), h.x11], x12 := by rw [g 12 (by decide), h.x12]
      x13 := by rw [g 13 (by decide), h.x13], x2 := by rw [g 2 (by decide), h.x2] }
termination_by isqrt N + 3 - p
decreasing_by all_goals (have := Nat.le_mul_self p; omega)

end TinyFive.LphaBinary
