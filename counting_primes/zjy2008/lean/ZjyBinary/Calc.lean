import ZjyBinary.Update

/-! `calc(p)`, the lambda at 36, as one sieve round at a prime `p` with `p⁴ ≤ N`: from the
memory invariant at stage `p` to the one at stage `p + 2`, returning to its caller. -/
namespace TinyFive.ZjyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

/-! ## Heap layout: `small` at 1520, then `rough`, `skip` and `large`, each 8-aligned. -/

def ZB (s0 : Nat) : Nat := (1520 + 4 * s0 + 7) / 8 * 8
def ZD (s0 : Nat) : Nat := (ZB s0 + 4 * s0 + 7) / 8 * 8
def ZC (s0 v : Nat) : Nat := (ZD s0 + (v + 1) + 7) / 8 * 8

theorem zlayout (s0 v : Nat) : 1520 + s0 * 4 ≤ ZB s0 ∧ ZB s0 + s0 * 4 ≤ ZD s0 ∧
    ZD s0 + v + 1 ≤ ZC s0 v ∧ ZB s0 ≤ 1520 + s0 * 4 + 7 ∧ ZD s0 ≤ ZB s0 + s0 * 4 + 7 ∧
    ZC s0 v ≤ ZD s0 + v + 8 ∧ ZB s0 % 8 = 0 ∧ ZD s0 % 8 = 0 ∧ ZC s0 v % 8 = 0 := by
  unfold ZC ZD ZB; omega

/-- The memory at a call of `calc(p)` (and in `pi`'s wheel loop): the tables at stage `p`,
and `pi`'s stack frame. -/
structure ZMem (N p : Nat) (mem : Array (BitVec 8)) : Prop where
  hN7 : 7 ≤ N
  hN : N < 100000000000
  hp3 : 3 ≤ p
  hpo : p % 2 = 1
  hpr : ∀ r, 3 ≤ r → r < p → Prime r → r * r * (r * r) ≤ N
  size : mem.size = 4194304
  pre : Prefix image mem 1480
  ra : readBytes mem 4194296 8 = some (bv 8)
  sl : Slots mem N (isqrt N) (C p (p - 1)) (RL N p).length 1520 (ZB ((isqrt N + 1) / 2))
    (ZD ((isqrt N + 1) / 2)) (ZC ((isqrt N + 1) / 2) (isqrt N))
  sm : Arr32 mem 1520 ((isqrt N + 1) / 2) (fun i => C p (2 * i + 1))
  ro : Arr32 mem (ZB ((isqrt N + 1) / 2)) (RL N p).length (fun k => (RL N p).getD k 0)
  la : Arr64 mem (ZC ((isqrt N + 1) / 2) (isqrt N)) (RL N p).length
    (fun k => C p (N / (RL N p).getD k 0))
  sk : Arr8 mem (ZD ((isqrt N + 1) / 2)) (isqrt N + 1) (fun i => if SkipMarked p i then 1 else 0)

theorem zmem_bounds {N p : Nat} {mem : Array (BitVec 8)} (h : ZMem N p mem) :
    isqrt N < 316228 ∧ ZC ((isqrt N + 1) / 2) (isqrt N) + (isqrt N + 1) / 2 * 8 ≤ 4194000 := by
  have hv := r_lt_of_sq (isqrt_spec N).1 h.hN
  have := zlayout ((isqrt N + 1) / 2) (isqrt N)
  omega

theorem calc_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (D p S : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h10 : x.get 10 = bv 4194160) (h11 : x.get 11 = bv p) (h2 : x.get 2 = bv 4194096)
    (h8 : x.get 8 = bv S) (hD : 1520 ≤ D) (hDp : D + p < 4194000) (hp : p < 1000)
    (hpp : p * p < 400000)
    (k0 : readBytes mem 4194160 8 = some (bv 4194144))
    (k1 : readBytes mem 4194168 8 = some (bv 4194116))
    (ssk : readBytes mem 4194144 8 = some (bv D))
    (sR : readBytes mem 4194116 4 = some (BitVec.ofNat 32 v)) (hv : v < 400000) :
    ∃ y, run 12 ⟨x, bv 36, mem, [], out, .running⟩ =
      ⟨y, bv 84, wr (wr mem 4194088 (bv S) 8) (D + p) (bv 1) 1, [], out, .running⟩ ∧
      y.get 15 = bv (p * p) ∧ y.get 14 = bv (p * 2) ∧ y.get 16 = bv 1 ∧ y.get 31 = bv D ∧
      y.get 12 = bv v ∧ y.get 30 = bv 4194116 ∧ y.get 2 = bv 4194080 ∧
      (∀ r : Reg, r ∉ ([2, 12, 14, 15, 16, 30, 31] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by frame_tac⟩

theorem compact_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1480) (h10 : x.get 10 = bv 4194160)
    (k2 : readBytes mem 4194176 8 = some (bv 4194124))
    (k6 : readBytes mem 4194208 8 = some (bv 4194120)) :
    ∃ y, run 4 ⟨x, bv 92, mem, [], out, .running⟩ = ⟨y, bv 108, mem, [], out, .running⟩ ∧
      y.get 7 = bv 4194124 ∧ y.get 28 = bv 4194120 ∧ y.get 16 = bv 0 ∧ y.get 12 = bv 0 ∧
      (∀ r : Reg, r ∉ ([7, 12, 16, 28] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by frame_tac⟩

theorem upd_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p ns : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h12 : x.get 12 = bv ns) (h7 : x.get 7 = bv 4194124) (h30 : x.get 30 = bv 4194116)
    (h11 : x.get 11 = bv p)
    (sR : readBytes mem 4194116 4 = some (BitVec.ofNat 32 v))
    (hpv : p ≤ v) (hv : v < 316228) (hp3 : 3 ≤ p) (hns : ns < 200000)
    (hj : ((v / p - 1) / 2 * 2 + 1) * p ≤ v) :
    ∃ y, run 11 ⟨x, bv 120, mem, [], out, .running⟩ =
      ⟨y, bv 164, wr mem 4194124 (bv ns) 4, [], out, .running⟩ ∧
      y.get 16 = bv ((v / p - 1) / 2 * 2 + 1) ∧ y.get 15 = bv (((v / p - 1) / 2 * 2 + 1) * p) ∧
      y.get 14 = bv ((v - 1) / 2) ∧ y.get 17 = m2p p ∧
      (∀ r : Reg, r ∉ ([14, 15, 16, 17] : List Reg) → y.get r = x.get r) := by
  have : 1 ≤ v / p := Nat.div_pos hpv (by omega)
  have := Nat.div_le_self v p
  exact ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by frame_tac⟩

theorem calc_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (pc S R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h12 : x.get 12 = bv pc) (h28 : x.get 28 = bv 4194120) (h2 : x.get 2 = bv 4194080)
    (h1 : x.get 1 = bv R) (hR : R % 2 = 0) (hR' : R < 1480) (hpc : pc < 200000)
    (hS : readBytes mem 4194088 8 = some (bv S)) :
    ∃ y, run 5 ⟨x, bv 172, mem, [], out, .running⟩ =
      ⟨y, bv R, wr mem 4194120 (bv (pc + 1)) 4, [], out, .running⟩ ∧
      y.get 8 = bv S ∧ y.get 2 = bv 4194096 ∧
      (∀ r : Reg, r ∉ ([2, 8, 12] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

/-- `calc(p)` for a prime `p` with `p⁴ ≤ N`: one sieve round, returning to `R` with the memory
at stage `p + 2`. -/
theorem calc_prime (N p : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (S R : Nat)
    (h : ZMem N p mem) (hprime : Prime p) (hq : p * p * (p * p) ≤ N)
    (h10 : x.get 10 = bv 4194160) (h11 : x.get 11 = bv p) (h2 : x.get 2 = bv 4194096)
    (h8 : x.get 8 = bv S) (h1 : x.get 1 = bv R) (hR : R % 2 = 0) (hR' : R < 1480) :
    ∃ n y mem', run n ⟨x, bv 36, mem, [], out, .running⟩ = ⟨y, bv R, mem', [], out, .running⟩ ∧
      ZMem N (p + 2) mem' ∧ y.get 8 = bv S ∧ y.get 2 = bv 4194096 ∧
      (∀ r : Reg, r ∉ ([2, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] : List Reg) →
        y.get r = x.get r) := by
  obtain ⟨hvb, hCe⟩ := zmem_bounds h
  have hp562 := p_small h.hN hq
  have hp3 := h.hp3
  have hpo := h.hpo
  have hppv : p * p ≤ isqrt N := le_isqrt hq
  have hpv : p ≤ isqrt N := Nat.le_trans (Nat.le_mul_of_pos_right p (by omega)) hppv
  have hlay := zlayout ((isqrt N + 1) / 2) (isqrt N)
  have hLlen := RL_len N p hp3 (by omega)
  have hpc : C p (p - 1) ≤ p := Nat.le_trans (C_le p _) (by omega)
  have hsz := h.size
  have hsl := h.sl
  have hsk := h.sk p (by omega)
  dsimp only at hsk
  rw [if_neg (show ¬ SkipMarked p p from fun hs => (skip_self_iff p hp3 hpo).mp hs hprime)] at hsk
  have hpp : p * p < 400000 := by
    have := Nat.mul_le_mul (show p ≤ 562 by omega) (show p ≤ 562 by omega); omega
  -- 36 → 84: save s0, set skip[p], start the marking at p²
  obtain ⟨y1, hr1, hy15, hy14, hy16, hy31, hy12, hy30, hy2, g1⟩ := calc_enter x mem out
    (ZD ((isqrt N + 1) / 2)) p S h.pre hsz h10 h11 h2 h8 (by omega) (by omega) (by omega) hpp
    hsl.k0 hsl.k1 hsl.sk hsl.R (by omega)
  have hw0 : 4194088 + 8 ≤ mem.size := by omega
  have hsk0 := h.sk.congr (wr_frame mem 4194088 (bv S) 8 _ _ hw0 (by omega))
  have hsk1 := hsk0.wr (by simp; omega) p 1 (by omega)
  have hpre1 : Prefix image (wr (wr mem 4194088 (bv S) 8) (ZD ((isqrt N + 1) / 2) + p) (bv 1) 1) 1480 :=
    prefix_wr _ _ _ (prefix_wr _ _ _ h.pre hw0 (by omega)) (by simp; omega) (by omega)
  obtain ⟨n2, y2, mem2, hr2, hsame2, hsk2, g2⟩ := mark_loop y1 _ out (ZD ((isqrt N + 1) / 2))
    (isqrt N) p (p * p) (upd (fun i => if SkipMarked p i then 1 else 0) p 1) hpre1 (by simp [hsz])
    hy15 hy14 hy16 hy31 hy12 (by omega) (by omega) (by omega) hpo hpv
    (Nat.dvd_mul_right p p) (odd_mul hpo hpo) (Nat.le_refl _) (by omega)
    (hsk1.ext (fun i _ => by
      have : ¬ (p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < p * p) := fun h' => by omega
      simp only [this, ite_false]))
  have hskF : Arr8 mem2 (ZD ((isqrt N + 1) / 2)) (isqrt N + 1)
      (fun i => if SkipMarked (p + 2) i then 1 else 0) :=
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
  -- the slot of the saved s0, and skip
  have hSa : Same mem (wr mem 4194088 (bv S) 8) 4194088 4194096 :=
    Same.wr mem 4194088 (bv S) 8 _ _ hw0 (by omega) (by omega)
  have hSb : Same (wr mem 4194088 (bv S) 8) mem2 (ZD ((isqrt N + 1) / 2))
      (ZD ((isqrt N + 1) / 2) + (isqrt N + 1)) :=
    (Same.wr _ _ (bv 1) 1 _ _ (by simp; omega) (by omega) (by omega)).trans hsame2
  have hpre2 : Prefix image mem2 1480 := hSb.zpre (hSa.zpre h.pre (by omega)) (by omega)
  have hsz2 : mem2.size = 4194304 := by rw [hSb.size_eq, hSa.size_eq, hsz]
  have hsl2 := (hsl.same hSa (by omega)).same hSb (by omega)
  have ar32 : ∀ {b n : Nat} {f : Nat → Nat}, Arr32 mem b n f → b + n * 4 ≤ ZD ((isqrt N + 1) / 2) →
      Arr32 mem2 b n f := fun ha hb => hSb.arr32 (hSa.arr32 ha (by omega)) (by omega)
  obtain ⟨y3, hr3, hy7, hy28, hy16', hy12', g3⟩ := compact_enter y2 mem2 out hpre2
    (by rw [g2 10 (by decide), g1 10 (by decide), h10]) hsl2.k2 hsl2.k6
  have f3 : ∀ r : Reg, r ∉ ([2, 7, 12, 13, 14, 15, 16, 28, 30, 31] : List Reg) → y3.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3 r (by simp [hr]), g2 r (by simp [hr]), g1 r (by simp [hr])]
  have hcm := cmath N p h.hN hp3 hprime hppv
  have hlenb : (RL N p).length < 200000 := by omega
  obtain ⟨n4, y4, mem4, hr4, hsame4, hro4, hla4, hsk4, hy4_12, g4⟩ := compact_loop (RL N p)
    (fun d => d % p != 0) (fun d => C p (N / d)) (fun d => C (p + 1) (N / d))
    (fun d => C p (N / d / p)) (fun i => C p (2 * i + 1))
    (fun i => if SkipMarked (p + 2) i then 1 else 0) 1520 (ZB ((isqrt N + 1) / 2))
    (ZC ((isqrt N + 1) / 2) (isqrt N)) (ZD ((isqrt N + 1) / 2)) N (isqrt N) p (C p (p - 1))
    ((isqrt N + 1) / 2) hcm rfl hLlen (by omega) (by omega) (by omega) (by omega) y3 mem2 out 0 0
    (fun k => (RL N p).getD k 0) (fun k => C p (N / (RL N p).getD k 0))
    ⟨by rw [f3 10 (by decide), h10], by rw [f3 11 (by decide), h11],
     by rw [g3 31 (by decide), g2 31 (by decide), hy31], by rw [g3 30 (by decide), g2 30 (by decide), hy30],
     hy7, hy28⟩
    ⟨hlenb, by omega, hpv, h.hN, Nat.le_refl _, by omega, by omega, by omega, by omega, by omega⟩
    hsl2 hpre2 hsz2 hy16' hy12' (Nat.zero_le _) (by simp)
    (ar32 h.ro (by omega)) (hSb.arr64 (hSa.arr64 h.la (by omega)) (by omega)) (ar32 h.sm (by omega)) hskF
    (fun j d hj => by simp at hj)
    (fun j d _ hj => by simp [List.getD_eq_getElem?_getD, hj])
  have hpre4 : Prefix image mem4 1480 := hsame4.zpre hpre2 (by omega)
  have hsz4 : mem4.size = 4194304 := by rw [hsame4.size_eq, hsz2]
  have hsl4 := hsl2.same hsame4 (by omega)
  have f4 : ∀ r : Reg, r ∉ ([2, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] : List Reg) →
      y4.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g4 r (by simp [hr]), f3 r (by simp [hr])]
  have hcr4 : CRegs y4 p (ZD ((isqrt N + 1) / 2)) := by
    refine CRegs.frame ⟨by rw [f3 10 (by decide), h10], by rw [f3 11 (by decide), h11],
     by rw [g3 31 (by decide), g2 31 (by decide), hy31], by rw [g3 30 (by decide), g2 30 (by decide), hy30],
     hy7, hy28⟩ g4
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
  have hflen : ((RL N p).filter (fun d => d % p != 0)).length < 200000 := by
    have := List.length_filter_le (fun d => d % p != 0) (RL N p); omega
  obtain ⟨y5, hr5, hy5_16, hy5_15, hy5_14, hy5_17, g5⟩ := upd_enter y4 mem4 out (isqrt N) p
    ((RL N p).filter (fun d => d % p != 0)).length hpre4 hsz4 hy4_12 hcr4.h7 hcr4.h30 hcr4.h11
    hsl4.R hpv (by omega) hp3 hflen hJv
  have hw5 : 4194124 + 4 ≤ mem4.size := by omega
  have hS5 := Same.wr mem4 4194124 (bv ((RL N p).filter (fun d => d % p != 0)).length) 4 4194124 4194128 hw5
    (by omega) (by omega)
  have hsm4 : Arr32 mem4 1520 ((isqrt N + 1) / 2) (fun i => C p (2 * i + 1)) :=
    hsame4.arr32 (ar32 h.sm (by omega)) (by omega)
  have hpre5 := prefix_wr _ (bv ((RL N p).filter (fun d => d % p != 0)).length) _ hpre4 hw5 (by omega)
  obtain ⟨n6, y6, mem6, hr6, hsame6, hsm6, hy6_12, g6⟩ := upd_loop y5 _ out 1520 (isqrt N)
    ((isqrt N + 1) / 2) p (C p (p - 1)) (fun i => C p (2 * i + 1)) (fun i => C (p + 1) (2 * i + 1))
    ((isqrt N / p - 1) / 2 * 2 + 1) ((isqrt N - 1) / 2) hpre5 (by simp [hsz4]) hy5_16 hy5_15 hy5_14
    (by rw [g5 11 (by decide), hcr4.h11]) hy5_17 (by rw [g5 10 (by decide), hcr4.h10])
    (by rw [g5 28 (by decide), hcr4.h28]) (hS5.read hsl4.C (by omega)) (hS5.read hsl4.sm (by omega))
    (hS5.read hsl4.k5 (by omega)) (by omega) (by omega) rfl (by omega) hp3 hpv hpo
    (by omega) hJv (by
      have : (isqrt N + 1) / 2 ≤ ((isqrt N / p - 1) / 2 * 2 + 1 + 2) * p / 2 := Nat.div_le_div_right hJ2
      omega) (by omega)
    (upd_math N p hp3 hprime hpo _) (fun u _ hu => upd_math0 p hp3 hpo u hu)
    (fun u _ => by have := C_le p (2 * u + 1); omega)
    ((hS5.arr32 hsm4 (by omega)).ext (fun u hu => by simp [show ¬ (isqrt N - 1) / 2 < u by omega]))
  have hpre6 : Prefix image mem6 1480 := hsame6.zpre hpre5 (by omega)
  have hsz6 : mem6.size = 4194304 := by rw [hsame6.size_eq, wr_size, hsz4]
  have f6 : ∀ r : Reg, r ∉ ([2, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] : List Reg) →
      y6.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g6 r (by simp [hr]), g5 r (by simp [hr]), f4 r (by simp [hr])]
  have hy6_2 : y6.get 2 = bv 4194080 := by
    rw [g6 2 (by decide), g5 2 (by decide), g4 2 (by decide), g3 2 (by decide), g2 2 (by decide), hy2]
  have hy6_28 : y6.get 28 = bv 4194120 := by rw [g6 28 (by decide), g5 28 (by decide), hcr4.h28]
  have hsave : readBytes (wr mem 4194088 (bv S) 8) 4194088 8 = some (bv S) := by
    rw [read_wr_same _ _ _ _ hw0]; simp
  have hsave6 : readBytes mem6 4194088 8 = some (bv S) :=
    hsame6.read (hS5.read (hsame4.read (hSb.read hsave (by omega)) (by omega)) (by omega)) (by omega)
  obtain ⟨y7, hr7, hy7_8, hy7_2, g7⟩ := calc_exit y6 mem6 out (C p (p - 1)) S R hpre6 hsz6 hy6_12
    hy6_28 hy6_2 (by rw [f6 1 (by decide), h1]) hR hR' (by omega) hsave6
  have hw7 : 4194120 + 4 ≤ mem6.size := by omega
  have hS7 := Same.wr mem6 4194120 (bv (C p (p - 1) + 1)) 4 4194120 4194124 hw7 (by omega) (by omega)
  -- reads from mem4 that survive to the end
  have tr : ∀ {a k : Nat} {w : BitVec (8 * k)}, readBytes mem4 a k = some w →
      a + k ≤ 1520 ∨ 1520 + (isqrt N + 1) / 2 * 4 ≤ a → a + k ≤ 4194120 ∨ 4194128 ≤ a →
      readBytes (wr mem6 4194120 (bv (C p (p - 1) + 1)) 4) a k = some w :=
    fun hr h1 h2 => hS7.read (hsame6.read (hS5.read hr (by omega)) (by omega)) (by omega)
  have hRL := RL_prime N p hp3 hpo hpv
  rw [hRL] at hro4 hla4
  have hlen2 := RL_len N (p + 2) (by omega) (by omega)
  refine ⟨12 + (n2 + (4 + (n4 + (11 + (n6 + 5))))), y7, wr mem6 4194120 (bv (C p (p - 1) + 1)) 4, ?_, ?_,
    hy7_8, hy7_2, ?_⟩
  · rw [run_add, hr1, run_add, hr2, run_add, hr3, run_add, hr4, run_add, hr5, run_add, hr6, hr7]
  · refine ⟨h.hN7, h.hN, by omega, by omega, ?_, by simp [hsz6], prefix_wr _ _ _ hpre6 hw7 (by omega),
      tr (hsame4.read (hSb.read (hSa.read h.ra (by omega)) (by omega)) (by omega)) (by omega) (by omega),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro r h3 hr hpr
      by_cases hrp : r < p
      · exact h.hpr r h3 hrp hpr
      · by_cases hre : r = p
        · subst hre; exact hq
        · exact absurd hpr (by rw [show r = p + 1 by omega]; exact not_prime_even p hp3 hpo)
    · rw [C_pc_prime p hp3 hpo hprime]
      exact ⟨tr hsl4.n (by omega) (by omega), tr hsl4.R (by omega) (by omega),
        by rw [read_wr_same _ _ _ _ hw7]; simp,
        hS7.read (hsame6.read (by rw [read_wr_same _ _ _ _ hw5]; simp [hRL]) (by omega)) (by omega),
        tr hsl4.sm (by omega) (by omega), tr hsl4.ro (by omega) (by omega),
        tr hsl4.sk (by omega) (by omega), tr hsl4.la (by omega) (by omega),
        tr hsl4.k0 (by omega) (by omega), tr hsl4.k1 (by omega) (by omega),
        tr hsl4.k2 (by omega) (by omega), tr hsl4.k3 (by omega) (by omega),
        tr hsl4.k4 (by omega) (by omega), tr hsl4.k5 (by omega) (by omega),
        tr hsl4.k6 (by omega) (by omega), tr hsl4.k7 (by omega) (by omega)⟩
    · exact (hS7.arr32 hsm6 (by omega)).ext (fun i _ => by
        rw [show p + 2 = (p + 1) + 1 by omega, C_composite (p + 1) (by omega) (not_prime_even p hp3 hpo)])
    · exact hS7.arr32 (hsame6.arr32 (hS5.arr32 hro4 (by omega)) (by omega)) (by omega)
    · exact (hS7.arr64 (hsame6.arr64 (hS5.arr64 hla4 (by omega)) (by omega)) (by omega)).ext (fun i _ => by
        rw [show p + 2 = (p + 1) + 1 by omega, C_composite (p + 1) (by omega) (not_prime_even p hp3 hpo)])
    · exact hS7.arr8 (hsame6.arr8 (hS5.arr8 hsk4 (by omega)) (by omega)) (by omega)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g7 r (by simp [hr]), f6 r (by simp [hr])]

end TinyFive.ZjyBinary
