import GrumpyBinary.RoundMath

/-! The outer loop of `prime_pi` at 388: its invariant, and one pass (a skipped `p`, or a sieve
round at a prime `p`). -/
namespace TinyFive.GrumpyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory

local notation "bv" => BitVec.ofNat 64

/-! ## Frames through `Same` -/

theorem Same.arr8 {m m' : Array (BitVec 8)} {lo hi base n : Nat} {f : Nat → Nat}
    (h : Same m m' lo hi) (ha : Arr8 m base n f) (hd : base + n ≤ lo ∨ hi ≤ base) :
    Arr8 m' base n f := ha.congr (fun j h1 h2 => h.frame j (by omega))

theorem Same.arr32 {m m' : Array (BitVec 8)} {lo hi base n : Nat} {f : Nat → Nat}
    (h : Same m m' lo hi) (ha : Arr32 m base n f) (hd : base + n * 4 ≤ lo ∨ hi ≤ base) :
    Arr32 m' base n f := ha.congr (fun j h1 h2 => h.frame j (by omega))

theorem Same.arr64 {m m' : Array (BitVec 8)} {lo hi base n : Nat} {f : Nat → Nat}
    (h : Same m m' lo hi) (ha : Arr64 m base n f) (hd : base + n * 8 ≤ lo ∨ hi ≤ base) :
    Arr64 m' base n f := ha.congr (fun j h1 h2 => h.frame j (by omega))

theorem Same.read {m m' : Array (BitVec 8)} {lo hi a k : Nat} {w : BitVec (8 * k)}
    (h : Same m m' lo hi) (hr : readBytes m a k = some w) (hd : a + k ≤ lo ∨ hi ≤ a) :
    readBytes m' a k = some w := by
  rw [readBytes_congr m' m a k (fun j h1 h2 => h.frame j (by omega))]; exact hr

theorem Arr32.shrink {m : Array (BitVec 8)} {base n n' : Nat} {f : Nat → Nat}
    (h : Arr32 m base n f) (hn : n' ≤ n) : Arr32 m base n' f := fun i hi => h i (by omega)

/-! ## Layout -/

/-- Tables: `smalls` at 1248, then `roughs`, `larges` (8-aligned) and `skip`. -/
def LB (s0 : Nat) : Nat := (1248 + 4 * s0 + 7) / 8 * 8
def LC (s0 : Nat) : Nat := (LB s0 + 4 * s0 + 7) / 8 * 8
def LD (s0 : Nat) : Nat := LC s0 + s0 * 8

theorem layout (s0 : Nat) : 1248 + s0 * 4 ≤ LB s0 ∧ LB s0 + s0 * 4 ≤ LC s0 ∧
    LB s0 ≤ 1248 + s0 * 4 + 7 ∧ LC s0 ≤ LB s0 + s0 * 4 + 7 ∧ LB s0 % 8 = 0 ∧ LC s0 % 8 = 0 := by
  unfold LC LB; omega

/-- The rough list at stage `p`, with the sentinel 1. -/
abbrev RL (N p : Nat) : List Nat := 1 :: roughList p (isqrt N)

/-- The state at the head of the outer loop (388) before stage `p`. -/
structure Inv (N p : Nat) (x : Regs 64) (mem : Array (BitVec 8)) : Prop where
  hN3 : 3 ≤ N
  hN : N < 100000000000
  hp3 : 3 ≤ p
  hpo : p % 2 = 1
  hpr : ∀ r, 3 ≤ r → r < p → Prime r → r * r * (r * r) ≤ N
  x8 : x.get 8 = bv (LC ((isqrt N + 1) / 2))
  x9 : x.get 9 = bv (RL N p).length
  x18 : x.get 18 = bv (isqrt N)
  x19 : x.get 19 = bv N
  x20 : x.get 20 = bv 1248
  x21 : x.get 21 = bv (LB ((isqrt N + 1) / 2))
  x22 : x.get 22 = bv ((isqrt N - 1) / 2)
  x23 : x.get 23 = bv (isqrt N + 1)
  x24 : x.get 24 = bv (LD ((isqrt N + 1) / 2))
  x25 : x.get 25 = bv 1240
  x12 : x.get 12 = bv p
  x14 : x.get 14 = bv (C p (p - 1))
  x10 : x.get 10 = bv 1
  x2 : x.get 2 = bv 4194192
  size : mem.size = 4194304
  pre : Prefix image mem 1236
  ra : readBytes mem 4194296 8 = some (bv 8)
  sm : Arr32 mem 1248 ((isqrt N + 1) / 2) (fun i => C p (2 * i + 1))
  ro : Arr32 mem (LB ((isqrt N + 1) / 2)) (RL N p).length (fun k => (RL N p).getD k 0)
  la : Arr64 mem (LC ((isqrt N + 1) / 2)) (RL N p).length (fun k => C p (N / (RL N p).getD k 0))
  sk : Arr8 mem (LD ((isqrt N + 1) / 2)) (isqrt N + 1) (fun i => if SkipMarked p i then 1 else 0)

/-! ## Counting facts -/

theorem count_imp {Q R : Nat → Prop} [DecidablePred Q] [DecidablePred R] (h : ∀ n, Q n → R n)
    (v : Nat) : count Q v ≤ count R v := by
  induction v with
  | zero => exact Nat.le_refl _
  | succ v ih =>
    rw [count_succ, count_succ]
    by_cases hq : Q (v + 1)
    · simp [hq, h _ hq]; omega
    · simp only [hq, ite_false]; split <;> omega

theorem C_le_half (p x : Nat) (hp : 3 ≤ p) : C p x ≤ (x - 1) / 2 := by
  rw [← C_init]
  apply count_imp
  rintro n ⟨h3, hm⟩
  exact ⟨h3, fun ⟨d, h1, h2, h3', h4⟩ => hm ⟨d, h1, by omega, h3', h4⟩⟩

theorem rough_len (p v : Nat) (hp : 3 ≤ p) : (roughList p v).length ≤ C p v := by
  by_cases hpv : p ≤ v + 1
  · have := interval_length p (v + 1 - p) hp
    rw [show p - 1 + (v + 1 - p) = v by omega] at this
    unfold roughList; omega
  · unfold roughList; rw [show v + 1 - p = 0 by omega]; simp

theorem RL_len (N p : Nat) (hp : 3 ≤ p) (hv : 1 ≤ isqrt N) : (RL N p).length ≤ (isqrt N + 1) / 2 := by
  have := rough_len p (isqrt N) hp
  have := C_le_half p (isqrt N) hp
  simp only [RL, List.length_cons]; omega

theorem rough_skip' {p v : Nat} (hp : 3 ≤ p) (hn : ¬ Prime p) :
    roughList (p + 1) v = roughList p v := by
  by_cases hpv : p ≤ v
  · exact rough_skip hp hpv hn
  · unfold roughList; rw [show v + 1 - p = 0 by omega, show v + 1 - (p + 1) = 0 by omega]; simp

/-- Bounds the round needs: `v ≤ 316227` and the table layout fits below the stack. -/
theorem inv_bounds {N p : Nat} {x : Regs 64} {mem : Array (BitVec 8)} (h : Inv N p x mem) :
    isqrt N < 316228 ∧ LD ((isqrt N + 1) / 2) + isqrt N + 1 ≤ 3000000 := by
  have hv := r_lt_of_sq (isqrt_spec N).1 h.hN
  have := layout ((isqrt N + 1) / 2)
  unfold LD; omega

theorem C_skip2 (p : Nat) (hp : 3 ≤ p) (hpo : p % 2 = 1) (hn : ¬ Prime p) (x : Nat) :
    C (p + 2) x = C p x := by
  rw [show p + 2 = (p + 1) + 1 by omega, C_composite (p + 1) (by omega) (not_prime_even p hp hpo),
    C_composite p hp hn]

theorem alive_even (p n : Nat) (hp : 3 ≤ p) (hn : 4 ≤ n) (he : n % 2 = 0) : ¬ Alive p n :=
  fun h => by have := alive_odd hp h; omega

theorem C_pc_skip (p : Nat) (hp : 3 ≤ p) (hpo : p % 2 = 1) (hn : ¬ Prime p) :
    C (p + 2) (p + 2 - 1) = C p (p - 1) := by
  rw [C_skip2 p hp hpo hn, show p + 2 - 1 = p + 1 by omega, C_succ, C_self p hp,
    if_neg (alive_even p (p + 1) hp (by omega) (by omega)), if_neg hn]
  rfl

theorem RL_skip (N p : Nat) (hp : 3 ≤ p) (hpo : p % 2 = 1) (hn : ¬ Prime p) :
    RL N (p + 2) = RL N p := by
  simp only [RL, show p + 2 = (p + 1) + 1 by omega, rough_skip' (by omega : 3 ≤ p + 1)
    (not_prime_even p hp hpo), rough_skip' hp hn]

/-- A composite `p ≤ v`: `skip[p]` is set and the loop moves on to `p + 2`. -/
theorem round_skip (N p : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h : Inv N p x mem) (hpv : p ≤ isqrt N) (hn : ¬ Prime p) :
    ∃ n y, run n ⟨x, bv 388, mem, [], out, .running⟩ = ⟨y, bv 388, mem, [], out, .running⟩ ∧
      Inv N (p + 2) y mem := by
  obtain ⟨hvb, hD⟩ := inv_bounds h
  have hsk := h.sk p (by omega)
  simp only [(skip_self_iff p h.hp3 h.hpo).mpr hn, ite_true] at hsk
  have := zext8
  have hmem := h.pre
  have hsz := h.size
  have h18 := h.x18; have h24 := h.x24; have h12 := h.x12
  refine ⟨7, ((((x.set 13 (bv p)).set 11 (bv (LD ((isqrt N + 1) / 2) + p))).set 15 1#64).set
    12 (bv (p + 2))).set 0 736#64, ?_, ?_⟩
  · gexec
  have g : ∀ r : Reg, r ∉ ([11, 12, 13, 15] : List Reg) →
      ((((((x.set 13 (bv p)).set 11 (bv (LD ((isqrt N + 1) / 2) + p))).set 15 1#64).set
        12 (bv (p + 2))).set 0 736#64).get r = x.get r) := by frame_tac
  have hRL := RL_skip N p h.hp3 h.hpo hn
  refine ⟨h.hN3, h.hN, by have := h.hp3; omega, by have := h.hpo; omega, ?_, by rw [g 8 (by decide), h.x8],
    by rw [g 9 (by decide), h.x9, hRL], by rw [g 18 (by decide), h.x18], by rw [g 19 (by decide), h.x19],
    by rw [g 20 (by decide), h.x20], by rw [g 21 (by decide), h.x21], by rw [g 22 (by decide), h.x22],
    by rw [g 23 (by decide), h.x23], by rw [g 24 (by decide), h.x24], by rw [g 25 (by decide), h.x25],
    by simp [Regs.get_set], by rw [g 14 (by decide), h.x14, C_pc_skip p h.hp3 h.hpo hn],
    by rw [g 10 (by decide), h.x10], by rw [g 2 (by decide), h.x2], h.size, h.pre, h.ra, ?_, ?_, ?_, ?_⟩
  · intro r h3 hr hpr
    by_cases hrp : r < p
    · exact h.hpr r h3 hrp hpr
    · by_cases hre : r = p
      · subst hre; exact absurd hpr hn
      · exact absurd hpr (by rw [show r = p + 1 by omega]; exact not_prime_even p h.hp3 h.hpo)
  · exact h.sm.ext (fun i _ => by rw [C_skip2 p h.hp3 h.hpo hn])
  · rw [hRL]; exact h.ro
  · rw [hRL]; exact h.la.ext (fun i _ => by rw [C_skip2 p h.hp3 h.hpo hn])
  · exact h.sk.ext (fun i _ => by
      simp only [show SkipMarked (p + 2) i ↔ SkipMarked p i from
        skip_step_composite p i h.hp3 h.hpo hn])

theorem p_small {N p : Nat} (hN : N < 100000000000) (hq : p * p * (p * p) ≤ N) : p ≤ 562 := by
  apply Decidable.byContradiction; intro h
  have h1 : 563 * 563 ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 563 * 563 * (563 * 563) ≤ p * p * (p * p) := Nat.mul_le_mul h1 h1
  omega

theorem C_pc_prime (p : Nat) (hp : 3 ≤ p) (hpo : p % 2 = 1) (hprime : Prime p) :
    C (p + 2) (p + 2 - 1) = C p (p - 1) + 1 := by
  rw [show p + 2 = (p + 1) + 1 by omega, C_composite (p + 1) (by omega) (not_prime_even p hp hpo),
    show p + 1 + 1 - 1 = p + 1 by omega, C_succ, if_neg (fun h => alive_even (p + 1) (p + 1) (by omega)
      (by omega) (by omega) h), C_small p p hp (by have := Nat.mul_le_mul_left p hp; omega),
    C_self p hp, if_pos hprime]

theorem RL_prime (N p : Nat) (hp : 3 ≤ p) (hpo : p % 2 = 1) (hpv : p ≤ isqrt N) :
    (RL N p).filter (fun d => d % p != 0) = RL N (p + 2) := by
  simp only [RL, List.filter_cons, show 1 % p = 1 by rw [Nat.mod_eq_of_lt (by omega)]]
  simp only [show ((1 != 0) = true) by decide, ite_true, List.cons.injEq, true_and]
  rw [show p + 2 = (p + 1) + 1 by omega, rough_skip' (by omega : 3 ≤ p + 1) (not_prime_even p hp hpo),
    rough_next hp hpv]

theorem round_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N v p D : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h18 : x.get 18 = bv v) (h24 : x.get 24 = bv D) (h12 : x.get 12 = bv p) (h19 : x.get 19 = bv N)
    (h10 : x.get 10 = bv 1)
    (hpv : p ≤ v) (hv : v < 316228) (hD : D + v + 1 ≤ 3000000) (hD' : 1248 ≤ D) (hp3 : 3 ≤ p)
    (hpp : p * p < 400000) (hN : N < 100000000000) (hq : p * p * (p * p) ≤ N)
    (hS : readBytes mem (D + p) 1 = some (BitVec.ofNat 8 0)) :
    ∃ y1, run 10 ⟨x, bv 388, mem, [], out, .running⟩ =
      ⟨y1, bv 668, wr mem (D + p) (bv 1) 1, [], out, .running⟩ ∧
      y1.get 15 = bv (p * p) ∧ y1.get 11 = bv (p * 2) ∧ y1.get 13 = bv p ∧
      (∀ r : Reg, r ∉ ([11, 13, 15, 16] : List Reg) → y1.get r = x.get r) := by
  have := zext8
  refine ⟨(((((x.set 13 (bv p)).set 11 (bv (D + p))).set 15 0#64).set 15
    (bv (p * p))).set 16 (bv (p * p * (p * p)))).set 11 (bv (p * 2)), ?_, by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec

theorem compact_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1236) :
    ∃ y, run 2 ⟨x, bv 676, mem, [], out, .running⟩ = ⟨y, bv 684, mem, [], out, .running⟩ ∧
      y.get 17 = bv 0 ∧ y.get 16 = bv 0 ∧
      (∀ r : Reg, r ∉ ([16, 17] : List Reg) → y.get r = x.get r) := by
  refine ⟨(x.set 17 0#64).set 16 0#64, ?_, by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec

theorem upd_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p : Nat)
    (hmem : Prefix image mem 1236)
    (h18 : x.get 18 = bv v) (h13 : x.get 13 = bv p) (h22 : x.get 22 = bv ((v - 1) / 2))
    (hpv : p ≤ v) (hv : v < 316228) (hp3 : 3 ≤ p)
    (hj : ((v / p - 1) / 2 * 2 + 1) * p ≤ v) :
    ∃ y, run 6 ⟨x, bv 692, mem, [], out, .running⟩ = ⟨y, bv 716, mem, [], out, .running⟩ ∧
      y.get 28 = bv ((v / p - 1) / 2 * 2 + 1) ∧ y.get 15 = bv (((v / p - 1) / 2 * 2 + 1) * p) ∧
      y.get 17 = bv ((v - 1) / 2) ∧
      (∀ r : Reg, r ∉ ([15, 17, 28] : List Reg) → y.get r = x.get r) := by
  have : 1 ≤ v / p := Nat.div_pos hpv (by omega)
  have := Nat.div_le_self v p
  refine ⟨(((((x.set 15 (bv (v / p))).set 17 (bv ((v - 1) / 2))).set 15 (bv (v / p - 1))).set 15
    (bv ((v / p - 1) / 2 * 2 + 1))).set 28 (bv ((v / p - 1) / 2 * 2 + 1))).set 15
    (bv (((v / p - 1) / 2 * 2 + 1) * p)), ?_, by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by frame_tac⟩
  gexec

theorem round_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (pc ns p : Nat)
    (hmem : Prefix image mem 1236)
    (h14 : x.get 14 = bv pc) (h16 : x.get 16 = bv ns) (h12 : x.get 12 = bv p)
    (hpc : pc < 1000) (hp : p < 1000) :
    ∃ y, run 4 ⟨x, bv 720, mem, [], out, .running⟩ = ⟨y, bv 388, mem, [], out, .running⟩ ∧
      y.get 14 = bv (pc + 1) ∧ y.get 9 = bv ns ∧ y.get 12 = bv (p + 2) ∧
      (∀ r : Reg, r ∉ ([9, 12, 14] : List Reg) → y.get r = x.get r) := by
  refine ⟨(((x.set 14 (bv (pc + 1))).set 9 (bv ns)).set 12 (bv (p + 2))).set 0 736#64, ?_,
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec

/-- A prime `p` with `p⁴ ≤ N`: one sieve round, back at 388 with `p + 2`. -/
theorem round_prime (N p : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h : Inv N p x mem) (hprime : Prime p) (hq : p * p * (p * p) ≤ N) :
    ∃ n y mem', run n ⟨x, bv 388, mem, [], out, .running⟩ = ⟨y, bv 388, mem', [], out, .running⟩ ∧
      Inv N (p + 2) y mem' := by
  obtain ⟨hvb, hDb⟩ := inv_bounds h
  have hp562 := p_small h.hN hq
  have hp3 := h.hp3
  have hpo := h.hpo
  have hppv : p * p ≤ isqrt N := le_isqrt hq
  have hpv : p ≤ isqrt N := Nat.le_trans (Nat.le_mul_of_pos_right p (by omega)) hppv
  have hlay := layout ((isqrt N + 1) / 2)
  have hLD : LD ((isqrt N + 1) / 2) = LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 := rfl
  have hLlen := RL_len N p hp3 (by omega)
  have hpc : C p (p - 1) ≤ p := Nat.le_trans (C_le p _) (by omega)
  -- 388 → 668: test skip[p], test p⁴ > N, set skip[p], a1 = 2p
  have hsk := h.sk p (by omega)
  dsimp only at hsk
  rw [if_neg (show ¬ SkipMarked p p from fun hs => (skip_self_iff p hp3 hpo).mp hs hprime)] at hsk
  have hpp : p * p < 400000 := by have := Nat.mul_le_mul (show p ≤ 562 by omega) (show p ≤ 562 by omega); omega
  obtain ⟨y1, hr1, hy15, hy11, hy13, g1⟩ := round_enter x mem out N (isqrt N) p
    (LD ((isqrt N + 1) / 2)) h.pre h.size h.x18 h.x24 h.x12 h.x19 h.x10 hpv (by omega) (by omega)
    (by omega) hp3 hpp h.hN hq hsk
  have hDp : LD ((isqrt N + 1) / 2) + p + 1 ≤ 4194304 := by omega
  -- the marking loop
  have hsk1 := (h.sk.wr (by rw [h.size]; omega) p 1 (by omega))
  obtain ⟨n2, y2, mem2, hr2, hsame2, hsk2, g2⟩ := mark_loop y1 _ out (LD ((isqrt N + 1) / 2)) (isqrt N) p (p * p)
    (upd (fun i => if SkipMarked p i then 1 else 0) p 1)
    (prefix_wr _ _ _ h.pre (by rw [h.size]; omega) (by omega)) (by simp [h.size]) hy15 hy11
    (by rw [g1 10 (by decide), h.x10]) (by rw [g1 24 (by decide), h.x24])
    (by rw [g1 18 (by decide), h.x18]) (by omega) (by omega) (by omega) hpo hpv
    (Nat.dvd_mul_right p p) (odd_mul hpo hpo) (Nat.le_refl _) (by omega)
    (hsk1.ext (fun i _ => by
      have : ¬ (p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < p * p) := fun h' => by omega
      simp only [this, ite_false]))
  have hskF : Arr8 mem2 (LD ((isqrt N + 1) / 2)) (isqrt N + 1) (fun i => if SkipMarked (p + 2) i then 1 else 0) :=
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
  have hpre2 : Prefix image mem2 1236 :=
    hsame2.prefix (prefix_wr _ _ _ h.pre (by rw [h.size]; omega) (by omega)) (by omega)
  have hsz2 : mem2.size = 4194304 := by rw [hsame2.size_eq, wr_size, h.size]
  have hs1 : Same mem mem2 (LD ((isqrt N + 1) / 2)) ((LD ((isqrt N + 1) / 2)) + (isqrt N + 1)) :=
    (Same.wr mem _ (bv 1) 1 (LD ((isqrt N + 1) / 2)) ((LD ((isqrt N + 1) / 2)) + (isqrt N + 1)) (by rw [h.size]; omega) (by omega) (by omega)).trans hsame2
  obtain ⟨y3, hr3, hy17, hy16, g3⟩ := compact_enter y2 mem2 out hpre2
  have f3 : ∀ r : Reg, r ∉ ([11, 13, 15, 16, 17] : List Reg) → y3.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3 r (by simp [hr]), g2 r (by simp [hr]), g1 r (by simp [hr])]
  have hcm := cmath N p h.hN hp3 hprime hppv
  have hlenb : (RL N p).length < 200000 := by omega
  obtain ⟨n4, y4, mem4, hr4, hsame4, hro4, hla4, hy4_16, g4⟩ := compact_loop (RL N p)
    (fun d => d % p != 0) (fun d => C p (N / d)) (fun d => C (p + 1) (N / d))
    (fun d => C p (N / d / p)) (fun i => C p (2 * i + 1))
    (fun i => if SkipMarked (p + 2) i then 1 else 0) 1248 (LB ((isqrt N + 1) / 2)) (LC ((isqrt N + 1) / 2)) (LD ((isqrt N + 1) / 2)) N (isqrt N) p (C p (p - 1))
    ((isqrt N + 1) / 2) hcm rfl hLlen (by omega) (by omega) (by rw [hLD]; exact Nat.le_refl _) y3 mem2 out 0 0
    (fun k => (RL N p).getD k 0) (fun k => C p (N / (RL N p).getD k 0))
    ⟨by rw [f3 9 (by decide), h.x9], by rw [f3 21 (by decide), h.x21], by rw [f3 24 (by decide), h.x24],
     by rw [f3 12 (by decide), h.x12], by rw [f3 8 (by decide), h.x8], by rw [f3 18 (by decide), h.x18],
     by rw [f3 20 (by decide), h.x20], by rw [f3 14 (by decide), h.x14], by rw [f3 19 (by decide), h.x19]⟩
    ⟨hlenb, by omega, hpv, h.hN, Nat.le_refl _, by omega, by omega, by omega, by omega, by omega⟩
    hpre2 hsz2 hy17 hy16 (Nat.zero_le _) (by simp)
    (hs1.arr32 h.ro (by omega)) (hs1.arr64 h.la (by omega)) (hs1.arr32 h.sm (by omega)) hskF
    (fun j d hj => by simp at hj)
    (fun j d _ hj => by simp [List.getD_eq_getElem?_getD, hj])
  have hpre4 : Prefix image mem4 1236 := hsame4.prefix hpre2 (by omega)
  have hsz4 : mem4.size = 4194304 := by rw [hsame4.size_eq, hsz2]
  have f4 : ∀ r : Reg, r ∉ ([5, 6, 11, 13, 15, 16, 17, 28, 29, 30] : List Reg) → y4.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g4 r (by simp [hr]), f3 r (by simp [hr])]
  have hy4_13 : y4.get 13 = bv p := by
    rw [g4 13 (by decide), g3 13 (by decide), g2 13 (by decide), hy13]
  have hy4_11 : y4.get 11 = bv (p * 2) := by
    rw [g4 11 (by decide), g3 11 (by decide), g2 11 (by decide), hy11]
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
  obtain ⟨y5, hr5, hy28, hy15', hy17', g5⟩ := upd_enter y4 mem4 out (isqrt N) p hpre4
    (by rw [f4 18 (by decide), h.x18]) hy4_13 (by rw [f4 22 (by decide), h.x22]) hpv (by omega) hp3
    hJv
  have hsm4 : Arr32 mem4 1248 ((isqrt N + 1) / 2) (fun i => C p (2 * i + 1)) :=
    hsame4.arr32 (hs1.arr32 h.sm (by omega)) (by omega)
  obtain ⟨n6, y6, mem6, hr6, hsame6, hsm6, g6⟩ := upd_loop y5 mem4 out 1248 (isqrt N)
    ((isqrt N + 1) / 2) p (C p (p - 1)) (fun i => C p (2 * i + 1)) (fun i => C (p + 1) (2 * i + 1))
    ((isqrt N / p - 1) / 2 * 2 + 1) ((isqrt N - 1) / 2) hpre4 hsz4 hy28 hy15' hy17'
    (by rw [g5 13 (by decide), hy4_13]) (by rw [g5 11 (by decide), hy4_11])
    (by rw [g5 20 (by decide), f4 20 (by decide), h.x20])
    (by rw [g5 14 (by decide), f4 14 (by decide), h.x14]) (by omega) (by omega) rfl (by omega) hp3 hpv hpo
    (by omega) hJv (by
      have : (isqrt N + 1) / 2 ≤ ((isqrt N / p - 1) / 2 * 2 + 1 + 2) * p / 2 := Nat.div_le_div_right hJ2
      omega) (by omega)
    (upd_math N p hp3 hprime hpo _) (fun u _ hu => upd_math0 p hp3 hpo u hu)
    (fun u _ => by have := C_le p (2 * u + 1); omega)
    (hsm4.ext (fun u hu => by simp [show ¬ (isqrt N - 1) / 2 < u by omega]))
  have hpre6 : Prefix image mem6 1236 := hsame6.prefix hpre4 (by omega)
  have f6 : ∀ r : Reg, r ∉ ([5, 6, 7, 11, 13, 15, 16, 17, 28, 29, 30, 31] : List Reg) →
      y6.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g6 r (by simp [hr]), g5 r (by simp [hr]), f4 r (by simp [hr])]
  have hRL := RL_prime N p hp3 hpo hpv
  obtain ⟨y7, hr7, hy7_14, hy7_9, hy7_12, g7⟩ := round_exit y6 mem6 out (C p (p - 1))
    ((RL N p).filter (fun d => d % p != 0)).length p hpre6
    (by rw [f6 14 (by decide), h.x14]) (by rw [g6 16 (by decide), g5 16 (by decide), hy4_16])
    (by rw [f6 12 (by decide), h.x12]) (by omega) (by omega)
  have f7 : ∀ r : Reg, r ∉ ([5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] : List Reg) →
      y7.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g7 r (by simp [hr]), f6 r (by simp [hr])]
  rw [hRL] at hro4 hla4 hy7_9
  refine ⟨10 + (n2 + (2 + (n4 + (6 + (n6 + 4))))), y7, mem6, ?_, ?_⟩
  · rw [run_add, hr1, run_add, hr2, run_add, hr3, run_add, hr4, run_add, hr5, run_add, hr6, hr7]
  refine ⟨h.hN3, h.hN, by omega, by omega, ?_, by rw [f7 8 (by decide), h.x8], hy7_9,
    by rw [f7 18 (by decide), h.x18], by rw [f7 19 (by decide), h.x19],
    by rw [f7 20 (by decide), h.x20], by rw [f7 21 (by decide), h.x21], by rw [f7 22 (by decide), h.x22],
    by rw [f7 23 (by decide), h.x23], by rw [f7 24 (by decide), h.x24], by rw [f7 25 (by decide), h.x25],
    hy7_12, by rw [hy7_14, C_pc_prime p hp3 hpo hprime], by rw [f7 10 (by decide), h.x10],
    by rw [f7 2 (by decide), h.x2], by rw [hsame6.size_eq, hsz4], hpre6, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h3 hr hpr
    by_cases hrp : r < p
    · exact h.hpr r h3 hrp hpr
    · by_cases hre : r = p
      · subst hre; exact hq
      · exact absurd hpr (by rw [show r = p + 1 by omega]; exact not_prime_even p hp3 hpo)
  · exact hsame6.read (hsame4.read (hs1.read h.ra (by omega)) (by omega)) (by omega)
  · exact hsm6.ext (fun i _ => by
      rw [show p + 2 = (p + 1) + 1 by omega, C_composite (p + 1) (by omega) (not_prime_even p hp3 hpo)])
  · have := RL_len N (p + 2) (by omega) (by omega)
    exact hsame6.arr32 hro4 (by omega)
  · have := RL_len N (p + 2) (by omega) (by omega)
    exact (hsame6.arr64 hla4 (by omega)).ext (fun i _ => by
      rw [show p + 2 = (p + 1) + 1 by omega, C_composite (p + 1) (by omega) (not_prime_even p hp3 hpo)])
  · exact hsame6.arr8 (hsame4.arr8 hskF (by omega)) (by omega)

end TinyFive.GrumpyBinary
