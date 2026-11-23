import GrumpyBinary.FinishMath
import LphaBinary.Bertrand

/-! lpha computes `k2_max = smalls[half(N/p/p)] - pc` in 32-bit unsigned arithmetic and then
zero-extends it, so the triple loop is right only if that subtraction never wraps: every row the
loop reaches has `smalls(N / q_l^2) ≥ pc`. This file proves it from the row before (which went on,
so `q_l q_{l-1}^2 ≤ N`), Bertrand's postulate, and `P^4 ≤ N` for the last sieving prime `P`. -/
namespace TinyFive.LphaBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon GrumpyBinary

/-- `C a` does not grow across a stretch below `a` with no primes. -/
theorem C_gap (a X : Nat) : ∀ d, X + d < a → (∀ t, X < t → t ≤ X + d → ¬ Prime t) →
    C a (X + d) = C a X := by
  intro d
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro hY hg
    rw [show X + (d + 1) = (X + d) + 1 by omega, C_succ, ih (by omega) (fun t h1 h2 => hg t h1 (by omega))]
    have hna : ¬ Alive a (X + d + 1) := by
      rintro ⟨h3, hm⟩
      have hnp := hg (X + d + 1) (by omega) (by omega)
      rw [prime_iff_no_proper_divisor] at hnp
      apply hm
      apply Decidable.byContradiction; intro hnm
      apply hnp
      refine ⟨by omega, fun e he2 he hdvd => hnm ⟨e, he2, by omega, he, hdvd⟩⟩
    rw [if_neg hna, Nat.add_zero]

/-- A prime `t ≥ 3` is counted by `C a`. -/
theorem C_prime_succ (a t : Nat) (ht : Prime t) (h3 : 3 ≤ t) : C a t = C a (t - 1) + 1 := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [C_succ, Nat.add_sub_cancel]
  have : Alive a (u + 1) := by
    refine ⟨h3, fun ⟨d, hd2, _, hdn, hdvd⟩ => ?_⟩
    exact ((prime_iff_no_proper_divisor _).mp ht).2 d hd2 hdn hdvd
  rw [if_pos this]

/-- The largest prime below `a`. -/
theorem last_prime : ∀ a, 3 < a → ∃ P, 3 ≤ P ∧ P < a ∧ Prime P ∧ ∀ t, P < t → t < a → ¬ Prime t := by
  intro a
  induction a with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    by_cases hn : 3 ≤ n ∧ Prime n
    · exact ⟨n, hn.1, by omega, hn.2, fun t h1 h2 => by omega⟩
    · have h3 : 3 < n := by
        apply Decidable.byContradiction; intro hc
        apply hn; obtain rfl : n = 3 := by omega
        exact ⟨Nat.le_refl 3, by decide⟩
      obtain ⟨P, h1, h2, h4, h5⟩ := ih h3
      refine ⟨P, h1, by omega, h4, fun t ht1 ht2 => ?_⟩
      by_cases htn : t = n
      · subst htn; exact fun hp => hn ⟨by omega, hp⟩
      · exact h5 t ht1 (by omega)

/-- One case of a small last sieving prime `P`, row `q` after row `q'`. -/
def Row (P q' q : Nat) : Prop := 3 ≤ P → Prime P → Prime q' → P < q' → q' < 2 * P →
    Prime q → q' < q → q ≤ 2 * q' → (∀ t < 64, q' < t → t < q → ¬ Prime t) →
    P * q * q ≤ q * q' * q' ∨ P * q * q ≤ P * P * (P * P)

instance (P q' q : Nat) : Decidable (Row P q' q) := by unfold Row; infer_instance

/-- The cases with a small last sieving prime. -/
theorem small_rows : ∀ P < 16, ∀ q' < 32, ∀ q < 64, Row P q' q := by
  decide +kernel

/-- The next row number `q` after `q'` (both roughs, `q'` of rank `pc + j`) is at most `2 q'`, and
no prime lies between them. -/
theorem next_rough {N a : Nat} (hc : Cut N a) (q' j : Nat) (hq'3 : 3 ≤ q') (hq' : q' < 159389)
    (hq'p : Prime q') (hrank : C a q' = C a (a - 1) + j)
    (hj1 : 1 ≤ j + 1) (hj : j + 1 < (RL N a).length) :
    qq N a (j + 1) ≤ 2 * q' ∧ ∀ t, q' < t → t < qq N a (j + 1) → ¬ Prime t := by
  obtain ⟨_, hqv, _⟩ := hc.qq_range (j + 1) hj1 hj
  have key : ∀ t, q' < t → t ≤ isqrt N → Prime t → qq N a (j + 1) ≤ t := by
    intro t h1 h2 ht
    apply (qq_le_iff N a (j + 1) t hc.ha hj1 hj).mpr
    rw [C_prime_succ a t ht (by omega)]
    have := C_mono a (show q' ≤ t - 1 by omega)
    omega
  refine ⟨?_, fun t h1 h2 ht => ?_⟩
  · obtain ⟨t, ht, h1, h2⟩ := bertrand q' hq'3 hq'
    by_cases htv : t ≤ isqrt N
    · exact Nat.le_trans (key t h1 htv ht) h2
    · omega
  · have := key t h1 (by omega) ht
    omega

theorem mul3_le {a b c d e f : Nat} (h1 : a ≤ d) (h2 : b ≤ e) (h3 : c ≤ f) : a * b * c ≤ d * e * f :=
  Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

/-- No wrap: each row the triple loop reaches has `smalls(N / q_l^2) ≥ pc`. -/
theorem nowrap {N a : Nat} (hc : Cut N a)
    (hpr : ∀ r, 3 ≤ r → r < a → Prime r → r * r * (r * r) ≤ N) (l : Nat) (hl1 : 1 ≤ l)
    (hl : l < (RL N a).length)
    (hprev : l = 1 ∨ C a (a - 1) + l ≤ C a (N / qq N a (l - 1) / qq N a (l - 1))) :
    C a (a - 1) ≤ C a (N / qq N a l / qq N a l) := by
  have ha := hc.ha
  have hN := hc.hN
  obtain ⟨hal, hlv, hlp⟩ := hc.qq_range l hl1 hl
  rcases Nat.lt_or_ge a 4 with ha3 | ha3
  · have : C a (a - 1) = 0 := by
      obtain rfl : a = 3 := by omega
      rw [C_init]
    omega
  obtain ⟨P, hP3, hPa, hPp, hPg⟩ := last_prime a (by omega)
  have hP4 := hpr P hP3 hPa hPp
  -- `C a (a - 1) = C a P`
  have hCP : C a (a - 1) = C a P := by
    have := C_gap a P (a - 1 - P) (by omega) (fun t h1 h2 => hPg t h1 (by omega))
    rwa [show P + (a - 1 - P) = a - 1 by omega] at this
  -- it suffices that `P q^2 ≤ N`
  suffices hs : P * qq N a l * qq N a l ≤ N by
    rw [hCP]
    apply C_mono
    rw [Nat.div_div_eq_div_mul]
    apply (Nat.le_div_iff_mul_le (by
      have := Nat.mul_le_mul (show 1 ≤ qq N a l by omega) (show 1 ≤ qq N a l by omega); omega)).mpr
    rw [← Nat.mul_assoc]; exact hs
  have hPb : P < 600 := by
    apply Decidable.byContradiction; intro hc'
    have := mul3_le (show 600 ≤ P by omega) (show 600 ≤ P by omega) (show 600 ≤ P by omega)
    have := Nat.mul_le_mul this (show 600 ≤ P by omega)
    rw [show P * P * P * P = P * P * (P * P) by simp only [Nat.mul_assoc]] at this
    omega
  rcases Nat.lt_or_ge l 2 with hl2 | hl2
  · -- row 1: `q_1 ≤ 2P`, the next prime after `P`
    obtain rfl : l = 1 := by omega
    have hP1 : C a P = C a (a - 1) + 0 := by omega
    obtain ⟨hq1, _⟩ := next_rough hc P 0 hP3 (by omega) hPp hP1 (by omega) hl
    simp only [Nat.zero_add] at hq1
    have hq1o : qq N a 1 ≠ 2 * P := by
      intro h; rw [h] at hlp
      exact ((prime_iff_no_proper_divisor _).mp hlp).2 2 (by omega) (by omega) ⟨P, rfl⟩
    have hqq : qq N a 1 * qq N a 1 ≤ P * P * P := by
      rcases Nat.lt_or_ge P 4 with hP | hP
      · obtain rfl : P = 3 := by omega
        have := Nat.mul_le_mul (show qq N a 1 ≤ 5 by omega) (show qq N a 1 ≤ 5 by omega); omega
      · have h1 := Nat.mul_le_mul hq1 hq1
        have h2 := Nat.mul_le_mul_right (P * P) hP
        have : 2 * P * (2 * P) = 4 * (P * P) := by
          simp only [Nat.mul_assoc, Nat.mul_comm P 2, Nat.mul_left_comm P 2]; omega
        rw [Nat.mul_assoc]
        omega
    have := Nat.mul_le_mul_left P hqq
    rw [← Nat.mul_assoc] at this
    rw [show P * (P * P * P) = P * P * (P * P) by simp only [Nat.mul_assoc]] at this
    omega
  · -- row `l ≥ 2`: `q_l q'^2 ≤ N` with `q' = q_{l-1}`, and `q_l ≤ 2 q'`
    rcases hprev with h | hprev
    · omega
    obtain ⟨hal', hlv', hlp'⟩ := hc.qq_range (l - 1) (by omega) (by omega)
    have hlt := qq_lt N a (l - 1) l ha (by omega) hl
    have hle := (qq_le_iff N a l _ ha hl1 hl).mpr hprev
    have hq'0 : 1 ≤ qq N a (l - 1) := by omega
    have h3 : qq N a l * qq N a (l - 1) * qq N a (l - 1) ≤ N := by
      have := (Nat.le_div_iff_mul_le hq'0).mp hle
      exact (Nat.le_div_iff_mul_le hq'0).mp this
    have hq'b : qq N a (l - 1) < 4642 := by
      apply Decidable.byContradiction; intro hc'
      have := mul3_le (show 4642 ≤ qq N a l by omega) (show 4642 ≤ qq N a (l - 1) by omega)
        (show 4642 ≤ qq N a (l - 1) by omega)
      omega
    have hrank := qq_rank N a (l - 1) ha (by omega) (by omega)
    obtain ⟨hq2, hgap⟩ := next_rough hc (qq N a (l - 1)) (l - 1) (by omega) (by omega) hlp' hrank
      (by omega) (by rw [show l - 1 + 1 = l by omega]; exact hl)
    rw [show l - 1 + 1 = l by omega] at hq2 hgap
    rcases Nat.lt_or_ge (qq N a (l - 1)) (2 * P) with hsm | hbig
    · rcases Nat.lt_or_ge P 16 with hP16 | hP16
      · rcases small_rows P hP16 (qq N a (l - 1)) (by omega) (qq N a l) (by omega) hP3 hPp hlp'
          (by omega) hsm hlp hlt hq2 (fun t _ h1 h2 => hgap t h1 h2) with h | h <;> omega
      · have h1 := Nat.mul_le_mul (show qq N a l ≤ 4 * P by omega) (show qq N a l ≤ 4 * P by omega)
        have h2 := Nat.mul_le_mul_right (P * P) hP16
        have : 4 * P * (4 * P) = 16 * (P * P) := by
          simp only [Nat.mul_assoc, Nat.mul_comm P 4, Nat.mul_left_comm P 4]; omega
        have h4 := Nat.mul_le_mul_left P (show qq N a l * qq N a l ≤ P * (P * P) by omega)
        rw [← Nat.mul_assoc] at h4
        rw [show P * (P * (P * P)) = P * P * (P * P) by simp only [Nat.mul_assoc]] at h4
        omega
    · -- `P q_l ≤ 2P q' ≤ q'^2`
      have h1 : P * qq N a l ≤ qq N a (l - 1) * qq N a (l - 1) := by
        have := Nat.mul_le_mul_left P hq2
        have h2 := Nat.mul_le_mul_right (qq N a (l - 1)) hbig
        rw [show P * (2 * qq N a (l - 1)) = 2 * P * qq N a (l - 1) by
          simp only [Nat.mul_assoc, Nat.mul_left_comm P 2]] at this
        omega
      have := Nat.mul_le_mul_right (qq N a l) h1
      rw [show qq N a (l - 1) * qq N a (l - 1) * qq N a l = qq N a l * qq N a (l - 1) * qq N a (l - 1) by
        simp only [Nat.mul_comm, Nat.mul_left_comm]] at this
      omega

end TinyFive.LphaBinary
