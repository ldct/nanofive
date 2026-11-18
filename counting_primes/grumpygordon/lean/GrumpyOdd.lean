import LucyMath

/-! Adapting LucyMath's sieve (counts start at 5) to grumpygordon's
initial table of odd numbers starting at 3. -/
namespace TinyFive.GrumpyGordon
open CountingPrimes SieveMath LucyMath

def Alive (p n : Nat) : Prop := 3 ≤ n ∧ ¬ Marked p n
instance (p : Nat) : DecidablePred (Alive p) := fun _ => by unfold Alive; infer_instance

def C (p v : Nat) := count (Alive p) v

private theorem three_alive (p : Nat) : Alive p 3 := by
  refine ⟨by decide, fun ⟨d, h1, _, h2, h3⟩ => ?_⟩
  exact ((prime_iff_no_proper_divisor 3).mp (by decide)).2 d h1 h2 h3

/-- All stages already exclude 4; the sole difference from Lucy's count is 3. -/
theorem C_eq_S (p : Nat) (hp : 3 ≤ p) (x : Nat) : C p x = S p x + (if 3 ≤ x then 1 else 0) := by
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [C, S, count_succ, count_succ, ← C, ← S, ih]
    by_cases h : x+1 = 3
    · simp [three_alive, Surv, show x = 2 by omega]
    by_cases h5 : 5 ≤ x+1
    · have he : Alive p (x+1) ↔ Surv p (x+1) := by simp [Surv, Alive, h5, show 3 ≤ x+1 by omega]
      simp only [he, ite_eq_left (by omega : 3 ≤ x), ite_eq_left (by omega : 3 ≤ x+1)]; omega
    · have hs : ¬Surv p (x+1) := fun h => h5 h.1
      have ha : ¬Alive p (x+1) := by
        rintro ⟨h3, hm⟩
        have h4 : x+1 = 4 := by omega
        exact hm ⟨2, by omega, by omega, by omega, by omega⟩
      simp [hs, ha]; split <;> split <;> omega

/-- The source's exact odd initialization, no wheel or pre-peeled prime. -/
theorem C_init (x : Nat) : C 3 x = (x-1)/2 := by
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [C, count_succ, ← C, ih]
    have ha : Alive 3 (x+1) ↔ 3 ≤ x+1 ∧ (x+1)%2=1 := by
      constructor
      · rintro ⟨h,hm⟩; refine ⟨h, ?_⟩
        apply Decidable.byContradiction; intro hn
        exact hm ⟨2, by omega, by omega, by omega, by omega⟩
      · rintro ⟨h,ho⟩; refine ⟨h, fun ⟨d,h1,h2,_,hd⟩ => ?_⟩
        have : d = 2 := by omega
        subst d; omega
    simp only [ha]; split <;> omega

theorem C_self (p : Nat) (hp : 3 ≤ p) : C p p = C p (p-1) + if Prime p then 1 else 0 := by
  obtain ⟨q,rfl⟩ : ∃ q, p = q+1 := ⟨p-1, by omega⟩
  rw [C, count_succ]; simp [C, Alive, hp, marked_self_iff_not_prime (q+1) (by omega)]

theorem C_small (p x : Nat) (hp : 3 ≤ p) (hx : x < p*p) : C (p+1) x = C p x := by
  rw [C_eq_S _ (by omega), C_eq_S _ hp, S_small p (by omega) x hx]

theorem C_composite (p : Nat) (hp : 3 ≤ p) (hn : ¬ Prime p) (x : Nat) : C (p+1) x = C p x := by
  rw [C_eq_S _ (by omega), C_eq_S _ hp, S_composite p (by omega) hn]

theorem C_odd_index (p : Nat) (hp : 3 ≤ p) (x : Nat) (hx : 1 ≤ x) :
    C p (2*((x-1)/2)+1) = C p x := by
  rw [C_eq_S _ hp, C_eq_S _ hp, S_odd_index p hp _ hx]; split <;> split <;> omega

/-- One prime step on odd-counting tables, including the first step `p = 3`. -/
theorem C_prime_step (p : Nat) (hprime : Prime p) (hp : 3 ≤ p) (x : Nat) (hx : p ≤ x/p) :
    C p x = C (p+1) x + (C p (x/p) - C p (p-1)) := by
  have hxx := Nat.div_le_self x p
  by_cases h5 : 5 ≤ p
  · have h := S_prime_step p hprime h5 x hx
    simp [C_eq_S, hp, show 3 ≤ x by omega, show 3 ≤ p-1 by omega, show 3 ≤ x/p by omega,
      show 3 ≤ p+1 by omega, h]; omega
  · have h3 : p = 3 := by
      by_cases h : p = 4
      · subst p; exact False.elim ((by decide : ¬Prime 4) hprime)
      · omega
    subst p
    rw [C_init, C_eq_S _ (by decide), ← S_composite 4 (by decide) (by decide), S_init,
      C_init, C_init]
    split <;> omega

theorem count_eq_C (N p : Nat) (hN : 3 ≤ N) (hp : 3 ≤ p) (hx : N < p*p) : countPrimes N = C p N + 1 := by
  rw [countPrimes_eq N p hN hx, C_eq_S p hp, ite_eq_left hN]

end TinyFive.GrumpyGordon
