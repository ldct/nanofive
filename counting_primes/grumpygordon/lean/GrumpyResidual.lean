import GrumpyOdd

/-! The two sums left after stopping the rough-number sieve at `a⁴ > N`.
The proof telescopes the one-prime removal identity twice; the executable
sums only read the *frozen* stage, never construct another sieve stage. -/
namespace TinyFive.GrumpyGordon
open CountingPrimes LucyMath

/-- The specification of the compact tail of the roughs list at cutoff. -/
def primesFrom (a len : Nat) := (List.range' a len).filter (fun q => decide (Prime q))

/-- Sum weights in an increasing list, stopping at the first failed guard. -/
def prefixSum (keep : Nat → Bool) (f : Nat → Nat) (ps : List Nat) : Nat :=
  ((ps.takeWhile keep).map f).sum

/-- Above `a`, passing another sieve stage cannot affect entries below `a²`. -/
theorem frozen {a b x : Nat} (hab : a ≤ b) (hx : x < a*a) : C a x = C b x := by
  apply count_congr
  intro m _ hm
  by_cases h5 : 3 ≤ m
  · have hbb := Nat.mul_le_mul hab hab
    simp [Alive, h5, unmarked_iff_prime a m (by omega) (by omega),
      unmarked_iff_prime b m (by omega) (by omega)]
  · simp [Alive, h5]

/-- Telescope only the prime steps before `b` for which `p² ≤ x`. The list
may run beyond `b`; the inner correction uses exactly that early exit. -/
theorem telescope (a len b x : Nat) (ha : 3 ≤ a) (hb : b ≤ a + len)
    (weight : Nat → Nat)
    (hw : ∀ p, a ≤ p → p < b → Prime p → p*p ≤ x →
      weight p = C p (x/p) - C p (p-1)) :
    C a x = C (max a b) x + prefixSum (fun p => p < b && p*p ≤ x) weight (primesFrom a len) := by
  induction len generalizing a with
  | zero => simp [primesFrom, prefixSum, Nat.max_eq_left (by omega : b ≤ a)]
  | succ len ih =>
    rw [primesFrom, List.range'_succ]
    by_cases hp : Prime a
    · simp only [List.filter_cons, hp, decide_true, ↓reduceIte]
      by_cases h : a < b ∧ a*a ≤ x
      · have hd := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr h.2
        have hstep := C_prime_step a hp ha x hd
        have hi := ih (a+1) (by omega) (by omega) (fun p h1 => hw p (by omega))
        simp only [Nat.max_eq_right (by omega : a ≤ b), Nat.max_eq_right (by omega : a+1 ≤ b)] at *
        simp [prefixSum, h.1, h.2, primesFrom] at hi ⊢
        rw [hw a (by omega) h.1 hp h.2]; omega
      · have htest : (decide (a < b) && decide (a*a ≤ x)) = false := by simp; omega
        simp [prefixSum, htest]
        by_cases hab : a < b
        · exact frozen (Nat.le_max_left ..) (by omega)
        · rw [Nat.max_eq_left (by omega)]
    · simp only [List.filter_cons, hp, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hi := ih (a+1) (by omega) (by omega) (fun p h1 => hw p (by omega))
      rw [← C_composite a (by omega) hp x]
      by_cases hab : a < b
      · simpa [primesFrom, Nat.max_eq_right (by omega : a ≤ b), Nat.max_eq_right (by omega : a+1 ≤ b)] using hi
      · simpa [primesFrom, Nat.max_eq_left (by omega : b ≤ a), Nat.max_eq_left (by omega : b ≤ a+1), C_composite a (by omega) hp] using hi

/-- The over-subtraction for a larger rough prime `q`: among potential
cofactors of `q`, remove those with least prime factor `r < q`. -/
def triples (small : Nat → Nat) (ps : List Nat) (q m : Nat) : Nat :=
  prefixSum (fun r => r < q && r*r ≤ m) (fun r => small (m/r) - small (r-1)) ps

/-- Remove multiples of each remaining least prime, correcting their cofactor
counts for triples. `large q` is the frozen count at `N/q`. -/
def finish (N top : Nat) (small large : Nat → Nat) (ps : List Nat) : Nat :=
  large 1 - prefixSum (fun q => q < top+1 && q*q ≤ N)
    (fun q => large q - triples small ps q (N/q) - small (q-1)) ps + 1

theorem finish_correct (N a : Nat) (hN : 3 ≤ N) (ha : 3 ≤ a)
    (hcut : N < (a*a)*(a*a)) (small large : Nat → Nat)
    (hs : ∀ x, x ≤ isqrt N → small x = C a x)
    (h1 : large 1 = C a N)
    (hl : ∀ q, a ≤ q → q ≤ isqrt N → Prime q → large q = C a (N/q)) :
    finish N (isqrt N) small large (primesFrom a (isqrt N+1-a)) = countPrimes N := by
  let v := isqrt N
  have hv := isqrt_spec N
  change v*v ≤ N ∧ N < (v+1)*(v+1) at hv
  have hvlt : v < a*a := by
    apply Decidable.byContradiction
    intro h
    have hn : a*a ≤ v := by omega
    have : (a*a)*(a*a) ≤ v*v := Nat.mul_le_mul hn hn
    omega
  have htop : N < max a (v+1) * max a (v+1) := Nat.lt_of_lt_of_le hv.2
    (Nat.mul_le_mul (Nat.le_max_right ..) (Nat.le_max_right ..))
  rw [count_eq_C N (max a (v+1)) hN (by omega) htop]
  unfold finish
  rw [h1]
  apply congrArg (· + 1)
  apply Nat.sub_eq_of_eq_add
  apply telescope a (v+1-a) (v+1) N ha (by omega)
  intro q haq hq hp _
  have hqv : q ≤ v := by omega
  have hqs : C a (q-1) = C q (q-1) := frozen haq (by omega)
  rw [hl q haq hqv hp, hs _ (by omega), hqs]
  have ht : C a (N/q) = C q (N/q) + triples small (primesFrom a (v+1-a)) q (N/q) := by
    unfold triples
    -- Feed the same compact list to the inner sum, but stop strictly before q.
    have h := telescope a (v+1-a) q (N/q) ha (by omega) (fun r => small (N/q/r) - small (r-1))
    rw [Nat.max_eq_right haq] at h
    apply h
    intro r har hr _ _
    have hprod : a*a ≤ q*r := Nat.mul_le_mul haq har
    have hdiv : N/q/r ≤ v := by
      rw [Nat.div_div_eq_div_mul]
      apply Decidable.byContradiction
      intro hc
      have hn : v+1 ≤ N/(q*r) := by omega
      have hlarge := (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega : 0 < q) (by omega : 0 < r))).mp hn
      have := Nat.mul_le_mul_left (v+1) (show v+1 ≤ q*r by omega)
      omega
    rw [hs _ hdiv, hs _ (by omega), frozen har (by omega : N/q/r < a*a), frozen har (by omega : r-1 < a*a)]
  rw [ht, Nat.add_sub_cancel]

end TinyFive.GrumpyGordon
