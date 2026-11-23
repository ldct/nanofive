import GrumpyBinary.FinishMath

/-! `π(n) < 2^32` for `n < 10^11`.

lpha returns `π(N)` as a `uint32_t`, so its output is right only because `π(10^11 - 1)`
(4118054813) is below `2^32`. No short certificate exists for an upper bound on `π`, so this file
computes `π(10^11 - 1)` with a Lucy_Hedgehog count, proves that count equal to `countPrimes`
(using `LucyMath.S`), and evaluates it once with `native_decide` (about 30 seconds). -/
namespace TinyFive.LphaBinary.PiBound
open CountingPrimes LucyMath

/-! ## The count -/

/-- `lg[k] -= S(N/k/p) - c` for `k = k0, ..., km`, reading `S(N/k/p)` from `lg[k*p]` or
`sm[N/(k*p)]`. -/
def lgLoop (N r p c km : Nat) (sm : Array Nat) (k : Nat) (lg : Array Nat) : Array Nat :=
  if k ≤ km then
    let d := if k * p ≤ r then lg[k * p]! else sm[N / (k * p)]!
    lgLoop N r p c km sm (k + 1) (lg.set! k (lg[k]! - (d - c)))
  else lg
termination_by km + 1 - k

/-- `sm[i] -= sm[i/p] - c` for `i = i0` down to `q`. -/
def smLoop (p c q : Nat) (i : Nat) (sm : Array Nat) : Array Nat :=
  if 1 ≤ q ∧ q ≤ i then smLoop p c q (i - 1) (sm.set! i (sm[i]! - (sm[i / p]! - c))) else sm
termination_by i

/-- The stages `p = p0, ..., r`; `p` is prime exactly when `sm[p] ≠ sm[p-1]`. -/
def outer (N r : Nat) (p : Nat) (sm lg : Array Nat) : Array Nat × Array Nat :=
  if p ≤ r then
    if sm[p]! ≠ sm[p - 1]! then
      let c := sm[p - 1]!
      let lg' := lgLoop N r p c (min r (N / (p * p))) sm 1 lg
      outer N r (p + 1) (smLoop p c (p * p) r sm) lg'
    else outer N r (p + 1) sm lg
  else (sm, lg)
termination_by r + 1 - p

def lucy (N : Nat) : Nat :=
  let r := isqrt N
  let sm := Array.ofFn (n := r + 1) fun i => (i.1 - 1) / 2 * 2 / 3
  let lg := Array.ofFn (n := r + 1) fun k => (N / k.1 - 1) / 2 * 2 / 3
  (outer N r 5 sm lg).2[1]! + 2

/-! ## It counts the primes -/

theorem get_set (a : Array Nat) (i j v : Nat) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by grind

theorem size_set (a : Array Nat) (i v : Nat) : (a.set! i v).size = a.size := by simp

theorem lgLoop_spec (N r p c km : Nat) (sm : Array Nat) (k : Nat) (lg : Array Nat)
    (hr : r * r ≤ N) (hr' : N < (r + 1) * (r + 1)) (hp : Prime p) (h5 : 5 ≤ p)
    (hkm : km ≤ r) (hkm' : km * (p * p) ≤ N) (hk1 : 1 ≤ k)
    (hc : c = S p (p - 1)) (hsms : sm.size = r + 1) (hsz : lg.size = r + 1)
    (hsm : ∀ i, i ≤ r → sm[i]! = S p i)
    (hlg : ∀ j, 1 ≤ j → j ≤ r → lg[j]! = if j < k then S (p + 1) (N / j) else S p (N / j)) :
    (lgLoop N r p c km sm k lg).size = r + 1 ∧
    ∀ j, 1 ≤ j → j ≤ r → (lgLoop N r p c km sm k lg)[j]! =
      if j < max k (km + 1) then S (p + 1) (N / j) else S p (N / j) := by
  unfold lgLoop
  split
  · rename_i hk
    have hp2 : 2 ≤ p := by omega
    have hkp : k < k * p := by
      have := Nat.mul_le_mul_left k hp2; omega
    have hkr : k ≤ r := by omega
    -- the value read for `S p (N / k / p)`
    have hd : (if k * p ≤ r then lg[k * p]! else sm[N / (k * p)]!) = S p (N / k / p) := by
      rw [Nat.div_div_eq_div_mul]
      split
      · rw [hlg (k * p) (by omega) (by assumption), if_neg (by omega)]
      · rename_i hkpr
        apply hsm
        apply Nat.le_of_lt_succ
        apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
        have := Nat.mul_le_mul_left (r + 1) (show r + 1 ≤ k * p by omega)
        simp only [Nat.succ_eq_add_one]; omega
    have hle : k * (p * p) ≤ N := Nat.le_trans (Nat.mul_le_mul_right _ hk) hkm'
    have hv : p ≤ N / k / p := by
      rw [Nat.div_div_eq_div_mul]
      apply (Nat.le_div_iff_mul_le (by have := Nat.mul_le_mul hk1 (Nat.le_refl p); omega)).mpr
      rw [show p * (k * p) = k * (p * p) by rw [Nat.mul_comm, Nat.mul_assoc]]; exact hle
    have hstep := S_prime_step p hp h5 (N / k) hv
    obtain ⟨h1, h2⟩ := lgLoop_spec N r p c km sm (k + 1)
      (lg.set! k (lg[k]! - ((if k * p ≤ r then lg[k * p]! else sm[N / (k * p)]!) - c))) hr hr' hp h5 hkm hkm' (by omega) hc hsms
      (by rw [size_set, hsz])
      hsm (fun j hj1 hjr => by
        rw [get_set, hd]
        by_cases hjk : j = k
        · subst hjk
          rw [if_pos ⟨rfl, by omega⟩, if_pos (by omega), hlg j hj1 hjr, if_neg (by omega), hc]
          omega
        · rw [if_neg (by omega), hlg j hj1 hjr]
          by_cases hjk' : j < k
          · rw [if_pos hjk', if_pos (by omega)]
          · rw [if_neg hjk', if_neg (by omega)])
    refine ⟨h1, fun j hj1 hjr => ?_⟩
    have hmx : max (k + 1) (km + 1) = max k (km + 1) := by
      simp only [Nat.max_def]; split <;> split <;> omega
    rw [h2 j hj1 hjr, hmx]
  · rename_i hk
    refine ⟨hsz, fun j hj1 hjr => ?_⟩
    rw [hlg j hj1 hjr]
    by_cases hjk : j < k
    · rw [if_pos hjk, if_pos (by omega)]
    · rw [if_neg hjk]
      by_cases hjm : j < km + 1
      · omega
      · rw [if_neg (by simp only [Nat.max_def]; split <;> omega)]
termination_by km + 1 - k

theorem smLoop_spec (r p c : Nat) (i : Nat) (sm : Array Nat) (hp : Prime p) (h5 : 5 ≤ p)
    (hc : c = S p (p - 1)) (hir : i ≤ r) (hsz : sm.size = r + 1)
    (hsm : ∀ j, j ≤ r → sm[j]! = if i < j then S (p + 1) j else S p j) :
    (smLoop p c (p * p) i sm).size = r + 1 ∧
    ∀ j, j ≤ r → (smLoop p c (p * p) i sm)[j]! = S (p + 1) j := by
  unfold smLoop
  split
  · rename_i hq
    have hpp : 25 ≤ p * p := Nat.mul_le_mul h5 h5
    have hip : i / p < i := Nat.div_lt_self (by omega) (by omega)
    have hv : p ≤ i / p := (Nat.le_div_iff_mul_le (by omega)).mpr hq.2
    have hstep := S_prime_step p hp h5 i hv
    obtain ⟨h1, h2⟩ := smLoop_spec r p c (i - 1) (sm.set! i (sm[i]! - (sm[i / p]! - c))) hp h5 hc
      (by omega) (by rw [size_set, hsz]) (fun j hjr => by
        rw [get_set]
        by_cases hji : j = i
        · subst hji
          rw [if_pos ⟨rfl, by omega⟩, if_pos (by omega), hsm j hjr, if_neg (by omega),
            hsm (j / p) (by omega), if_neg (by omega), hc]
          omega
        · rw [if_neg (by omega), hsm j hjr]
          by_cases hij : i < j
          · rw [if_pos hij, if_pos (by omega)]
          · rw [if_neg hij, if_neg (by omega)])
    exact ⟨h1, h2⟩
  · rename_i hq
    have hpp : 25 ≤ p * p := Nat.mul_le_mul h5 h5
    refine ⟨hsz, fun j hjr => ?_⟩
    rw [hsm j hjr]
    by_cases hij : i < j
    · rw [if_pos hij]
    · rw [if_neg hij, S_small p (by omega) j (by omega)]
termination_by i

theorem outer_spec (N r p : Nat) (sm lg : Array Nat) (hr : r * r ≤ N) (hr' : N < (r + 1) * (r + 1))
    (h5 : 5 ≤ p) (hsms : sm.size = r + 1) (hsz : lg.size = r + 1)
    (hsm : ∀ i, i ≤ r → sm[i]! = S p i) (hlg : ∀ k, 1 ≤ k → k ≤ r → lg[k]! = S p (N / k)) :
    ∃ P, r < P ∧ ∀ k, 1 ≤ k → k ≤ r → (outer N r p sm lg).2[k]! = S P (N / k) := by
  unfold outer
  split
  · rename_i hpr
    have hself := S_self p h5
    rw [← hsm p hpr, ← hsm (p - 1) (by omega)] at hself
    split
    · rename_i hne
      have hp : Prime p := by
        apply Decidable.byContradiction; intro hnp; rw [if_neg hnp] at hself; omega
      have hpp : 25 ≤ p * p := Nat.mul_le_mul h5 h5
      have hkm : min r (N / (p * p)) * (p * p) ≤ N :=
        Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_right _ _)) (Nat.div_mul_le_self N _)
      obtain ⟨l1, l2⟩ := lgLoop_spec N r p (sm[p - 1]!) (min r (N / (p * p))) sm 1 lg hr hr' hp h5
        (Nat.min_le_left _ _) hkm (Nat.le_refl 1) (hsm (p - 1) (by omega)) hsms hsz hsm
        (fun j hj1 hjr => by rw [hlg j hj1 hjr, if_neg (by omega)])
      obtain ⟨s1, s2⟩ := smLoop_spec r p (sm[p - 1]!) r sm hp h5 (hsm (p - 1) (by omega))
        (Nat.le_refl r) hsms (fun j hjr => by rw [hsm j hjr, if_neg (by omega)])
      exact outer_spec N r (p + 1) _ _ hr hr' (by omega) s1 l1 s2 (fun k hk1 hkr => by
        rw [l2 k hk1 hkr]
        split
        · rfl
        · rename_i hk
          have hm : min r (N / (p * p)) < k := by simp only [Nat.max_def] at hk; split at hk <;> omega
          have : N / (p * p) < k := by simp only [Nat.min_def] at hm; split at hm <;> omega
          rw [S_small p (by omega) _ (div_lt_sq (by omega) this)])
    · rename_i heq
      have hnp : ¬ Prime p := by
        intro hp; rw [if_pos hp] at hself; omega
      exact outer_spec N r (p + 1) sm lg hr hr' (by omega) hsms hsz
        (fun i hi => by rw [hsm i hi, S_composite p (by omega) hnp])
        (fun k hk1 hkr => by rw [hlg k hk1 hkr, S_composite p (by omega) hnp])
  · rename_i hpr
    exact ⟨p, by omega, hlg⟩
termination_by r + 1 - p

theorem ofFn_get (n : Nat) (f : Fin n → Nat) (i : Nat) (h : i < n) : (Array.ofFn f)[i]! = f ⟨i, h⟩ := by
  have h' : i < (Array.ofFn f).size := by simpa using h
  rw [getElem!_pos (Array.ofFn f) i h', Array.getElem_ofFn]

theorem lucy_eq (N : Nat) (hN : 3 ≤ N) : lucy N = countPrimes N := by
  obtain ⟨hr, hr'⟩ := isqrt_spec N
  have hr1 : 1 ≤ isqrt N := le_isqrt (by omega)
  obtain ⟨P, hP, hval⟩ := outer_spec N (isqrt N) 5
    (Array.ofFn (n := isqrt N + 1) fun i => (i.1 - 1) / 2 * 2 / 3)
    (Array.ofFn (n := isqrt N + 1) fun k => (N / k.1 - 1) / 2 * 2 / 3) hr hr' (Nat.le_refl 5)
    (by simp) (by simp)
    (fun i hi => by rw [ofFn_get _ _ i (by omega), S_init])
    (fun k hk1 hkr => by rw [ofFn_get _ _ k (by omega), S_init])
  have hPP : N < P * P := Nat.lt_of_lt_of_le hr' (Nat.mul_le_mul hP hP)
  simp only [lucy]
  rw [hval 1 (Nat.le_refl 1) hr1, Nat.div_one, countPrimes_eq N P hN hPP]

theorem lucy_val : lucy (10 ^ 11 - 1) = 4118054813 := by native_decide

/-- `π(n) < 2^32` below `10^11`. -/
theorem countPrimes_lt (n : Nat) (hn : n < 10 ^ 11) : countPrimes n < 2 ^ 32 := by
  have h1 := GrumpyBinary.countPrimes_mono (show n ≤ 10 ^ 11 - 1 by omega)
  rw [← lucy_eq (10 ^ 11 - 1) (by decide), lucy_val] at h1
  omega

end TinyFive.LphaBinary.PiBound
