import GrumpyBinary.Finish
import GrumpyGordon

/-! The arithmetic of the finish: the binary's smaller-prime-first triple correction, with its
early break and its triangular term, is the larger-prime-first regrouping in `finish`, so the
value it returns is `countPrimes N`. -/
namespace TinyFive.GrumpyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon

/-! ## Integer sums over index ranges -/

/-- `f a + ... + f (b-1)`. -/
def isum (f : Nat → Int) (a b : Nat) : Int := ((List.range' a (b - a)).map f).sum

theorem isum_succ (f : Nat → Int) (a b : Nat) (h : a < b) : isum f a b = f a + isum f (a + 1) b := by
  simp only [isum]; rw [show b - a = (b - (a + 1)) + 1 by omega, List.range'_succ]; simp

theorem isum_self (f : Nat → Int) (a b : Nat) (h : b ≤ a) : isum f a b = 0 := by
  simp [isum, show b - a = 0 by omega]

theorem isum_congr {f g : Nat → Int} {a b : Nat} (h : ∀ k, a ≤ k → k < b → f k = g k) :
    isum f a b = isum g a b := by
  by_cases hab : a < b
  · rw [isum_succ f a b hab, isum_succ g a b hab, h a (Nat.le_refl a) hab,
      isum_congr (fun k h1 h2 => h k (by omega) h2)]
  · rw [isum_self f a b (by omega), isum_self g a b (by omega)]
termination_by b - a

theorem isum_zero (a b : Nat) : isum (fun _ => 0) a b = 0 := by
  by_cases hab : a < b
  · rw [isum_succ _ a b hab, isum_zero (a + 1) b]; rfl
  · exact isum_self _ a b (by omega)
termination_by b - a

theorem isum_add (f g : Nat → Int) (a b : Nat) :
    isum (fun k => f k + g k) a b = isum f a b + isum g a b := by
  by_cases hab : a < b
  · rw [isum_succ _ a b hab, isum_succ f a b hab, isum_succ g a b hab, isum_add f g (a + 1) b]; omega
  · simp [isum_self _ a b (by omega)]
termination_by b - a

theorem isum_sub (f g : Nat → Int) (a b : Nat) :
    isum (fun k => f k - g k) a b = isum f a b - isum g a b := by
  by_cases hab : a < b
  · rw [isum_succ _ a b hab, isum_succ f a b hab, isum_succ g a b hab, isum_sub f g (a + 1) b]; omega
  · simp [isum_self _ a b (by omega)]
termination_by b - a

theorem isum_const (c : Int) (a b : Nat) : isum (fun _ => c) a b = ((b - a : Nat) : Int) * c := by
  by_cases hab : a < b
  · rw [isum_succ _ a b hab, isum_const c (a + 1) b, show b - a = (b - (a + 1)) + 1 by omega]
    push_cast; grind
  · simp [isum_self _ a b (by omega), show b - a = 0 by omega]
termination_by b - a

theorem isum_split (f : Nat → Int) (a c b : Nat) (h1 : a ≤ c) (h2 : c ≤ b) :
    isum f a b = isum f a c + isum f c b := by
  by_cases hac : a < c
  · rw [isum_succ f a b (by omega), isum_succ f a c hac, isum_split f (a + 1) c b (by omega) h2]; omega
  · obtain rfl : a = c := by omega
    rw [isum_self f a a (Nat.le_refl a)]; omega
termination_by c - a

/-- Sum of a function vanishing outside `[c, d)`. -/
theorem isum_window (f : Nat → Int) (a c d b : Nat) (h1 : a ≤ c) (h2 : c ≤ d) (h3 : d ≤ b)
    (g : Nat → Int) (hg : ∀ k, a ≤ k → k < b → g k = if c ≤ k ∧ k < d then f k else 0) :
    isum g a b = isum f c d := by
  rw [isum_split g a c b h1 (by omega), isum_split g c d b h2 h3,
    isum_congr (f := g) (g := fun _ => 0) (fun k h h' => by rw [hg k h (by omega)]; simp; omega),
    isum_congr (f := g) (g := f) (a := c) (b := d) (fun k h h' => by rw [hg k (by omega) (by omega)]; simp; omega),
    isum_congr (f := g) (g := fun _ => 0) (a := d) (b := b) (fun k h h' => by rw [hg k (by omega) h']; simp; omega),
    isum_zero, isum_zero]
  omega

theorem isum_swap (F : Nat → Nat → Int) (a b c d : Nat) :
    isum (fun k => isum (fun l => F l k) c d) a b = isum (fun l => isum (fun k => F l k) a b) c d := by
  by_cases hab : a < b
  · rw [isum_succ _ a b hab, isum_swap F (a + 1) b c d,
      isum_congr (f := fun l => isum (fun k => F l k) a b)
        (g := fun l => F l a + isum (fun k => F l k) (a + 1) b) (fun l _ _ => isum_succ _ a b hab),
      isum_add]
  · rw [isum_self _ a b (by omega),
      isum_congr (f := fun l => isum (fun k => F l k) a b) (g := fun _ => 0)
        (fun l _ _ => isum_self _ a b (by omega)), isum_zero]
termination_by b - a

theorem sumR_cast (f : Nat → Nat) (a b : Nat) : ((sumR f a b : Nat) : Int) = isum (fun k => (f k : Int)) a b := by
  by_cases hab : a < b
  · rw [sumR_succ f a b hab, isum_succ _ a b hab, ← sumR_cast f (a + 1) b]; push_cast; rfl
  · rw [sumR_self f a b (by omega), isum_self _ a b (by omega)]; rfl
termination_by b - a

/-- The triangular term is `Σ_{k=1}^{s-1} (pc + k - 1)`. -/
theorem tri_succ (s pc : Nat) (hs : 1 ≤ s) : tri (s + 1) pc = tri s pc + (pc + s - 1) := by
  have h2 : 2 * tri (s + 1) pc = 2 * tri s pc + 2 * (pc + s - 1) := by
    simp only [tri]
    have e1 : (s + 1 + 2 * pc - 2) * (s + 1 - 1) % 2 = 0 := by
      rw [Nat.mul_mod]; rcases Nat.mod_two_eq_zero_or_one (s + 1 - 1) with h | h <;>
        rcases Nat.mod_two_eq_zero_or_one (s + 1 + 2 * pc - 2) with h' | h' <;> simp [h, h'] <;> omega
    have e2 : (s + 2 * pc - 2) * (s - 1) % 2 = 0 := by
      rw [Nat.mul_mod]; rcases Nat.mod_two_eq_zero_or_one (s - 1) with h | h <;>
        rcases Nat.mod_two_eq_zero_or_one (s + 2 * pc - 2) with h' | h' <;> simp [h, h'] <;> omega
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero e1), Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero e2)]
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rcases Nat.eq_zero_or_pos pc with h0 | h0
    · subst h0
      rcases t with _ | t
      · simp
      · simp only [show t + 1 + 1 + 1 + 2 * 0 - 2 = t + 1 by omega,
          show t + 1 + 1 + 2 * 0 - 2 = t by omega, show t + 1 + 1 + 1 - 1 = t + 2 by omega,
          show t + 1 + 1 - 1 = t + 1 by omega, show 0 + (t + 1 + 1) - 1 = t + 1 by omega]; grind
    · obtain ⟨u, rfl⟩ : ∃ u, pc = u + 1 := ⟨pc - 1, by omega⟩
      simp only [show t + 1 + 1 + 2 * (u + 1) - 2 = t + 1 + 2 * u + 1 by omega,
        show t + 1 + 2 * (u + 1) - 2 = t + 2 * u + 1 by omega, show t + 1 + 1 - 1 = t + 1 by omega,
        show t + 1 - 1 = t by omega, show u + 1 + (t + 1) - 1 = u + t + 1 by omega]; grind
  omega

/-- The triangular term is `Σ_{k=1}^{s-1} (pc + k - 1)`. -/
theorem tri_eq (s pc : Nat) (hs : 1 ≤ s) :
    ((tri s pc : Nat) : Int) = isum (fun k => ((pc + k - 1 : Nat) : Int)) 1 s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  induction t with
  | zero => rw [isum_self _ 1 1 (Nat.le_refl 1)]; simp [tri]
  | succ t ih =>
    rw [isum_split _ 1 (t + 1) (t + 1 + 1) (by omega) (by omega), ← ih (by omega),
      isum_succ _ (t + 1) (t + 1 + 1) (by omega), isum_self _ (t + 1 + 1) (t + 1 + 1) (Nat.le_refl _),
      tri_succ _ _ (by omega)]
    push_cast; omega

/-! ## List sums -/

theorem list_sum_isum (f : Nat → Int) (L : List Nat) (j : Nat) :
    (L.map f).sum = isum (fun k => f (L.getD (k - j) 0)) j (j + L.length) := by
  induction L generalizing j with
  | nil => simp [isum_self]
  | cons x L ih =>
    rw [isum_succ _ j _ (by simp), List.map_cons, List.sum_cons, ih (j + 1)]
    simp only [Nat.sub_self, List.getD_cons_zero, List.length_cons]
    congr 1
    rw [show j + (L.length + 1) = j + 1 + L.length by omega]
    apply isum_congr
    intro k h1 _
    rw [show k - j = (k - (j + 1)) + 1 by omega, List.getD_cons_succ]

theorem list_sum_filter (f : Nat → Int) (P : Nat → Bool) (L : List Nat) :
    ((L.filter P).map f).sum = (L.map (fun x => if P x then f x else 0)).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => by_cases h : P x <;> simp [List.filter_cons, h, ih]

theorem list_sum_cast_sub (g h : Nat → Nat) (L : List Nat) (hle : ∀ x ∈ L, h x ≤ g x) :
    (((L.map (fun x => g x - h x)).sum : Nat) : Int) = (L.map (fun x => (g x : Int) - h x)).sum := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    have := hle x (by simp)
    push_cast [ih (fun y hy => hle y (by simp [hy]))]
    omega

/-- On an increasing list, `takeWhile` of a downward-closed predicate is `filter`. -/
theorem takeWhile_eq_filter (P : Nat → Bool) (L : List Nat) (hs : L.Pairwise (· < ·))
    (hP : ∀ x y, x < y → P y = true → P x = true) : L.takeWhile P = L.filter P := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.pairwise_cons] at hs
    by_cases h : P x
    · simp [List.takeWhile_cons, List.filter_cons, h, ih hs.2]
    · simp only [List.takeWhile_cons, List.filter_cons, h, Bool.false_eq_true, ↓reduceIte]
      symm; rw [List.filter_eq_nil_iff]
      intro y hy hPy
      exact h (hP x y (hs.1 y hy) hPy)

theorem countPrimes_mono {m n : Nat} (h : m ≤ n) : countPrimes m ≤ countPrimes n := by
  induction n with
  | zero => obtain rfl : m = 0 := by omega
            exact Nat.le_refl _
  | succ n ih =>
    by_cases hm : m = n + 1
    · rw [hm]; exact Nat.le_refl _
    · have := ih (by omega); simp only [countPrimes]; omega

/-! ## The rough primes at the cutoff -/

theorem getD_lt (L : List Nat) (k : Nat) (h : k < L.length) : L.getD k 0 = L[k] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- `roughs[k]`, with `roughs[0] = 1`. -/
abbrev qq (N a k : Nat) : Nat := (RL N a).getD k 0

theorem qq_mem (N a k : Nat) (hk1 : 1 ≤ k) (hk : k < (RL N a).length) :
    qq N a k ∈ roughList a (isqrt N) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [qq, RL, List.getD_cons_succ]
  simp only [RL, List.length_cons] at hk
  rw [getD_lt _ _ (by omega)]
  exact List.getElem_mem _

theorem qq_get (N a k : Nat) (hk : k < (RL N a).length) : (RL N a)[k]? = some (qq N a k) := by
  simp only [qq]; rw [getD_lt _ _ hk]; exact List.getElem?_eq_getElem hk

theorem qq_lt (N a l k : Nat) (ha : 3 ≤ a) (hlk : l < k) (hk : k < (RL N a).length) :
    qq N a l < qq N a k := by
  have hk' : k < (1 :: roughList a (isqrt N)).length := hk
  have hs := List.pairwise_iff_getElem.mp (rough_sorted a (isqrt N) ha) l k (by omega) hk' hlk
  simp only [qq]
  rw [getD_lt _ _ (by omega), getD_lt _ _ hk]
  exact hs

/-- The rank: `C a (roughs[k]) = pc + k`. -/
theorem qq_rank (N a k : Nat) (ha : 3 ≤ a) (hk1 : 1 ≤ k) (hk : k < (RL N a).length) :
    C a (qq N a k) = C a (a - 1) + k := by
  have hm := qq_mem N a k hk1 hk
  have hr := rough_rank ha hm
  have hnd : (RL N a).Nodup := (rough_sorted a (isqrt N) ha).imp (fun h => Nat.ne_of_lt h)
  have hge : C a (a - 1) ≤ C a (qq N a k) := C_mono a (by have := (mem_rough.mp hm).1; omega)
  have hidx : C a (qq N a k) - C a (a - 1) < (RL N a).length := by
    apply Decidable.byContradiction; intro hc
    rw [List.getElem?_eq_none (by simp only [RL] at hc; omega)] at hr
    cases hr
  have := (List.Nodup.getElem?_inj (i := k) (j := C a (qq N a k) - C a (a - 1)) hk hnd).mp
    (by rw [qq_get N a k hk, hr])
  omega

theorem qq_rank1 (N a k : Nat) (ha : 3 ≤ a) (hk1 : 1 ≤ k) (hk : k < (RL N a).length) :
    C a (qq N a k - 1) = C a (a - 1) + k - 1 := by
  have hm := mem_rough.mp (qq_mem N a k hk1 hk)
  have hs := C_succ a (qq N a k - 1)
  rw [show qq N a k - 1 + 1 = qq N a k by omega, if_pos hm.2.2, qq_rank N a k ha hk1 hk] at hs
  omega

/-- `roughs[k] ≤ X` iff `smalls(X) - pc ≥ k`. -/
theorem qq_le_iff (N a k X : Nat) (ha : 3 ≤ a) (hk1 : 1 ≤ k) (hk : k < (RL N a).length) :
    qq N a k ≤ X ↔ C a (a - 1) + k ≤ C a X := by
  constructor
  · intro h; rw [← qq_rank N a k ha hk1 hk]; exact C_mono a h
  · intro h
    apply Decidable.byContradiction; intro hc
    have := C_mono a (show X ≤ qq N a k - 1 by omega)
    rw [qq_rank1 N a k ha hk1 hk] at this
    omega

theorem C_isqrt (N a : Nat) (ha : 3 ≤ a) (hs : 2 ≤ (RL N a).length) :
    C a (isqrt N) = C a (a - 1) + (RL N a).length - 1 := by
  have hm := mem_rough.mp (qq_mem N a 1 (Nat.le_refl 1) (by omega))
  have := interval_length a (isqrt N + 1 - a) ha
  rw [show a - 1 + (isqrt N + 1 - a) = isqrt N by omega] at this
  simp only [RL, List.length_cons]
  unfold roughList at *
  omega

/-! ## Facts at the cutoff -/

/-- The hypotheses of the finish. -/
structure Cut (N a : Nat) : Prop where
  hN3 : 3 ≤ N
  hN : N < 100000000000
  ha : 3 ≤ a
  hcut : N < a * a * (a * a)

theorem Cut.v_lt {N a : Nat} (h : Cut N a) : isqrt N < a * a := by
  have hv := (isqrt_spec N).1
  have := h.hcut
  apply Decidable.byContradiction; intro hc
  have := Nat.mul_le_mul (show a * a ≤ isqrt N by omega) (show a * a ≤ isqrt N by omega)
  omega

theorem Cut.qq_range {N a : Nat} (h : Cut N a) (k : Nat) (hk1 : 1 ≤ k) (hk : k < (RL N a).length) :
    a ≤ qq N a k ∧ qq N a k ≤ isqrt N ∧ Prime (qq N a k) := by
  have hm := qq_mem N a k hk1 hk
  obtain ⟨h1, h2, _⟩ := mem_rough.mp hm
  rw [cutoff_roughs h.ha h.hcut] at hm
  simp only [primesFrom, List.mem_filter, decide_eq_true_eq] at hm
  exact ⟨h1, h2, hm.2⟩

/-- `N / x / y` lies in `[1, v]` for `a ≤ x, y ≤ v`. -/
theorem Cut.div2 {N a : Nat} (h : Cut N a) (x y : Nat) (hx : a ≤ x) (hy : a ≤ y) (hxv : x ≤ isqrt N)
    (hyv : y ≤ isqrt N) : 1 ≤ N / x / y ∧ N / x / y ≤ isqrt N := by
  have hv := isqrt_spec N
  have hva := h.v_lt
  have ha := h.ha
  rw [Nat.div_div_eq_div_mul]
  have hxy : x * y ≤ isqrt N * isqrt N := Nat.mul_le_mul hxv hyv
  have haa : a * a ≤ x * y := Nat.mul_le_mul hx hy
  constructor
  · exact (Nat.le_div_iff_mul_le (by
      have := Nat.mul_le_mul (show 3 ≤ x by omega) (show 3 ≤ y by omega); omega)).mpr (by omega)
  · have := Nat.mul_le_mul_left (isqrt N + 1) (show isqrt N + 1 ≤ x * y by omega)
    have h2 : N / (x * y) < isqrt N + 1 := (Nat.div_lt_iff_lt_mul (by
      have := Nat.mul_le_mul (show 3 ≤ x by omega) (show 3 ≤ y by omega); omega)).mpr (by omega)
    omega

theorem smd_C (a d : Nat) (ha : 3 ≤ a) (hd : 1 ≤ d) : smd (fun i => C a (2 * i + 1)) d = C a d := by
  simp only [smd]; exact C_odd_index a ha d hd

/-! ## The binary's rows -/

/-- Row `l` of the binary's triple correction, as a sum over all `k`. -/
def rowF (N a l k : Nat) : Int :=
  if l < k ∧ qq N a k ≤ N / qq N a l / qq N a l then
    (C a (N / qq N a l / qq N a k) : Int) - ((C a (a - 1) + l - 1 : Nat) : Int)
  else 0

theorem row_zero {N a : Nat} (h : Cut N a) (l l' : Nat) (hl1 : 1 ≤ l) (hll : l ≤ l')
    (hl' : l' < (RL N a).length)
    (hbrk : C a (N / qq N a l / qq N a l) < C a (a - 1) + l + 1) :
    isum (rowF N a l') 1 (RL N a).length = 0 := by
  rw [isum_congr (g := fun _ => 0), isum_zero]
  intro k hk1 hk
  simp only [rowF]
  rw [if_neg]
  rintro ⟨hlk, hq⟩
  have hql : qq N a l ≤ qq N a l' := by
    rcases Nat.lt_or_ge l l' with h1 | h1
    · exact Nat.le_of_lt (qq_lt N a l l' h.ha h1 hl')
    · obtain rfl : l = l' := by omega
      exact Nat.le_refl _
  have hpos : 0 < qq N a l := by have := (h.qq_range l hl1 (by omega)).1; have := h.ha; omega
  have hX : N / qq N a l' / qq N a l' ≤ N / qq N a l / qq N a l := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_left (Nat.mul_le_mul hql hql) (Nat.mul_pos hpos hpos)
  have := (qq_le_iff N a k _ h.ha hk1 hk).mp (Nat.le_trans hq hX)
  omega

theorem triLoop_eq {N a : Nat} (h : Cut N a) (l : Nat) (hl1 : 1 ≤ l) (hl : l ≤ (RL N a).length) :
    triLoop (fun i => C a (2 * i + 1)) (qq N a) N (RL N a).length (C a (a - 1)) l =
      isum (fun l' => isum (rowF N a l') 1 (RL N a).length) l (RL N a).length := by
  by_cases hls : l < (RL N a).length
  · obtain ⟨hal, hlv, _⟩ := h.qq_range l hl1 hls
    obtain ⟨hX1, hXv⟩ := h.div2 _ _ hal hal hlv hlv
    rw [triLoop, if_pos hls, smd_C a _ h.ha hX1]
    by_cases hbrk : C a (N / qq N a l / qq N a l) < C a (a - 1) + l + 1
    · rw [if_pos hbrk, isum_congr (g := fun _ => 0) (fun l' h1 h2 => row_zero h l l' hl1 h1 h2 hbrk),
        isum_zero]
    · rw [if_neg hbrk, isum_succ _ l _ hls, ← triLoop_eq h (l + 1) (by omega) (by omega)]
      congr 1
      have hCv := C_isqrt N a h.ha (by omega)
      have hXs : C a (N / qq N a l / qq N a l) ≤ C a (isqrt N) := C_mono a hXv
      have hw := isum_window (fun k => (C a (N / qq N a l / qq N a k) : Int) -
          ((C a (a - 1) + l - 1 : Nat) : Int)) 1 (l + 1)
          (C a (N / qq N a l / qq N a l) - C a (a - 1) + 1) (RL N a).length (by omega) (by omega)
          (by omega) (rowF N a l) (by
            intro k hk1 hk
            simp only [rowF]
            have := qq_le_iff N a k (N / qq N a l / qq N a l) h.ha hk1 hk
            by_cases hc : l < k ∧ qq N a k ≤ N / qq N a l / qq N a l
            · rw [if_pos hc, if_pos (by omega)]
            · rw [if_neg hc, if_neg (by omega)])
      rw [hw, isum_sub, isum_const, sumR_cast]
      rw [isum_congr (f := fun k => ((smd (fun i => C a (2 * i + 1)) (N / qq N a l / qq N a k) : Nat) : Int))
        (g := fun k => (C a (N / qq N a l / qq N a k) : Int))]
      · push_cast
        rfl
      · intro k hk1 hk
        obtain ⟨hak, hkv, _⟩ := h.qq_range k (by omega) (by omega)
        rw [smd_C a _ h.ha (h.div2 _ _ hal hak hlv hkv).1]
  · obtain rfl : l = (RL N a).length := by omega
    rw [triLoop, if_neg hls, isum_self _ _ _ (Nat.le_refl _)]
termination_by (RL N a).length - l
decreasing_by all_goals (try simp_wf); simp only [RL, List.length_cons] at *; omega

/-! ## The specification's regrouping -/

/-- The triple correction for `roughs[k]` in `finish`, as a sum over all `l`. -/
def TkF (N a k l : Nat) : Int :=
  if l < k ∧ qq N a l * qq N a l ≤ N / qq N a k then
    (C a (N / qq N a k / qq N a l) : Int) - ((C a (a - 1) + l - 1 : Nat) : Int)
  else 0

theorem swap_eq {N a : Nat} (h : Cut N a) :
    isum (fun k => isum (TkF N a k) 1 (RL N a).length) 1 (RL N a).length =
      isum (fun l => isum (rowF N a l) 1 (RL N a).length) 1 (RL N a).length := by
  refine Eq.trans ?_ (isum_swap (fun l k => rowF N a l k) 1 (RL N a).length 1 (RL N a).length)
  apply isum_congr; intro k hk1 hk
  apply isum_congr; intro l hl1 hl
  obtain ⟨hak, _, _⟩ := h.qq_range k hk1 hk
  obtain ⟨hal, _, _⟩ := h.qq_range l hl1 hl
  have hk0 : 0 < qq N a k := by have := h.ha; omega
  have hl0 : 0 < qq N a l := by have := h.ha; omega
  have hiff : qq N a l * qq N a l ≤ N / qq N a k ↔ qq N a k ≤ N / qq N a l / qq N a l := by
    rw [Nat.le_div_iff_mul_le hk0, Nat.div_div_eq_div_mul, Nat.le_div_iff_mul_le (Nat.mul_pos hl0 hl0),
      Nat.mul_comm]
  have hdiv : N / qq N a k / qq N a l = N / qq N a l / qq N a k := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp only [TkF, rowF, hiff, hdiv]

theorem list_sum_cast (f : Nat → Nat) (L : List Nat) :
    (((L.map f).sum : Nat) : Int) = (L.map (fun x => (f x : Int))).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons, List.sum_cons]; push_cast [ih]; rfl

theorem ht_eq {N a : Nat} (h : Cut N a) (q : Nat) (haq : a ≤ q) (hqv : q ≤ isqrt N) :
    C a (N / q) = C q (N / q) + triples (C a) (primesFrom a (isqrt N + 1 - a)) q (N / q) := by
  have hva := h.v_lt
  unfold triples
  have h' := telescope a (isqrt N + 1 - a) q (N / q) h.ha (by omega) (fun r => C a (N / q / r) - C a (r - 1))
  rw [Nat.max_eq_right haq] at h'
  apply h'
  intro r har hr _ _
  have := (h.div2 q r haq har hqv (by omega)).2
  rw [frozen har (by omega : N / q / r < a * a), frozen har (by omega : r - 1 < a * a)]

theorem mem_Qs {N a : Nat} (h : Cut N a) (q : Nat) (hq : q ∈ primesFrom a (isqrt N + 1 - a)) :
    a ≤ q ∧ q ≤ isqrt N ∧ Prime q := by
  simp only [primesFrom, List.mem_filter, List.mem_range'_1, decide_eq_true_eq] at hq
  have := h.ha
  exact ⟨hq.1.1, by omega, hq.2⟩

theorem Qs_sorted (a len : Nat) : (primesFrom a len).Pairwise (· < ·) :=
  (List.pairwise_lt_range' (s := a) (n := len)).filter _

/-- The triple correction for one `q`, cast to `Int` and indexed. -/
theorem triples_cast {N a : Nat} (h : Cut N a) (k : Nat) (hk1 : 1 ≤ k) (hk : k < (RL N a).length) :
    ((triples (C a) (primesFrom a (isqrt N + 1 - a)) (qq N a k) (N / qq N a k) : Nat) : Int) =
      isum (TkF N a k) 1 (RL N a).length := by
  have hRL : RL N a = 1 :: primesFrom a (isqrt N + 1 - a) := by
    simp only [RL]; rw [cutoff_roughs h.ha h.hcut]
  obtain ⟨hak, hkv, _⟩ := h.qq_range k hk1 hk
  unfold triples prefixSum
  rw [takeWhile_eq_filter _ _ (Qs_sorted _ _) (by
    intro x y hxy hy
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hy ⊢
    exact ⟨by omega, Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt hxy) (Nat.le_of_lt hxy)) hy.2⟩)]
  rw [list_sum_cast_sub _ _ _ (by
    intro r hr
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨har, _, _⟩ := mem_Qs h r hr.1
    apply C_mono
    have : r ≤ N / qq N a k / r :=
      (Nat.le_div_iff_mul_le (by have := h.ha; omega)).mpr hr.2.2
    omega)]
  rw [list_sum_filter, list_sum_isum _ _ 1]
  have hlen : 1 + (primesFrom a (isqrt N + 1 - a)).length = (RL N a).length := by
    rw [hRL]; simp; omega
  rw [hlen]
  apply isum_congr; intro l hl1 hl
  have hget : (primesFrom a (isqrt N + 1 - a)).getD (l - 1) 0 = qq N a l := by
    simp only [qq]; rw [hRL, show l = (l - 1) + 1 by omega, List.getD_cons_succ]; simp
  rw [hget, qq_rank1 N a l h.ha hl1 hl]
  simp only [TkF, Bool.and_eq_true, decide_eq_true_eq]
  have hlt : qq N a l < qq N a k ↔ l < k := by
    constructor
    · intro hq; apply Decidable.byContradiction; intro hc
      rcases Nat.lt_or_ge k l with h1 | h1
      · have := qq_lt N a k l h.ha h1 hl; omega
      · obtain rfl : k = l := by omega
        omega
    · intro hlk; exact qq_lt N a l k h.ha hlk hk
  simp only [hlt]

/-- `finish_correct`, in `Int` and indexed by the slots of the roughs table. -/
theorem spec_eq {N a : Nat} (h : Cut N a) :
    (countPrimes N : Int) = C a N - isum (fun k => (C a (N / qq N a k) : Int) -
      isum (TkF N a k) 1 (RL N a).length - ((C a (a - 1) + k - 1 : Nat) : Int)) 1 (RL N a).length + 1 := by
  have hRL : RL N a = 1 :: primesFrom a (isqrt N + 1 - a) := by
    simp only [RL]; rw [cutoff_roughs h.ha h.hcut]
  have hva := h.v_lt
  have hv := isqrt_spec N
  have hf := finish_correct N a h.hN3 h.ha h.hcut (C a) (fun d => C a (N / d)) (fun _ _ => rfl)
    (by simp) (fun _ _ _ _ => rfl)
  have hcp : countPrimes 3 ≤ countPrimes N := countPrimes_mono h.hN3
  have h3 : countPrimes 3 = 2 := by decide
  unfold finish at hf
  simp only [Nat.div_one] at hf
  unfold prefixSum at hf
  rw [takeWhile_eq_filter _ _ (Qs_sorted _ _) (by
    intro x y hxy hy
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hy ⊢
    exact ⟨by omega, Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt hxy) (Nat.le_of_lt hxy)) hy.2⟩),
    List.filter_eq_self.mpr (by
      intro q hq
      obtain ⟨_, hqv, _⟩ := mem_Qs h q hq
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, Nat.le_trans (Nat.mul_le_mul hqv hqv) hv.1⟩)] at hf
  -- each term is exact
  have hex : ∀ q ∈ primesFrom a (isqrt N + 1 - a),
      triples (C a) (primesFrom a (isqrt N + 1 - a)) q (N / q) + C a (q - 1) ≤ C a (N / q) := by
    intro q hq
    obtain ⟨haq, hqv, _⟩ := mem_Qs h q hq
    rw [ht_eq h q haq hqv, frozen haq (by omega : q - 1 < a * a)]
    have : q - 1 ≤ N / q := by
      have : q ≤ N / q := (Nat.le_div_iff_mul_le (by have := h.ha; omega)).mpr
        (Nat.le_trans (Nat.mul_le_mul hqv hqv) hv.1)
      omega
    have := C_mono q this
    omega
  have hsum : (((primesFrom a (isqrt N + 1 - a)).map (fun q => C a (N / q) -
      triples (C a) (primesFrom a (isqrt N + 1 - a)) q (N / q) - C a (q - 1))).sum : Int) =
      ((primesFrom a (isqrt N + 1 - a)).map (fun q => (C a (N / q) : Int) -
        (triples (C a) (primesFrom a (isqrt N + 1 - a)) q (N / q) : Nat) - (C a (q - 1) : Int))).sum := by
    rw [list_sum_cast]
    congr 1
    apply List.map_congr_left
    intro q hq
    have := hex q hq
    push_cast [Nat.sub_sub]
    omega
  rw [list_sum_isum _ _ 1] at hsum
  have hlen : 1 + (primesFrom a (isqrt N + 1 - a)).length = (RL N a).length := by
    rw [hRL]; simp; omega
  rw [hlen] at hsum
  have hfin : (countPrimes N : Int) = C a N - (((primesFrom a (isqrt N + 1 - a)).map (fun q => C a (N / q) -
      triples (C a) (primesFrom a (isqrt N + 1 - a)) q (N / q) - C a (q - 1))).sum : Nat) + 1 := by
    omega
  rw [hfin, hsum]
  congr 2
  apply isum_congr; intro k hk1 hk
  have hget : (primesFrom a (isqrt N + 1 - a)).getD (k - 1) 0 = qq N a k := by
    simp only [qq]; rw [hRL, show k = (k - 1) + 1 by omega, List.getD_cons_succ]; simp
  rw [hget, triples_cast h k hk1 hk, qq_rank1 N a k h.ha hk1 hk]

/-! ## The value the binary returns -/

theorem finish_value {N a : Nat} (h : Cut N a) :
    ((tri (RL N a).length (C a (a - 1)) + C a (N / qq N a 0) : Nat) : Int) -
      (sumR (fun k => C a (N / qq N a k)) 1 (RL N a).length : Nat) +
      triLoop (fun i => C a (2 * i + 1)) (qq N a) N (RL N a).length (C a (a - 1)) 1 + 1 =
      countPrimes N := by
  have hs : 1 ≤ (RL N a).length := by simp [RL]
  have h0 : qq N a 0 = 1 := rfl
  rw [spec_eq h, triLoop_eq h 1 (Nat.le_refl 1) hs, ← swap_eq h, h0, Nat.div_one, sumR_cast,
    isum_sub, isum_sub]
  push_cast
  rw [tri_eq _ _ hs]
  omega

end TinyFive.GrumpyBinary
