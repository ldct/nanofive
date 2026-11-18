import GrumpyResidual

/-! Snapshot form of the fourth-root sieve: dense odd small entries, and
large entries only for the sentinel 1 and the ascending compact roughs. -/
namespace TinyFive.GrumpyGordon
open CountingPrimes LucyMath SieveMath

structure Tables where
  smalls : Array Nat
  roughs : List Nat  -- excludes sentinel 1
  larges : Array Nat
  pc : Nat

def small (t : Tables) (x : Nat) := t.smalls[(x-1)/2]!
def large (t : Tables) (d : Nat) := t.larges[if d = 1 then 0 else small t d - t.pc]!

private def smallTable (v : Nat) (f : Nat → Nat) :=
  Array.ofFn (n := (v+1)/2) fun i => f (2*i.val+1)

private def pack (v pc : Nat) (ks : List Nat) (f g : Nat → Nat) : Tables :=
  ⟨smallTable v f, ks, ((1::ks).map g).toArray, pc⟩

private theorem smallTable_read {v p : Nat} (hp : 3 ≤ p) (hv : 1 ≤ v)
    (f : Nat → Nat) (hf : ∀ x, x ≤ v → f x = C p x) {x : Nat} (hx : x ≤ v) :
    (smallTable v f)[(x-1)/2]! = C p x := by
  unfold smallTable
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn, hf _ (by omega)]
  by_cases h : 1 ≤ x
  · exact C_odd_index p (by omega) x h
  · have : x = 0 := by omega
    subst x
    simp [C, count, Alive]

/-- Specification only: the live large-table denominators other than 1. -/
def roughList (p v : Nat) := (List.range' p (v+1-p)).filter (fun d => decide (Alive p d))

theorem mem_rough {p v d : Nat} : d ∈ roughList p v ↔ p ≤ d ∧ d ≤ v ∧ Alive p d := by
  simp only [roughList, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

private theorem C_succ (p x : Nat) : C p (x+1) = C p x + if Alive p (x+1) then 1 else 0 := rfl

private theorem interval_length (p len : Nat) (hp : 3 ≤ p) :
    ((List.range' p len).filter (fun d => decide (Alive p d))).length + C p (p-1) = C p (p-1+len) := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [List.range'_1_concat, List.filter_append, List.length_append,
      show p-1+(len+1) = (p-1+len)+1 by omega, C_succ,
      show p-1+len+1 = p+len by omega]
    by_cases h : Alive p (p+len) <;> simp [h] <;> omega

/-- `smalls[d >> 1] - pc` is exactly the slot of live odd denominator `d`,
with slot zero reserved for 1. No dictionary or search in the rough list. -/
theorem rough_rank {p v d : Nat} (hp : 3 ≤ p) (hd : d ∈ roughList p v) :
    (1 :: roughList p v)[C p d - C p (p-1)]? = some d := by
  obtain ⟨hpd, hdv, ha⟩ := mem_rough.mp hd
  let front := (List.range' p (d-p)).filter (fun x => decide (Alive p x))
  have hr := interval_length p (d-p) hp
  change front.length + C p (p-1) = _ at hr
  rw [show p-1+(d-p) = d-1 by omega] at hr
  have hc : C p d = C p (d-1) + 1 := by
    simpa [show d-1+1 = d by omega, ha] using C_succ p (d-1)
  have hsplit : roughList p v = front ++ d :: ((List.range' (d+1) (v+1-(d+1))).filter (fun x => decide (Alive p x))) := by
    unfold roughList front
    rw [show v+1-p = (d-p)+((v+1-(d+1))+1) by omega, ← List.range'_append_1,
      show p+(d-p)=d by omega, List.range'_succ, List.filter_append]
    simp [ha]
  rw [show C p d - C p (p-1) = front.length+1 by omega, hsplit,
    List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- The two table equations, plus *exactness and order* of the compact list. -/
structure Valid (N p : Nat) (t : Tables) : Prop where
  pc_eq : t.pc = C p (p-1)
  keys : t.roughs = roughList p (isqrt N)
  lo : ∀ x, x ≤ isqrt N → small t x = C p x
  hi : ∀ d, d ∈ 1 :: t.roughs → large t d = C p (N/d)

private theorem pack_valid {N p pc : Nat} (hp : 3 ≤ p) (hv : 1 ≤ isqrt N)
    {ks : List Nat} {f g : Nat → Nat} (hpc : pc = C p (p-1)) (hk : ks = roughList p (isqrt N))
    (hf : ∀ x, x ≤ isqrt N → f x = C p x) (hg : ∀ d, d ∈ 1::ks → g d = C p (N/d)) :
    Valid N p (pack (isqrt N) pc ks f g) := by
  have hs (x : Nat) (hx : x ≤ isqrt N) := smallTable_read hp hv f hf hx
  refine ⟨hpc, hk, fun _ hx => hs _ hx, ?_⟩
  intro d hd
  change d ∈ 1 :: ks at hd
  rw [← hg _ hd]
  have hidx : (1::ks)[if d = 1 then 0 else small (pack (isqrt N) pc ks f g) d - pc]? = some d := by
    rcases List.mem_cons.mp hd with rfl | h
    · simp
    · rw [hk] at h ⊢
      obtain ⟨hpd, hdv, _⟩ := mem_rough.mp h
      simp only [show d ≠ 1 by omega, ↓reduceIte, small, pack, hs _ hdv, hpc]
      exact rough_rank hp h
  unfold large
  change (((1::ks).map g).toArray)[if d = 1 then 0 else small (pack (isqrt N) pc ks f g) d - pc]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, hidx]
  rfl

/-- All odd candidates ≥ 3; the sentinel 1 has a large entry too. -/
def init (N v : Nat) : Tables :=
  let seed := fun x => (x-1)/2
  let ks := (List.range' 3 (v+1-3)).filter (fun d => decide (d%2 = 1))
  pack v 0 ks seed (fun d => seed (N/d))

theorem init_valid (N : Nat) (hv : 1 ≤ isqrt N) : Valid N 3 (init N (isqrt N)) := by
  have hk : (init N (isqrt N)).roughs = roughList 3 (isqrt N) := by
    apply List.filter_congr
    intro x hx
    have hx3 := (List.mem_range'_1.mp hx).1
    have he : Alive 3 x ↔ x%2=1 := by
      constructor
      · intro h; apply Decidable.byContradiction; intro hn
        exact h.2 ⟨2, by omega, by omega, by omega, by omega⟩
      · refine fun ho => ⟨hx3, fun ⟨d,h1,h2,_,hd⟩ => ?_⟩
        have : d = 2 := by omega
        subst d; omega
    simp [he]
  exact pack_valid (by decide) hv (by decide) hk (fun x _ => (C_init x).symm)
    (fun d _ => (C_init (N/d)).symm)

private theorem rough_next {p v : Nat} (hp : 3 ≤ p) (hpv : p ≤ v) :
    roughList (p+1) v = (roughList p v).filter (fun d => d%p != 0) := by
  unfold roughList
  rw [show v+1-p = (v+1-(p+1))+1 by omega, List.range'_succ]
  simp only [List.filter_cons]
  by_cases hs : Alive p p <;> simp [hs, List.filter_filter] <;> apply List.filter_congr <;>
    intro x hx <;> have hpx := (List.mem_range'_1.mp hx).1 <;>
    simp [Alive, marked_step p x (by omega), show p < x by omega, Nat.dvd_iff_mod_eq_zero] <;> grind

private theorem rough_skip {p v : Nat} (hp : 3 ≤ p) (hpv : p ≤ v) (hn : ¬ Prime p) :
    roughList (p+1) v = roughList p v := by
  unfold roughList
  rw [show v+1-p = (v+1-(p+1))+1 by omega, List.range'_succ]
  have hm := (marked_self_iff_not_prime p (by omega)).mpr hn
  have hs : ¬ Alive p p := fun hh => hh.2 hm
  simp only [List.filter_cons, hs, decide_false, Bool.false_eq_true, ↓reduceIte]
  apply List.filter_congr
  intro x _
  simp only [Alive, composite_skip p x hm]

/-- A simultaneous update, reading only the previous snapshot. Nat subtraction
makes the small-table decrement zero below `p²`. -/
def step (N v p : Nat) (t : Tables) : Tables :=
  let pc := t.pc
  let ks := t.roughs.filter (fun d => d%p != 0)
  pack v (pc+1) ks (fun x => small t x - (small t (x/p) - pc)) fun d =>
     let e := d*p
     let quotient := if e ≤ v then large t e else small t (N/e)
     large t d - (quotient - pc)

private theorem update_eq (p x : Nat) (hp : 3 ≤ p) (hprime : Prime p) :
    C p x - (C p (x/p) - C p (p-1)) = C (p+1) x := by
  by_cases hx : p ≤ x/p
  · have := C_prime_step p hprime hp x hx
    omega
  · have h1 : C p (x/p) ≤ C p (p-1) := count_mono (Alive p) (show x/p ≤ p-1 by omega)
    have h2 := (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).mp (show x/p < p by omega)
    rw [C_small p x hp h2]; omega

/-- On a surviving denominator `d`, `d*p` is an *old* rough denominator.
This justifies the large/large read in the compaction loop. -/
private theorem product_rough {p v d : Nat} (hp : 3 ≤ p) (hprime : Prime p)
    (hd : d ∈ 1 :: roughList (p+1) v) (he : d*p ≤ v) : d*p ∈ roughList p v := by
  apply mem_rough.mpr
  rcases List.mem_cons.mp hd with rfl | h
  · simp only [Nat.one_mul] at *
    exact ⟨by omega, he, hp, fun hm => (marked_self_iff_not_prime p (by omega)).mp hm hprime⟩
  · obtain ⟨hpd, _, hsurv⟩ := mem_rough.mp h
    have hs : Alive p d := ⟨hsurv.1, fun ⟨r, h1, h2, h3, h4⟩ =>
      hsurv.2 ⟨r, h1, by omega, h3, h4⟩⟩
    have hpd' := Nat.le_mul_of_pos_right d (by omega : 0 < p)
    refine ⟨by omega, he, by omega, ?_⟩
    rintro ⟨r, hr2, hrp, _, hdvd⟩
    have hrd : r ∣ d := (coprime_of_lt_prime hprime (by omega) hrp).dvd_of_dvd_mul_right hdvd
    exact hs.2 ⟨r, hr2, hrp, by omega, hrd⟩

theorem step_valid {N p : Nat} {t : Tables} (hp : 3 ≤ p) (hpv : p ≤ isqrt N)
    (hprime : Prime p) (h : Valid N p t) : Valid N (p+1) (step N (isqrt N) p t) := by
  let v := isqrt N
  have hk : (step N v p t).roughs = roughList (p+1) v := by
    simp [step, pack, h.keys, rough_next hp hpv, v]
  have hpc := h.pc_eq
  have hpp := Nat.mul_le_mul_right p hp
  refine pack_valid (by omega) (by omega) ?_ hk ?_ ?_
  · rw [Nat.add_sub_cancel, C_small p p hp (by omega), C_self p hp, hpc, ite_eq_left hprime]
  · intro y hy
    have hdiv := Nat.div_le_self y p
    simp only [h.lo y hy, h.lo (y/p) (by omega), hpc, update_eq p y hp hprime]
  · intro d hd
    change d ∈ 1 :: (step N v p t).roughs at hd
    rw [hk] at hd
    have hold : d ∈ 1 :: t.roughs := by
      rw [h.keys]; rw [rough_next hp hpv] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_filter.mp hd).1
    rw [h.hi _ hold, hpc]
    have hquot : (if d*p ≤ v then large t (d*p) else small t (N/(d*p))) = C p (N/d/p) := by
      rw [Nat.div_div_eq_div_mul]
      split
      · apply h.hi; rw [h.keys]; exact List.mem_cons_of_mem _ (product_rough hp hprime hd ‹_›)
      · apply h.lo
        have hpos : 0 < d*p := by omega
        have hlt := (isqrt_spec N).2
        have hm := Nat.mul_le_mul_left (isqrt N+1) (show isqrt N+1 ≤ d*p by omega)
        have := (Nat.div_lt_iff_lt_mul hpos).mpr (Nat.lt_of_lt_of_le hlt hm)
        omega
    dsimp only at *
    rw [hquot, update_eq p _ hp hprime]

theorem skip_valid {N p : Nat} {t : Tables} (hp : 3 ≤ p) (hpv : p ≤ isqrt N)
    (hn : ¬ Prime p) (h : Valid N p t) : Valid N (p+1) t := by
  refine ⟨?_, h.keys.trans (rough_skip hp hpv hn).symm,
    fun x hx => (h.lo x hx).trans (C_composite p (by omega) hn _).symm,
    fun d hd => (h.hi d hd).trans (C_composite p (by omega) hn _).symm⟩
  simp [C_composite p hp hn, C_self p hp, hn, h.pc_eq]

end TinyFive.GrumpyGordon
