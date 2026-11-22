import GrumpyBinary.Init

/-! The loops inside one round of `prime_pi`'s sieve: marking the odd multiples of `p` in `skip`
(at 668) and compacting `roughs` and `larges` in place (at 684). The compaction is proved against
an abstract list `L` of rough numbers and value functions; `Round.lean` supplies the arithmetic. -/
namespace TinyFive.GrumpyBinary
open SieveMemory LucyMath

local notation "bv" => BitVec.ofNat 64

theorem mark_upd (p m i : Nat) (hp : p % 2 = 1) (hm : p ∣ m) (hm2 : m % 2 = 1) :
    (p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < m + p * 2) ↔
      (i = m ∧ p * p ≤ m) ∨ (p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < m) := by
  constructor
  · rintro ⟨hd, h1, h2, h3⟩
    by_cases him : i < m
    · exact Or.inr ⟨hd, h1, h2, him⟩
    · left
      obtain ⟨a, rfl⟩ := hd
      obtain ⟨b, rfl⟩ := hm
      have hba : b ≤ a := by
        apply Decidable.byContradiction; intro h
        have := Nat.mul_lt_mul_of_pos_left (show a < b by omega) (show 0 < p by omega)
        omega
      have hab : a < b + 2 := by
        apply Decidable.byContradiction; intro h
        have := Nat.mul_le_mul_left p (show b + 2 ≤ a by omega)
        rw [Nat.mul_add] at this; omega
      by_cases hab' : a = b
      · subst hab'; exact ⟨rfl, h1⟩
      · have : a = b + 1 := by omega
        subst this
        rw [Nat.mul_succ] at h2; omega
  · rintro (⟨rfl, h⟩ | ⟨hd, h1, h2, h3⟩)
    · exact ⟨hm, h, hm2, by omega⟩
    · exact ⟨hd, h1, h2, by omega⟩

/-- The marking loop at 668: `skip[i] = 1` for odd multiples `i` of `p` from `p²` to `v`. -/
theorem mark_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (D v p m : Nat)
    (g0 : Nat → Nat) (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = bv m) (h11 : x.get 11 = bv (p * 2)) (h10 : x.get 10 = bv 1)
    (h24 : x.get 24 = bv D) (h18 : x.get 18 = bv v)
    (hD : 1236 ≤ D) (hDv : D + (v + 1) ≤ 4194304) (hv : v < 1000000) (hp : p % 2 = 1)
    (hpv : p ≤ v) (hm : p ∣ m) (hm2 : m % 2 = 1) (hpm : p * p ≤ m) (hmv : m ≤ v + p * 2)
    (harr : Arr8 mem D (v + 1)
      (fun i => if p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < m then 1 else g0 i)) :
    ∃ k y mem', run k ⟨x, bv 668, mem, [], out, .running⟩ = ⟨y, bv 676, mem', [], out, .running⟩ ∧
      Same mem mem' D (D + (v + 1)) ∧
      Arr8 mem' D (v + 1) (fun i => if p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 then 1 else g0 i) ∧
      (∀ r : Reg, r ∉ ([15, 16] : List Reg) → y.get r = x.get r) := by
  by_cases hmv' : m ≤ v
  · have hstep : ∃ y, run 6 ⟨x, bv 668, mem, [], out, .running⟩ =
        ⟨y, bv 668, wr mem (D + m) (bv 1) 1, [], out, .running⟩ ∧ y.get 15 = bv (m + p * 2) ∧
        (∀ r : Reg, r ∉ ([15, 16] : List Reg) → y.get r = x.get r) := by
      refine ⟨(((x.set 16 (bv m)).set 16 (bv (D + m))).set 15 (bv (m + p * 2))).set 0 752#64, ?_,
        by simp [Regs.get_set], by frame_tac⟩
      gexec
    obtain ⟨y, hr, hy15, hfy⟩ := hstep
    have harr' := (harr.wr (by omega) m 1 (by omega)).ext
      (g := fun i => if p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < m + p * 2 then 1 else g0 i)
      (fun i _ => by
        simp only [mark_upd p m i hp hm hm2]
        by_cases hi : i = m
        · subst hi; simp [hpm]
        · rw [upd_other _ _ _ _ hi]; simp [hi])
    obtain ⟨k, z, mem', hr2, hsame, harr2, hfz⟩ := mark_loop y _ out D v p (m + p * 2) g0
      (prefix_wr _ _ _ hmem (by omega) (by omega)) (by simp [hsz]) hy15
      (by rw [hfy 11 (by decide), h11]) (by rw [hfy 10 (by decide), h10])
      (by rw [hfy 24 (by decide), h24]) (by rw [hfy 18 (by decide), h18]) hD hDv hv hp hpv
      (Nat.dvd_add hm (Nat.dvd_mul_right p 2)) (by omega) (by omega) (by omega) harr'
    refine ⟨6 + k, z, mem', by rw [run_add, hr, hr2], ?_, harr2,
      fun r hr => by rw [hfz r hr, hfy r hr]⟩
    exact (Same.wr mem _ _ 1 D (D + (v + 1)) (by omega) (by omega) (by omega)).trans
      ⟨hsame.size_eq.trans (by simp), hsame.frame⟩
  · refine ⟨2, x.set 16 (bv m), mem, ?_, Same.refl _ _ _,
      harr.ext (fun i hi => by
        by_cases h : p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1
        · simp [h, show i < m by omega]
        · simp only [h, ite_false]; rw [if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩)]),
      by frame_tac⟩
    gexec
termination_by v + 1 - m
/-- Registers the compaction loop reads but does not write. -/
structure CRegs (x : Regs 64) (A B Cb D N v p pc s : Nat) : Prop where
  h9 : x.get 9 = bv s
  h21 : x.get 21 = bv B
  h24 : x.get 24 = bv D
  h12 : x.get 12 = bv p
  h8 : x.get 8 = bv Cb
  h18 : x.get 18 = bv v
  h20 : x.get 20 = bv A
  h14 : x.get 14 = bv pc
  h19 : x.get 19 = bv N

abbrev cfr : List Reg := [5, 6, 15, 16, 17, 28, 29, 30]

theorem CRegs.frame {x y : Regs 64} {A B Cb D N v p pc s : Nat} (h : CRegs x A B Cb D N v p pc s)
    (hf : ∀ r : Reg, r ∉ cfr → y.get r = x.get r) : CRegs y A B Cb D N v p pc s :=
  ⟨by rw [hf 9 (by decide), h.h9], by rw [hf 21 (by decide), h.h21], by rw [hf 24 (by decide), h.h24],
   by rw [hf 12 (by decide), h.h12], by rw [hf 8 (by decide), h.h8], by rw [hf 18 (by decide), h.h18],
   by rw [hf 20 (by decide), h.h20], by rw [hf 14 (by decide), h.h14], by rw [hf 19 (by decide), h.h19]⟩

/-- The address bounds of the compaction loop. -/
structure CBounds (A B Cb D N v p pc s : Nat) : Prop where
  hs : s < 200000
  hv : v < 400000
  hpv : p ≤ v
  hN : N < 100000000000
  hA : 1248 ≤ A
  hB : A + 200000 * 4 ≤ B
  hC : B + 200000 * 4 ≤ Cb
  hD : Cb + 200000 * 8 ≤ D
  hDv : D + 400000 < 4194192
  hpc : pc < 200000

theorem compact_keep_small (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (A B Cb D N v p pc s k ns d lk ce q : Nat) (hx : CRegs x A B Cb D N v p pc s)
    (hb : CBounds A B Cb D N v p pc s)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h17 : x.get 17 = bv k) (h16 : x.get 16 = bv ns)
    (hk : k < s) (hns : ns ≤ k) (hdv : d ≤ v)
    (hdp : d * p ≤ v) (hce : pc ≤ ce) (hce' : ce < 200000) (hlk : q ≤ lk) (hlk' : lk < 100000000000)
    (hq : q < 100000000000) (hidx : ce - pc < 200000)
    (hR : readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (D + d) 1 = some (BitVec.ofNat 8 0))
    (hL : readBytes mem (k * 8 + Cb) 8 = some (bv lk))
    (hSm : readBytes mem (A + d * p / 2 * 4) 4 = some (BitVec.ofNat 32 ce))
    (hL2 : readBytes mem (Cb + (ce - pc) * 8) 8 = some (bv q)) :
    ∃ y, run 32 ⟨x, bv 684, mem, [], out, .running⟩ =
      ⟨y, bv 684, wr (wr mem (Cb + ns * 8) (bv (lk - q + pc)) 8) (B + ns * 4) (bv d) 4, [], out,
        .running⟩ ∧ y.get 16 = bv (ns + 1) ∧ y.get 17 = bv (k + 1) ∧
      (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  obtain ⟨h9, h21, h24, h12, h8, h18, h20, h14, h19⟩ := hx
  obtain ⟨hs, hv, hpv, hN, hA, hB, hC, hD, hDv, hpc⟩ := hb
  refine ⟨((((((((((((((((((((((((((x.set 15 (bv k)).set 15 (bv (k * 4))).set 15 (bv (B + k * 4))).set 6 (bv d)).set 15
    (bv (D + d))).set 15 0#64).set 15 (bv (d * p))).set 28 (bv (k * 8))).set 28 (bv (k * 8 + Cb))).set
    28 (bv lk)).set 15 (bv (d * p / 2))).set 15 (bv (d * p / 2 * 4))).set 15 (bv (A + d * p / 2 * 4))).set
    15 (bv ce)).set 15 (bv (ce - pc))).set 15 (bv ((ce - pc) * 8))).set 15 (bv (Cb + (ce - pc) * 8))).set
    30 (bv q)).set 29 (bv (ns * 8))).set 28 (bv (lk - q))).set 15 (bv (ns * 4))).set 29 (bv (Cb + ns * 8))).set
    28 (bv (lk - q + pc))).set 15 (bv (B + ns * 4))).set 16 (bv (ns + 1))).set 17 (bv (k + 1))).set 0 872#64,
    ?_, by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec

theorem compact_keep_large (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (A B Cb D N v p pc s k ns d lk q : Nat) (hx : CRegs x A B Cb D N v p pc s)
    (hb : CBounds A B Cb D N v p pc s)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h17 : x.get 17 = bv k) (h16 : x.get 16 = bv ns)
    (hk : k < s) (hns : ns ≤ k) (hdv : d ≤ v)
    (hdp : v < d * p) (hdp' : d * p < 100000000000) (hNd : 1 ≤ N / (d * p)) (hNd' : N / (d * p) ≤ v)
    (hlk : q ≤ lk) (hlk' : lk < 100000000000) (hq : q < 2147483648)
    (hR : readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (D + d) 1 = some (BitVec.ofNat 8 0))
    (hL : readBytes mem (k * 8 + Cb) 8 = some (bv lk))
    (hSm : readBytes mem (A + (N / (d * p) - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 q)) :
    ∃ y, run 31 ⟨x, bv 684, mem, [], out, .running⟩ =
      ⟨y, bv 684, wr (wr mem (Cb + ns * 8) (bv (lk - q + pc)) 8) (B + ns * 4) (bv d) 4, [], out,
        .running⟩ ∧ y.get 16 = bv (ns + 1) ∧ y.get 17 = bv (k + 1) ∧
      (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  obtain ⟨h9, h21, h24, h12, h8, h18, h20, h14, h19⟩ := hx
  obtain ⟨hs, hv, hpv, hN, hA, hB, hC, hD, hDv, hpc⟩ := hb
  refine ⟨(((((((((((((((((((((((((x.set 15 (bv k)).set 15 (bv (k * 4))).set 15 (bv (B + k * 4))).set
    6 (bv d)).set 15 (bv (D + d))).set 15 0#64).set 15 (bv (d * p))).set 28 (bv (k * 8))).set
    28 (bv (k * 8 + Cb))).set 28 (bv lk)).set 15 (bv (N / (d * p)))).set 15 (bv (N / (d * p) - 1))).set
    15 (bv ((N / (d * p) - 1) / 2))).set 15 (bv ((N / (d * p) - 1) / 2 * 4))).set
    15 (bv (A + (N / (d * p) - 1) / 2 * 4))).set 30 (bv q)).set 0 900#64).set 29 (bv (ns * 8))).set
    28 (bv (lk - q))).set 15 (bv (ns * 4))).set 29 (bv (Cb + ns * 8))).set 28 (bv (lk - q + pc))).set
    15 (bv (B + ns * 4))).set 16 (bv (ns + 1))).set 17 (bv (k + 1))).set 0 872#64,
    ?_, by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec

theorem compact_skip (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (A B Cb D N v p pc s k ns d : Nat) (hx : CRegs x A B Cb D N v p pc s)
    (hb : CBounds A B Cb D N v p pc s)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h17 : x.get 17 = bv k) (h16 : x.get 16 = bv ns)
    (hk : k < s) (hdv : d ≤ v)
    (hR : readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (D + d) 1 = some (BitVec.ofNat 8 1)) :
    ∃ y, run 10 ⟨x, bv 684, mem, [], out, .running⟩ = ⟨y, bv 684, mem, [], out, .running⟩ ∧
      y.get 16 = bv ns ∧ y.get 17 = bv (k + 1) ∧ (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  obtain ⟨h9, h21, h24, h12, h8, h18, h20, h14, h19⟩ := hx
  obtain ⟨hs, hv, hpv, hN, hA, hB, hC, hD, hDv, hpc⟩ := hb
  refine ⟨(((((((x.set 15 (bv k)).set 15 (bv (k * 4))).set 15 (bv (B + k * 4))).set 6 (bv d)).set 15
    (bv (D + d))).set 15 1#64).set 17 (bv (k + 1))).set 0 872#64, ?_, by simp [Regs.get_set, h16],
    by simp [Regs.get_set], by frame_tac⟩
  gexec

theorem compact_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (A B Cb D N v p pc s k : Nat) (hx : CRegs x A B Cb D N v p pc s)
    (hb : CBounds A B Cb D N v p pc s)
    (hmem : Prefix image mem 1236) (h17 : x.get 17 = bv k) (hk : s ≤ k) (hk' : k < 200000) :
    ∃ y, run 2 ⟨x, bv 684, mem, [], out, .running⟩ = ⟨y, bv 692, mem, [], out, .running⟩ ∧
      y.get 16 = x.get 16 ∧ (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  obtain ⟨h9, h21, h24, h12, h8, h18, h20, h14, h19⟩ := hx
  obtain ⟨hs, hv, hpv, hN, hA, hB, hC, hD, hDv, hpc⟩ := hb
  refine ⟨x.set 15 (bv k), ?_, by simp [Regs.get_set], by frame_tac⟩
  gexec

theorem filter_take_succ (L : List Nat) (keep : Nat → Bool) (k d : Nat) (h : L[k]? = some d) :
    (L.take (k + 1)).filter keep = (L.take k).filter keep ++ (if keep d then [d] else []) := by
  rw [List.take_add_one, h, List.filter_append]
  simp only [Option.toList_some, List.filter_cons, List.filter_nil]

theorem sorted_idx {L : List Nat} (hs : L.Pairwise (· < ·)) {i j a b : Nat} (hi : L[i]? = some a)
    (hj : L[j]? = some b) (hab : a < b) : i < j := by
  apply Decidable.byContradiction
  intro hc
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
  by_cases hij : i = j
  · subst hij; omega
  · have := List.pairwise_iff_getElem.mp hs j i hj' hi' (by omega)
    omega

/-- The facts about the compacted list the loop relies on. -/
structure CMath (L : List Nat) (keep : Nat → Bool) (oldv newv quot Sm Sk : Nat → Nat)
    (N v p pc : Nat) : Prop where
  bound : ∀ d ∈ L, 1 ≤ d ∧ d ≤ v
  sorted : L.Pairwise (· < ·)
  skip : ∀ d ∈ L, Sk d = if keep d then 0 else 1
  small : ∀ d ∈ L, keep d = true → d * p ≤ v →
    pc ≤ Sm (d * p / 2) ∧ d * p / 2 ≤ (v - 1) / 2 ∧ L[Sm (d * p / 2) - pc]? = some (d * p) ∧
      oldv (d * p) = quot d
  large : ∀ d ∈ L, keep d = true → v < d * p →
    d * p < 100000000000 ∧ 1 ≤ N / (d * p) ∧ N / (d * p) ≤ v ∧ Sm ((N / (d * p) - 1) / 2) = quot d
  new : ∀ d ∈ L, keep d = true → quot d ≤ oldv d ∧ newv d = oldv d - quot d + pc
  oldb : ∀ d ∈ L, oldv d < 100000000000
  quotb : ∀ d ∈ L, quot d < 2147483648
  smb : ∀ i, i ≤ (v - 1) / 2 → Sm i < 200000
  p3 : 3 ≤ p

theorem compact_loop (L : List Nat) (keep : Nat → Bool) (oldv newv quot Sm Sk : Nat → Nat)
    (A B Cb D N v p pc s0 : Nat) (hm : CMath L keep oldv newv quot Sm Sk N v p pc)
    (hs0 : s0 = (v + 1) / 2) (hLs : L.length ≤ s0)
    (hAB : A + s0 * 4 ≤ B) (hBC : B + s0 * 4 ≤ Cb) (hCD : Cb + s0 * 8 ≤ D)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (k ns : Nat) (R Lg : Nat → Nat)
    (hx : CRegs x A B Cb D N v p pc L.length) (hb : CBounds A B Cb D N v p pc L.length)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h17 : x.get 17 = bv k) (h16 : x.get 16 = bv ns) (hk : k ≤ L.length)
    (hns : ns = ((L.take k).filter keep).length)
    (hRA : Arr32 mem B L.length R) (hLA : Arr64 mem Cb L.length Lg)
    (hSmA : Arr32 mem A s0 Sm) (hSkA : Arr8 mem D (v + 1) Sk)
    (hnewI : ∀ j d, ((L.take k).filter keep)[j]? = some d → R j = d ∧ Lg j = newv d)
    (holdI : ∀ j d, k ≤ j → L[j]? = some d → R j = d ∧ Lg j = oldv d) :
    ∃ n y mem', run n ⟨x, bv 684, mem, [], out, .running⟩ = ⟨y, bv 692, mem', [], out, .running⟩ ∧
      Same mem mem' B (Cb + L.length * 8) ∧
      Arr32 mem' B (L.filter keep).length (fun j => (L.filter keep).getD j 0) ∧
      Arr64 mem' Cb (L.filter keep).length (fun j => newv ((L.filter keep).getD j 0)) ∧
      y.get 16 = bv (L.filter keep).length ∧ (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  have hcb := hb
  obtain ⟨hs, hv, hpv, hN, hA, hB, hC, hD, hDv, hpc⟩ := hcb
  by_cases hkL : k < L.length
  · obtain ⟨d, hd⟩ : ∃ d, L[k]? = some d := ⟨L[k], List.getElem?_eq_getElem hkL⟩
    have hdL : d ∈ L := List.mem_of_getElem? hd
    obtain ⟨hRk, hLgk⟩ := holdI k d (Nat.le_refl k) hd
    have hd1 := hm.bound d hdL
    have hR : readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 d) := by
      have := hRA k hkL; rwa [hRk] at this
    have hnsk : ns ≤ k := by
      rw [hns]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
    have hfts := filter_take_succ L keep k d hd
    by_cases hkeep : keep d = true
    · have hS : readBytes mem (D + d) 1 = some (BitVec.ofNat 8 0) := by
        have := hSkA d (by omega); rwa [hm.skip d hdL, if_pos hkeep] at this
      have hL : readBytes mem (k * 8 + Cb) 8 = some (bv (oldv d)) := by
        have := hLA k hkL; rwa [hLgk, Nat.add_comm] at this
      obtain ⟨hqo, hnv⟩ := hm.new d hdL hkeep
      have hob := hm.oldb d hdL
      have hqb := hm.quotb d hdL
      obtain ⟨n1, y, hr, hy16, hy17, hfy⟩ : ∃ n1 y, run n1 ⟨x, bv 684, mem, [], out, .running⟩ =
          ⟨y, bv 684, wr (wr mem (Cb + ns * 8) (bv (newv d)) 8) (B + ns * 4) (bv d) 4, [], out,
            .running⟩ ∧ y.get 16 = bv (ns + 1) ∧ y.get 17 = bv (k + 1) ∧
          (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
        rw [hnv]
        by_cases hdp : d * p ≤ v
        · obtain ⟨hpc1, hidx1, hidx, hov⟩ := hm.small d hdL hkeep hdp
          have hkidx : k < Sm (d * p / 2) - pc := sorted_idx hm.sorted hd hidx
            (by have := Nat.mul_le_mul_left d hm.p3; omega)
          obtain ⟨_, hLg2⟩ := holdI _ _ (by omega) hidx
          have hidxL : Sm (d * p / 2) - pc < L.length := (List.getElem?_eq_some_iff.mp hidx).1
          have hSmr : readBytes mem (A + d * p / 2 * 4) 4 = some (BitVec.ofNat 32 (Sm (d * p / 2))) :=
            hSmA _ (by omega)
          have hL2 : readBytes mem (Cb + (Sm (d * p / 2) - pc) * 8) 8 = some (bv (quot d)) := by
            have := hLA _ hidxL; rwa [hLg2, hov] at this
          have := hm.smb _ hidx1
          exact ⟨32, compact_keep_small x mem out A B Cb D N v p pc L.length k ns d (oldv d)
            (Sm (d * p / 2)) (quot d) hx hb hmem hsz h17 h16 hkL hnsk hd1.2 hdp hpc1 (by omega) hqo hob
            (by omega) (by omega) hR hS hL hSmr hL2⟩
        · obtain ⟨hdpb, hN1, hN2, hq⟩ := hm.large d hdL hkeep (by omega)
          have hSmr : readBytes mem (A + (N / (d * p) - 1) / 2 * 4) 4 =
              some (BitVec.ofNat 32 (quot d)) := by
            have := hSmA ((N / (d * p) - 1) / 2) (by omega); rwa [hq] at this
          exact ⟨31, compact_keep_large x mem out A B Cb D N v p pc L.length k ns d (oldv d) (quot d)
            hx hb hmem hsz h17 h16 hkL hnsk hd1.2 (by omega) hdpb hN1 hN2 hqo hob hqb hR hS hL hSmr⟩
      rw [if_pos hkeep] at hfts
      have hw1 : Cb + ns * 8 + 8 ≤ mem.size := by omega
      have hw2 : B + ns * 4 + 4 ≤ (wr mem (Cb + ns * 8) (bv (newv d)) 8).size := by simp; omega
      have hRA' := (hRA.congr (wr_frame mem _ (bv (newv d)) 8 B (B + L.length * 4) hw1 (by omega))).wr
        (by simp; omega) ns d (by omega)
      have hLA' := (hLA.wr (by omega) ns (newv d) (by omega)).congr
        (wr_frame _ (B + ns * 4) (bv d) 4 Cb (Cb + L.length * 8) hw2 (by omega))
      have hSmA' := (hSmA.congr (wr_frame mem _ (bv (newv d)) 8 A (A + s0 * 4) hw1 (by omega))).congr
        (wr_frame _ (B + ns * 4) (bv d) 4 A (A + s0 * 4) hw2 (by omega))
      have hSkA' := (hSkA.congr (wr_frame mem _ (bv (newv d)) 8 D (D + (v + 1)) hw1 (by omega))).congr
        (wr_frame _ (B + ns * 4) (bv d) 4 D (D + (v + 1)) hw2 (by omega))
      have hpre := prefix_wr _ (bv d) _ (prefix_wr _ _ _ hmem (by omega) (by omega)) hw2 (by omega)
      obtain ⟨n, z, mem', hr2, hsame, h1, h2, h3, hfz⟩ := compact_loop L keep oldv newv quot Sm Sk
        A B Cb D N v p pc s0 hm hs0 hLs hAB hBC hCD y _ out (k + 1) (ns + 1) (upd R ns d)
        (upd Lg ns (newv d)) (hx.frame hfy) hb hpre (by simp [hsz]) hy17 hy16 (by omega)
        (by rw [hfts, List.length_append, ← hns]; rfl) hRA' hLA' hSmA' hSkA'
        (fun j d' h => by
          rw [hfts] at h
          by_cases hj : j < ns
          · rw [List.getElem?_append_left (by omega)] at h
            rw [upd_other _ _ _ _ (by omega), upd_other _ _ _ _ (by omega)]
            exact hnewI j d' h
          · rw [List.getElem?_append_right (by omega), ← hns] at h
            have hj' : j - ns = 0 := by
              rcases hh : j - ns with _ | m
              · rfl
              · rw [hh] at h; simp at h
            rw [hj'] at h
            simp at h; subst h
            rw [show j = ns by omega]; simp)
        (fun j d' hj h => by
          rw [upd_other _ _ _ _ (by omega), upd_other _ _ _ _ (by omega)]
          exact holdI j d' (by omega) h)
      refine ⟨n1 + n, z, mem', by rw [run_add, hr, hr2], ?_, h1, h2, h3,
        fun r hr => by rw [hfz r hr, hfy r hr]⟩
      exact ((Same.wr mem _ _ 8 B (Cb + L.length * 8) hw1 (by omega) (by omega)).trans
        (Same.wr _ _ _ 4 B (Cb + L.length * 8) hw2 (by omega) (by omega))).trans hsame
    · have hS : readBytes mem (D + d) 1 = some (BitVec.ofNat 8 1) := by
        have := hSkA d (by omega); rwa [hm.skip d hdL, if_neg hkeep] at this
      obtain ⟨y, hr, hy16, hy17, hfy⟩ := compact_skip x mem out A B Cb D N v p pc L.length k ns d
        hx hb hmem hsz h17 h16 hkL (by omega) hR hS
      rw [if_neg hkeep, List.append_nil] at hfts
      obtain ⟨n, z, mem', hr2, hsame, h1, h2, h3, hfz⟩ := compact_loop L keep oldv newv quot Sm Sk
        A B Cb D N v p pc s0 hm hs0 hLs hAB hBC hCD y mem out (k + 1) ns R Lg (hx.frame hfy) hb hmem
        hsz hy17 hy16 (by omega) (by rw [hfts]; exact hns) hRA hLA hSmA hSkA
        (fun j d' h => hnewI j d' (by rw [← hfts]; exact h))
        (fun j d' hj h => holdI j d' (by omega) h)
      exact ⟨10 + n, z, mem', by rw [run_add, hr, hr2], hsame, h1, h2, h3,
        fun r hr => by rw [hfz r hr, hfy r hr]⟩
  · have hkL' : k = L.length := by omega
    obtain ⟨y, hr, hy16, hfy⟩ := compact_exit x mem out A B Cb D N v p pc L.length k hx hb hmem h17
      (by omega) (by omega)
    subst hkL'
    rw [List.take_length] at hns hnewI
    refine ⟨2, y, mem, hr, Same.refl _ _ _, ?_, ?_, by rw [hy16, h16, hns], hfy⟩
    · intro j hj
      have h := hRA j (by have := List.length_filter_le keep L; omega)
      rw [(hnewI j _ (List.getElem?_eq_getElem hj)).1] at h
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h
    · intro j hj
      have h := hLA j (by have := List.length_filter_le keep L; omega)
      rw [(hnewI j _ (List.getElem?_eq_getElem hj)).2] at h
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h
termination_by L.length - k

end TinyFive.GrumpyBinary
