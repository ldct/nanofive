import ZjyBinary.Mark

/-! The compaction loop of `calc(p)` at 108: keep the entries `rough[i]` not marked in `skip`,
with their updated `large` values. Unlike grumpygordon's, it reads `R`, `V`, `C`, `n` and the
table pointers from `pi`'s stack frame through the closure on every iteration. -/
namespace TinyFive.ZjyBinary
open SieveMemory LucyMath GrumpyBinary

local notation "bv" => BitVec.ofNat 64

/-- `pi`'s stack frame (at `sp = 4194096`) as `calc` reads it: `n` at 8, `R`, `C`, `V` at 20, 24,
28, the four table pointers at 32 to 56, and the closure at 64. -/
structure Slots (mem : Array (BitVec 8)) (N v pc s A B D Cb : Nat) : Prop where
  n : readBytes mem 4194104 8 = some (bv N)
  R : readBytes mem 4194116 4 = some (BitVec.ofNat 32 v)
  C : readBytes mem 4194120 4 = some (BitVec.ofNat 32 pc)
  V : readBytes mem 4194124 4 = some (BitVec.ofNat 32 s)
  sm : readBytes mem 4194128 8 = some (bv A)
  ro : readBytes mem 4194136 8 = some (bv B)
  sk : readBytes mem 4194144 8 = some (bv D)
  la : readBytes mem 4194152 8 = some (bv Cb)
  k0 : readBytes mem 4194160 8 = some (bv 4194144)
  k1 : readBytes mem 4194168 8 = some (bv 4194116)
  k2 : readBytes mem 4194176 8 = some (bv 4194124)
  k3 : readBytes mem 4194184 8 = some (bv 4194136)
  k4 : readBytes mem 4194192 8 = some (bv 4194152)
  k5 : readBytes mem 4194200 8 = some (bv 4194128)
  k6 : readBytes mem 4194208 8 = some (bv 4194120)
  k7 : readBytes mem 4194216 8 = some (bv 4194104)

theorem Slots.same {mem mem' : Array (BitVec 8)} {N v pc s A B D Cb lo hi : Nat}
    (h : Slots mem N v pc s A B D Cb) (hs : Same mem mem' lo hi) (hhi : hi ≤ 4194104) :
    Slots mem' N v pc s A B D Cb :=
  ⟨hs.read h.n (by omega), hs.read h.R (by omega), hs.read h.C (by omega), hs.read h.V (by omega),
   hs.read h.sm (by omega), hs.read h.ro (by omega), hs.read h.sk (by omega), hs.read h.la (by omega),
   hs.read h.k0 (by omega), hs.read h.k1 (by omega), hs.read h.k2 (by omega), hs.read h.k3 (by omega),
   hs.read h.k4 (by omega), hs.read h.k5 (by omega), hs.read h.k6 (by omega), hs.read h.k7 (by omega)⟩

/-- Registers the compaction loop reads but does not write. -/
structure CRegs (x : Regs 64) (p D : Nat) : Prop where
  h10 : x.get 10 = bv 4194160
  h11 : x.get 11 = bv p
  h31 : x.get 31 = bv D
  h30 : x.get 30 = bv 4194116
  h7 : x.get 7 = bv 4194124
  h28 : x.get 28 = bv 4194120

abbrev cfr : List Reg := [5, 6, 8, 12, 13, 14, 15, 16, 17, 29]

theorem CRegs.frame {x y : Regs 64} {p D : Nat} (h : CRegs x p D)
    (hf : ∀ r : Reg, r ∉ cfr → y.get r = x.get r) : CRegs y p D :=
  ⟨by rw [hf 10 (by decide), h.h10], by rw [hf 11 (by decide), h.h11], by rw [hf 31 (by decide), h.h31],
   by rw [hf 30 (by decide), h.h30], by rw [hf 7 (by decide), h.h7], by rw [hf 28 (by decide), h.h28]⟩

/-- The address bounds of the compaction loop. -/
structure CBounds (A B Cb D N v p pc s : Nat) : Prop where
  hs : s < 200000
  hv : v < 400000
  hpv : p ≤ v
  hN : N < 100000000000
  hA : 1520 ≤ A
  hB : A + s * 4 ≤ B
  hD : B + s * 4 ≤ D
  hC : D + v + 1 ≤ Cb
  hCe : Cb + s * 8 ≤ 4194000
  hpc : pc < 200000

theorem compact_keep_small (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (A B Cb D N v p pc s k ns d lk ce q : Nat) (hx : CRegs x p D)
    (hb : CBounds A B Cb D N v p pc s) (hsl : Slots mem N v pc s A B D Cb)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h16 : x.get 16 = bv k) (h12 : x.get 12 = bv ns)
    (hk : k < s) (hns : ns ≤ k) (hdv : d ≤ v)
    (hdp : d * p ≤ v) (hce : pc ≤ ce) (hce' : ce < 400000) (hlk : q ≤ lk) (hlk' : lk < 100000000000)
    (hq : q < 100000000000) (hidx : ce - pc < 400000)
    (hR : readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (D + d) 1 = some (BitVec.ofNat 8 0))
    (hL : readBytes mem (Cb + k * 8) 8 = some (bv lk))
    (hSm : readBytes mem (A + d * p / 2 * 4) 4 = some (BitVec.ofNat 32 ce))
    (hL2 : readBytes mem (Cb + (ce - pc) * 8) 8 = some (bv q)) :
    ∃ y, run 41 ⟨x, bv 108, mem, [], out, .running⟩ =
      ⟨y, bv 108, wr (wr mem (Cb + ns * 8) (bv (lk - q + pc)) 8) (B + ns * 4) (bv d) 4, [], out,
        .running⟩ ∧ y.get 12 = bv (ns + 1) ∧ y.get 16 = bv (k + 1) ∧
      (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  obtain ⟨h10, h11, h31, h30, h7, h28⟩ := hx
  obtain ⟨hs, hv, hpv, hN, hA, hB, hD, hC, hCe, hpc⟩ := hb
  obtain ⟨sn, sR, sC, sV, ssm, sro, ssk, sla, k0, k1, k2, k3, k4, k5, k6, k7⟩ := hsl
  refine ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

theorem compact_keep_large (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (A B Cb D N v p pc s k ns d lk q : Nat) (hx : CRegs x p D)
    (hb : CBounds A B Cb D N v p pc s) (hsl : Slots mem N v pc s A B D Cb)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h16 : x.get 16 = bv k) (h12 : x.get 12 = bv ns)
    (hk : k < s) (hns : ns ≤ k) (hdv : d ≤ v)
    (hdp : v < d * p) (hdp' : d * p < 100000000000) (hNd : 1 ≤ N / (d * p)) (hNd' : N / (d * p) ≤ v)
    (hlk : q ≤ lk) (hlk' : lk < 100000000000) (hq : q < 2147483648)
    (hR : readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (D + d) 1 = some (BitVec.ofNat 8 0))
    (hL : readBytes mem (Cb + k * 8) 8 = some (bv lk))
    (hSm : readBytes mem (A + (N / (d * p) - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 q)) :
    ∃ y, run 42 ⟨x, bv 108, mem, [], out, .running⟩ =
      ⟨y, bv 108, wr (wr mem (Cb + ns * 8) (bv (lk - q + pc)) 8) (B + ns * 4) (bv d) 4, [], out,
        .running⟩ ∧ y.get 12 = bv (ns + 1) ∧ y.get 16 = bv (k + 1) ∧
      (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  obtain ⟨h10, h11, h31, h30, h7, h28⟩ := hx
  obtain ⟨hs, hv, hpv, hN, hA, hB, hD, hC, hCe, hpc⟩ := hb
  obtain ⟨sn, sR, sC, sV, ssm, sro, ssk, sla, k0, k1, k2, k3, k4, k5, k6, k7⟩ := hsl
  refine ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

theorem compact_skip (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (A B Cb D N v p pc s k ns d : Nat) (hx : CRegs x p D)
    (hb : CBounds A B Cb D N v p pc s) (hsl : Slots mem N v pc s A B D Cb)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h16 : x.get 16 = bv k) (h12 : x.get 12 = bv ns)
    (hk : k < s) (hdv : d ≤ v)
    (hR : readBytes mem (B + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (D + d) 1 = some (BitVec.ofNat 8 1)) :
    ∃ y, run 13 ⟨x, bv 108, mem, [], out, .running⟩ = ⟨y, bv 108, mem, [], out, .running⟩ ∧
      y.get 12 = bv ns ∧ y.get 16 = bv (k + 1) ∧ (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  obtain ⟨h10, h11, h31, h30, h7, h28⟩ := hx
  obtain ⟨hs, hv, hpv, hN, hA, hB, hD, hC, hCe, hpc⟩ := hb
  obtain ⟨sn, sR, sC, sV, ssm, sro, ssk, sla, k0, k1, k2, k3, k4, k5, k6, k7⟩ := hsl
  refine ⟨_, by zexec; rfl, by simp [Regs.get_set, h12], by simp [Regs.get_set], by frame_tac⟩

theorem compact_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (A B Cb D N v p pc s k : Nat) (hx : CRegs x p D)
    (hb : CBounds A B Cb D N v p pc s) (hsl : Slots mem N v pc s A B D Cb)
    (hmem : Prefix image mem 1480) (h16 : x.get 16 = bv k) (hk : s ≤ k) (hk' : k < 200000) :
    ∃ y, run 3 ⟨x, bv 108, mem, [], out, .running⟩ = ⟨y, bv 120, mem, [], out, .running⟩ ∧
      y.get 12 = x.get 12 ∧ (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  obtain ⟨h10, h11, h31, h30, h7, h28⟩ := hx
  obtain ⟨hs, hv, hpv, hN, hA, hB, hD, hC, hCe, hpc⟩ := hb
  obtain ⟨sn, sR, sC, sV, ssm, sro, ssk, sla, k0, k1, k2, k3, k4, k5, k6, k7⟩ := hsl
  refine ⟨_, by zexec; rfl, by simp [Regs.get_set], by frame_tac⟩

theorem compact_loop (L : List Nat) (keep : Nat → Bool) (oldv newv quot Sm Sk : Nat → Nat)
    (A B Cb D N v p pc s0 : Nat) (hm : CMath L keep oldv newv quot Sm Sk N v p pc)
    (hs0 : s0 = (v + 1) / 2) (hLs : L.length ≤ s0)
    (hAB : A + s0 * 4 ≤ B) (hBD : B + s0 * 4 ≤ D) (hDC : D + v + 1 ≤ Cb) (hCe : Cb + s0 * 8 ≤ 4194000)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (k ns : Nat) (R Lg : Nat → Nat)
    (hx : CRegs x p D) (hb : CBounds A B Cb D N v p pc L.length)
    (hsl : Slots mem N v pc L.length A B D Cb)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h16 : x.get 16 = bv k) (h12 : x.get 12 = bv ns) (hk : k ≤ L.length)
    (hns : ns = ((L.take k).filter keep).length)
    (hRA : Arr32 mem B L.length R) (hLA : Arr64 mem Cb L.length Lg)
    (hSmA : Arr32 mem A s0 Sm) (hSkA : Arr8 mem D (v + 1) Sk)
    (hnewI : ∀ j d, ((L.take k).filter keep)[j]? = some d → R j = d ∧ Lg j = newv d)
    (holdI : ∀ j d, k ≤ j → L[j]? = some d → R j = d ∧ Lg j = oldv d) :
    ∃ n y mem', run n ⟨x, bv 108, mem, [], out, .running⟩ = ⟨y, bv 120, mem', [], out, .running⟩ ∧
      Same mem mem' B (Cb + L.length * 8) ∧
      Arr32 mem' B (L.filter keep).length (fun j => (L.filter keep).getD j 0) ∧
      Arr64 mem' Cb (L.filter keep).length (fun j => newv ((L.filter keep).getD j 0)) ∧
      Arr8 mem' D (v + 1) Sk ∧
      y.get 12 = bv (L.filter keep).length ∧ (∀ r : Reg, r ∉ cfr → y.get r = x.get r) := by
  have hcb := hb
  obtain ⟨hs, hv, hpv, hN, hA, hB, hD, hC, hCe', hpc⟩ := hcb
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
      have hL : readBytes mem (Cb + k * 8) 8 = some (bv (oldv d)) := by
        have := hLA k hkL; rwa [hLgk] at this
      obtain ⟨hqo, hnv⟩ := hm.new d hdL hkeep
      have hob := hm.oldb d hdL
      have hqb := hm.quotb d hdL
      obtain ⟨n1, y, hr, hy12, hy16, hfy⟩ : ∃ n1 y, run n1 ⟨x, bv 108, mem, [], out, .running⟩ =
          ⟨y, bv 108, wr (wr mem (Cb + ns * 8) (bv (newv d)) 8) (B + ns * 4) (bv d) 4, [], out,
            .running⟩ ∧ y.get 12 = bv (ns + 1) ∧ y.get 16 = bv (k + 1) ∧
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
          exact ⟨41, compact_keep_small x mem out A B Cb D N v p pc L.length k ns d (oldv d)
            (Sm (d * p / 2)) (quot d) hx hb hsl hmem hsz h16 h12 hkL hnsk hd1.2 hdp hpc1 (by omega) hqo hob
            (by omega) (by omega) hR hS hL hSmr hL2⟩
        · obtain ⟨hdpb, hN1, hN2, hq⟩ := hm.large d hdL hkeep (by omega)
          have hSmr : readBytes mem (A + (N / (d * p) - 1) / 2 * 4) 4 =
              some (BitVec.ofNat 32 (quot d)) := by
            have := hSmA ((N / (d * p) - 1) / 2) (by omega); rwa [hq] at this
          have hqb' : quot d < 2147483648 := by
            rw [← hq]; have := hm.smb ((N / (d * p) - 1) / 2) (by omega); omega
          exact ⟨42, compact_keep_large x mem out A B Cb D N v p pc L.length k ns d (oldv d) (quot d)
            hx hb hsl hmem hsz h16 h12 hkL hnsk hd1.2 (by omega) hdpb hN1 hN2 hqo hob hqb' hR hS hL hSmr⟩
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
      have hS2 := (Same.wr mem _ (bv (newv d)) 8 B (Cb + L.length * 8) hw1 (by omega) (by omega)).trans
        (Same.wr _ _ (bv d) 4 B (Cb + L.length * 8) hw2 (by omega) (by omega))
      obtain ⟨n, z, mem', hr2, hsame, h1, h2, h0, h3, hfz⟩ := compact_loop L keep oldv newv quot Sm Sk
        A B Cb D N v p pc s0 hm hs0 hLs hAB hBD hDC hCe y _ out (k + 1) (ns + 1) (upd R ns d)
        (upd Lg ns (newv d)) (hx.frame hfy) hb (hsl.same hS2 (by omega)) hpre (by simp [hsz]) hy16 hy12 (by omega)
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
      exact ⟨n1 + n, z, mem', by rw [run_add, hr, hr2], hS2.trans hsame, h1, h2, h0, h3,
        fun r hr => by rw [hfz r hr, hfy r hr]⟩
    · have hS : readBytes mem (D + d) 1 = some (BitVec.ofNat 8 1) := by
        have := hSkA d (by omega); rwa [hm.skip d hdL, if_neg hkeep] at this
      obtain ⟨y, hr, hy12, hy16, hfy⟩ := compact_skip x mem out A B Cb D N v p pc L.length k ns d
        hx hb hsl hmem hsz h16 h12 hkL (by omega) hR hS
      rw [if_neg hkeep, List.append_nil] at hfts
      obtain ⟨n, z, mem', hr2, hsame, h1, h2, h0, h3, hfz⟩ := compact_loop L keep oldv newv quot Sm Sk
        A B Cb D N v p pc s0 hm hs0 hLs hAB hBD hDC hCe y mem out (k + 1) ns R Lg (hx.frame hfy) hb hsl hmem
        hsz hy16 hy12 (by omega) (by rw [hfts]; exact hns) hRA hLA hSmA hSkA
        (fun j d' h => hnewI j d' (by rw [← hfts]; exact h))
        (fun j d' hj h => holdI j d' (by omega) h)
      exact ⟨13 + n, z, mem', by rw [run_add, hr, hr2], hsame, h1, h2, h0, h3,
        fun r hr => by rw [hfz r hr, hfy r hr]⟩
  · have hkL' : k = L.length := by omega
    obtain ⟨y, hr, hy12, hfy⟩ := compact_exit x mem out A B Cb D N v p pc L.length k hx hb hsl hmem h16
      (by omega) (by omega)
    subst hkL'
    rw [List.take_length] at hns hnewI
    refine ⟨3, y, mem, hr, Same.refl _ _ _, ?_, ?_, hSkA, by rw [hy12, h12, hns], hfy⟩
    · intro j hj
      have h := hRA j (by have := List.length_filter_le keep L; omega)
      rw [(hnewI j _ (List.getElem?_eq_getElem hj)).1] at h
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h
    · intro j hj
      have h := hLA j (by have := List.length_filter_le keep L; omega)
      rw [(hnewI j _ (List.getElem?_eq_getElem hj)).2] at h
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h
termination_by L.length - k

end TinyFive.ZjyBinary
