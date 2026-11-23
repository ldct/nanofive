import LphaBinary.Mark

/-! The compaction of one sieve round, in two loops: at 932 while `j * p ≤ v`
(`larges[ns] = larges[k] + pc - larges[smalls[j * p / 2] - pc]`), and from the first kept rough
with `j * p > v` on, at 1004 (`larges[ns] = larges[k] + pc - smalls[(invs[k] / p - 1) / 2]`).
`larges` is a `uint32_t` array: its words are the true counts mod `2^32`. -/
namespace TinyFive.LphaBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

set_option linter.unusedVariables false

/-- The registers both loops keep. -/
structure RF (x : Regs 64) (v p pc s : Nat) : Prop where
  x7 : x.get 7 = bv (SM + 1008)
  x28 : x.get 28 = bv (LB - 1504)
  x29 : x.get 29 = bv (SB + 168)
  x9 : x.get 9 = bv v
  x15 : x.get 15 = bv p
  x14 : x.get 14 = bv pc
  x8 : x.get 8 = bv s
  x2 : x.get 2 = bv 715648

/-- The registers the compaction may change. -/
abbrev kfr : List Reg := [5, 6, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 30]

theorem RF.frame {x y : Regs 64} {v p pc s : Nat} (h : RF x v p pc s)
    (hf : ∀ r : Reg, r ∉ kfr → y.get r = x.get r) : RF y v p pc s :=
  ⟨by rw [hf 7 (by decide), h.x7], by rw [hf 28 (by decide), h.x28], by rw [hf 29 (by decide), h.x29],
   by rw [hf 9 (by decide), h.x9], by rw [hf 15 (by decide), h.x15], by rw [hf 14 (by decide), h.x14],
   by rw [hf 8 (by decide), h.x8], by rw [hf 2 (by decide), h.x2]⟩

theorem frame_kfr {x y : Regs 64} {l : List Reg} (hl : ∀ r, r ∈ l → r ∈ kfr)
    (hf : ∀ r : Reg, r ∉ l → y.get r = x.get r) : ∀ r : Reg, r ∉ kfr → y.get r = x.get r :=
  fun r hr => hf r (fun h => hr (hl r h))

/-- 872 → 932: the loop pointers, `k = ns = 0`. -/
theorem compact_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1536) (h2 : x.get 2 = bv 715648) (h11 : x.get 11 = bv LB)
    (h12 : x.get 12 = bv RB) (h13 : x.get 13 = bv IB) :
    ∃ y, run 15 ⟨x, bv 872, mem, [], out, .running⟩ = ⟨y, bv 932, mem, [], out, .running⟩ ∧
      y.get 21 = bv (RB + 0 * 4) ∧ y.get 20 = bv (LB + 0 * 4) ∧ y.get 19 = bv (IB + 0 * 8) ∧
      y.get 17 = bv 0 ∧ y.get 16 = bv 0 ∧ y.get 22 = bv (IB - 752) ∧ y.get 23 = bv (RB + 920) ∧
      (∀ r : Reg, r ∉ kfr → y.get r = x.get r) :=
  ⟨_, by lexec; rfl, by rg, by rg, by rg, by rg, by rg, by rg, by rg, by frame_tac⟩

/-- Loop 1, a marked rough: `k++`. -/
theorem k1_skip (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p pc s k ns d : Nat)
    (hx : RF x v p pc s) (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h21 : x.get 21 = bv (RB + k * 4)) (h20 : x.get 20 = bv (LB + k * 4))
    (h19 : x.get 19 = bv (IB + k * 8)) (h17 : x.get 17 = bv k)
    (hk : k < 158114) (hd : d ≤ v) (hv : v < 316228)
    (hR : readBytes mem (RB + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (SM + d) 1 = some (BitVec.ofNat 8 1)) :
    ∃ y, run 11 ⟨x, bv 932, mem, [], out, .running⟩ = ⟨y, bv 932, mem, [], out, .running⟩ ∧
      y.get 17 = bv (k + 1) ∧ y.get 21 = bv (RB + (k + 1) * 4) ∧
      y.get 20 = bv (LB + (k + 1) * 4) ∧ y.get 19 = bv (IB + (k + 1) * 8) ∧
      (∀ r : Reg, r ∉ ([5, 6, 17, 19, 20, 21, 25] : List Reg) → y.get r = x.get r) := by
  have := zext8
  obtain ⟨h7, h28, h29, h9, h15, h14, h8, h2⟩ := hx
  exact ⟨_, by lexec; rfl, by rg, by rg, by rg, by rg, by frame_tac⟩

/-- Loop 1, a kept rough `d` with `p * d ≤ v`. -/
theorem k1_small (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (v p pc s k ns d Smv Lk Q I : Nat) (hx : RF x v p pc s)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h21 : x.get 21 = bv (RB + k * 4)) (h20 : x.get 20 = bv (LB + k * 4))
    (h19 : x.get 19 = bv (IB + k * 8)) (h17 : x.get 17 = bv k) (h16 : x.get 16 = bv ns)
    (h22 : x.get 22 = bv (IB - 752)) (h23 : x.get 23 = bv (RB + 920))
    (hk : k < 158114) (hns : ns ≤ k) (hd : d ≤ v) (hv : v < 316228) (hdp : p * d ≤ v)
    (hpc : pc ≤ Smv) (hSmv : Smv < 400000) (hidx : Smv - pc < 158114) (hQ : Q ≤ Lk)
    (hLk : Lk < 100000000000) (hI : I < 100000000000)
    (hR : readBytes mem (RB + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (SM + d) 1 = some (BitVec.ofNat 8 0))
    (hSm : readBytes mem (SB + p * d / 2 * 4) 4 = some (BitVec.ofNat 32 Smv))
    (hL : readBytes mem (LB + k * 4) 4 = some (BitVec.ofNat 32 Lk))
    (hL2 : readBytes mem (LB + (Smv - pc) * 4) 4 = some (BitVec.ofNat 32 Q))
    (hIk : readBytes mem (IB + k * 8) 8 = some (bv I)) :
    ∃ y, run 35 ⟨x, bv 932, mem, [], out, .running⟩ = ⟨y, bv 932,
      wr (wr (wr mem (LB + ns * 4) (bv (Lk + pc - Q)) 4) (IB + ns * 8) (bv I) 8) (RB + ns * 4) (bv d) 4,
      [], out, .running⟩ ∧
      y.get 17 = bv (k + 1) ∧ y.get 16 = bv (ns + 1) ∧ y.get 21 = bv (RB + (k + 1) * 4) ∧
      y.get 20 = bv (LB + (k + 1) * 4) ∧ y.get 19 = bv (IB + (k + 1) * 8) ∧
      (∀ r : Reg, r ∉ ([5, 6, 16, 17, 18, 19, 20, 21, 25, 26, 30] : List Reg) → y.get r = x.get r) := by
  have := zext8
  obtain ⟨h7, h28, h29, h9, h15, h14, h8, h2⟩ := hx
  exact ⟨_, by lexec; rfl, by rg, by rg, by rg, by rg, by rg, by frame_tac⟩

/-- Loop 1 ends at a kept rough `d` with `p * d > v`: on to loop 2 at 1004. -/
theorem k1_break (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p pc s k d : Nat)
    (hx : RF x v p pc s) (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h21 : x.get 21 = bv (RB + k * 4)) (h17 : x.get 17 = bv k)
    (hk : k < 158114) (hd : d ≤ v) (hv : v < 316228) (hdp : v < p * d) (hp : p ≤ 563)
    (hR : readBytes mem (RB + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (SM + d) 1 = some (BitVec.ofNat 8 0)) :
    ∃ y, run 18 ⟨x, bv 932, mem, [], out, .running⟩ = ⟨y, bv 1004, mem, [], out, .running⟩ ∧
      y.get 19 = bv (IB - 752) ∧ y.get 20 = bv (RB + 920) ∧
      (∀ r : Reg, r ∉ ([5, 6, 19, 20, 25, 30] : List Reg) → y.get r = x.get r) := by
  have := zext8
  have : p * d < 1000000000 := by
    have := Nat.mul_le_mul (show p ≤ 563 by omega) (show d ≤ 316228 by omega); omega
  obtain ⟨h7, h28, h29, h9, h15, h14, h8, h2⟩ := hx
  exact ⟨_, by lexec; rfl, by rg, by rg, by frame_tac⟩

/-- Loop 2, a marked rough: `k++`. -/
theorem k2_skip (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p pc s k d : Nat)
    (hx : RF x v p pc s) (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h17 : x.get 17 = bv k) (hks : k < s) (hs : s ≤ 158114) (hd : d ≤ v) (hv : v < 316228)
    (hs8 : readBytes mem 715656 8 = some (bv RB))
    (hR : readBytes mem (RB + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (SM + d) 1 = some (BitVec.ofNat 8 1)) :
    ∃ y, run 12 ⟨x, bv 1004, mem, [], out, .running⟩ = ⟨y, bv 1004, mem, [], out, .running⟩ ∧
      y.get 17 = bv (k + 1) ∧
      (∀ r : Reg, r ∉ ([5, 6, 17, 21] : List Reg) → y.get r = x.get r) := by
  have := zext8
  obtain ⟨h7, h28, h29, h9, h15, h14, h8, h2⟩ := hx
  exact ⟨_, by lexec; rfl, by rg, by frame_tac⟩

/-- Loop 2, a kept rough `d` (then `p * d > v`). -/
theorem k2_keep (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (v p pc s k ns d Lk Q I : Nat) (hx : RF x v p pc s)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h17 : x.get 17 = bv k) (h16 : x.get 16 = bv ns)
    (h19 : x.get 19 = bv (IB - 752)) (h20 : x.get 20 = bv (RB + 920))
    (hks : k < s) (hs : s ≤ 158114) (hns : ns ≤ k) (hd : d ≤ v) (hv : v < 316228) (hp : 3 ≤ p)
    (hp' : p ≤ 563)
    (hI1 : 1 ≤ I / p) (hI2 : (I / p - 1) / 2 < 158114) (hQ : Q ≤ Lk) (hQb : Q < 400000)
    (hLk : Lk < 100000000000) (hI : I < 100000000000)
    (hs8 : readBytes mem 715656 8 = some (bv RB)) (hs16 : readBytes mem 715664 8 = some (bv IB))
    (hs24 : readBytes mem 715672 8 = some (bv LB))
    (hR : readBytes mem (RB + k * 4) 4 = some (BitVec.ofNat 32 d))
    (hS : readBytes mem (SM + d) 1 = some (BitVec.ofNat 8 0))
    (hIk : readBytes mem (IB + k * 8) 8 = some (bv I))
    (hL : readBytes mem (LB + k * 4) 4 = some (BitVec.ofNat 32 Lk))
    (hSm : readBytes mem (SB + (I / p - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 Q)) :
    ∃ y, run 36 ⟨x, bv 1004, mem, [], out, .running⟩ = ⟨y, bv 1004,
      wr (wr (wr mem (RB + ns * 4) (bv d) 4) (LB + ns * 4) (bv (Lk + pc - Q)) 4) (IB + ns * 8) (bv I) 8,
      [], out, .running⟩ ∧
      y.get 17 = bv (k + 1) ∧ y.get 16 = bv (ns + 1) ∧
      (∀ r : Reg, r ∉ ([5, 6, 16, 17, 18, 21, 22, 23, 30] : List Reg) → y.get r = x.get r) := by
  have := zext8
  obtain ⟨h7, h28, h29, h9, h15, h14, h8, h2⟩ := hx
  have hIp := Nat.div_le_self I p
  exact ⟨_, by lexec; rfl, by rg, by rg, by frame_tac⟩

/-- Loop 2 ends at `k = s`: on to 1008. -/
theorem k2_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p pc s k : Nat)
    (hx : RF x v p pc s) (hmem : Prefix image mem 1536) (h17 : x.get 17 = bv k) (hks : s ≤ k)
    (hk : k < 158115) :
    ∃ y, run 1 ⟨x, bv 1004, mem, [], out, .running⟩ = ⟨y, bv 1008, mem, [], out, .running⟩ ∧
      (∀ r : Reg, y.get r = x.get r) := by
  obtain ⟨h7, h28, h29, h9, h15, h14, h8, h2⟩ := hx
  exact ⟨x, by lexec, fun _ => rfl⟩

/-! ## The two loops over the rough list `L` -/

/-- What both loops need: `L` with its math (`CMath`), the bounds, the spills. -/
structure KCtx (L : List Nat) (keep : Nat → Bool) (oldv newv quot Sm Sk : Nat → Nat)
    (N v p pc : Nat) : Prop where
  hm : CMath L keep oldv newv quot Sm Sk N v p pc
  hLs : L.length ≤ (v + 1) / 2
  hv : v < 316228
  hp : p ≤ 563
  hN : N < 100000000000
  hpc : pc < 400000

/-- The arrays during the compaction: `roughs`, `larges` and `invs` hold the new entries below
`ns` and the old ones from `k` on. -/
structure KArr (L : List Nat) (keep : Nat → Bool) (oldv newv Sm Sk : Nat → Nat) (N v k : Nat)
    (mem : Array (BitVec 8)) : Prop where
  size : mem.size = 4194304
  pre : Prefix image mem 1536
  s8 : readBytes mem 715656 8 = some (bv RB)
  s16 : readBytes mem 715664 8 = some (bv IB)
  s24 : readBytes mem 715672 8 = some (bv LB)
  sm : Arr32 mem SB ((v + 1) / 2) Sm
  sk : Arr8 mem SM (v + 1) Sk
  newI : ∃ R Lg Iv : Nat → Nat, Arr32 mem RB L.length R ∧ Arr32 mem LB L.length Lg ∧
    Arr64 mem IB L.length Iv ∧
    (∀ j d, ((L.take k).filter keep)[j]? = some d → R j = d ∧ Lg j = newv d ∧ Iv j = N / d) ∧
    (∀ j d, k ≤ j → L[j]? = some d → R j = d ∧ Lg j = oldv d ∧ Iv j = N / d)

/-- The result of the compaction. -/
def KDone (L : List Nat) (keep : Nat → Bool) (newv : Nat → Nat) (N : Nat)
    (mem : Array (BitVec 8)) : Prop :=
  Arr32 mem RB (L.filter keep).length (fun j => (L.filter keep).getD j 0) ∧
  Arr32 mem LB (L.filter keep).length (fun j => newv ((L.filter keep).getD j 0)) ∧
  Arr64 mem IB (L.filter keep).length (fun j => N / (L.filter keep).getD j 0)

theorem KArr.same {L : List Nat} {keep : Nat → Bool} {oldv newv Sm Sk : Nat → Nat} {N v k : Nat}
    {mem mem' : Array (BitVec 8)} (h : KArr L keep oldv newv Sm Sk N v k mem)
    (hs : Same mem mem' LB (IB + 158114 * 8)) (hL : L.length ≤ 158114) (hv : v < 316228)
    (R Lg Iv : Nat → Nat) (hR : Arr32 mem' RB L.length R) (hLg : Arr32 mem' LB L.length Lg)
    (hIv : Arr64 mem' IB L.length Iv) (k' : Nat)
    (hn : ∀ j d, ((L.take k').filter keep)[j]? = some d → R j = d ∧ Lg j = newv d ∧ Iv j = N / d)
    (ho : ∀ j d, k' ≤ j → L[j]? = some d → R j = d ∧ Lg j = oldv d ∧ Iv j = N / d) :
    KArr L keep oldv newv Sm Sk N v k' mem' :=
  ⟨by rw [hs.size_eq, h.size], hs.lpre h.pre (by omega), hs.read h.s8 (by omega),
   hs.read h.s16 (by omega), hs.read h.s24 (by omega), hs.arr32 h.sm (by omega),
   hs.arr8 h.sk (by omega), R, Lg, Iv, hR, hLg, hIv, hn, ho⟩

theorem KArr.done {L : List Nat} {keep : Nat → Bool} {oldv newv Sm Sk : Nat → Nat} {N v : Nat}
    {mem : Array (BitVec 8)} (h : KArr L keep oldv newv Sm Sk N v L.length mem) :
    KDone L keep newv N mem := by
  obtain ⟨R, Lg, Iv, hR, hLg, hIv, hn, _⟩ := h.newI
  rw [List.take_length] at hn
  have hfl := List.length_filter_le keep L
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have e := hR j (by omega)
    rw [(hn j _ (List.getElem?_eq_getElem hj)).1] at e
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using e
  · have e := hLg j (by omega)
    rw [(hn j _ (List.getElem?_eq_getElem hj)).2.1] at e
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using e
  · have e := hIv j (by omega)
    rw [(hn j _ (List.getElem?_eq_getElem hj)).2.2] at e
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using e

/-- Three stores at index `ns` (in any order) keep `KArr` with `k + 1`. -/
theorem karr_keep {L : List Nat} {keep : Nat → Bool} {oldv newv Sm Sk : Nat → Nat} {N v k ns d : Nat}
    {mem : Array (BitVec 8)} (h : KArr L keep oldv newv Sm Sk N v k mem)
    (hL : L.length ≤ 158114) (hv : v < 316228) (hk : k < L.length) (hns : ns ≤ k)
    (hd : L[k]? = some d) (hkeep : keep d = true)
    (hnsd : ns = ((L.take k).filter keep).length)
    (mem' : Array (BitVec 8)) (hs : Same mem mem' LB (IB + 158114 * 8))
    (hrR : ∀ i, i < 158114 → i ≠ ns → readBytes mem' (RB + i * 4) 4 = readBytes mem (RB + i * 4) 4)
    (hrL : ∀ i, i < 158114 → i ≠ ns → readBytes mem' (LB + i * 4) 4 = readBytes mem (LB + i * 4) 4)
    (hrI : ∀ i, i < 158114 → i ≠ ns → readBytes mem' (IB + i * 8) 8 = readBytes mem (IB + i * 8) 8)
    (hR : readBytes mem' (RB + ns * 4) 4 = some (BitVec.ofNat 32 d))
    (hLg : readBytes mem' (LB + ns * 4) 4 = some (BitVec.ofNat 32 (newv d)))
    (hIv : readBytes mem' (IB + ns * 8) 8 = some (bv (N / d))) :
    KArr L keep oldv newv Sm Sk N v (k + 1) mem' := by
  obtain ⟨R, Lg, Iv, hRA, hLA, hIA, hn, ho⟩ := h.newI
  have hfts := filter_take_succ L keep k d hd
  rw [if_pos hkeep] at hfts
  refine h.same hs hL hv (upd R ns d) (upd Lg ns (newv d)) (upd Iv ns (N / d)) ?_ ?_ ?_ (k + 1) ?_ ?_
  · intro i hi
    by_cases hin : i = ns
    · subst hin; rw [upd_same]; exact hR
    · rw [upd_other _ _ _ _ hin, hrR i (by omega) hin]
      exact hRA i hi
  · intro i hi
    by_cases hin : i = ns
    · subst hin; rw [upd_same]; exact hLg
    · rw [upd_other _ _ _ _ hin, hrL i (by omega) hin]
      exact hLA i hi
  · intro i hi
    by_cases hin : i = ns
    · subst hin; rw [upd_same]; exact hIv
    · rw [upd_other _ _ _ _ hin, hrI i (by omega) hin]
      exact hIA i hi
  · intro j d' hj
    rw [hfts] at hj
    by_cases hjn : j < ns
    · rw [List.getElem?_append_left (by omega)] at hj
      rw [upd_other _ _ _ _ (by omega), upd_other _ _ _ _ (by omega), upd_other _ _ _ _ (by omega)]
      exact hn j d' hj
    · rw [List.getElem?_append_right (by omega), ← hnsd] at hj
      have hj' : j - ns = 0 := by
        rcases hh : j - ns with _ | m
        · rfl
        · rw [hh] at hj; simp at hj
      rw [hj'] at hj
      simp at hj; subst hj
      rw [show j = ns by omega]; simp
  · intro j d' hj hjd
    rw [upd_other _ _ _ _ (by omega), upd_other _ _ _ _ (by omega), upd_other _ _ _ _ (by omega)]
    exact ho j d' (by omega) hjd

/-- Reads at other indices survive stores at index `ns` of the three arrays. -/
macro "kfr_rd" : tactic => `(tactic| (intro i hi hin; repeat rw [read_wr_other _ _ _ _ _ _ (by first | omega | (simp only [wr_size]; omega)) (by omega)]))

/-- Loop 2 at 1004, from `k` to the end of `L`. -/
theorem compact2 (L : List Nat) (keep : Nat → Bool) (oldv newv quot Sm Sk : Nat → Nat)
    (N v p pc : Nat) (hc : KCtx L keep oldv newv quot Sm Sk N v p pc)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (k ns : Nat)
    (hx : RF x v p pc L.length) (h17 : x.get 17 = bv k) (h16 : x.get 16 = bv ns)
    (h19 : x.get 19 = bv (IB - 752)) (h20 : x.get 20 = bv (RB + 920))
    (hk : k ≤ L.length) (hns : ns = ((L.take k).filter keep).length)
    (ha : KArr L keep oldv newv Sm Sk N v k mem)
    (hbig : ∀ j d, k ≤ j → L[j]? = some d → keep d = true → v < d * p) :
    ∃ n y mem', run n ⟨x, bv 1004, mem, [], out, .running⟩ = ⟨y, bv 1008, mem', [], out, .running⟩ ∧
      Same mem mem' LB (IB + 158114 * 8) ∧ KArr L keep oldv newv Sm Sk N v L.length mem' ∧
      y.get 16 = bv (L.filter keep).length ∧ (∀ r : Reg, r ∉ kfr → y.get r = x.get r) := by
  obtain ⟨hm, hLs, hv, hp, hN, hpc⟩ := hc
  have hsz := ha.size
  by_cases hkL : k < L.length
  · obtain ⟨d, hd⟩ : ∃ d, L[k]? = some d := ⟨L[k], List.getElem?_eq_getElem hkL⟩
    have hdL : d ∈ L := List.mem_of_getElem? hd
    obtain ⟨R, Lg, Iv, hRA, hLA, hIA, hn, ho⟩ := ha.newI
    obtain ⟨hRk, hLgk, hIvk⟩ := ho k d (Nat.le_refl k) hd
    have hd1 := hm.bound d hdL
    have hR : readBytes mem (RB + k * 4) 4 = some (BitVec.ofNat 32 d) := by
      have := hRA k hkL; rwa [hRk] at this
    have hnsk : ns ≤ k := by
      rw [hns]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
    have hfts := filter_take_succ L keep k d hd
    by_cases hkeep : keep d = true
    · have hS : readBytes mem (SM + d) 1 = some (BitVec.ofNat 8 0) := by
        have := ha.sk d (by omega); rwa [hm.skip d hdL, if_pos hkeep] at this
      have hL : readBytes mem (LB + k * 4) 4 = some (BitVec.ofNat 32 (oldv d)) := by
        have := hLA k hkL; rwa [hLgk] at this
      have hI : readBytes mem (IB + k * 8) 8 = some (bv (N / d)) := by
        have := hIA k hkL; rwa [hIvk] at this
      obtain ⟨hqo, hnv⟩ := hm.new d hdL hkeep
      have hob := hm.oldb d hdL
      obtain ⟨hdpb, hN1, hN2, hq⟩ := hm.large d hdL hkeep (hbig k d (Nat.le_refl k) hd hkeep)
      have hdiv : N / d / p = N / (d * p) := Nat.div_div_eq_div_mul N d p
      have hSmr : readBytes mem (SB + (N / d / p - 1) / 2 * 4) 4 = some (BitVec.ofNat 32 (quot d)) := by
        have := ha.sm ((N / (d * p) - 1) / 2) (by omega); rwa [hq, ← hdiv] at this
      have hqb : quot d < 400000 := by
        rw [← hq]; exact hm.smb _ (by omega)
      have hNd := Nat.div_le_self N d
      obtain ⟨y, hr, hy17, hy16, hfy⟩ := k2_keep x mem out v p pc L.length k ns d (oldv d) (quot d)
        (N / d) hx ha.pre hsz h17 h16 h19 h20 hkL (by omega) hnsk hd1.2 hv hm.p3 hp (by omega)
        (by omega) hqo hqb hob (by omega) ha.s8 ha.s16 ha.s24 hR hS hI hL hSmr
      have hw1 : RB + ns * 4 + 4 ≤ mem.size := by omega
      have S := (Same.wr mem (RB + ns * 4) (bv d) 4 LB (IB + 158114 * 8) hw1 (by omega) (by omega)).trans
        ((Same.wr _ (LB + ns * 4) (bv (oldv d + pc - quot d)) 4 LB (IB + 158114 * 8)
          (by simp only [wr_size]; omega) (by omega) (by omega)).trans
        (Same.wr _ (IB + ns * 8) (bv (N / d)) 8 LB (IB + 158114 * 8)
          (by simp only [wr_size]; omega) (by omega) (by omega)))
      have ha' := karr_keep ha (by omega) hv hkL hnsk hd hkeep hns _ S
        (by kfr_rd) (by kfr_rd) (by kfr_rd)
        (by
          rw [read_wr_other _ _ _ _ _ _ (by simp only [wr_size]; omega) (by omega),
            read_wr_other _ _ _ _ _ _ (by simp only [wr_size]; omega) (by omega)]
          exact ZjyBinary.rd32 _ _ _ (by omega))
        (by
          rw [read_wr_other _ _ _ _ _ _ (by simp only [wr_size]; omega) (by omega),
            read_wr_same _ _ _ _ (by simp only [wr_size]; omega)]
          simp only [setWidth_ofNat_le 64 32 _ (by omega)]
          congr 2; omega)
        (ZjyBinary.rd64 _ _ _ (by simp only [wr_size]; omega))
      obtain ⟨n, z, mem', hr2, S', ha2, hz16, hfz⟩ := compact2 L keep oldv newv quot Sm Sk N v p pc
        ⟨hm, hLs, hv, hp, hN, hpc⟩ y _ out (k + 1) (ns + 1) (hx.frame (frame_kfr (by decide) hfy))
        hy17 hy16 (by rw [hfy 19 (by decide), h19]) (by rw [hfy 20 (by decide), h20]) (by omega)
        (by rw [hfts, if_pos hkeep, List.length_append, ← hns]; rfl) ha'
        (fun j d' hj => hbig j d' (by omega))
      exact ⟨36 + n, z, mem', by rw [run_add, hr, hr2], S.trans S', ha2, hz16,
        fun r hr => by rw [hfz r hr, frame_kfr (by decide) hfy r hr]⟩
    · have hS : readBytes mem (SM + d) 1 = some (BitVec.ofNat 8 1) := by
        have := ha.sk d (by omega); rwa [hm.skip d hdL, if_neg hkeep] at this
      obtain ⟨y, hr, hy17, hfy⟩ := k2_skip x mem out v p pc L.length k d hx ha.pre hsz h17 hkL
        (by omega) hd1.2 hv ha.s8 hR hS
      rw [if_neg hkeep, List.append_nil] at hfts
      obtain ⟨n, z, mem', hr2, S', ha2, hz16, hfz⟩ := compact2 L keep oldv newv quot Sm Sk N v p pc
        ⟨hm, hLs, hv, hp, hN, hpc⟩ y mem out (k + 1) ns (hx.frame (frame_kfr (by decide) hfy))
        hy17 (by rw [hfy 16 (by decide), h16]) (by rw [hfy 19 (by decide), h19])
        (by rw [hfy 20 (by decide), h20]) (by omega) (by rw [hfts]; exact hns)
        (ha.same (Same.refl _ _ _) (by omega) hv R Lg Iv hRA hLA hIA (k + 1)
          (fun j d' h => hn j d' (by rw [← hfts]; exact h)) (fun j d' hj h => ho j d' (by omega) h))
        (fun j d' hj => hbig j d' (by omega))
      exact ⟨12 + n, z, mem', by rw [run_add, hr, hr2], S', ha2, hz16,
        fun r hr => by rw [hfz r hr, frame_kfr (by decide) hfy r hr]⟩
  · have hkL' : k = L.length := by omega
    obtain ⟨y, hr, hfy⟩ := k2_exit x mem out v p pc L.length k hx ha.pre h17 (by omega) (by omega)
    subst hkL'
    rw [List.take_length] at hns
    exact ⟨1, y, mem, hr, Same.refl _ _ _, ha, by rw [hfy, h16, hns], fun r _ => hfy r⟩
termination_by L.length - k

/-- Loop 1 at 932, from `k` until the first kept rough `d` with `d * p > v` (there is one), then
loop 2. -/
theorem compact1 (L : List Nat) (keep : Nat → Bool) (oldv newv quot Sm Sk : Nat → Nat)
    (N v p pc : Nat) (hc : KCtx L keep oldv newv quot Sm Sk N v p pc)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (k ns : Nat)
    (hx : RF x v p pc L.length) (h17 : x.get 17 = bv k) (h16 : x.get 16 = bv ns)
    (h21 : x.get 21 = bv (RB + k * 4)) (h20 : x.get 20 = bv (LB + k * 4))
    (h19 : x.get 19 = bv (IB + k * 8))
    (h22 : x.get 22 = bv (IB - 752)) (h23 : x.get 23 = bv (RB + 920))
    (hns : ns = ((L.take k).filter keep).length)
    (ha : KArr L keep oldv newv Sm Sk N v k mem)
    (hbrk : ∃ j d, k ≤ j ∧ L[j]? = some d ∧ keep d = true ∧ v < d * p) :
    ∃ n y mem', run n ⟨x, bv 932, mem, [], out, .running⟩ = ⟨y, bv 1008, mem', [], out, .running⟩ ∧
      Same mem mem' LB (IB + 158114 * 8) ∧ KArr L keep oldv newv Sm Sk N v L.length mem' ∧
      y.get 16 = bv (L.filter keep).length ∧ (∀ r : Reg, r ∉ kfr → y.get r = x.get r) := by
  have hc' := hc
  obtain ⟨hm, hLs, hv, hp, hN, hpc⟩ := hc'
  have hsz := ha.size
  obtain ⟨jb, db, hjb, hdb, hkb, hvb⟩ := hbrk
  have hkL : k < L.length := by
    have := (List.getElem?_eq_some_iff.mp hdb).1; omega
  obtain ⟨d, hd⟩ : ∃ d, L[k]? = some d := ⟨L[k], List.getElem?_eq_getElem hkL⟩
  have hdL : d ∈ L := List.mem_of_getElem? hd
  obtain ⟨R, Lg, Iv, hRA, hLA, hIA, hn, ho⟩ := ha.newI
  obtain ⟨hRk, hLgk, hIvk⟩ := ho k d (Nat.le_refl k) hd
  have hd1 := hm.bound d hdL
  have hR : readBytes mem (RB + k * 4) 4 = some (BitVec.ofNat 32 d) := by
    have := hRA k hkL; rwa [hRk] at this
  have hnsk : ns ≤ k := by
    rw [hns]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
  have hfts := filter_take_succ L keep k d hd
  by_cases hkeep : keep d = true
  · have hS : readBytes mem (SM + d) 1 = some (BitVec.ofNat 8 0) := by
      have := ha.sk d (by omega); rwa [hm.skip d hdL, if_pos hkeep] at this
    by_cases hdp : d * p ≤ v
    · have hjk : jb ≠ k := fun h => by subst h; rw [hd] at hdb; cases hdb; omega
      obtain ⟨hpc1, hidx1, hidx, hov⟩ := hm.small d hdL hkeep hdp
      have hkidx : k < Sm (d * p / 2) - pc := sorted_idx hm.sorted hd hidx
        (by have := Nat.mul_le_mul_left d hm.p3; omega)
      obtain ⟨_, hLg2, _⟩ := ho _ _ (by omega) hidx
      have hidxL : Sm (d * p / 2) - pc < L.length := (List.getElem?_eq_some_iff.mp hidx).1
      have hSmr : readBytes mem (SB + p * d / 2 * 4) 4 = some (BitVec.ofNat 32 (Sm (d * p / 2))) := by
        rw [Nat.mul_comm p d]; exact ha.sm _ (by omega)
      have hL2 : readBytes mem (LB + (Sm (d * p / 2) - pc) * 4) 4 = some (BitVec.ofNat 32 (quot d)) := by
        have := hLA _ hidxL; rwa [hLg2, hov] at this
      have hL : readBytes mem (LB + k * 4) 4 = some (BitVec.ofNat 32 (oldv d)) := by
        have := hLA k hkL; rwa [hLgk] at this
      have hI : readBytes mem (IB + k * 8) 8 = some (bv (N / d)) := by
        have := hIA k hkL; rwa [hIvk] at this
      obtain ⟨hqo, hnv⟩ := hm.new d hdL hkeep
      have hob := hm.oldb d hdL
      have := hm.smb _ hidx1
      have hNd := Nat.div_le_self N d
      obtain ⟨y, hr, hy17, hy16, hy21, hy20, hy19, hfy⟩ := k1_small x mem out v p pc L.length k ns d
        (Sm (d * p / 2)) (oldv d) (quot d) (N / d) hx ha.pre hsz h21 h20 h19 h17 h16 h22 h23
        (by omega) hnsk hd1.2 hv (by rw [Nat.mul_comm]; exact hdp) hpc1 (by omega) (by omega) hqo hob
        (by omega) hR hS hSmr hL hL2 hI
      have S := (Same.wr mem (LB + ns * 4) (bv (oldv d + pc - quot d)) 4 LB (IB + 158114 * 8)
          (by omega) (by omega) (by omega)).trans
        ((Same.wr _ (IB + ns * 8) (bv (N / d)) 8 LB (IB + 158114 * 8)
          (by simp only [wr_size]; omega) (by omega) (by omega)).trans
        (Same.wr _ (RB + ns * 4) (bv d) 4 LB (IB + 158114 * 8)
          (by simp only [wr_size]; omega) (by omega) (by omega)))
      have ha' := karr_keep ha (by omega) hv hkL hnsk hd hkeep hns _ S
        (by kfr_rd) (by kfr_rd) (by kfr_rd)
        (ZjyBinary.rd32 _ _ _ (by simp only [wr_size]; omega))
        (by
          rw [read_wr_other _ _ _ _ _ _ (by simp only [wr_size]; omega) (by omega),
            read_wr_other _ _ _ _ _ _ (by simp only [wr_size]; omega) (by omega),
            read_wr_same _ _ _ _ (by omega)]
          simp only [setWidth_ofNat_le 64 32 _ (by omega)]
          congr 2; omega)
        (by
          rw [read_wr_other _ _ _ _ _ _ (by simp only [wr_size]; omega) (by omega)]
          exact ZjyBinary.rd64 _ _ _ (by simp only [wr_size]; omega))
      obtain ⟨n, z, mem', hr2, S', ha2, hz16, hfz⟩ := compact1 L keep oldv newv quot Sm Sk N v p pc
        hc y _ out (k + 1) (ns + 1) (hx.frame (frame_kfr (by decide) hfy))
        hy17 hy16 hy21 hy20 hy19 (by rw [hfy 22 (by decide), h22]) (by rw [hfy 23 (by decide), h23])
        (by rw [hfts, if_pos hkeep, List.length_append, ← hns]; rfl) ha'
        ⟨jb, db, by omega, hdb, hkb, hvb⟩
      exact ⟨35 + n, z, mem', by rw [run_add, hr, hr2], S.trans S', ha2, hz16,
        fun r hr => by rw [hfz r hr, frame_kfr (by decide) hfy r hr]⟩
    · obtain ⟨y, hr, hy19, hy20, hfy⟩ := k1_break x mem out v p pc L.length k d hx ha.pre hsz h21 h17
        (by omega) hd1.2 hv (by rw [Nat.mul_comm]; omega) hp hR hS
      obtain ⟨n, z, mem', hr2, S', ha2, hz16, hfz⟩ := compact2 L keep oldv newv quot Sm Sk N v p pc
        hc y mem out k ns (hx.frame (frame_kfr (by decide) hfy))
        (by rw [hfy 17 (by decide), h17]) (by rw [hfy 16 (by decide), h16]) hy19 hy20 (by omega) hns
        ⟨hsz, ha.pre, ha.s8, ha.s16, ha.s24, ha.sm, ha.sk, R, Lg, Iv, hRA, hLA, hIA, hn, ho⟩
        (fun j d' hj hjd _ => by
          by_cases hjk : j = k
          · subst hjk; rw [hd] at hjd; cases hjd; omega
          · have := sorted_idx hm.sorted hd hjd
            have hlt : d < d' := by
              apply Decidable.byContradiction; intro hc2
              rcases Nat.lt_or_ge d' d with h' | h'
              · have := sorted_idx hm.sorted hjd hd h'; omega
              · have : d' = d := by omega
                subst this
                have h1 := (List.getElem?_eq_some_iff.mp hd)
                have h2 := (List.getElem?_eq_some_iff.mp hjd)
                have := List.pairwise_iff_getElem.mp hm.sorted k j h1.1 h2.1
                by_cases hkj : k < j
                · have := this hkj; rw [h1.2, h2.2] at this; omega
                · have := List.pairwise_iff_getElem.mp hm.sorted j k h2.1 h1.1 (by omega)
                  rw [h1.2, h2.2] at this; omega
            have := Nat.mul_le_mul_right p (show d ≤ d' by omega)
            omega)
      exact ⟨18 + n, z, mem', by rw [run_add, hr, hr2], S', ha2, hz16,
        fun r hr => by rw [hfz r hr, frame_kfr (by decide) hfy r hr]⟩
  · have hS : readBytes mem (SM + d) 1 = some (BitVec.ofNat 8 1) := by
      have := ha.sk d (by omega); rwa [hm.skip d hdL, if_neg hkeep] at this
    have hjk : jb ≠ k := fun h => by subst h; rw [hd] at hdb; cases hdb; exact hkeep hkb
    obtain ⟨y, hr, hy17, hy21, hy20, hy19, hfy⟩ := k1_skip x mem out v p pc L.length k ns d hx ha.pre
      hsz h21 h20 h19 h17 (by omega) hd1.2 hv hR hS
    rw [if_neg hkeep, List.append_nil] at hfts
    obtain ⟨n, z, mem', hr2, S', ha2, hz16, hfz⟩ := compact1 L keep oldv newv quot Sm Sk N v p pc
      hc y mem out (k + 1) ns (hx.frame (frame_kfr (by decide) hfy))
      hy17 (by rw [hfy 16 (by decide), h16]) hy21 hy20 hy19 (by rw [hfy 22 (by decide), h22])
      (by rw [hfy 23 (by decide), h23]) (by rw [hfts]; exact hns)
      (ha.same (Same.refl _ _ _) (by omega) hv R Lg Iv hRA hLA hIA (k + 1)
        (fun j d' h => hn j d' (by rw [← hfts]; exact h)) (fun j d' hj h => ho j d' (by omega) h))
      ⟨jb, db, by omega, hdb, hkb, hvb⟩
    exact ⟨11 + n, z, mem', by rw [run_add, hr, hr2], S', ha2, hz16,
      fun r hr => by rw [hfz r hr, frame_kfr (by decide) hfy r hr]⟩
termination_by L.length - k

end TinyFive.LphaBinary
