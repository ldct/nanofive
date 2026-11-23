import LphaBinary.Setup

/-! The head of the sieve loop at 544: leaving it for the final sum, skipping a marked `p`, and
for an unmarked `p`, `smooth[p] = 1` and the loop at 852 marking the odd multiples of `p` from
`p²` to `v`. -/
namespace TinyFive.LphaBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

set_option linter.unusedVariables false

theorem p_le_563 {p v : Nat} (hpv : p * p ≤ v) (hv : v < 316228) : p ≤ 563 := by
  apply Decidable.byContradiction; intro h
  have := Nat.mul_le_mul (show 564 ≤ p by omega) (show 564 ≤ p by omega); omega

/-- 544 → 852 for an unmarked `p` with `p² ≤ v`: `smooth[p] = 1`, `i = p²`, `s8 = 2p`. -/
theorem round_enter (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = bv p) (h10 : x.get 10 = bv (SM + p - 3)) (h9 : x.get 9 = bv v)
    (hpv : p * p ≤ v) (hv : v < 316228) (hp3 : 3 ≤ p)
    (hS : readBytes mem (SM + p) 1 = some (BitVec.ofNat 8 0)) :
    ∃ y, run 8 ⟨x, bv 544, mem, [], out, .running⟩ =
      ⟨y, bv 852, wr mem (SM + p) (bv 1) 1, [], out, .running⟩ ∧
      y.get 16 = bv (p * p) ∧ y.get 24 = bv (p * 2) ∧ y.get 6 = bv 1 ∧
      (∀ r : Reg, r ∉ ([6, 16, 17, 24] : List Reg) → y.get r = x.get r) := by
  have := zext8
  have hp := p_le_563 hpv hv
  exact ⟨_, by lexec; rfl, by rg, by rg, by rg, by frame_tac⟩

/-- 544 → 544 for a marked `p` with `p² ≤ v`: `p += 2`. -/
theorem round_skip_run (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = bv p) (h10 : x.get 10 = bv (SM + p - 3)) (h9 : x.get 9 = bv v)
    (hpv : p * p ≤ v) (hv : v < 316228) (hp3 : 3 ≤ p)
    (hS : readBytes mem (SM + p) 1 = some (BitVec.ofNat 8 1)) :
    ∃ y, run 7 ⟨x, bv 544, mem, [], out, .running⟩ = ⟨y, bv 544, mem, [], out, .running⟩ ∧
      y.get 15 = bv (p + 2) ∧ y.get 10 = bv (SM + (p + 2) - 3) ∧
      (∀ r : Reg, r ∉ ([10, 15, 16, 17] : List Reg) → y.get r = x.get r) := by
  have := zext8
  have hp := p_le_563 hpv hv
  exact ⟨_, by lexec; rfl, by rg, by rg, by frame_tac⟩

/-- 544 → 552 once `v < p²`. -/
theorem outer_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p : Nat)
    (hmem : Prefix image mem 1536) (h15 : x.get 15 = bv p) (h9 : x.get 9 = bv v)
    (hpv : v < p * p) (hp : p < 1000) :
    ∃ y, run 2 ⟨x, bv 544, mem, [], out, .running⟩ = ⟨y, bv 552, mem, [], out, .running⟩ ∧
      y.get 16 = bv (p * p) ∧ (∀ r : Reg, r ∉ ([16] : List Reg) → y.get r = x.get r) := by
  have : p * p < 1000000 := by have := Nat.mul_le_mul (show p ≤ 999 by omega) (show p ≤ 999 by omega); omega
  exact ⟨_, by lexec; rfl, by rg, by frame_tac⟩

/-- The marking loop at 852 (a do-while): `smooth[i] = 1` for odd multiples `i` of `p` from `m`
to `v`, ending at 872. -/
theorem mark_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p m : Nat)
    (g0 : Nat → Nat) (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h16 : x.get 16 = bv m) (h24 : x.get 24 = bv (p * 2)) (h6 : x.get 6 = bv 1)
    (h2 : x.get 2 = bv 715648) (h9 : x.get 9 = bv v)
    (hs0 : readBytes mem 715648 8 = some (bv SM))
    (hv : v < 316228) (hp : p % 2 = 1)
    (hpv : p ≤ v) (hm : p ∣ m) (hm2 : m % 2 = 1) (hpm : p * p ≤ m) (hmv : m ≤ v)
    (harr : Arr8 mem SM (v + 1)
      (fun i => if p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < m then 1 else g0 i)) :
    ∃ k y mem', run k ⟨x, bv 852, mem, [], out, .running⟩ = ⟨y, bv 872, mem', [], out, .running⟩ ∧
      Same mem mem' SM (SM + (v + 1)) ∧
      Arr8 mem' SM (v + 1) (fun i => if p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 then 1 else g0 i) ∧
      (∀ r : Reg, r ∉ ([16, 17] : List Reg) → y.get r = x.get r) := by
  have harr' := (harr.wr (by rw [hsz]; omega) m 1 (by omega)).ext
    (g := fun i => if p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < m + p * 2 then 1 else g0 i)
    (fun i _ => by
      simp only [mark_upd p m i hp hm hm2]
      by_cases hi : i = m
      · subst hi; simp [hpm]
      · rw [upd_other _ _ _ _ hi]; simp [hi])
  have S1 := Same.wr mem (SM + m) (bv 1) 1 SM (SM + (v + 1)) (by rw [hsz]; omega) (by omega) (by omega)
  have hpre := prefix_wr (SM + m) (bv 1) 1 hmem (by rw [hsz]; omega) (by omega)
  by_cases hmv' : m + p * 2 ≤ v
  · obtain ⟨y, hr, hy16, hfy⟩ : ∃ y, run 5 ⟨x, bv 852, mem, [], out, .running⟩ =
        ⟨y, bv 852, wr mem (SM + m) (bv 1) 1, [], out, .running⟩ ∧ y.get 16 = bv (m + p * 2) ∧
        (∀ r : Reg, r ∉ ([16, 17] : List Reg) → y.get r = x.get r) :=
      ⟨_, by lexec; rfl, by rg, by frame_tac⟩
    obtain ⟨k, z, mem', hr2, hsame, harr2, hfz⟩ := mark_loop y _ out v p (m + p * 2) g0
      hpre (by simp [hsz]) hy16
      (by rw [hfy 24 (by decide), h24]) (by rw [hfy 6 (by decide), h6])
      (by rw [hfy 2 (by decide), h2]) (by rw [hfy 9 (by decide), h9])
      (by rw [read_wr_other _ _ _ _ _ _ (by omega) (by omega)]; exact hs0) hv hp hpv
      (Nat.dvd_add hm (Nat.dvd_mul_right p 2)) (by omega) (by omega) hmv' harr'
    refine ⟨5 + k, z, mem', by rw [run_add, hr, hr2], S1.trans ⟨hsame.size_eq, hsame.frame⟩, harr2,
      fun r hr => by rw [hfz r hr, hfy r hr]⟩
  · obtain ⟨y, hr, hfy⟩ : ∃ y, run 5 ⟨x, bv 852, mem, [], out, .running⟩ =
        ⟨y, bv 872, wr mem (SM + m) (bv 1) 1, [], out, .running⟩ ∧
        (∀ r : Reg, r ∉ ([16, 17] : List Reg) → y.get r = x.get r) :=
      ⟨_, by lexec; rfl, by frame_tac⟩
    refine ⟨5, y, _, hr, S1, harr'.ext (fun i hi => by
        by_cases h : p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1
        · simp [h, show i < m + p * 2 by omega]
        · simp only [h, ite_false]; rw [if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩)]), hfy⟩
termination_by v + 1 - m

end TinyFive.LphaBinary
