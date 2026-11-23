import GrumpyBinary.Round

/-! The whole outer loop of `prime_pi`: from stage 3 to the stage `a` where it stops, with
`N < a⁴`. -/
namespace TinyFive.GrumpyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory

local notation "bv" => BitVec.ofNat 64

theorem prime_563 : Prime 563 := by decide +kernel

theorem outer_exit_v (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v p : Nat)
    (hmem : Prefix image mem 1236) (h18 : x.get 18 = bv v) (h12 : x.get 12 = bv p)
    (hvp : v < p) (hp : p < 400000) :
    ∃ y, run 2 ⟨x, bv 388, mem, [], out, .running⟩ = ⟨y, bv 396, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([13] : List Reg) → y.get r = x.get r) := by
  refine ⟨x.set 13 (bv p), ?_, by frame_tac⟩
  gexec

theorem outer_exit_cut (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N v p D : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h18 : x.get 18 = bv v) (h24 : x.get 24 = bv D) (h12 : x.get 12 = bv p) (h19 : x.get 19 = bv N)
    (hpv : p ≤ v) (hv : v < 316228) (hD : D + v + 1 ≤ 3000000) (hD' : 1248 ≤ D) (hp3 : 3 ≤ p)
    (hpp : p * p < 400000) (hpq : p * p * (p * p) < 200000000000) (hN : N < 100000000000)
    (hq : N < p * p * (p * p))
    (hS : readBytes mem (D + p) 1 = some (BitVec.ofNat 8 0)) :
    ∃ y, run 8 ⟨x, bv 388, mem, [], out, .running⟩ = ⟨y, bv 396, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([11, 13, 15, 16] : List Reg) → y.get r = x.get r) := by
  have := zext8
  refine ⟨((((x.set 13 (bv p)).set 11 (bv (D + p))).set 15 0#64).set 15
    (bv (p * p))).set 16 (bv (p * p * (p * p))), ?_, by frame_tac⟩
  gexec

theorem Inv.frame {N p : Nat} {x y : Regs 64} {mem : Array (BitVec 8)} (h : Inv N p x mem)
    (hf : ∀ r : Reg, r ∉ ([11, 13, 15, 16] : List Reg) → y.get r = x.get r) : Inv N p y mem :=
  { h with
    x8 := by rw [hf 8 (by decide), h.x8], x9 := by rw [hf 9 (by decide), h.x9]
    x18 := by rw [hf 18 (by decide), h.x18], x19 := by rw [hf 19 (by decide), h.x19]
    x20 := by rw [hf 20 (by decide), h.x20], x21 := by rw [hf 21 (by decide), h.x21]
    x22 := by rw [hf 22 (by decide), h.x22], x23 := by rw [hf 23 (by decide), h.x23]
    x24 := by rw [hf 24 (by decide), h.x24], x25 := by rw [hf 25 (by decide), h.x25]
    x12 := by rw [hf 12 (by decide), h.x12], x14 := by rw [hf 14 (by decide), h.x14]
    x10 := by rw [hf 10 (by decide), h.x10], x2 := by rw [hf 2 (by decide), h.x2] }

/-- From any stage, the outer loop reaches the final sums at 396 at a stage `a` with `N < a⁴`. -/
theorem outer_loop (N p : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h : Inv N p x mem) :
    ∃ n a y mem', run n ⟨x, bv 388, mem, [], out, .running⟩ = ⟨y, bv 396, mem', [], out, .running⟩ ∧
      Inv N a y mem' ∧ N < a * a * (a * a) := by
  obtain ⟨hvb, hDb⟩ := inv_bounds h
  have hp3 := h.hp3
  have hpo := h.hpo
  have hv := isqrt_spec N
  have hN := h.hN
  -- every stage reached is at most 563
  have hp563 : p ≤ 564 := by
    apply Decidable.byContradiction; intro hc
    have := h.hpr 563 (by decide) (by omega) prime_563
    omega
  by_cases hpv : p ≤ isqrt N
  · have hsk := h.sk p (by omega)
    dsimp only at hsk
    by_cases hprime : Prime p
    · rw [if_neg (show ¬ SkipMarked p p from fun hs => (skip_self_iff p hp3 hpo).mp hs hprime)] at hsk
      by_cases hq : p * p * (p * p) ≤ N
      · obtain ⟨n1, y1, mem1, hr1, h1⟩ := round_prime N p x mem out h hprime hq
        obtain ⟨n2, a, y2, mem2, hr2, h2, hc⟩ := outer_loop N (p + 2) y1 mem1 out h1
        exact ⟨n1 + n2, a, y2, mem2, by rw [run_add, hr1, hr2], h2, hc⟩
      · have hpp : p * p ≤ 318096 := Nat.mul_le_mul (show p ≤ 564 by omega) (show p ≤ 564 by omega)
        have hpq : p * p * (p * p) ≤ 101185065216 := Nat.le_trans (Nat.mul_le_mul hpp hpp) (by decide)
        have hLD : LD ((isqrt N + 1) / 2) = LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 := rfl
        have hlay := layout ((isqrt N + 1) / 2)
        obtain ⟨y, hr, hf⟩ := outer_exit_cut x mem out N (isqrt N) p (LD ((isqrt N + 1) / 2)) h.pre
          h.size h.x18 h.x24 h.x12 h.x19 hpv hvb (by omega) (by omega) hp3 (by omega) (by omega) h.hN (by omega) hsk
        exact ⟨8, p, y, mem, hr, h.frame hf, by omega⟩
    · rw [if_pos ((skip_self_iff p hp3 hpo).mpr hprime)] at hsk
      obtain ⟨n1, y1, hr1, h1⟩ := round_skip N p x mem out h hpv hprime
      obtain ⟨n2, a, y2, mem2, hr2, h2, hc⟩ := outer_loop N (p + 2) y1 mem out h1
      exact ⟨n1 + n2, a, y2, mem2, by rw [run_add, hr1, hr2], h2, hc⟩
  · obtain ⟨y, hr, hf⟩ := outer_exit_v x mem out (isqrt N) p h.pre h.x18 h.x12 (by omega) (by omega)
    refine ⟨2, p, y, mem, hr, h.frame (fun r hr => hf r (fun hm => hr (by simp at hm; simp [hm]))), ?_⟩
    have h1 : (isqrt N + 1) * (isqrt N + 1) ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
    have h2 : p * p ≤ p * p * (p * p) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
    omega
termination_by isqrt N + 3 - p
decreasing_by all_goals omega

end TinyFive.GrumpyBinary
