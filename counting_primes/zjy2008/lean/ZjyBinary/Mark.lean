import GrumpyBinary.Outer
import ZjyBinary.Tactic

/-! The start of `calc(p)` (the lambda at 36): `skip[p] = 1`, and the loop at 84 marking the odd
multiples of `p` from `p²` to `R`. `calc` reaches its captures through the closure at `a0`; the
stack slots it reads are given as `readBytes` facts. -/
namespace TinyFive.ZjyBinary
open SieveMemory LucyMath GrumpyBinary

local notation "bv" => BitVec.ofNat 64

theorem _root_.TinyFive.GrumpyBinary.Same.zpre {mem mem' : Array (BitVec 8)} {lo hi : Nat}
    (h : Same mem mem' lo hi) (hp : Prefix image mem 1480) (hlo : 1480 ≤ lo) :
    Prefix image mem' 1480 :=
  fun i hi => by rw [h.frame i (by omega)]; exact hp i hi

/-- The marking loop at 84: `skip[i] = 1` for odd multiples `i` of `p` from `p²` to `v`. -/
theorem mark_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (D v p m : Nat)
    (g0 : Nat → Nat) (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = bv m) (h14 : x.get 14 = bv (p * 2)) (h16 : x.get 16 = bv 1)
    (h31 : x.get 31 = bv D) (h12 : x.get 12 = bv v)
    (hD : 1480 ≤ D) (hDv : D + (v + 1) ≤ 4194304) (hv : v < 1000000) (hp : p % 2 = 1)
    (hpv : p ≤ v) (hm : p ∣ m) (hm2 : m % 2 = 1) (hpm : p * p ≤ m) (hmv : m ≤ v + p * 2)
    (harr : Arr8 mem D (v + 1)
      (fun i => if p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 ∧ i < m then 1 else g0 i)) :
    ∃ k y mem', run k ⟨x, bv 84, mem, [], out, .running⟩ = ⟨y, bv 92, mem', [], out, .running⟩ ∧
      Same mem mem' D (D + (v + 1)) ∧
      Arr8 mem' D (v + 1) (fun i => if p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1 then 1 else g0 i) ∧
      (∀ r : Reg, r ∉ ([13, 15] : List Reg) → y.get r = x.get r) := by
  by_cases hmv' : m ≤ v
  · have hstep : ∃ y, run 6 ⟨x, bv 84, mem, [], out, .running⟩ =
        ⟨y, bv 84, wr mem (D + m) (bv 1) 1, [], out, .running⟩ ∧ y.get 15 = bv (m + p * 2) ∧
        (∀ r : Reg, r ∉ ([13, 15] : List Reg) → y.get r = x.get r) := by
      refine ⟨(((x.set 13 (bv m)).set 13 (bv (D + m))).set 15 (bv (m + p * 2))).set 0 208#64, ?_,
        by simp [Regs.get_set], by frame_tac⟩
      zexec
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
      (by rw [hfy 14 (by decide), h14]) (by rw [hfy 16 (by decide), h16])
      (by rw [hfy 31 (by decide), h31]) (by rw [hfy 12 (by decide), h12]) hD hDv hv hp hpv
      (Nat.dvd_add hm (Nat.dvd_mul_right p 2)) (by omega) (by omega) (by omega) harr'
    refine ⟨6 + k, z, mem', by rw [run_add, hr, hr2], ?_, harr2,
      fun r hr => by rw [hfz r hr, hfy r hr]⟩
    exact (Same.wr mem _ _ 1 D (D + (v + 1)) (by omega) (by omega) (by omega)).trans
      ⟨hsame.size_eq.trans (by simp), hsame.frame⟩
  · refine ⟨2, x.set 13 (bv m), mem, ?_, Same.refl _ _ _,
      harr.ext (fun i hi => by
        by_cases h : p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1
        · simp [h, show i < m by omega]
        · simp only [h, ite_false]; rw [if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩)]),
      by frame_tac⟩
    zexec
termination_by v + 1 - m

end TinyFive.ZjyBinary
