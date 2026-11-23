import GrumpyBinary.Layout
import GrumpyBinary.Newton

/-! The loops that set up `prime_pi`'s tables: the inlined Newton iteration for `isqrt`, and the
loops filling `smalls`, `roughs` and `larges`. -/
namespace TinyFive.GrumpyBinary
open SieveMemory LucyMath

local notation "bv" => BitVec.ofNat 64

/-- Memory changed only inside `[lo, hi)`. -/
structure Same (mem mem' : Array (BitVec 8)) (lo hi : Nat) : Prop where
  size_eq : mem'.size = mem.size
  frame : ∀ j, j < lo ∨ hi ≤ j → mem'[j]? = mem[j]?

theorem Same.refl (mem : Array (BitVec 8)) (lo hi : Nat) : Same mem mem lo hi := ⟨rfl, fun _ _ => rfl⟩

theorem Same.trans {m1 m2 m3 : Array (BitVec 8)} {lo hi : Nat} (h1 : Same m1 m2 lo hi)
    (h2 : Same m2 m3 lo hi) : Same m1 m3 lo hi :=
  ⟨h2.size_eq.trans h1.size_eq, fun j hj => (h2.frame j hj).trans (h1.frame j hj)⟩

theorem Same.wr (mem : Array (BitVec 8)) (a : Nat) {k : Nat} (v : BitVec k) (m lo hi : Nat)
    (h : a + m ≤ mem.size) (h1 : lo ≤ a) (h2 : a + m ≤ hi) : Same mem (GrumpyBinary.wr mem a v m) lo hi :=
  ⟨wr_size .., fun j hj => wr_get mem a v m h j (by omega)⟩

theorem Same.prefix {mem mem' : Array (BitVec 8)} {lo hi : Nat} (h : Same mem mem' lo hi)
    (hp : Prefix image mem 1236) (hlo : 1236 ≤ lo) : Prefix image mem' 1236 :=
  fun i hi => by rw [h.frame i (by omega)]; exact hp i hi

/-- `smalls[i] = i` for `1 ≤ i < s` (loop at 236). -/
theorem smalls_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A s i : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = bv i) (h9 : x.get 9 = bv s) (h20 : x.get 20 = bv A)
    (hA : 1236 ≤ A) (hAs : A + s * 4 ≤ 4194304) (hs : s < 2147483648) (hi : i ≤ s)
    (harr : Arr32 mem A s (fun j => if j < i then j else 0)) :
    ∃ k y mem', run k ⟨x, bv 236, mem, [], out, .running⟩ = ⟨y, bv 244, mem', [], out, .running⟩ ∧
      Same mem mem' A (A + s * 4) ∧ Arr32 mem' A s (fun j => j) ∧
      (∀ r : Reg, r ∉ ([13, 14, 15] : List Reg) → y.get r = x.get r) := by
  by_cases his : i < s
  · have hstep : ∃ y, run 7 ⟨x, bv 236, mem, [], out, .running⟩ =
        ⟨y, bv 236, wr mem (A + i * 4) (bv i) 4, [], out, .running⟩ ∧ y.get 15 = bv (i + 1) ∧
        (∀ r : Reg, r ∉ ([13, 14, 15] : List Reg) → y.get r = x.get r) := by
      refine ⟨((((x.set 13 (bv i)).set 14 (bv (i * 4))).set 14 (bv (A + i * 4))).set 15
        (bv (i + 1))).set 0 568#64, ?_, by simp [Regs.get_set], by frame_tac⟩
      gexec
    obtain ⟨y, hr, hy15, hfy⟩ := hstep
    have harr' := (harr.wr (by omega) i i his).ext (g := fun j => if j < i + 1 then j else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    obtain ⟨k, z, mem', hr2, hsame, harr2, hfz⟩ := smalls_loop y _ out A s (i + 1)
      (prefix_wr _ _ _ hmem (by omega) (by omega)) (by simp [hsz]) hy15
      (by rw [hfy 9 (by decide), h9]) (by rw [hfy 20 (by decide), h20]) hA hAs hs his harr'
    refine ⟨7 + k, z, mem', by rw [run_add, hr, hr2], ?_, harr2,
      fun r hr => by rw [hfz r hr, hfy r hr]⟩
    exact (Same.wr mem _ _ 4 A (A + s * 4) (by omega) (by omega) (by omega)).trans
      ⟨hsame.size_eq.trans (by simp), hsame.frame⟩
  · refine ⟨2, x.set 13 (bv i), mem, ?_, Same.refl _ _ _,
      harr.ext (fun j hj => by simp [show j < i by omega]), by frame_tac⟩
    gexec
termination_by s - i
/-- `roughs[i] = 2i + 1` for `i < s` (loop at 268). -/
theorem roughs_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A s i : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = bv i) (h9 : x.get 9 = bv s) (h21 : x.get 21 = bv A)
    (hA : 1236 ≤ A) (hAs : A + s * 4 ≤ 4194304) (hs : s < 2147483648) (hi : i ≤ s)
    (harr : Arr32 mem A s (fun j => if j < i then j * 2 + 1 else 0)) :
    ∃ k y mem', run k ⟨x, bv 268, mem, [], out, .running⟩ = ⟨y, bv 276, mem', [], out, .running⟩ ∧
      Same mem mem' A (A + s * 4) ∧ Arr32 mem' A s (fun j => j * 2 + 1) ∧
      (∀ r : Reg, r ∉ ([13, 14, 15] : List Reg) → y.get r = x.get r) := by
  by_cases his : i < s
  · have hstep : ∃ y, run 9 ⟨x, bv 268, mem, [], out, .running⟩ =
        ⟨y, bv 268, wr mem (A + i * 4) (bv (i * 2 + 1)) 4, [], out, .running⟩ ∧ y.get 15 = bv (i + 1) ∧
        (∀ r : Reg, r ∉ ([13, 14, 15] : List Reg) → y.get r = x.get r) := by
      refine ⟨((((((x.set 14 (bv i)).set 14 (bv (i * 4))).set 13 (bv (i * 2))).set 14 (bv (A + i * 4))).set 13
        (bv (i * 2 + 1))).set 15 (bv (i + 1))).set 0 596#64, ?_, by simp [Regs.get_set], by frame_tac⟩
      gexec
    obtain ⟨y, hr, hy15, hfy⟩ := hstep
    have harr' := (harr.wr (by omega) i (i * 2 + 1) his).ext (g := fun j => if j < i + 1 then j * 2 + 1 else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    obtain ⟨k, z, mem', hr2, hsame, harr2, hfz⟩ := roughs_loop y _ out A s (i + 1)
      (prefix_wr _ _ _ hmem (by omega) (by omega)) (by simp [hsz]) hy15
      (by rw [hfy 9 (by decide), h9]) (by rw [hfy 21 (by decide), h21]) hA hAs hs his harr'
    refine ⟨9 + k, z, mem', by rw [run_add, hr, hr2], ?_, harr2,
      fun r hr => by rw [hfz r hr, hfy r hr]⟩
    exact (Same.wr mem _ _ 4 A (A + s * 4) (by omega) (by omega) (by omega)).trans
      ⟨hsame.size_eq.trans (by simp), hsame.frame⟩
  · refine ⟨2, x.set 14 (bv i), mem, ?_, Same.refl _ _ _,
      harr.ext (fun j hj => by simp [show j < i by omega]), by frame_tac⟩
    gexec
termination_by s - i
/-- `larges[i] = (N / (2i + 1) - 1) / 2` for `i < s` (loop at 328). -/
theorem larges_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N Cb s i : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h14 : x.get 14 = bv i) (h9 : x.get 9 = bv s) (h8 : x.get 8 = bv Cb) (h19 : x.get 19 = bv N)
    (h12 : x.get 12 = bv 2)
    (hC : 1236 ≤ Cb) (hCs : Cb + s * 8 ≤ 4194304) (hsN : 2 * s ≤ N + 1) (hN : N < 100000000000)
    (hi : i ≤ s)
    (harr : Arr64 mem Cb s (fun j => if j < i then (N / (j * 2 + 1) - 1) / 2 else 0)) :
    ∃ k y mem', run k ⟨x, bv 328, mem, [], out, .running⟩ = ⟨y, bv 336, mem', [], out, .running⟩ ∧
      Same mem mem' Cb (Cb + s * 8) ∧ Arr64 mem' Cb s (fun j => (N / (j * 2 + 1) - 1) / 2) ∧
      (∀ r : Reg, r ∉ ([13, 14, 15] : List Reg) → y.get r = x.get r) := by
  by_cases his : i < s
  · have hd1 : 1 ≤ N / (i * 2 + 1) := Nat.div_pos (by omega) (by omega)
    have hd2 := Nat.div_le_self N (i * 2 + 1)
    have hstep : ∃ y, run 12 ⟨x, bv 328, mem, [], out, .running⟩ =
        ⟨y, bv 328, wr mem (Cb + i * 8) (bv ((N / (i * 2 + 1) - 1) / 2)) 8, [], out, .running⟩ ∧
        y.get 14 = bv (i + 1) ∧
        (∀ r : Reg, r ∉ ([13, 14, 15] : List Reg) → y.get r = x.get r) := by
      refine ⟨(((((((((x.set 15 (bv i)).set 15 (bv (i * 2))).set 15 (bv (i * 2 + 1))).set 15
        (bv (N / (i * 2 + 1)))).set 13 (bv (i * 8))).set 13 (bv (i * 8 + Cb))).set 14 (bv (i + 1))).set
        15 (bv (N / (i * 2 + 1) - 1))).set 15 (bv ((N / (i * 2 + 1) - 1) / 2))).set 0 636#64,
        ?_, by simp [Regs.get_set], by frame_tac⟩
      rw [show Cb + i * 8 = i * 8 + Cb by omega]
      gexec
    obtain ⟨y, hr, hy14, hfy⟩ := hstep
    have harr' := (harr.wr (by omega) i ((N / (i * 2 + 1) - 1) / 2) his).ext
      (g := fun j => if j < i + 1 then (N / (j * 2 + 1) - 1) / 2 else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    obtain ⟨k, z, mem', hr2, hsame, harr2, hfz⟩ := larges_loop y _ out N Cb s (i + 1)
      (prefix_wr _ _ _ hmem (by omega) (by omega)) (by simp [hsz]) hy14
      (by rw [hfy 9 (by decide), h9]) (by rw [hfy 8 (by decide), h8])
      (by rw [hfy 19 (by decide), h19]) (by rw [hfy 12 (by decide), h12]) hC hCs hsN hN his harr'
    refine ⟨12 + k, z, mem', by rw [run_add, hr, hr2], ?_, harr2,
      fun r hr => by rw [hfz r hr, hfy r hr]⟩
    exact (Same.wr mem _ _ 8 Cb (Cb + s * 8) (by omega) (by omega) (by omega)).trans
      ⟨hsame.size_eq.trans (by simp), hsame.frame⟩
  · refine ⟨2, x.set 15 (bv i), mem, ?_, Same.refl _ _ _,
      harr.ext (fun j hj => by simp [show j < i by omega]), by frame_tac⟩
    gexec
termination_by s - i

/-- The Newton loop of `isqrt64` (inlined at 192) ends with `s6 = isqrt N`. -/
theorem newton_loop (N : Nat) (hN : 1 ≤ N) (hN' : N < 100000000000) (X : Nat) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1236) (h19 : x.get 19 = bv N) (h22 : x.get 22 = bv X)
    (h15 : x.get 15 = bv ((X + N / X) / 2)) (hX : isqrt N ≤ X) (hXN : X ≤ N) :
    ∃ k y, run k ⟨x, bv 192, mem, [], out, .running⟩ = ⟨y, bv 196, mem, [], out, .running⟩ ∧
      y.get 22 = bv (isqrt N) ∧
      (∀ i : Reg, i ∉ ([14, 15, 22] : List Reg) → y.get i = x.get i) := by
  have hX1 : 1 ≤ isqrt N := le_isqrt (by omega)
  have hY := newton_ge N X (by omega)
  have hdX := Nat.div_le_self N X
  by_cases hlt : (X + N / X) / 2 < X
  · have hstep : ∃ y, run 6 ⟨x, bv 192, mem, [], out, .running⟩ =
        ⟨y, bv 192, mem, [], out, .running⟩ ∧ y.get 22 = bv ((X + N / X) / 2) ∧
        y.get 15 = bv (((X + N / X) / 2 + N / ((X + N / X) / 2)) / 2) ∧
        (∀ i : Reg, i ∉ ([14, 15, 22] : List Reg) → y.get i = x.get i) := by
      have hdY := Nat.div_le_self N ((X + N / X) / 2)
      refine ⟨((((x.set 14 (bv (N / ((X + N / X) / 2)))).set 22 (bv ((X + N / X) / 2))).set 14
        (bv (N / ((X + N / X) / 2) + (X + N / X) / 2))).set 15
        (bv ((N / ((X + N / X) / 2) + (X + N / X) / 2) / 2))).set 0 548#64, ?_, ?_, ?_, ?_⟩
      · gexec
      · simp [Regs.get_set]
      · simp [Regs.get_set]; congr 1; omega
      · frame_tac
    obtain ⟨y, hr, hy22, hy15, hfy⟩ := hstep
    obtain ⟨k, z, hr2, hz22, hfz⟩ := newton_loop N hN hN' ((X + N / X) / 2) y mem out hmem
      (by rw [hfy 19 (by decide), h19]) hy22 hy15 hY (by omega)
    refine ⟨6 + k, z, by rw [run_add, hr, hr2], hz22, fun i hi => by rw [hfz i hi, hfy i hi]⟩
  · have hXX : X * X ≤ N := by
      have : X ≤ N / X := by omega
      exact (Nat.le_div_iff_mul_le (by omega)).mp this
    have hXe : X = isqrt N := Nat.le_antisymm (le_isqrt hXX) hX
    refine ⟨1, x, ?_, by rw [h22, hXe], fun _ _ => rfl⟩
    clear hXe
    gexec
termination_by X
decreasing_by omega
end TinyFive.GrumpyBinary
