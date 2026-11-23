import ZjyBinary.Wheel
import ZjyBinary.Memset
import GrumpyBinary.Init
import GrumpyBinary.Setup

/-! From the entry at 0 to `pi`'s wheel loop (1296) or straight to the finish (956): the call,
the prologue, the two Newton loops (`R = isqrt n`, `isqrt R`), the four tables, the closure,
and `calc(3)`, `calc(5)`. Also the small inputs `n ≤ 6`. -/
namespace TinyFive.ZjyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

set_option linter.unusedVariables false

theorem _root_.TinyFive.GrumpyBinary.Same.wid {m m' : Array (BitVec 8)} {lo hi : Nat}
    (h : Same m m' lo hi) (lo' hi' : Nat) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : Same m m' lo' hi' :=
  ⟨h.size_eq, fun j hj => h.frame j (by omega)⟩

/-- Discharges `Same m (wr (wr … ) …) lo hi` for a chain of writes inside `[lo, hi)`. -/
macro "same_tac" : tactic => `(tactic| (
  repeat (refine Same.wr' ?_ _ _ _ (by first | omega | (simp only [wr_size]; omega)) (by omega) (by omega))
  exact Same.refl _ _ _))

/-- Reads through a chain of writes: skips disjoint ones, then reads the matching one. -/
macro "rd_tac" : tactic => `(tactic| (
  repeat rw [read_wr_other _ _ _ _ _ _ (by first | omega | (simp only [wr_size]; omega)) (by omega)]
  first
    | (rw [read_wr_same _ _ _ _ (by first | omega | (simp only [wr_size]; omega))]; first | rfl | simp | simp [*])
    | assumption))

/-- 0 → 664: the call, `pi`'s prologue (saving `ra = 8` and eight zero registers, and `n`),
and the branch `6 < n`. -/
theorem setup_entry (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv N) (hN : 7 ≤ N)
    (hN' : N < 100000000000) :
    ∃ y mem', run 15 ⟨x, 0, mem, [], out, .running⟩ = ⟨y, bv 664, mem', [], out, .running⟩ ∧
      Same mem mem' 4194104 4194304 ∧ readBytes mem' 4194104 8 = some (bv N) ∧
      readBytes mem' 4194296 8 = some (bv 8) ∧ y.get 2 = bv 4194096 ∧ y.get 10 = bv N ∧
      (∀ r : Reg, r ∉ ([1, 2, 15] : List Reg) → y.get r = x.get r) := by
  have h1 := hx 1 (by decide)
  have h2 := hx 2 (by decide)
  have h15 := hx 15 (by decide)
  refine ⟨_, _, by zexec; exact ⟨rfl, rfl⟩, by same_tac, by rd_tac, by rd_tac, by simp [Regs.get_set],
    by simp [Regs.get_set, h10], by frame_tac⟩

/-- 0 → 620 for `n ≤ 6`: `pi` returns `π(n)` from the table-free branch. -/
theorem setup_small (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv N) (hN : N ≤ 6) :
    ∃ y mem', run 23 ⟨x, 0, mem, [], out, .running⟩ = ⟨y, bv 620, mem', [], out, .running⟩ ∧
      Prefix image mem' 1480 ∧ mem'.size = 4194304 ∧
      readBytes mem' 4194296 8 = some (bv 8) ∧ y.get 2 = bv 4194096 ∧
      y.get 10 = bv (countPrimes N) := by
  have h1 := hx 1 (by decide)
  have h2 := hx 2 (by decide)
  rcases (by omega : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · refine ⟨_, _, by zexec; exact ⟨rfl, rfl⟩, fun i hi => ?_, by first | omega | (simp only [wr_size]; omega), by rd_tac,
      by simp [Regs.get_set], ?_⟩
    · repeat rw [wr_get _ _ _ _ (by first | omega | (simp only [wr_size]; omega)) i (by omega)]
      exact hmem i hi
    · simp [Regs.get_set]; decide

/-- The Newton loop at 676 (body at 1128) for `isqrt` of `x10`, with `x = x11`, `y = x15`. -/
theorem newton1 (N : Nat) (hN : 1 ≤ N) (hN' : N < 100000000000) (X : Nat) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1480) (hn : x.get 10 = bv N) (hx : x.get 11 = bv X)
    (h15 : x.get 15 = bv ((X + N / X) / 2)) (hX : isqrt N ≤ X) (hXN : X ≤ N) :
    ∃ k y, run k ⟨x, bv 676, mem, [], out, .running⟩ = ⟨y, bv 680, mem, [], out, .running⟩ ∧
      y.get 11 = bv (isqrt N) ∧
      (∀ i : Reg, i ∉ ([14, 15, 11] : List Reg) → y.get i = x.get i) := by
  have hX1 : 1 ≤ isqrt N := le_isqrt (by omega)
  have hY := newton_ge N X (by omega)
  have hdX := Nat.div_le_self N X
  by_cases hlt : (X + N / X) / 2 < X
  · have hdY := Nat.div_le_self N ((X + N / X) / 2)
    obtain ⟨y, hr, hyX, hy15, hfy⟩ : ∃ y, run 6 ⟨x, bv 676, mem, [], out, .running⟩ =
        ⟨y, bv 676, mem, [], out, .running⟩ ∧ y.get 11 = bv ((X + N / X) / 2) ∧
        y.get 15 = bv (((X + N / X) / 2 + N / ((X + N / X) / 2)) / 2) ∧
        (∀ i : Reg, i ∉ ([14, 15, 11] : List Reg) → y.get i = x.get i) :=
      ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set]; congr 1; omega, by frame_tac⟩
    obtain ⟨k, z, hr2, hzX, hfz⟩ := newton1 N hN hN' ((X + N / X) / 2) y mem out hmem
      (by rw [hfy 10 (by decide), hn]) hyX hy15 hY (by omega)
    exact ⟨6 + k, z, by rw [run_add, hr, hr2], hzX, fun i hi => by rw [hfz i hi, hfy i hi]⟩
  · have hXX : X * X ≤ N := by
      have : X ≤ N / X := by omega
      exact (Nat.le_div_iff_mul_le (by omega)).mp this
    have hXe : X = isqrt N := Nat.le_antisymm (le_isqrt hXX) hX
    refine ⟨1, x, ?_, by rw [hx, hXe], fun _ _ => rfl⟩
    clear hXe
    zexec
termination_by X
decreasing_by omega

/-- The Newton loop at 700 (body at 1148) for `isqrt` of `x11`, with `x = x19`, `y = x15`. -/
theorem newton2 (N : Nat) (hN : 1 ≤ N) (hN' : N < 100000000000) (X : Nat) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1480) (hn : x.get 11 = bv N) (hx : x.get 19 = bv X)
    (h15 : x.get 15 = bv ((X + N / X) / 2)) (hX : isqrt N ≤ X) (hXN : X ≤ N) :
    ∃ k y, run k ⟨x, bv 700, mem, [], out, .running⟩ = ⟨y, bv 704, mem, [], out, .running⟩ ∧
      y.get 19 = bv (isqrt N) ∧
      (∀ i : Reg, i ∉ ([14, 15, 19] : List Reg) → y.get i = x.get i) := by
  have hX1 : 1 ≤ isqrt N := le_isqrt (by omega)
  have hY := newton_ge N X (by omega)
  have hdX := Nat.div_le_self N X
  by_cases hlt : (X + N / X) / 2 < X
  · have hdY := Nat.div_le_self N ((X + N / X) / 2)
    obtain ⟨y, hr, hyX, hy15, hfy⟩ : ∃ y, run 6 ⟨x, bv 700, mem, [], out, .running⟩ =
        ⟨y, bv 700, mem, [], out, .running⟩ ∧ y.get 19 = bv ((X + N / X) / 2) ∧
        y.get 15 = bv (((X + N / X) / 2 + N / ((X + N / X) / 2)) / 2) ∧
        (∀ i : Reg, i ∉ ([14, 15, 19] : List Reg) → y.get i = x.get i) :=
      ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set]; congr 1; omega, by frame_tac⟩
    obtain ⟨k, z, hr2, hzX, hfz⟩ := newton2 N hN hN' ((X + N / X) / 2) y mem out hmem
      (by rw [hfy 11 (by decide), hn]) hyX hy15 hY (by omega)
    exact ⟨6 + k, z, by rw [run_add, hr, hr2], hzX, fun i hi => by rw [hfz i hi, hfy i hi]⟩
  · have hXX : X * X ≤ N := by
      have : X ≤ N / X := by omega
      exact (Nat.le_div_iff_mul_le (by omega)).mp this
    have hXe : X = isqrt N := Nat.le_antisymm (le_isqrt hXX) hX
    refine ⟨1, x, ?_, by rw [hx, hXe], fun _ _ => rfl⟩
    clear hXe
    zexec
termination_by X
decreasing_by omega

/-- The table loop at 876: `small[i] = i`, `rough[i] = 2i + 1`, `large[i] = (n / (2i + 1) - 1) / 2`
for `i < s`, leaving the skip bitmap (between `rough` and `large`) alone. -/
theorem init_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N s A B D L Cb i : Nat)
    (g : Nat → Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h8 : x.get 8 = bv A) (h9 : x.get 9 = bv B) (h18 : x.get 18 = bv Cb) (h2 : x.get 2 = bv 4194096)
    (h14 : x.get 14 = bv i) (h13 : x.get 13 = bv (2 * i + 1))
    (hV : readBytes mem 4194124 4 = some (BitVec.ofNat 32 s))
    (hn : readBytes mem 4194104 8 = some (bv N))
    (hA : 1520 ≤ A) (hAB : A + s * 4 ≤ B) (hBD : B + s * 4 ≤ D) (hDC : D + L ≤ Cb)
    (hC : Cb + s * 8 ≤ 4194000)
    (hs : s < 1000000) (his : i ≤ s) (hN : N < 100000000000) (hsN : 2 * s ≤ N + 1)
    (hsm : Arr32 mem A s (fun j => if j < i then j else 0))
    (hro : Arr32 mem B s (fun j => if j < i then 2 * j + 1 else 0))
    (hla : Arr64 mem Cb s (fun j => if j < i then (N / (2 * j + 1) - 1) / 2 else 0))
    (hsk : Arr8 mem D L g) :
    ∃ k y mem', run k ⟨x, bv 876, mem, [], out, .running⟩ = ⟨y, bv 888, mem', [], out, .running⟩ ∧
      Same mem mem' A (Cb + s * 8) ∧ Arr32 mem' A s (fun j => j) ∧
      Arr32 mem' B s (fun j => 2 * j + 1) ∧ Arr64 mem' Cb s (fun j => (N / (2 * j + 1) - 1) / 2) ∧
      Arr8 mem' D L g ∧
      (∀ r : Reg, r ∉ ([11, 12, 13, 14, 15] : List Reg) → y.get r = x.get r) := by
  by_cases hi : i < s
  · have hd1 : 1 ≤ N / (2 * i + 1) := Nat.div_pos (by omega) (by omega)
    have hd2 := Nat.div_le_self N (2 * i + 1)
    obtain ⟨y, hr, y14, y13, fy⟩ : ∃ y, run 18 ⟨x, bv 876, mem, [], out, .running⟩ = ⟨y, bv 876,
        wr (wr (wr mem (A + i * 4) (bv i) 4) (B + i * 4) (bv (2 * i + 1)) 4) (Cb + i * 8)
          (bv ((N / (2 * i + 1) - 1) / 2)) 8, [], out, .running⟩ ∧ y.get 14 = bv (i + 1) ∧
        y.get 13 = bv (2 * (i + 1) + 1) ∧
        (∀ r : Reg, r ∉ ([11, 12, 13, 14, 15] : List Reg) → y.get r = x.get r) :=
      ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set]; (try congr 1); try omega, by frame_tac⟩
    have S1 := Same.ofwr mem (A + i * 4) (bv i) 4 (by omega)
    have S2 := Same.ofwr (wr mem (A + i * 4) (bv i) 4) (B + i * 4) (bv (2 * i + 1)) 4
      (by simp only [wr_size]; omega)
    have S3 := Same.ofwr (wr (wr mem (A + i * 4) (bv i) 4) (B + i * 4) (bv (2 * i + 1)) 4) (Cb + i * 8)
      (bv ((N / (2 * i + 1) - 1) / 2)) 8 (by simp only [wr_size]; omega)
    have sm1 := (hsm.wr (by omega) i i hi).ext (g := fun j => if j < i + 1 then j else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    have sm3 := S3.arr32 (S2.arr32 sm1 (by omega)) (by omega)
    have ro1 := S1.arr32 hro (by omega)
    have ro2 := (ro1.wr (by simp only [wr_size]; omega) i (2 * i + 1) hi).ext
      (g := fun j => if j < i + 1 then 2 * j + 1 else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    have ro3 := S3.arr32 ro2 (by omega)
    have la2 := S2.arr64 (S1.arr64 hla (by omega)) (by omega)
    have la3 := (la2.wr (by simp only [wr_size]; omega) i ((N / (2 * i + 1) - 1) / 2) hi).ext
      (g := fun j => if j < i + 1 then (N / (2 * j + 1) - 1) / 2 else 0)
      (fun j _ => by
        by_cases hj : j = i
        · subst hj; simp
        · rw [upd_other _ _ _ _ hj]; by_cases h1 : j < i <;> simp [h1] <;> omega)
    have sk3 := S3.arr8 (S2.arr8 (S1.arr8 hsk (by omega)) (by omega)) (by omega)
    have S := (S1.wid A (Cb + s * 8) (by omega) (by omega)).trans
      ((S2.wid A (Cb + s * 8) (by omega) (by omega)).trans (S3.wid A (Cb + s * 8) (by omega) (by omega)))
    obtain ⟨k, z, mem', hr2, S', sm', ro', la', sk', fz⟩ := init_loop y _ out N s A B D L Cb (i + 1) g
      (S.zpre hmem (by omega)) (by rw [S.size_eq, hsz])
      (by rw [fy 8 (by decide), h8]) (by rw [fy 9 (by decide), h9]) (by rw [fy 18 (by decide), h18])
      (by rw [fy 2 (by decide), h2]) y14 y13 (S.read hV (by omega)) (S.read hn (by omega))
      hA hAB hBD hDC hC hs hi hN hsN sm3 ro3 la3 sk3
    exact ⟨18 + k, z, mem', by rw [run_add, hr, hr2], S.trans S', sm', ro', la', sk',
      fun r hr => by rw [fz r hr, fy r hr]⟩
  · have hie : i = s := by omega
    subst hie
    refine ⟨3, _, mem, by zexec; rfl, Same.refl _ _ _, hsm.ext (fun j hj => by simp [hj]),
      hro.ext (fun j hj => by simp [hj]), hla.ext (fun j hj => by simp [hj]), hsk, by frame_tac⟩
termination_by s - i

/-- 664 → 676: the first Newton step `(n + 1) / 2`. -/
theorem seg_n1 (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1480) (h10 : x.get 10 = bv N) (hN : N < 100000000000) :
    ∃ y, run 3 ⟨x, bv 664, mem, [], out, .running⟩ = ⟨y, bv 676, mem, [], out, .running⟩ ∧
      y.get 11 = bv N ∧ y.get 15 = bv ((N + 1) / 2) ∧
      (∀ r : Reg, r ∉ ([11, 15] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set, h10], by simp [Regs.get_set], by frame_tac⟩

/-- 680 → 700: store `R = isqrt n`, and the first Newton step of `isqrt R`. -/
theorem seg_r (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h11 : x.get 11 = bv R)
    (h2 : x.get 2 = bv 4194096) (hR : R < 316228) :
    ∃ y, run 5 ⟨x, bv 680, mem, [], out, .running⟩ =
        ⟨y, bv 700, wr mem 4194116 (bv R) 4, [], out, .running⟩ ∧
      y.get 11 = bv R ∧ y.get 19 = bv R ∧ y.get 15 = bv ((R + 1) / 2) ∧
      (∀ r : Reg, r ∉ ([11, 15, 19] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by frame_tac⟩

/-- 704 → 1428: `V = (R + 1) / 2`, `C = 0`, and the call constructing `small`. -/
theorem seg_v (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h11 : x.get 11 = bv R)
    (h2 : x.get 2 = bv 4194096) (hR : R < 316228) :
    ∃ y mem', run 12 ⟨x, bv 704, mem, [], out, .running⟩ =
        ⟨y, bv 1428, mem', [], out, .running⟩ ∧ Same mem mem' 4194120 4194128 ∧ mem'.size = 4194304 ∧
      readBytes mem' 4194120 4 = some (BitVec.ofNat 32 0) ∧
      readBytes mem' 4194124 4 = some (BitVec.ofNat 32 ((R + 1) / 2)) ∧
      y.get 1 = bv 752 ∧ y.get 10 = bv 4194128 ∧ y.get 11 = bv ((R + 1) / 2) ∧
      y.get 20 = bv 4194128 ∧ y.get 21 = bv 4194136 ∧ y.get 18 = bv 1512 ∧
      (∀ r : Reg, r ∉ ([1, 10, 11, 15, 18, 20, 21] : List Reg) → y.get r = x.get r) :=
  ⟨_, _, by zexec; exact ⟨rfl, rfl⟩, by same_tac, by simp only [wr_size]; omega, by rd_tac, by rd_tac,
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

/-- 752 → 1428: the call constructing `rough`. -/
theorem seg_c (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h21 : x.get 21 = bv 4194136)
    (h2 : x.get 2 = bv 4194096) (hV : readBytes mem 4194124 4 = some (BitVec.ofNat 32 s))
    (hs : s < 200000) :
    ∃ y, run 4 ⟨x, bv 752, mem, [], out, .running⟩ = ⟨y, bv 1428, mem, [], out, .running⟩ ∧
      y.get 1 = bv 768 ∧ y.get 10 = bv 4194136 ∧ y.get 11 = bv s ∧
      (∀ r : Reg, r ∉ ([1, 10, 11] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set, h21], by simp [Regs.get_set],
    by frame_tac⟩

/-- 768 → 508: `skip` at the 8-aligned heap cursor, and `memset(skip, 0, R + 1)`. -/
theorem seg_d (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (H R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h2 : x.get 2 = bv 4194096)
    (h18 : x.get 18 = bv 1512) (hH : readBytes mem 1512 8 = some (bv H)) (hR : readBytes mem 4194116 4 = some (BitVec.ofNat 32 R))
    (hHb : H < 4000000) (hRb : R < 316228) :
    ∃ y mem', run 11 ⟨x, bv 768, mem, [], out, .running⟩ = ⟨y, bv 508, mem', [], out, .running⟩ ∧
      Same mem mem' 4194144 4194152 ∧ mem'.size = 4194304 ∧
      readBytes mem' 4194144 8 = some (bv ((H + 7) / 8 * 8)) ∧
      y.get 1 = bv 812 ∧ y.get 8 = bv ((H + 7) / 8 * 8) ∧ y.get 9 = bv (R + 1) ∧
      y.get 10 = bv ((H + 7) / 8 * 8) ∧ y.get 11 = bv 0 ∧ y.get 12 = bv (R + 1) ∧
      (∀ r : Reg, r ∉ ([1, 8, 9, 10, 11, 12] : List Reg) → y.get r = x.get r) :=
  ⟨_, _, by zexec; exact ⟨rfl, rfl⟩, by same_tac, by simp only [wr_size]; omega, by rd_tac,
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

/-- 812 → 508: `large` after `skip`, recorded in the heap cursor, and `memset(large, 0, 8s)`. -/
theorem seg_e (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (D R s : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h2 : x.get 2 = bv 4194096)
    (h8 : x.get 8 = bv D) (h9 : x.get 9 = bv (R + 1)) (h18 : x.get 18 = bv 1512)
    (hV : readBytes mem 4194124 4 = some (BitVec.ofNat 32 s))
    (hD : D < 4000000) (hRb : R < 316228) (hs : s < 200000) :
    ∃ y, run 11 ⟨x, bv 812, mem, [], out, .running⟩ = ⟨y, bv 508,
        wr (wr mem 1512 (bv ((D + (R + 1 + 7)) / 8 * 8 + s * 8)) 8) 4194152
          (bv ((D + (R + 1 + 7)) / 8 * 8)) 8, [], out, .running⟩ ∧
      y.get 1 = bv 856 ∧ y.get 10 = bv ((D + (R + 1 + 7)) / 8 * 8) ∧ y.get 11 = bv 0 ∧
      y.get 12 = bv (s * 8) ∧
      (∀ r : Reg, r ∉ ([1, 9, 10, 11, 12, 15] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by frame_tac⟩

/-- 856 → 876: load the table pointers; `rough` index 0 holds odd number 1. -/
theorem seg_f (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A B Cb : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h2 : x.get 2 = bv 4194096)
    (hA : readBytes mem 4194128 8 = some (bv A)) (hB : readBytes mem 4194136 8 = some (bv B))
    (hC : readBytes mem 4194152 8 = some (bv Cb)) :
    ∃ y, run 5 ⟨x, bv 856, mem, [], out, .running⟩ = ⟨y, bv 876, mem, [], out, .running⟩ ∧
      y.get 8 = bv A ∧ y.get 9 = bv B ∧ y.get 18 = bv Cb ∧ y.get 13 = bv (2 * 0 + 1) ∧
      y.get 14 = bv 0 ∧
      (∀ r : Reg, r ∉ ([8, 9, 13, 14, 18] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩

/-- 888 → 1228: the closure `{&skip, &R, &V, &rough, &large, &small, &C, &n}` at 4194160, and the
branch on `8 < R`. -/
theorem seg_g (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h2 : x.get 2 = bv 4194096)
    (h20 : x.get 20 = bv 4194128) (h21 : x.get 21 = bv 4194136)
    (hR : readBytes mem 4194116 4 = some (BitVec.ofNat 32 R)) (hRb : R < 316228) (hc : 8 < R) :
    ∃ y mem', run 17 ⟨x, bv 888, mem, [], out, .running⟩ = ⟨y, bv 1228, mem', [], out, .running⟩ ∧
      Same mem mem' 4194160 4194224 ∧ mem'.size = 4194304 ∧
      readBytes mem' 4194160 8 = some (bv 4194144) ∧ readBytes mem' 4194168 8 = some (bv 4194116) ∧
      readBytes mem' 4194176 8 = some (bv 4194124) ∧ readBytes mem' 4194184 8 = some (bv 4194136) ∧
      readBytes mem' 4194192 8 = some (bv 4194152) ∧ readBytes mem' 4194200 8 = some (bv 4194128) ∧
      readBytes mem' 4194208 8 = some (bv 4194120) ∧ readBytes mem' 4194216 8 = some (bv 4194104) ∧
      (∀ r : Reg, r ∉ ([14, 15] : List Reg) → y.get r = x.get r) :=
  ⟨_, _, by zexec; exact ⟨rfl, rfl⟩, by same_tac, by simp only [wr_size]; omega, by rd_tac, by rd_tac,
    by rd_tac, by rd_tac, by rd_tac, by rd_tac, by rd_tac, by rd_tac, by frame_tac⟩

/-- 888 → 956: the closure `{&skip, &R, &V, &rough, &large, &small, &C, &n}` at 4194160, and the
branch on `8 < R`. -/
theorem seg_g0 (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h2 : x.get 2 = bv 4194096)
    (h20 : x.get 20 = bv 4194128) (h21 : x.get 21 = bv 4194136)
    (hR : readBytes mem 4194116 4 = some (BitVec.ofNat 32 R)) (hRb : R < 316228) (hc : R ≤ 8) :
    ∃ y mem', run 17 ⟨x, bv 888, mem, [], out, .running⟩ = ⟨y, bv 956, mem', [], out, .running⟩ ∧
      Same mem mem' 4194160 4194224 ∧ mem'.size = 4194304 ∧
      readBytes mem' 4194160 8 = some (bv 4194144) ∧ readBytes mem' 4194168 8 = some (bv 4194116) ∧
      readBytes mem' 4194176 8 = some (bv 4194124) ∧ readBytes mem' 4194184 8 = some (bv 4194136) ∧
      readBytes mem' 4194192 8 = some (bv 4194152) ∧ readBytes mem' 4194200 8 = some (bv 4194128) ∧
      readBytes mem' 4194208 8 = some (bv 4194120) ∧ readBytes mem' 4194216 8 = some (bv 4194104) ∧
      (∀ r : Reg, r ∉ ([14, 15] : List Reg) → y.get r = x.get r) :=
  ⟨_, _, by zexec; exact ⟨rfl, rfl⟩, by same_tac, by simp only [wr_size]; omega, by rd_tac, by rd_tac,
    by rd_tac, by rd_tac, by rd_tac, by rd_tac, by rd_tac, by rd_tac, by frame_tac⟩

/-- 1228 → 36: `calc(3)`, returning to 1248. -/
theorem seg_h (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1480) (h2 : x.get 2 = bv 4194096) :
    ∃ y, run 5 ⟨x, bv 1228, mem, [], out, .running⟩ = ⟨y, bv 36, mem, [], out, .running⟩ ∧
      y.get 1 = bv 1248 ∧ y.get 10 = bv 4194160 ∧ y.get 11 = bv 3 ∧ y.get 22 = bv 4194160 ∧
      (∀ r : Reg, r ∉ ([1, 10, 11, 22] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by frame_tac⟩

/-- 1248 → 956 when `R ≤ 24`. -/
theorem seg_i0 (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h2 : x.get 2 = bv 4194096)
    (hR : readBytes mem 4194116 4 = some (BitVec.ofNat 32 R)) (hRb : R < 316228) (hc : R ≤ 24) :
    ∃ y, run 3 ⟨x, bv 1248, mem, [], out, .running⟩ = ⟨y, bv 956, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([14, 15] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by frame_tac⟩

/-- 1248 → 36 when `24 < R`: `calc(5)`, returning to 1280. -/
theorem seg_i (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (R q : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304) (h2 : x.get 2 = bv 4194096)
    (h22 : x.get 22 = bv 4194160) (h19 : x.get 19 = bv q) (hq : q < 1000)
    (hR : readBytes mem 4194116 4 = some (BitVec.ofNat 32 R)) (hRb : R < 316228) (hc : 24 < R) :
    ∃ y, run 8 ⟨x, bv 1248, mem, [], out, .running⟩ = ⟨y, bv 36, mem, [], out, .running⟩ ∧
      y.get 1 = bv 1280 ∧ y.get 10 = bv 4194160 ∧ y.get 11 = bv 5 ∧ y.get 19 = bv q ∧
      (∀ r : Reg, r ∉ ([1, 10, 11, 14, 15, 19] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set, h22], by simp [Regs.get_set],
    by simp [Regs.get_set], by frame_tac⟩

/-- 1280 → 1296: the wheel starts at `p = 7`, `c = 0`. -/
theorem seg_k (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 1480) :
    ∃ y, run 4 ⟨x, bv 1280, mem, [], out, .running⟩ = ⟨y, bv 1296, mem, [], out, .running⟩ ∧
      y.get 20 = bv 7 ∧ y.get 21 = bv 0 ∧ y.get 23 = bv 1480 ∧
      (∀ r : Reg, r ∉ ([20, 21, 23] : List Reg) → y.get r = x.get r) :=
  ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by frame_tac⟩

/-! ## Gluing: from the entry to the closure -/

/-- Moves a read back through the `Same` facts in context. -/
macro "tr_rd" : tactic => `(tactic| (repeat (first | with_reducible assumption |
  (refine Same.read (by with_reducible assumption) ?_ (by omega)))))

/-- Moves an array fact back through the `Same` facts in context. -/
macro "tr_arr" : tactic => `(tactic| (repeat (first | with_reducible assumption |
  (refine Same.arr32 (by with_reducible assumption) ?_ (by omega)) | (refine Same.arr64 (by with_reducible assumption) ?_ (by omega)) |
  (refine Same.arr8 (by with_reducible assumption) ?_ (by omega)))))

/-- Moves a code-prefix fact back through the `Same` facts in context. -/
macro "tr_pfx" : tactic => `(tactic| (repeat (first | with_reducible assumption |
  (refine Same.pfx (by with_reducible assumption) ?_ (by omega)))))

/-- The state at 888, after the tables are built: `v = isqrt n`, `s = (v + 1) / 2`. -/
structure Tab (N : Nat) (y : Regs 64) (mem : Array (BitVec 8)) : Prop where
  size : mem.size = 4194304
  wh : Prefix image mem 1512
  ra : readBytes mem 4194296 8 = some (bv 8)
  n : readBytes mem 4194104 8 = some (bv N)
  R : readBytes mem 4194116 4 = some (BitVec.ofNat 32 (isqrt N))
  C : readBytes mem 4194120 4 = some (BitVec.ofNat 32 0)
  V : readBytes mem 4194124 4 = some (BitVec.ofNat 32 ((isqrt N + 1) / 2))
  psm : readBytes mem 4194128 8 = some (bv 1520)
  pro : readBytes mem 4194136 8 = some (bv (ZB ((isqrt N + 1) / 2)))
  psk : readBytes mem 4194144 8 = some (bv (ZD ((isqrt N + 1) / 2)))
  pla : readBytes mem 4194152 8 = some (bv (ZC ((isqrt N + 1) / 2) (isqrt N)))
  sm : Arr32 mem 1520 ((isqrt N + 1) / 2) (fun j => j)
  ro : Arr32 mem (ZB ((isqrt N + 1) / 2)) ((isqrt N + 1) / 2) (fun j => 2 * j + 1)
  la : Arr64 mem (ZC ((isqrt N + 1) / 2) (isqrt N)) ((isqrt N + 1) / 2) (fun j => (N / (2 * j + 1) - 1) / 2)
  sk : Arr8 mem (ZD ((isqrt N + 1) / 2)) (isqrt N + 1) (fun _ => 0)
  x2 : y.get 2 = bv 4194096
  x8 : y.get 8 = bv 1520
  x9 : y.get 9 = bv (ZB ((isqrt N + 1) / 2))
  x18 : y.get 18 = bv (ZC ((isqrt N + 1) / 2) (isqrt N))
  x19 : y.get 19 = bv (isqrt (isqrt N))
  x20 : y.get 20 = bv 4194128
  x21 : y.get 21 = bv 4194136

theorem rd32 (m : Array (BitVec 8)) (a v : Nat) (hs : a + 4 ≤ m.size) :
    readBytes (wr m a (bv v) 4) a 4 = some (BitVec.ofNat 32 v) := by
  rw [read_wr_same _ _ _ _ hs]; simp

theorem rd64 (m : Array (BitVec 8)) (a v : Nat) (hs : a + 8 ≤ m.size) :
    readBytes (wr m a (bv v) 8) a 8 = some (bv v) := by
  rw [read_wr_same _ _ _ _ hs]; simp

/-- From the entry at 0 to 888, for `7 ≤ n`: `isqrt`, the four tables. -/
theorem pi_tables (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1520) (hsz : mem.size = 4194304)
    (hheap : readBytes mem 1512 8 = some (bv 1520))
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv N) (hN7 : 7 ≤ N)
    (hN : N < 100000000000) :
    ∃ n y mem', run n ⟨x, 0, mem, [], out, .running⟩ = ⟨y, bv 888, mem', [], out, .running⟩ ∧
      Tab N y mem' := by
  have hv := isqrt_spec N
  have hvb : isqrt N < 316228 := r_lt_of_sq hv.1 hN
  have hv1 : 2 ≤ isqrt N := le_isqrt (by omega)
  have hvN : isqrt N ≤ N := Nat.le_trans (Nat.le_mul_self _) hv.1
  have hq := isqrt_spec (isqrt N)
  have hqv : isqrt (isqrt N) ≤ isqrt N := Nat.le_trans (Nat.le_mul_self _) hq.1
  have hlay := zlayout ((isqrt N + 1) / 2) (isqrt N)
  have hZB : ZB ((isqrt N + 1) / 2) = (1520 + 4 * ((isqrt N + 1) / 2) + 7) / 8 * 8 := rfl
  have hZD : ZD ((isqrt N + 1) / 2) = (ZB ((isqrt N + 1) / 2) + 4 * ((isqrt N + 1) / 2) + 7) / 8 * 8 := rfl
  have hZC : ZC ((isqrt N + 1) / 2) (isqrt N) =
      (ZD ((isqrt N + 1) / 2) + (isqrt N + 1 + 7)) / 8 * 8 := by
    show (_ + (isqrt N + 1) + 7) / 8 * 8 = _; congr 1
  have hpre0 : Prefix image mem 1480 := fun i hi => hmem i (by omega)
  have hwh0 : Prefix image mem 1512 := fun i hi => hmem i (by omega)
  -- 0 → 664
  obtain ⟨y0, m0, r0, S0, n0, ra0, y0_2, y0_10, g0⟩ := setup_entry x mem out N hpre0 hsz hx h10 hN7 hN
  have sz0 : m0.size = 4194304 := by rw [S0.size_eq, hsz]
  have pre0 : Prefix image m0 1480 := by tr_pfx
  -- isqrt n
  obtain ⟨y1, r1, y1_11, y1_15, g1⟩ := seg_n1 y0 m0 out N pre0 y0_10 hN
  obtain ⟨n2, y2, r2, y2_11, g2⟩ := newton1 N (by omega) hN N y1 m0 out pre0
    (by simp (disch := decide) only [g1, y0_10]) y1_11 (by rw [y1_15, Nat.div_self (by omega)]) hvN
    (Nat.le_refl N)
  obtain ⟨y3, r3, y3_11, y3_19, y3_15, g3⟩ := seg_r y2 m0 out (isqrt N) pre0 sz0 y2_11
    (by simp (disch := decide) only [g2, g1, y0_2]) hvb
  have S1 := Same.ofwr m0 4194116 (bv (isqrt N)) 4 (by omega)
  have sz1 : (wr m0 4194116 (bv (isqrt N)) 4).size = 4194304 := by simp only [wr_size]; omega
  have pre1 : Prefix image (wr m0 4194116 (bv (isqrt N)) 4) 1480 := by tr_pfx
  obtain ⟨n4, y4, r4, y4_19, g4⟩ := newton2 (isqrt N) (by omega) (by omega) (isqrt N) y3 _ out pre1
    y3_11 y3_19 (by rw [y3_15, Nat.div_self (by omega)]) (Nat.le_trans (Nat.le_trans (Nat.le_refl _) hqv)
      (Nat.le_refl _)) (Nat.le_refl _)
  -- small
  obtain ⟨y5, m2, r5, S2, sz2, C2, V2, y5_1, y5_10, y5_11, y5_20, y5_21, y5_18, g5⟩ :=
    seg_v y4 _ out (isqrt N) pre1 sz1 (by simp (disch := decide) only [g4, y3_11])
      (by simp (disch := decide) only [g4, g3, g2, g1, y0_2]) hvb
  have pre2 : Prefix image m2 1480 := by tr_pfx
  have heap2 : readBytes m2 1512 8 = some (bv 1520) := by tr_rd
  obtain ⟨x6, m3, r6, pre3, Z3, x6_10, g6⟩ := vec_ctor y5 m2 out 4194128 ((isqrt N + 1) / 2) 1520 752
    pre2 sz2 y5_10 y5_11 y5_1 (by decide) (by decide) heap2 (Nat.le_refl _) (by omega) (by omega)
  rw [show (1520 + 7) / 8 * 8 = 1520 from rfl, show heapAddr = 1512 from rfl] at Z3
  rw [show (1520 + 7) / 8 * 8 = 1520 from rfl] at x6_10
  have W3a := Same.ofwr m2 4194128 (bv 1520) 8 (by omega)
  have W3b := Same.ofwr (wr m2 4194128 (bv 1520) 8) 1512 (bv (1520 + 4 * ((isqrt N + 1) / 2))) 8
    (by simp only [wr_size]; omega)
  have S3 := Z3.same
  have sz3 : m3.size = 4194304 := by rw [Z3.size_eq]; simp only [wr_size]; omega
  -- rough
  obtain ⟨y7, r7, y7_1, y7_10, y7_11, g7⟩ := seg_c x6 m3 out ((isqrt N + 1) / 2) pre3 sz3
    (by simp (disch := decide) only [g6, y5_21]) (by simp (disch := decide) only [g6, g5, g4, g3, g2, g1, y0_2])
    (by tr_rd) (by omega)
  have heap3 : readBytes m3 1512 8 = some (bv (1520 + 4 * ((isqrt N + 1) / 2))) := by
    refine S3.read ?_ (by omega); exact rd64 _ _ _ (by first | omega | (simp only [wr_size]; omega))
  obtain ⟨x8, m4, r8, pre4, Z4, x8_10, g8⟩ := vec_ctor y7 m3 out 4194136 ((isqrt N + 1) / 2)
    (1520 + 4 * ((isqrt N + 1) / 2)) 768 pre3 sz3 y7_10 y7_11 y7_1 (by decide) (by decide) heap3
    (by omega) (by omega) (by omega)
  rw [← hZB, show heapAddr = 1512 from rfl] at Z4
  rw [← hZB] at x8_10
  have W4a := Same.ofwr m3 4194136 (bv (ZB ((isqrt N + 1) / 2))) 8 (by omega)
  have W4b := Same.ofwr (wr m3 4194136 (bv (ZB ((isqrt N + 1) / 2))) 8) 1512
    (bv (ZB ((isqrt N + 1) / 2) + 4 * ((isqrt N + 1) / 2))) 8 (by simp only [wr_size]; omega)
  have S4 := Z4.same
  have sz4 : m4.size = 4194304 := by rw [Z4.size_eq]; simp only [wr_size]; omega
  -- skip
  have heap4 : readBytes m4 1512 8 = some (bv (ZB ((isqrt N + 1) / 2) + 4 * ((isqrt N + 1) / 2))) := by
    refine S4.read ?_ (by omega); exact rd64 _ _ _ (by first | omega | (simp only [wr_size]; omega))
  obtain ⟨y9, m5, r9, S5, sz5, sk5, y9_1, y9_8, y9_9, y9_10, y9_11, y9_12, g9⟩ := seg_d x8 m4 out
    (ZB ((isqrt N + 1) / 2) + 4 * ((isqrt N + 1) / 2)) (isqrt N) pre4 sz4
    (by simp (disch := decide) only [g8, g7, g6, g5, g4, g3, g2, g1, y0_2])
    (by simp (disch := decide) only [g8, g7, g6, y5_18]) heap4 (by tr_rd; exact rd32 _ _ _ (by first | omega | (simp only [wr_size]; omega)))
    (by omega) hvb
  rw [← hZD] at sk5 y9_8 y9_10
  have pre5 : Prefix image m5 1480 := by tr_pfx
  obtain ⟨x10, m6, r10, pre6, Z6, g10⟩ := memset y9 m5 out (ZD ((isqrt N + 1) / 2)) (isqrt N + 1) 812
    pre5 sz5 y9_10 y9_12 y9_11 y9_1 (by decide) (by decide) (by omega) (by omega)
  have S6 := Z6.same
  have sz6 : m6.size = 4194304 := by rw [Z6.size_eq, sz5]
  -- large
  obtain ⟨y11, r11, y11_1, y11_10, y11_11, y11_12, g11⟩ := seg_e x10 m6 out (ZD ((isqrt N + 1) / 2))
    (isqrt N) ((isqrt N + 1) / 2) pre6 sz6 (by simp (disch := decide) only [g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, y0_2])
    (by simp (disch := decide) only [g10, y9_8]) (by simp (disch := decide) only [g10, y9_9])
    (by simp (disch := decide) only [g10, g9, g8, g7, g6, y5_18]) (by tr_rd) (by omega) hvb (by omega)
  rw [← hZC] at r11 y11_10
  have W7a := Same.ofwr m6 1512
    (bv (ZC ((isqrt N + 1) / 2) (isqrt N) + (isqrt N + 1) / 2 * 8)) 8 (by omega)
  have W7b := Same.ofwr (wr m6 1512 (bv (ZC ((isqrt N + 1) / 2) (isqrt N) + (isqrt N + 1) / 2 * 8)) 8)
    4194152 (bv (ZC ((isqrt N + 1) / 2) (isqrt N))) 8 (by simp only [wr_size]; omega)
  have sz7 : (wr (wr m6 1512 (bv (ZC ((isqrt N + 1) / 2) (isqrt N) + (isqrt N + 1) / 2 * 8)) 8)
    4194152 (bv (ZC ((isqrt N + 1) / 2) (isqrt N))) 8).size = 4194304 := by simp only [wr_size]; omega
  have pre7 : Prefix image (wr (wr m6 1512 (bv (ZC ((isqrt N + 1) / 2) (isqrt N) +
    (isqrt N + 1) / 2 * 8)) 8) 4194152 (bv (ZC ((isqrt N + 1) / 2) (isqrt N))) 8) 1480 := by tr_pfx
  obtain ⟨x12, m8, r12, pre8, Z8, g12⟩ := memset y11 _ out (ZC ((isqrt N + 1) / 2) (isqrt N))
    ((isqrt N + 1) / 2 * 8) 856 pre7 sz7 y11_10 y11_12 y11_11 y11_1 (by decide) (by decide) (by omega)
    (by omega)
  have S8 := Z8.same
  have sz8 : m8.size = 4194304 := by rw [Z8.size_eq, sz7]
  -- the table loop
  obtain ⟨y13, r13, y13_8, y13_9, y13_18, y13_13, y13_14, g13⟩ := seg_f x12 m8 out 1520
    (ZB ((isqrt N + 1) / 2)) (ZC ((isqrt N + 1) / 2) (isqrt N)) pre8 sz8
    (by simp (disch := decide) only [g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, y0_2])
    (by tr_rd; exact rd64 _ _ _ (by first | omega | (simp only [wr_size]; omega))) (by tr_rd; exact rd64 _ _ _ (by first | omega | (simp only [wr_size]; omega)))
    (by tr_rd; exact rd64 _ _ _ (by first | omega | (simp only [wr_size]; omega)))
  have sm8 : Arr32 m8 1520 ((isqrt N + 1) / 2) (fun j => if j < 0 then j else 0) := by
    have := Zeroed.arr32 (n := (isqrt N + 1) / 2) Z3
    refine Arr32.ext (f := fun _ => 0) ?_ (fun j _ => by simp)
    tr_arr
  have ro8 : Arr32 m8 (ZB ((isqrt N + 1) / 2)) ((isqrt N + 1) / 2)
      (fun j => if j < 0 then 2 * j + 1 else 0) := by
    have := Zeroed.arr32 (n := (isqrt N + 1) / 2) Z4
    refine Arr32.ext (f := fun _ => 0) ?_ (fun j _ => by simp)
    tr_arr
  have la8 : Arr64 m8 (ZC ((isqrt N + 1) / 2) (isqrt N)) ((isqrt N + 1) / 2)
      (fun j => if j < 0 then (N / (2 * j + 1) - 1) / 2 else 0) :=
    (Zeroed.arr64 (n := (isqrt N + 1) / 2) (by rw [Nat.mul_comm]; exact Z8)).ext (fun j _ => by simp)
  have sk8 : Arr8 m8 (ZD ((isqrt N + 1) / 2)) (isqrt N + 1) (fun _ => 0) := by
    have := Z6.arr8
    tr_arr
  have V8 : readBytes m8 4194124 4 = some (BitVec.ofNat 32 ((isqrt N + 1) / 2)) := by tr_rd
  have n8 : readBytes m8 4194104 8 = some (bv N) := by tr_rd
  obtain ⟨n14, y14, m9, r14, S9, sm9, ro9, la9, sk9, g14⟩ := init_loop y13 m8 out N ((isqrt N + 1) / 2)
    1520 (ZB ((isqrt N + 1) / 2)) (ZD ((isqrt N + 1) / 2)) (isqrt N + 1) (ZC ((isqrt N + 1) / 2) (isqrt N))
    0 (fun _ => 0) pre8 sz8 y13_8 y13_9 y13_18
    (by simp (disch := decide) only [g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, y0_2])
    y13_14 y13_13 V8 n8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hN
    (by omega) sm8 ro8 la8 sk8
  refine ⟨_, y14, m9, run_seq r0 (run_seq r1 (run_seq r2 (run_seq r3 (run_seq r4 (run_seq r5 (run_seq r6
    (run_seq r7 (run_seq r8 (run_seq r9 (run_seq r10 (run_seq r11 (run_seq r12 (run_seq r13 r14))))))))))))), ?_⟩
  exact {
    size := by rw [S9.size_eq, sz8]
    wh := by tr_pfx
    ra := by tr_rd
    n := by tr_rd
    R := by tr_rd; exact rd32 _ _ _ (by first | omega | (simp only [wr_size]; omega))
    C := by tr_rd
    V := V8 |> fun h => by tr_rd
    psm := by tr_rd; exact rd64 _ _ _ (by first | omega | (simp only [wr_size]; omega))
    pro := by tr_rd; exact rd64 _ _ _ (by first | omega | (simp only [wr_size]; omega))
    psk := by tr_rd
    pla := by tr_rd; exact rd64 _ _ _ (by first | omega | (simp only [wr_size]; omega))
    sm := sm9
    ro := ro9
    la := la9
    sk := sk9
    x2 := by simp (disch := decide) only [g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, y0_2]
    x8 := by simp (disch := decide) only [g14, y13_8]
    x9 := by simp (disch := decide) only [g14, y13_9]
    x18 := by simp (disch := decide) only [g14, y13_18]
    x19 := by simp (disch := decide) only [g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, y4_19]
    x20 := by simp (disch := decide) only [g14, g13, g12, g11, g10, g9, g8, g7, g6, y5_20]
    x21 := by simp (disch := decide) only [g14, g13, g12, g11, g10, g9, g8, g7, g6, y5_21] }

/-- The tables and the closure give the stage-3 memory. -/
theorem zmem3 {N : Nat} {y : Regs 64} {m m' : Array (BitVec 8)} (T : Tab N y m) (hN7 : 7 ≤ N)
    (hN : N < 100000000000) (S : Same m m' 4194160 4194224) (sz : m'.size = 4194304)
    (k0 : readBytes m' 4194160 8 = some (bv 4194144)) (k1 : readBytes m' 4194168 8 = some (bv 4194116))
    (k2 : readBytes m' 4194176 8 = some (bv 4194124)) (k3 : readBytes m' 4194184 8 = some (bv 4194136))
    (k4 : readBytes m' 4194192 8 = some (bv 4194152)) (k5 : readBytes m' 4194200 8 = some (bv 4194128))
    (k6 : readBytes m' 4194208 8 = some (bv 4194120)) (k7 : readBytes m' 4194216 8 = some (bv 4194104)) :
    ZMem N 3 m' := by
  have hv := isqrt_spec N
  have hv1 : 1 ≤ isqrt N := le_isqrt (by omega)
  have hs0 : (RL N 3).length = (isqrt N + 1) / 2 := RL3_len N hv1
  have hlay := zlayout ((isqrt N + 1) / 2) (isqrt N)
  have hvb : isqrt N < 316228 := r_lt_of_sq hv.1 hN
  exact {
    hN7 := hN7
    hN := hN
    hp3 := Nat.le_refl 3
    hpo := rfl
    hpr := fun r h1 h2 => by omega
    size := sz
    pre := S.zpre (fun i hi => T.wh i (by omega)) (by omega)
    wh := S.pfx T.wh (by omega)
    ra := S.read T.ra (by omega)
    sl := ⟨S.read T.n (by omega), S.read T.R (by omega),
      by rw [C_init]; exact S.read T.C (by omega), by rw [hs0]; exact S.read T.V (by omega),
      S.read T.psm (by omega), S.read T.pro (by omega), S.read T.psk (by omega), S.read T.pla (by omega),
      k0, k1, k2, k3, k4, k5, k6, k7⟩
    sm := (S.arr32 T.sm (by omega)).ext (fun i _ => by rw [C_init]; omega)
    ro := by
      rw [hs0]
      exact (S.arr32 T.ro (by omega)).ext (fun i hi => by rw [RL3_get N i hi])
    la := by
      rw [hs0]
      exact (S.arr64 T.la (by omega)).ext (fun i hi => by rw [RL3_get N i hi, C_init])
    sk := (S.arr8 T.sk (by omega)).ext (fun i _ => by rw [if_neg (not_skip3 i)]) }

/-- From the entry at 0 to the finish at 956, for `7 ≤ n`: the tables, then `calc(p)` for every
odd prime `p` with `p⁴ ≤ n`. -/
theorem pi_run (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N : Nat)
    (hmem : Prefix image mem 1520) (hsz : mem.size = 4194304)
    (hheap : readBytes mem 1512 8 = some (bv 1520))
    (hx : ∀ r : Reg, r ≠ 10 → x.get r = 0) (h10 : x.get 10 = bv N) (hN7 : 7 ≤ N)
    (hN : N < 100000000000) :
    ∃ n a y mem', run n ⟨x, 0, mem, [], out, .running⟩ = ⟨y, bv 956, mem', [], out, .running⟩ ∧
      ZMem N a mem' ∧ N < a * a * (a * a) ∧ y.get 2 = bv 4194096 ∧ y.get 8 = bv 1520 ∧
      y.get 9 = bv (ZB ((isqrt N + 1) / 2)) ∧ y.get 18 = bv (ZC ((isqrt N + 1) / 2) (isqrt N)) := by
  have hv := isqrt_spec N
  have hvb : isqrt N < 316228 := r_lt_of_sq hv.1 hN
  have hq := isqrt_spec (isqrt N)
  have hsq := isqrt4_small hN
  obtain ⟨n1, y1, m1, r1, T⟩ := pi_tables x mem out N hmem hsz hheap hx h10 hN7 hN
  have pre1 : Prefix image m1 1480 := fun i hi => T.wh i (by omega)
  by_cases h8 : isqrt N ≤ 8
  · obtain ⟨y2, m2, r2, S2, sz2, k0, k1, k2, k3, k4, k5, k6, k7, g2⟩ :=
      seg_g0 y1 m1 out (isqrt N) pre1 T.size T.x2 T.x20 T.x21 T.R hvb h8
    have hc : N < 3 * 3 * (3 * 3) := by
      have := Nat.mul_le_mul (show isqrt N + 1 ≤ 9 by omega) (show isqrt N + 1 ≤ 9 by omega)
      omega
    exact ⟨n1 + 17, 3, y2, m2, run_seq r1 r2, zmem3 T hN7 hN S2 sz2 k0 k1 k2 k3 k4 k5 k6 k7, hc,
      by simp (disch := decide) only [g2, T.x2], by simp (disch := decide) only [g2, T.x8],
      by simp (disch := decide) only [g2, T.x9], by simp (disch := decide) only [g2, T.x18]⟩
  obtain ⟨y2, m2, r2, S2, sz2, k0, k1, k2, k3, k4, k5, k6, k7, g2⟩ :=
    seg_g y1 m1 out (isqrt N) pre1 T.size T.x2 T.x20 T.x21 T.R hvb (by omega)
  have Z3 := zmem3 T hN7 hN S2 sz2 k0 k1 k2 k3 k4 k5 k6 k7
  obtain ⟨y3, r3, y3_1, y3_10, y3_11, y3_22, g3⟩ := seg_h y2 m2 out Z3.pre
    (by simp (disch := decide) only [g2, T.x2])
  have h81 : 3 * 3 * (3 * 3) ≤ N := by
    have := Nat.mul_le_mul (show 9 ≤ isqrt N by omega) (show 9 ≤ isqrt N by omega)
    omega
  obtain ⟨n4, y4, m4, r4, Z5, y4_8, y4_2, g4⟩ := calc_prime N 3 y3 m2 out 1520 1248 Z3 (by decide) h81
    y3_10 y3_11 (by simp (disch := decide) only [g3, g2, T.x2])
    (by simp (disch := decide) only [g3, g2, T.x8]) y3_1 (by decide) (by decide)
  have hR4 : readBytes m4 4194116 4 = some (BitVec.ofNat 32 (isqrt N)) := Z5.sl.R
  by_cases h24 : isqrt N ≤ 24
  · obtain ⟨y5, r5, g5⟩ := seg_i0 y4 m4 out (isqrt N) Z5.pre Z5.size y4_2 hR4 hvb h24
    have hc : N < 5 * 5 * (5 * 5) := by
      have := Nat.mul_le_mul (show isqrt N + 1 ≤ 25 by omega) (show isqrt N + 1 ≤ 25 by omega)
      omega
    exact ⟨n1 + 17 + 5 + n4 + 3, 3 + 2, y5, m4, run_seq (run_seq (run_seq (run_seq r1 r2) r3) r4) r5,
      Z5, hc, by simp (disch := decide) only [g5, y4_2], by simp (disch := decide) only [g5, y4_8],
      by simp (disch := decide) only [g5, g4, g3, g2, T.x9],
      by simp (disch := decide) only [g5, g4, g3, g2, T.x18]⟩
  obtain ⟨y5, r5, y5_1, y5_10, y5_11, y5_19, g5⟩ := seg_i y4 m4 out (isqrt N) (isqrt (isqrt N)) Z5.pre
    Z5.size y4_2 (by simp (disch := decide) only [g4, g3, y3_22])
    (by simp (disch := decide) only [g4, g3, g2, T.x19]) (by omega) hR4 hvb (by omega)
  have h625 : 5 * 5 * (5 * 5) ≤ N := by
    have := Nat.mul_le_mul (show 25 ≤ isqrt N by omega) (show 25 ≤ isqrt N by omega)
    omega
  obtain ⟨n6, y6, m6, r6, Z7, y6_8, y6_2, g6⟩ := calc_prime N 5 y5 m4 out 1520 1280 Z5
    (by decide) h625 y5_10 y5_11 (by simp (disch := decide) only [g5, y4_2])
    (by simp (disch := decide) only [g5, y4_8]) y5_1 (by decide) (by decide)
  obtain ⟨y7, r7, y7_20, y7_21, y7_23, g7⟩ := seg_k y6 m6 out Z7.pre
  have hW : WRegs y7 N 7 0 := {
    h19 := by simp (disch := decide) only [g7, g6, y5_19]
    h20 := y7_20
    h21 := y7_21
    h22 := by simp (disch := decide) only [g7, g6, g5, g4, g3, y3_22]
    h23 := y7_23
    h2 := by simp (disch := decide) only [g7, y6_2]
    h8 := by simp (disch := decide) only [g7, y6_8]
    h9 := by simp (disch := decide) only [g7, g6, g5, g4, g3, g2, T.x9]
    h18 := by simp (disch := decide) only [g7, g6, g5, g4, g3, g2, T.x18] }
  have hq5 : 5 ≤ isqrt (isqrt N) := le_isqrt (by omega)
  obtain ⟨n8, a, y8, m8, r8, Z8, hc8, z2, z8, z9, z18⟩ := wheel_loop N 7 0 y7 m6 out Z7 hW rfl
    (by decide) (by decide) (by omega)
  exact ⟨_, a, y8, m8, run_seq (run_seq (run_seq (run_seq (run_seq (run_seq (run_seq r1 r2) r3) r4) r5)
    r6) r7) r8, Z8, hc8, z2, z8, z9, z18⟩

end TinyFive.ZjyBinary
