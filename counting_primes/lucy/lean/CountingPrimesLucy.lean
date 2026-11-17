import LucyBlocks

namespace TinyFive.CountingPrimesLucy
open CountingPrimes SieveMemory LucyMath LucyMemory

local notation "bv" => BitVec.ofNat 64

/-! ## The two tables in memory -/

/-- A 64-bit slot holding a natural number. -/
def Cell (mem : Array (BitVec 8)) (a v : Nat) : Prop :=
  readBytes mem a 8 = some (bv v)

/-- `small[(v-1)/2]`, at `BASE - 8 + 8v`, holds `f v` for every odd `v ≤ r`. -/
def Small (mem : Array (BitVec 8)) (r : Nat) (f : Nat → Nat) : Prop :=
  ∀ v, v % 2 = 1 → v ≤ r → Cell mem (8 * v + 504) (f v)

/-- `large[k]`, at `BASE + 8k`, holds `g k` for every odd `k` with `lo ≤ k ≤ r`. -/
def Large (mem : Array (BitVec 8)) (lo r : Nat) (g : Nat → Nat) : Prop :=
  ∀ k, k % 2 = 1 → lo ≤ k → k ≤ r → Cell mem (8 * k + 512) (g k)

theorem store_cell {mem : Array (BitVec 8)} {cap : Nat} (hl : Layout image 380 cap mem)
    (a w : Nat) (hlo : 380 ≤ a) (hhi : a + 8 ≤ cap) :
    ∃ mem', writeBytes mem a (bv w) 8 = some mem' ∧ Layout image 380 cap mem' ∧
      Cell mem' a w ∧ ∀ b u, b + 8 ≤ a ∨ a + 8 ≤ b → Cell mem b u → Cell mem' b u := by
  obtain ⟨mem', hw, hl', hr, hf⟩ := store64 hl a (bv w) hlo hhi
  exact ⟨mem', hw, hl', hr, fun b u hb hc => by unfold Cell; rw [hf b hb]; exact hc⟩

/-- What holds of the input `N`, of `r` and of the memory size once the tables are set up: `r` is
the largest odd number with `r * r ≤ N`, and `large[r]` is inside memory. -/
structure Ctx (N r cap : Nat) : Prop where
  hN : N < 100000000000
  h3 : 3 ≤ N
  hodd : r % 2 = 1
  hlo : r * r ≤ N
  hhi : N < (r + 2) * (r + 2)
  hcap : 8 * r + 520 ≤ cap

theorem Ctx.r_lt {N r cap : Nat} (ctx : Ctx N r cap) : r < 316228 := r_lt_of_sq ctx.hlo ctx.hN

theorem Ctx.r_le {N r cap : Nat} (ctx : Ctx N r cap) : r ≤ N :=
  Nat.le_trans (Nat.le_mul_self r) ctx.hlo

/-- The registers of the outer loop: `a0 = N`, `a1 = 8r`, `a2 = 4N`, `a3 = large[1]`, `a4 = 8p`
and `t6 = c`. -/
structure OReg (x : Regs 64) (N r a p c : Nat) : Prop where
  h10 : x.get 10 = bv N
  h11 : x.get 11 = bv (8 * r)
  h12 : x.get 12 = bv (4 * N)
  h13 : x.get 13 = bv a
  h14 : x.get 14 = bv (8 * p)
  h31 : x.get 31 = bv c

/-- The registers of one stage: those of the outer loop with `a7 = 16p`, `s5 = 8p*p` and
`s1 = 8*kmax*p`. -/
structure SReg (x : Regs 64) (N r a p c K : Nat) : Prop where
  h10 : x.get 10 = bv N
  h11 : x.get 11 = bv (8 * r)
  h12 : x.get 12 = bv (4 * N)
  h13 : x.get 13 = bv a
  h14 : x.get 14 = bv (8 * p)
  h31 : x.get 31 = bv c
  h17 : x.get 17 = bv (16 * p)
  h21 : x.get 21 = bv (8 * (p * p))
  h9 : x.get 9 = bv (8 * (K * p))

theorem OReg.frame {x x' : Regs 64} {N r a p c : Nat} {W : List Reg} (h : OReg x N r a p c)
    (hfr : ∀ i : Reg, i ∉ W → x'.get i = x.get i)
    (hW : ∀ i ∈ ([10, 11, 12, 13, 14, 31] : List Reg), i ∉ W) : OReg x' N r a p c :=
  ⟨by rw [hfr 10 (hW 10 (by decide))]; exact h.h10,
   by rw [hfr 11 (hW 11 (by decide))]; exact h.h11,
   by rw [hfr 12 (hW 12 (by decide))]; exact h.h12,
   by rw [hfr 13 (hW 13 (by decide))]; exact h.h13,
   by rw [hfr 14 (hW 14 (by decide))]; exact h.h14,
   by rw [hfr 31 (hW 31 (by decide))]; exact h.h31⟩

theorem SReg.frame {x x' : Regs 64} {N r a p c K : Nat} {W : List Reg} (h : SReg x N r a p c K)
    (hfr : ∀ i : Reg, i ∉ W → x'.get i = x.get i)
    (hW : ∀ i ∈ ([10, 11, 12, 13, 14, 31, 17, 21, 9] : List Reg), i ∉ W) :
    SReg x' N r a p c K :=
  ⟨by rw [hfr 10 (hW 10 (by decide))]; exact h.h10,
   by rw [hfr 11 (hW 11 (by decide))]; exact h.h11,
   by rw [hfr 12 (hW 12 (by decide))]; exact h.h12,
   by rw [hfr 13 (hW 13 (by decide))]; exact h.h13,
   by rw [hfr 14 (hW 14 (by decide))]; exact h.h14,
   by rw [hfr 31 (hW 31 (by decide))]; exact h.h31,
   by rw [hfr 17 (hW 17 (by decide))]; exact h.h17,
   by rw [hfr 21 (hW 21 (by decide))]; exact h.h21,
   by rw [hfr 9 (hW 9 (by decide))]; exact h.h9⟩

theorem SReg.toOReg {x : Regs 64} {N r a p c K : Nat} (h : SReg x N r a p c K) :
    OReg x N r a p c :=
  ⟨h.h10, h.h11, h.h12, h.h13, h.h14, h.h31⟩

/-- Restate a register's value as an equal natural number. -/
theorem bv_of {x : Regs 64} {i : Reg} {a b : Nat} (h : x.get i = bv a) (hab : a = b) :
    x.get i = bv b := hab ▸ h

/-! ## The three inner loops of a stage -/

/-- The first loop, addresses 156 to 184: `large[k] -= large[k*p] - c` while `k * p ≤ r`. -/
theorem first_loop (N r cap p a : Nat) (ctx : Ctx N r cap) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (hprime : Prime p) (hpp : (p + 2) * p ≤ r)
    (k d : Nat) (hkodd : k % 2 = 1) (hk : p + 2 ≤ k) (hd : d = k * p) (hdr : d ≤ r)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : SReg x N r a p (S p (p - 1)) (kmax N r p))
    (h8 : x.get 8 = bv (8 * d)) (h18 : x.get 18 = bv (8 * k + 512))
    (hlay : Layout image 380 cap mem) (hs : Small mem r (S p))
    (hl : Large mem (p + 2) r (fun j => if j < k then S (p + 1) (N / j) else S p (N / j))) :
    ∃ fuel k' x' mem', fuel + 4 * k ≤ 4 * k' ∧ k' ≤ r ∧ k' % 2 = 1 ∧ p + 2 ≤ k' ∧
      r < k' * p ∧ k' * (p * p) ≤ N ∧
      run fuel ⟨x, 156, mem, [], out, .running⟩ = ⟨x', 188, mem', [], out, .running⟩ ∧
      SReg x' N r a p (S p (p - 1)) (kmax N r p) ∧
      x'.get 8 = bv (8 * (k' * p)) ∧ x'.get 18 = bv (8 * k' + 512) ∧
      Layout image 380 cap mem' ∧ Small mem' r (S p) ∧
      Large mem' (p + 2) r (fun j => if j < k' then S (p + 1) (N / j) else S p (N / j)) := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hcap := ctx.hcap
  have hp0 : 0 < p := by omega
  have hkd : k ≤ d := by rw [hd]; exact Nat.le_mul_of_pos_right k hp0
  have hk5 : k * 5 ≤ k * p := Nat.mul_le_mul_left k hp5
  have hdodd : d % 2 = 1 := by rw [hd]; exact odd_mul hkodd hpodd
  have hpd : p * d ≤ N := Nat.le_trans (Nat.mul_le_mul hpr hdr) ctx.hlo
  have hpNd : p ≤ N / d := (Nat.le_div_iff_mul_le (by omega)).mpr hpd
  have hdiv : N / k / p = N / d := by rw [Nat.div_div_eq_div_mul, hd]
  have hA : Cell mem (8 * d + 512) (S p (N / d)) := by
    have := hl d hdodd (by omega) hdr
    simpa [show ¬ d < k by omega] using this
  have hB : Cell mem (8 * k + 512) (S p (N / k)) := by
    have := hl k hkodd hk (by omega)
    simpa using this
  have hstep := S_prime_step p hprime hp5 (N / k) (by rw [hdiv]; exact hpNd)
  rw [hdiv] at hstep
  have hcA : S p (p - 1) ≤ S p (N / d) := S_mono p (by omega)
  have hAle : S p (N / d) ≤ N := Nat.le_trans (S_le _ _) (Nat.div_le_self _ _)
  have hBle : S p (N / k) ≤ N := Nat.le_trans (S_le _ _) (Nat.div_le_self _ _)
  obtain ⟨mem', hw, hlay', hcell, hframe⟩ :=
    store_cell hlay (8 * k + 512) (S (p + 1) (N / k)) (by omega) (by omega)
  have hval : S p (N / k) - (S p (N / d) - S p (p - 1)) = S (p + 1) (N / k) := by omega
  have hs' : Small mem' r (S p) := fun v hv hvr => hframe _ _ (by omega) (hs v hv hvr)
  have hl' : Large mem' (p + 2) r
      (fun j => if j < k + 2 then S (p + 1) (N / j) else S p (N / j)) := by
    intro j hj hjlo hjr
    by_cases hjk : j = k
    · subst hjk
      simpa using hcell
    · have := hframe _ _ (by omega) (hl j hj hjlo hjr)
      by_cases hlt : j < k
      · simpa [hlt, show j < k + 2 by omega] using this
      · simpa [hlt, show ¬ j < k + 2 by omega] using this
  have hd' : d + 2 * p = (k + 2) * p := by rw [hd, Nat.add_mul]
  by_cases hcont : d + 2 * p ≤ r
  · obtain ⟨y, hrun, hfr, hy18, hy8⟩ := blk_first x mem out (8 * d) (8 * k + 512) (S p (p - 1))
      (16 * p) (8 * r) (S p (N / d)) (S p (N / k)) mem' hlay.code_eq hlay'.code_eq h8 h18
      hreg.h31 hreg.h17 hreg.h11 (by omega) (by omega) (by omega) (by omega) hA hB hcA
      (by omega) (by rw [hval]; exact hw) 156 (Or.inl ⟨by omega, rfl⟩)
    obtain ⟨fuel, k', x', mem'', hfuel, hk'r, hk'odd, hk', hrk', hk'N, hrun', hreg', h8', h18',
        hlay'', hs'', hl''⟩ :=
      first_loop N r cap p a ctx hp5 hpodd hpr hprime hpp (k + 2) (d + 2 * p) (by omega)
        (by omega) hd' hcont y mem' out (hreg.frame hfr (by decide))
        (bv_of hy8 (by omega)) (bv_of hy18 (by omega)) hlay' hs' hl'
    refine ⟨8 + fuel, k', x', mem'', by omega, hk'r, hk'odd, by omega, hrk', hk'N, ?_, hreg',
      h8', h18', hlay'', hs'', hl''⟩
    rw [run_add, hrun]
    exact hrun'
  · obtain ⟨y, hrun, hfr, hy18, hy8⟩ := blk_first x mem out (8 * d) (8 * k + 512) (S p (p - 1))
      (16 * p) (8 * r) (S p (N / d)) (S p (N / k)) mem' hlay.code_eq hlay'.code_eq h8 h18
      hreg.h31 hreg.h17 hreg.h11 (by omega) (by omega) (by omega) (by omega) hA hB hcA
      (by omega) (by rw [hval]; exact hw) 188 (Or.inr ⟨by omega, rfl⟩)
    refine ⟨8, k + 2, y, mem', by omega, by omega, by omega, by omega, by rw [← hd']; omega,
      first_exit hp0 (hd ▸ hdr) hpp ctx.hlo, hrun, hreg.frame hfr (by decide), ?_, ?_, hlay',
      hs', hl'⟩
    · exact bv_of hy8 (by omega)
    · exact bv_of hy18 (by omega)
termination_by r + 2 - k
decreasing_by omega

/-- The second loop, addresses 200 to 240: `large[k] -= small[(N/(k*p) - 1) >> 1] - c` while
`k ≤ kmax`. -/
theorem second_loop (N r cap p a : Nat) (ctx : Ctx N r cap) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (hprime : Prime p)
    (k d : Nat) (hkodd : k % 2 = 1) (hk : p + 2 ≤ k) (hkK : k ≤ kmax N r p) (hd : d = k * p)
    (hrd : r < d)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : SReg x N r a p (S p (p - 1)) (kmax N r p))
    (h8 : x.get 8 = bv (8 * d)) (h18 : x.get 18 = bv (8 * k + 512))
    (h19 : x.get 19 = bv (8 * ((N - d) / 2)))
    (hlay : Layout image 380 cap mem) (hs : Small mem r (S p))
    (hl : Large mem (p + 2) r (fun j => if j < k then S (p + 1) (N / j) else S p (N / j))) :
    ∃ fuel x' mem', fuel + 6 * k ≤ 6 * (r + 2) ∧
      run fuel ⟨x, 200, mem, [], out, .running⟩ = ⟨x', 244, mem', [], out, .running⟩ ∧
      SReg x' N r a p (S p (p - 1)) (kmax N r p) ∧
      Layout image 380 cap mem' ∧ Small mem' r (S p) ∧
      Large mem' (p + 2) r (fun j => S (p + 1) (N / j)) := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hcap := ctx.hcap
  have hrodd := ctx.hodd
  have hp0 : 0 < p := by omega
  have hkr : k ≤ r := kmax_le hp0 hpodd ctx.hodd ctx.hhi hkodd hkK
  have hkN : k * (p * p) ≤ N := (kmax_iff hp0 ctx.hlo hkr).mp hkK
  have hpd : p * d ≤ N := by rw [hd, Nat.mul_left_comm]; exact hkN
  have hdN : d ≤ N := Nat.le_trans (Nat.le_mul_of_pos_left d hp0) hpd
  have hd0 : 0 < d := by omega
  have hpNd : p ≤ N / d := (Nat.le_div_iff_mul_le hd0).mpr hpd
  have hdodd : d % 2 = 1 := by rw [hd]; exact odd_mul hkodd hpodd
  have hNd : N / d < r + 2 := by
    rw [Nat.div_lt_iff_lt_mul hd0]
    exact Nat.lt_of_lt_of_le ctx.hhi (Nat.mul_le_mul_left _ (by omega))
  have hKp := kmax_mul_le (N := N) hp0 hpr ctx.hlo
  have hdiv : N / k / p = N / d := by rw [Nat.div_div_eq_div_mul, hd]
  have hj := scaled_half_div N d hdN
  have hA : Cell mem ((N / d - 1) / 2 * 16 + 512) (S p (N / d)) := by
    have := hs (2 * ((N / d - 1) / 2) + 1) (by omega) (by omega)
    rw [S_odd_index p (by omega) (N / d) (by omega)] at this
    rw [show (N / d - 1) / 2 * 16 + 512 = 8 * (2 * ((N / d - 1) / 2) + 1) + 504 by omega]
    exact this
  have hB : Cell mem (8 * k + 512) (S p (N / k)) := by
    have := hl k hkodd hk (by omega)
    simpa using this
  have hstep := S_prime_step p hprime hp5 (N / k) (by rw [hdiv]; exact hpNd)
  rw [hdiv] at hstep
  have hcA : S p (p - 1) ≤ S p (N / d) := S_mono p (by omega)
  have hAle : S p (N / d) ≤ N := Nat.le_trans (S_le _ _) (Nat.div_le_self _ _)
  have hBle : S p (N / k) ≤ N := Nat.le_trans (S_le _ _) (Nat.div_le_self _ _)
  obtain ⟨mem', hw, hlay', hcell, hframe⟩ :=
    store_cell hlay (8 * k + 512) (S (p + 1) (N / k)) (by omega) (by omega)
  have hval : S p (N / k) - (S p (N / d) - S p (p - 1)) = S (p + 1) (N / k) := by omega
  have hs' : Small mem' r (S p) := fun v hv hvr => hframe _ _ (by omega) (hs v hv hvr)
  have hl' : Large mem' (p + 2) r
      (fun j => if j < k + 2 then S (p + 1) (N / j) else S p (N / j)) := by
    intro j hj hjlo hjr
    by_cases hjk : j = k
    · subst hjk
      simpa using hcell
    · have := hframe _ _ (by omega) (hl j hj hjlo hjr)
      by_cases hlt : j < k
      · simpa [hlt, show j < k + 2 by omega] using this
      · simpa [hlt, show ¬ j < k + 2 by omega] using this
  have hd' : d + 2 * p = (k + 2) * p := by rw [hd, Nat.add_mul]
  by_cases hcont : k + 2 ≤ kmax N r p
  · have hk2r : k + 2 ≤ r := kmax_le hp0 hpodd ctx.hodd ctx.hhi (by omega) hcont
    have hk2N : (k + 2) * (p * p) ≤ N := (kmax_iff hp0 ctx.hlo hk2r).mp hcont
    have hk2p : (k + 2) * p ≤ (k + 2) * (p * p) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left p hp0)
    have hmul : (k + 2) * p ≤ kmax N r p * p := Nat.mul_le_mul_right p hcont
    obtain ⟨y, hrun, hfr, hy18, hy8, hy19⟩ := blk_second x mem out (8 * d) (8 * k + 512)
      (8 * ((N - d) / 2)) (S p (p - 1)) (16 * p) (8 * p) (8 * (kmax N r p * p))
      ((N / d - 1) / 2) (S p (N / d)) (S p (N / k)) mem' hlay.code_eq hlay'.code_eq h8 h18 h19
      hreg.h31 hreg.h17 hreg.h14 hreg.h9 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hj (by omega) hA hB hcA (by omega) (by rw [hval]; exact hw) 200
      (Or.inl ⟨by omega, rfl⟩)
    obtain ⟨fuel, x', mem'', hfuel, hrun', hreg', hlay'', hs'', hl''⟩ :=
      second_loop N r cap p a ctx hp5 hpodd hpr hprime (k + 2) (d + 2 * p) (by omega)
        (by omega) hcont hd' (by omega) y mem' out (hreg.frame hfr (by decide))
        (bv_of hy8 (by omega)) (bv_of hy18 (by omega)) (bv_of (hy19 (by omega)) (by omega))
        hlay' hs' hl'
    refine ⟨11 + fuel, x', mem'', by omega, ?_, hreg', hlay'', hs'', hl''⟩
    rw [run_add, hrun]
    exact hrun'
  · have hmul : kmax N r p * p < (k + 2) * p := (Nat.mul_lt_mul_right hp0).mpr (by omega)
    obtain ⟨y, hrun, hfr, hy18, hy8, hy19⟩ := blk_second x mem out (8 * d) (8 * k + 512)
      (8 * ((N - d) / 2)) (S p (p - 1)) (16 * p) (8 * p) (8 * (kmax N r p * p))
      ((N / d - 1) / 2) (S p (N / d)) (S p (N / k)) mem' hlay.code_eq hlay'.code_eq h8 h18 h19
      hreg.h31 hreg.h17 hreg.h14 hreg.h9 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hj (by omega) hA hB hcA (by omega) (by rw [hval]; exact hw) 244
      (Or.inr ⟨by omega, rfl⟩)
    refine ⟨11, y, mem', by omega, hrun, hreg.frame hfr (by decide), hlay', hs', ?_⟩
    intro j hj hjlo hjr
    have := hl' j hj hjlo hjr
    by_cases hlt : j < k + 2
    · simpa [hlt] using this
    · have hnot : ¬ j * (p * p) ≤ N := fun h => by
        have := (kmax_iff hp0 ctx.hlo hjr).mpr h
        omega
      have hsm := S_small p (by omega) (N / j) (div_lt_sq_of_not (by omega) hnot)
      simp only [hlt, ite_false] at this
      show Cell mem' (8 * j + 512) (S (p + 1) (N / j))
      rw [hsm]
      exact this
termination_by r + 2 - k
decreasing_by
  have := kmax_le (by omega : 0 < p) hpodd ctx.hodd ctx.hhi hkodd hkK
  omega

/-- The third loop, addresses 252 to 288: `small[(v-1)/2] -= small[(v/p - 1) >> 1] - c` for `v`
from `r` down to `p * p`. -/
theorem third_loop (N r cap p a : Nat) (ctx : Ctx N r cap) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (hprime : Prime p)
    (v : Nat) (hvodd : v % 2 = 1) (hpv : p * p ≤ v) (hvr : v ≤ r)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : SReg x N r a p (S p (p - 1)) (kmax N r p))
    (h20 : x.get 20 = bv (8 * v))
    (hlay : Layout image 380 cap mem)
    (hs : Small mem r (fun u => if v < u then S (p + 1) u else S p u))
    (g : Nat → Nat) (hl : Large mem (p + 2) r g) :
    ∃ fuel x' mem', fuel ≤ 5 * v ∧
      run fuel ⟨x, 252, mem, [], out, .running⟩ = ⟨x', 292, mem', [], out, .running⟩ ∧
      SReg x' N r a p (S p (p - 1)) (kmax N r p) ∧
      Layout image 380 cap mem' ∧ Small mem' r (S (p + 1)) ∧ Large mem' (p + 2) r g := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hcap := ctx.hcap
  have hp0 : 0 < p := by omega
  have hppp : p ≤ p * p := Nat.le_mul_of_pos_left p hp0
  have hpvp : p ≤ v / p := (Nat.le_div_iff_mul_le hp0).mpr hpv
  have hvp : v / p ≤ v := Nat.div_le_self v p
  have hj := scaled_half_div' v p (by omega)
  have hA : Cell mem ((v / p - 1) / 2 * 16 + 512) (S p (v / p)) := by
    have := hs (2 * ((v / p - 1) / 2) + 1) (by omega) (by omega)
    simp only [show ¬ v < 2 * ((v / p - 1) / 2) + 1 by omega, ite_false] at this
    rw [S_odd_index p (by omega) (v / p) (by omega)] at this
    rw [show (v / p - 1) / 2 * 16 + 512 = 8 * (2 * ((v / p - 1) / 2) + 1) + 504 by omega]
    exact this
  have hB : Cell mem (8 * v + 504) (S p v) := by
    have := hs v hvodd hvr
    simpa using this
  have hstep := S_prime_step p hprime hp5 v hpvp
  have hcA : S p (p - 1) ≤ S p (v / p) := S_mono p (by omega)
  have hAle : S p (v / p) ≤ v := Nat.le_trans (S_le _ _) hvp
  have hBle : S p v ≤ v := S_le _ _
  obtain ⟨mem', hw, hlay', hcell, hframe⟩ :=
    store_cell hlay (8 * v + 504) (S (p + 1) v) (by omega) (by omega)
  have hval : S p v - (S p (v / p) - S p (p - 1)) = S (p + 1) v := by omega
  have hs' : Small mem' r (fun u => if v - 2 < u then S (p + 1) u else S p u) := by
    intro u hu hur
    by_cases huv : u = v
    · subst huv
      simpa [show u - 2 < u by omega] using hcell
    · have := hframe _ _ (by omega) (hs u hu hur)
      by_cases hlt : v < u
      · simpa [hlt, show v - 2 < u by omega] using this
      · simpa [hlt, show ¬ v - 2 < u by omega] using this
  have hl' : Large mem' (p + 2) r g := fun k hk hklo hkr =>
    hframe _ _ (by omega) (hl k hk hklo hkr)
  by_cases hcont : p * p ≤ v - 2
  · obtain ⟨y, hrun, hfr, hy20⟩ := blk_third x mem out (8 * v) (8 * p) (16 * p) (8 * (p * p))
      (S p (p - 1)) ((v / p - 1) / 2) (S p (v / p)) (S p v) mem' hlay.code_eq hlay'.code_eq
      h20 hreg.h14 hreg.h17 hreg.h31 hreg.h21 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hj (by omega) hA hB hcA (by omega) (by rw [hval]; exact hw) 252
      (Or.inl ⟨by omega, rfl⟩)
    obtain ⟨fuel, x', mem'', hfuel, hrun', hreg', hlay'', hs'', hl''⟩ :=
      third_loop N r cap p a ctx hp5 hpodd hpr hprime (v - 2) (by omega) hcont (by omega)
        y mem' out (hreg.frame hfr (by decide)) (bv_of hy20 (by omega)) hlay' hs' g hl'
    refine ⟨10 + fuel, x', mem'', by omega, ?_, hreg', hlay'', hs'', hl''⟩
    rw [run_add, hrun]
    exact hrun'
  · obtain ⟨y, hrun, hfr, hy20⟩ := blk_third x mem out (8 * v) (8 * p) (16 * p) (8 * (p * p))
      (S p (p - 1)) ((v / p - 1) / 2) (S p (v / p)) (S p v) mem' hlay.code_eq hlay'.code_eq
      h20 hreg.h14 hreg.h17 hreg.h31 hreg.h21 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hj (by omega) hA hB hcA (by omega) (by rw [hval]; exact hw) 292
      (Or.inr ⟨by omega, rfl⟩)
    refine ⟨10, y, mem', by omega, hrun, hreg.frame hfr (by decide), hlay', ?_, hl'⟩
    intro u hu hur
    have := hs' u hu hur
    by_cases hlt : v - 2 < u
    · simpa [hlt] using this
    · simp only [hlt, ite_false] at this
      rw [S_small p (by omega) u (by omega)]
      exact this
termination_by v
decreasing_by omega

end TinyFive.CountingPrimesLucy
