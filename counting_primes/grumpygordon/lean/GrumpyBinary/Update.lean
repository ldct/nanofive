import GrumpyBinary.Compact

/-! The `smalls` update of one sieve round: the descending decrement loops at 716 and 932. -/
namespace TinyFive.GrumpyBinary
open SieveMemory LucyMath

local notation "bv" => BitVec.ofNat 64

theorem setWidth_signExtend32 (z : BitVec 32) : (z.signExtend 64).setWidth 32 = z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega
theorem sub_add32 (e i : Nat) (h1 : 1 ≤ e) (h2 : e ≤ i + 1) (hi : i < 2147483648) :
    (alu .add ((BitVec.signExtend 64 (alu .sub (BitVec.ofNat 32 e) (BitVec.ofNat 32 (i + 1)))).setWidth 32)
      (BitVec.ofNat 32 i)).signExtend 64 = bv (e - 1) := by
  rw [setWidth_signExtend32]
  have : alu .add (alu .sub (BitVec.ofNat 32 e) (BitVec.ofNat 32 (i + 1))) (BitVec.ofNat 32 i) =
      BitVec.ofNat 32 (e - 1) := by
    simp only [alu]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [this, sext32 _ (by omega)]

/-- The decrement loop at 932: `smalls[t] -= c` for `t` from the current index down to `e`. -/
theorem dec_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A s0 e c t : Nat)
    (Sm new : Nat → Nat) (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h6 : x.get 6 = bv t) (h7 : x.get 7 = bv e) (h30 : x.get 30 = bv c) (h20 : x.get 20 = bv A)
    (hA : 1236 ≤ A) (hAs : A + s0 * 4 ≤ 4194304) (hs0 : s0 ≤ 200000) (he : 1 ≤ e) (het : e ≤ t + 1)
    (hts : t < s0) (hSm : ∀ u, u < s0 → Sm u < 200000)
    (hnew : ∀ u, e ≤ u → u ≤ t → c ≤ Sm u ∧ new u = Sm u - c)
    (harr : Arr32 mem A s0 (fun u => if t < u then new u else Sm u)) :
    ∃ n y mem', run n ⟨x, bv 932, mem, [], out, .running⟩ = ⟨y, bv 940, mem', [], out, .running⟩ ∧
      Same mem mem' A (A + s0 * 4) ∧
      Arr32 mem' A s0 (fun u => if e - 1 < u then new u else Sm u) ∧
      (∀ r : Reg, r ∉ ([6, 29, 31] : List Reg) → y.get r = x.get r) := by
  by_cases hte : e ≤ t
  · obtain ⟨hc, hn⟩ := hnew t hte (Nat.le_refl t)
    have hrd : readBytes mem (A + t * 4) 4 = some (BitVec.ofNat 32 (Sm t)) := by
      have := harr t hts; simpa using this
    have := hSm t hts
    have hstep : ∃ y, run 9 ⟨x, bv 932, mem, [], out, .running⟩ =
        ⟨y, bv 932, wr mem (A + t * 4) (bv (Sm t - c)) 4, [], out, .running⟩ ∧
        y.get 6 = bv (t - 1) ∧
        (∀ r : Reg, r ∉ ([6, 29, 31] : List Reg) → y.get r = x.get r) := by
      refine ⟨((((((x.set 29 (bv t)).set 29 (bv (t * 4))).set 29 (bv (A + t * 4))).set 31 (bv (Sm t))).set
        6 (bv (t - 1))).set 31 (bv (Sm t - c))).set 0 1004#64, ?_, by simp [Regs.get_set], by frame_tac⟩
      gexec
    obtain ⟨y, hr, hy6, hfy⟩ := hstep
    have harr' := (harr.wr (by omega) t (Sm t - c) hts).ext
      (g := fun u => if t - 1 < u then new u else Sm u)
      (fun u _ => by
        by_cases hu : u = t
        · subst hu; simp [hn]; omega
        · rw [upd_other _ _ _ _ hu]
          by_cases h1 : t < u
          · simp [h1, show t - 1 < u by omega]
          · simp [h1, show ¬ t - 1 < u by omega])
    obtain ⟨n, z, mem', hr2, hsame, harr2, hfz⟩ := dec_loop y _ out A s0 e c (t - 1) Sm new
      (prefix_wr _ _ _ hmem (by omega) (by omega)) (by simp [hsz]) hy6
      (by rw [hfy 7 (by decide), h7]) (by rw [hfy 30 (by decide), h30])
      (by rw [hfy 20 (by decide), h20]) hA hAs hs0 he (by omega) (by omega) hSm
      (fun u h1 h2 => hnew u h1 (by omega)) harr'
    refine ⟨9 + n, z, mem', by rw [run_add, hr, hr2], ?_, harr2,
      fun r hr => by rw [hfz r hr, hfy r hr]⟩
    exact (Same.wr mem _ _ 4 A (A + s0 * 4) (by omega) (by omega) (by omega)).trans
      ⟨hsame.size_eq.trans (by simp), hsame.frame⟩
  · have ht : t = e - 1 := by omega
    subst ht
    refine ⟨2, x.set 29 (bv (e - 1)), mem, ?_, Same.refl _ _ _, harr, by frame_tac⟩
    gexec
termination_by t + 1

theorem back_step (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (e i j p : Nat)
    (hmem : Prefix image mem 1236)
    (h5 : x.get 5 = bv e) (h17 : x.get 17 = bv i) (h28 : x.get 28 = bv j)
    (h15 : x.get 15 = bv (j * p)) (h11 : x.get 11 = bv (p * 2))
    (he : 1 ≤ e) (hei : e ≤ i + 1) (hi : i < 200000) (hj : 3 ≤ j) (hj' : j < 400000)
    (hjp : j * p < 400000) (hpj : p * 2 ≤ j * p) :
    ∃ y, run 9 ⟨x, bv 940, mem, [], out, .running⟩ = ⟨y, bv 716, mem, [], out, .running⟩ ∧
      y.get 17 = bv (e - 1) ∧ y.get 28 = bv (j - 2) ∧ y.get 15 = bv ((j - 2) * p) ∧
      (∀ r : Reg, r ∉ ([6, 15, 17, 28, 29] : List Reg) → y.get r = x.get r) := by
  have := sub_add32
  rw [Nat.sub_mul, Nat.mul_comm 2 p]
  refine ⟨(((((((x.set 29 (bv (e - 1))).set 6 0#64).set 6 (bv (i + 1))).set 6
    (BitVec.signExtend 64 (alu AluOp.sub (BitVec.ofNat 32 e) (BitVec.ofNat 32 (i + 1))))).set 17
    (bv (e - 1))).set 28 (bv (j - 2))).set 15 (bv (j * p - p * 2))).set 0 976#64, ?_,
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set], by frame_tac⟩
  gexec

/-- The `smalls` update at 716: for each odd `j` from `((v / p) - 1) | 1` down to `p`, subtract
`smalls[j >> 1] - pc` from the entries `(j * p) >> 1 ≤ u ≤ i`, then set `i = ((j * p) >> 1) - 1`. -/
theorem upd_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (A v s0 p pc : Nat)
    (Sm new : Nat → Nat) (j i : Nat) (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h28 : x.get 28 = bv j) (h15 : x.get 15 = bv (j * p)) (h17 : x.get 17 = bv i)
    (h13 : x.get 13 = bv p) (h11 : x.get 11 = bv (p * 2)) (h20 : x.get 20 = bv A)
    (h14 : x.get 14 = bv pc)
    (hA : 1236 ≤ A) (hAs : A + s0 * 4 ≤ 4194304) (hs0 : s0 = (v + 1) / 2) (hv : v < 400000)
    (hp3 : 3 ≤ p) (hpv : p ≤ v) (hpo : p % 2 = 1) (hj : j % 2 = 1) (hjv : j * p ≤ v) (hi : i + 1 = min s0 ((j + 2) * p / 2))
    (hpc : pc < 200000)
    (H : ∀ j', j' % 2 = 1 → p ≤ j' → j' ≤ j → ∀ u, j' * p / 2 ≤ u → u < (j' + 2) * p / 2 → u < s0 →
      pc ≤ Sm (j' / 2) ∧ Sm (j' / 2) - pc ≤ Sm u ∧ new u = Sm u - (Sm (j' / 2) - pc))
    (H0 : ∀ u, u < s0 → u < p * p / 2 → new u = Sm u)
    (hSm : ∀ u, u < s0 → Sm u < 200000)
    (harr : Arr32 mem A s0 (fun u => if i < u then new u else Sm u)) :
    ∃ n y mem', run n ⟨x, bv 716, mem, [], out, .running⟩ = ⟨y, bv 720, mem', [], out, .running⟩ ∧
      Same mem mem' A (A + s0 * 4) ∧ Arr32 mem' A s0 new ∧
      (∀ r : Reg, r ∉ ([5, 6, 7, 15, 17, 28, 29, 30, 31] : List Reg) → y.get r = x.get r) := by
  have hjp2 := Nat.mul_le_mul_right p (show j ≤ j + 2 by omega)
  have hjv' : j ≤ v := Nat.le_trans (Nat.le_mul_of_pos_right j (by omega)) hjv
  by_cases hpj : p ≤ j
  · have hpp := Nat.mul_le_mul_right p hpj
    have hj3 : 3 ≤ j := by omega
    have hjp3 := Nat.mul_le_mul_left j hp3
    have hp2j : p * 2 ≤ j * p := by rw [Nat.mul_comm p 2]; exact Nat.mul_le_mul_right p (by omega)
    have he1 : 4 ≤ j * p / 2 := by omega
    have hjpo : (j * p) % 2 = 1 := odd_mul hj hpo
    have hes : j * p / 2 ≤ s0 := by omega
    have hjs : j / 2 < s0 := by omega
    have hji : j / 2 ≤ i := by
      have : (j + 2) * p = j * p + 2 * p := by rw [Nat.add_mul, Nat.mul_comm 2 p]
      omega
    obtain ⟨hcpc, _, _⟩ := H j hj hpj (Nat.le_refl j) (j * p / 2) (Nat.le_refl _)
      (by have : (j + 2) * p = j * p + 2 * p := by rw [Nat.add_mul, Nat.mul_comm 2 p]
          omega) (by omega)
    have hrd : readBytes mem (A + j / 2 * 4) 4 = some (BitVec.ofNat 32 (Sm (j / 2))) := by
      have := harr (j / 2) hjs; simpa [show ¬ i < j / 2 by omega] using this
    have := hSm (j / 2) hjs
    -- to the decrement loop
    have hstep1 : ∃ y1, run 9 ⟨x, bv 716, mem, [], out, .running⟩ =
        ⟨y1, bv 932, mem, [], out, .running⟩ ∧ y1.get 6 = bv i ∧ y1.get 7 = bv (j * p / 2) ∧
        y1.get 30 = bv (Sm (j / 2) - pc) ∧ y1.get 20 = bv A ∧ y1.get 5 = bv (j * p / 2) ∧
        y1.get 28 = bv j ∧ y1.get 15 = bv (j * p) ∧ y1.get 17 = bv i ∧
        (∀ r : Reg, r ∉ ([5, 6, 7, 15, 17, 28, 29, 30, 31] : List Reg) → y1.get r = x.get r) := by
      refine ⟨(((((((x.set 6 (bv (j / 2))).set 6 (bv (j / 2 * 4))).set 6 (bv (A + j / 2 * 4))).set 30
        (bv (Sm (j / 2)))).set 5 (bv (j * p / 2))).set 7 (bv (j * p / 2))).set 30
        (bv (Sm (j / 2) - pc))).set 6 (bv i), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by frame_tac⟩
      · gexec
      all_goals simp [Regs.get_set, h20, h28, h15, h17]
    obtain ⟨y1, hr1, hy6, hy7, hy30, hy20, hy5, hy28, hy15, hy17, hfy1⟩ := hstep1
    have hle : (j + 2) * p = j * p + 2 * p := by rw [Nat.add_mul, Nat.mul_comm 2 p]
    obtain ⟨n2, y2, mem2, hr2, hsame2, harr2, hfy2⟩ := dec_loop y1 mem out A s0 (j * p / 2)
      (Sm (j / 2) - pc) i Sm new hmem hsz hy6 hy7 hy30 hy20 hA hAs (by omega) (by omega)
      (by omega) (by omega) hSm
      (fun u h1 h2 => by
        obtain ⟨_, h3, h4⟩ := H j hj hpj (Nat.le_refl j) u h1 (by omega) (by omega)
        exact ⟨h3, h4⟩) harr
    have g := fun r (h : r ∉ ([6, 29, 31] : List Reg)) => hfy2 r h
    obtain ⟨y3, hr3, hy17', hy28', hy15', hfy3⟩ := back_step y2 mem2 out (j * p / 2) i j p
      (hsame2.prefix hmem (by omega)) (by rw [g 5 (by decide), hy5]) (by rw [g 17 (by decide), hy17])
      (by rw [g 28 (by decide), hy28]) (by rw [g 15 (by decide), hy15])
      (by rw [g 11 (by decide), hfy1 11 (by decide), h11]) (by omega) (by omega) (by omega) hj3
      (by omega) (by omega) hp2j
    have f3 : ∀ r : Reg, r ∉ ([5, 6, 7, 15, 17, 28, 29, 30, 31] : List Reg) → y3.get r = x.get r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [hfy3 r (by simp [hr]), hfy2 r (by simp [hr]), hfy1 r (by simp [hr])]
    obtain ⟨n4, z, mem', hr4, hsame4, harr4, hfz⟩ := upd_loop y3 mem2 out A v s0 p pc Sm new (j - 2)
      (j * p / 2 - 1) (hsame2.prefix hmem (by omega)) (by rw [hsame2.size_eq, hsz]) hy28' hy15'
      hy17' (by rw [f3 13 (by decide), h13]) (by rw [f3 11 (by decide), h11])
      (by rw [f3 20 (by decide), h20]) (by rw [f3 14 (by decide), h14]) hA hAs hs0 hv hp3 hpv hpo
      (by omega) (Nat.le_trans (Nat.mul_le_mul_right p (Nat.sub_le j 2)) hjv)
      (by rw [show j - 2 + 2 = j by omega]; omega) hpc
      (fun j' h1 h2 h3 => H j' h1 h2 (by omega)) H0 hSm harr2
    refine ⟨9 + (n2 + (9 + n4)), z, mem', ?_, hsame2.trans hsame4, harr4,
      fun r hr => by rw [hfz r hr, f3 r hr]⟩
    rw [run_add, hr1, run_add, hr2, run_add, hr3, hr4]
  · refine ⟨1, x, mem, ?_, Same.refl _ _ _, harr.ext (fun u hu => ?_), fun _ _ => rfl⟩
    · gexec
    · by_cases h : i < u
      · simp [h]
      · have hjp : (j + 2) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
        simp only [h, ite_false]
        exact (H0 u hu (by omega)).symm
termination_by j
end TinyFive.GrumpyBinary
