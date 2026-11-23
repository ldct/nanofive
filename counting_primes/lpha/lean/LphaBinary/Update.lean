import LphaBinary.Compact

/-! The `smalls` update of one sieve round (1008 to 1032): for each odd `j` from
`((v / p) - 1) | 1` down to `p`, `smalls[i] -= smalls[j / 2] - pc` for `i` from the current index
down to `j * p / 2` (the loop at 1332). The difference is computed in 32 bits as
`pc - smalls[j / 2]` and added. -/
namespace TinyFive.LphaBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

set_option linter.unusedVariables false

/-- `addw` of `pc - S` (wrapped) and `smalls[i]`. -/
theorem add_sub32' (a b c : Nat) (hab : a ≤ b) (hc : b - a ≤ c) (hb : b < 4294967296)
    (hc' : c < 4294967296) :
    alu .add (alu .sub (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)) (BitVec.ofNat 32 c) =
      BitVec.ofNat 32 (c - (b - a)) := by
  simp only [alu]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- One pass of the decrement loop at 1332: `smalls[t] += pc - S`, `t--`. -/
theorem dec_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (s0 e pc S t : Nat)
    (Sm new : Nat → Nat) (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h5 : x.get 5 = bv t) (h20 : x.get 20 = bv e) (h6 : x.get 6 = bv (SB + t * 4))
    (h18 : x.get 18 = (alu .sub (BitVec.ofNat 32 pc) (BitVec.ofNat 32 S)).signExtend 64)
    (hs0 : s0 ≤ 158114) (he : 1 ≤ e) (het : e ≤ t + 1) (hpcS : pc ≤ S) (hS : S < 400000)
    (hts : t < s0) (hSm : ∀ u, u < s0 → Sm u < 400000)
    (hnew : ∀ u, e ≤ u → u ≤ t → S - pc ≤ Sm u ∧ new u = Sm u - (S - pc))
    (harr : Arr32 mem SB s0 (fun u => if t < u then new u else Sm u)) :
    ∃ n y mem', run n ⟨x, bv 1332, mem, [], out, .running⟩ = ⟨y, bv 1336, mem', [], out, .running⟩ ∧
      Same mem mem' SB (SB + s0 * 4) ∧
      Arr32 mem' SB s0 (fun u => if e - 1 < u then new u else Sm u) ∧ y.get 5 = bv (e - 1) ∧
      (∀ r : Reg, r ∉ ([5, 6, 19] : List Reg) → y.get r = x.get r) := by
  have := add_sub32'
  by_cases hte : e ≤ t
  · obtain ⟨hc, hn⟩ := hnew t hte (Nat.le_refl t)
    have hrd : readBytes mem (SB + t * 4) 4 = some (BitVec.ofNat 32 (Sm t)) := by
      have := harr t hts; simpa using this
    have := hSm t hts
    obtain ⟨y, hr, hy5, hy6, hfy⟩ : ∃ y, run 7 ⟨x, bv 1332, mem, [], out, .running⟩ =
        ⟨y, bv 1332, wr mem (SB + t * 4) (bv (Sm t - (S - pc))) 4, [], out, .running⟩ ∧
        y.get 5 = bv (t - 1) ∧ y.get 6 = bv (SB + (t - 1) * 4) ∧
        (∀ r : Reg, r ∉ ([5, 6, 19] : List Reg) → y.get r = x.get r) :=
      ⟨_, by lexec; rfl, by rg, by rg, by frame_tac⟩
    have harr' := (harr.wr (by omega) t (Sm t - (S - pc)) hts).ext
      (g := fun u => if t - 1 < u then new u else Sm u)
      (fun u _ => by
        by_cases hu : u = t
        · subst hu; simp [hn]; omega
        · rw [upd_other _ _ _ _ hu]
          by_cases h1 : t < u
          · simp [h1, show t - 1 < u by omega]
          · simp [h1, show ¬ t - 1 < u by omega])
    obtain ⟨n, z, mem', hr2, hsame, harr2, hz5, hfz⟩ := dec_loop y _ out s0 e pc S (t - 1) Sm new
      (prefix_wr _ _ _ hmem (by omega) (by omega)) (by simp [hsz]) hy5
      (by rw [hfy 20 (by decide), h20]) hy6 (by rw [hfy 18 (by decide), h18]) hs0 he (by omega)
      hpcS hS (by omega) hSm (fun u h1 h2 => hnew u h1 (by omega)) harr'
    refine ⟨7 + n, z, mem', by rw [run_add, hr, hr2], ?_, harr2, hz5,
      fun r hr => by rw [hfz r hr, hfy r hr]⟩
    exact (Same.wr mem _ _ 4 SB (SB + s0 * 4) (by omega) (by omega) (by omega)).trans
      ⟨hsame.size_eq.trans (by simp), hsame.frame⟩
  · have ht : t = e - 1 := by omega
    subst ht
    exact ⟨1, x, mem, by lexec, Same.refl _ _ _, harr, h5, fun _ _ => rfl⟩
termination_by t + 1

/-- The `smalls` update loop at 1028 from `j` with the current index `i`, ending at 1032. -/
theorem upd_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (v s0 p pc : Nat)
    (Sm new : Nat → Nat) (j i : Nat) (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h17 : x.get 17 = bv j) (h8 : x.get 8 = bv (p * j)) (h5 : x.get 5 = bv i)
    (h15 : x.get 15 = bv p) (h24 : x.get 24 = bv (p * 2)) (h29 : x.get 29 = bv (SB + 168))
    (h31 : x.get 31 = bv SB) (h14 : x.get 14 = bv pc)
    (hs0 : s0 = (v + 1) / 2) (hv : v < 316228)
    (hp3 : 3 ≤ p) (hpv : p ≤ v) (hpo : p % 2 = 1) (hj : j % 2 = 1) (hjv : j * p ≤ v)
    (hi : i + 1 = min s0 ((j + 2) * p / 2)) (hpc : pc < 200000)
    (H : ∀ j', j' % 2 = 1 → p ≤ j' → j' ≤ j → ∀ u, j' * p / 2 ≤ u → u < (j' + 2) * p / 2 → u < s0 →
      pc ≤ Sm (j' / 2) ∧ Sm (j' / 2) - pc ≤ Sm u ∧ new u = Sm u - (Sm (j' / 2) - pc))
    (H0 : ∀ u, u < s0 → u < p * p / 2 → new u = Sm u)
    (hSm : ∀ u, u < s0 → Sm u < 400000)
    (harr : Arr32 mem SB s0 (fun u => if i < u then new u else Sm u)) :
    ∃ n y mem', run n ⟨x, bv 1028, mem, [], out, .running⟩ = ⟨y, bv 1032, mem', [], out, .running⟩ ∧
      Same mem mem' SB (SB + s0 * 4) ∧ Arr32 mem' SB s0 new ∧
      (∀ r : Reg, r ∉ ([5, 6, 8, 17, 18, 19, 20] : List Reg) → y.get r = x.get r) := by
  have hjp2 := Nat.mul_le_mul_right p (show j ≤ j + 2 by omega)
  have hjv' : j ≤ v := Nat.le_trans (Nat.le_mul_of_pos_right j (by omega)) hjv
  have hpjc : p * j = j * p := Nat.mul_comm p j
  by_cases hpj : p ≤ j
  · have hpp := Nat.mul_le_mul_right p hpj
    have hj3 : 3 ≤ j := by omega
    have hjp3 := Nat.mul_le_mul_left j hp3
    have hp2j : p * 2 ≤ j * p := by rw [Nat.mul_comm p 2]; exact Nat.mul_le_mul_right p (by omega)
    have he1 : 4 ≤ j * p / 2 := by omega
    have hjpo : (j * p) % 2 = 1 := odd_mul hj hpo
    have hes : j * p / 2 ≤ s0 := by omega
    have hjs : j / 2 < s0 := by omega
    have hle : (j + 2) * p = j * p + 2 * p := by rw [Nat.add_mul, Nat.mul_comm 2 p]
    have hji : j / 2 ≤ i := by omega
    obtain ⟨hcpc, _, _⟩ := H j hj hpj (Nat.le_refl j) (j * p / 2) (Nat.le_refl _) (by omega) (by omega)
    have hrd : readBytes mem (SB + j / 2 * 4) 4 = some (BitVec.ofNat 32 (Sm (j / 2))) := by
      have := harr (j / 2) hjs; simpa [show ¬ i < j / 2 by omega] using this
    have := hSm (j / 2) hjs
    obtain ⟨y1, hr1, hy5, hy6, hy18, hy20, hfy1⟩ : ∃ y1, run 9 ⟨x, bv 1028, mem, [], out, .running⟩ =
        ⟨y1, bv 1332, mem, [], out, .running⟩ ∧ y1.get 5 = bv i ∧ y1.get 6 = bv (SB + i * 4) ∧
        y1.get 18 = (alu .sub (BitVec.ofNat 32 pc) (BitVec.ofNat 32 (Sm (j / 2)))).signExtend 64 ∧
        y1.get 20 = bv (j * p / 2) ∧
        (∀ r : Reg, r ∉ ([6, 18, 20] : List Reg) → y1.get r = x.get r) :=
      ⟨_, by lexec; try rfl, by rg, by rg, by rg, by rg, by frame_tac⟩
    obtain ⟨n2, y2, mem2, hr2, hsame2, harr2, hy2_5, hfy2⟩ := dec_loop y1 mem out s0 (j * p / 2) pc
      (Sm (j / 2)) i Sm new hmem hsz hy5 hy20 hy6 hy18 (by omega) (by omega) (by omega) hcpc
      (by omega) (by omega) hSm
      (fun u h1 h2 => by
        obtain ⟨_, h3, h4⟩ := H j hj hpj (Nat.le_refl j) u h1 (by omega) (by omega)
        exact ⟨h3, h4⟩) harr
    have hpre2 := hsame2.lpre hmem (by omega)
    have g : ∀ r : Reg, r ∉ ([5, 6, 18, 19, 20] : List Reg) → y2.get r = x.get r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [hfy2 r (by simp [hr]), hfy1 r (by simp [hr])]
    obtain ⟨y3, hr3, hy17, hy8, hfy3⟩ : ∃ y3, run 3 ⟨y2, bv 1336, mem2, [], out, .running⟩ =
        ⟨y3, bv 1028, mem2, [], out, .running⟩ ∧ y3.get 17 = bv (j - 2) ∧
        y3.get 8 = bv (p * (j - 2)) ∧
        (∀ r : Reg, r ∉ ([8, 17] : List Reg) → y3.get r = y2.get r) := by
      have h17' : y2.get 17 = bv j := by rw [g 17 (by decide), h17]
      have h8' : y2.get 8 = bv (p * j) := by rw [g 8 (by decide), h8]
      have h24' : y2.get 24 = bv (p * 2) := by rw [g 24 (by decide), h24]
      rw [Nat.mul_sub]
      exact ⟨_, by lexec; rfl, by rg, by rg, by frame_tac⟩
    have f3 : ∀ r : Reg, r ∉ ([5, 6, 8, 17, 18, 19, 20] : List Reg) → y3.get r = x.get r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [hfy3 r (by simp [hr]), g r (by simp [hr])]
    obtain ⟨n4, z, mem', hr4, hsame4, harr4, hfz⟩ := upd_loop y3 mem2 out v s0 p pc Sm new (j - 2)
      (j * p / 2 - 1) hpre2 (by rw [hsame2.size_eq, hsz]) hy17 hy8
      (by rw [hfy3 5 (by decide), hy2_5]) (by rw [f3 15 (by decide), h15])
      (by rw [f3 24 (by decide), h24]) (by rw [f3 29 (by decide), h29]) (by rw [f3 31 (by decide), h31])
      (by rw [f3 14 (by decide), h14]) hs0 hv hp3 hpv hpo
      (by omega) (Nat.le_trans (Nat.mul_le_mul_right p (Nat.sub_le j 2)) hjv)
      (by rw [show j - 2 + 2 = j by omega]; omega) hpc
      (fun j' h1 h2 h3 => H j' h1 h2 (by omega)) H0 hSm harr2
    refine ⟨9 + (n2 + (3 + n4)), z, mem', ?_, hsame2.trans hsame4, harr4,
      fun r hr => by rw [hfz r hr, f3 r hr]⟩
    rw [run_add, hr1, run_add, hr2, run_add, hr3, hr4]
  · refine ⟨1, x, mem, by lexec, Same.refl _ _ _, harr.ext (fun u hu => ?_), fun _ _ => rfl⟩
    by_cases h : i < u
    · simp [h]
    · have hjp : (j + 2) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
      simp only [h, ite_false]
      exact (H0 u hu (by omega)).symm
termination_by j

end TinyFive.LphaBinary
