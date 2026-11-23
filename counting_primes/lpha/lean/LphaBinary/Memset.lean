import LphaBinary.Tactic
import GrumpyBinary.Memset

/-! `memset(d, 0, n)` at address 44 of the lpha image (the same code as grumpygordon's). -/
namespace TinyFive.LphaBinary
open SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

set_option linter.unusedVariables false

theorem step64 (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (a : Nat)
    (hmem : Prefix image mem 1536) (h15 : x.get 15 = bv a) (ha : 1 ≤ a) (hs : a ≤ mem.size) (hsz : mem.size = 4194304) :
    step ⟨x, bv 64, mem, [], out, .running⟩ =
      ⟨x, bv 68, wr mem (a - 1) (x.get 11) 1, [], out, .running⟩ := by
  rw [step_at x 64 mem out .running hmem (by decide) (by decide), instrAt_64,
    exec_store_at _ _ _ _ x _ mem [] out .running (a - 1)
      (by rw [h15, sext_12_4095]; exact addr_neg1 a ha (by omega)) (by simp only [Width.bytes]; omega)]
  simp only [Width.bytes]
  rfl

theorem memset_loop (x : Regs 64) (mem0 mem : Array (BitVec 8)) (out : String) (d n j R : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = bv (d + j)) (h12 : x.get 12 = bv (d + n)) (h11 : x.get 11 = bv 0)
    (h1 : x.get 1 = bv R) (hR : R % 2 = 0) (hR' : R < 4194304)
    (hd : 1536 ≤ d) (hdn : d + n ≤ 4194304) (hj : j ≤ n)
    (hz : Zeroed mem0 mem d j) (hsz0 : mem0.size = 4194304) :
    ∃ x' mem', run (4 * (n - j) + 2) ⟨x, bv 52, mem, [], out, .running⟩ =
        ⟨x', bv R, mem', [], out, .running⟩ ∧ Prefix image mem' 1536 ∧
      Zeroed mem0 mem' d n ∧
      (∀ i : Reg, i ∉ ([15] : List Reg) → x'.get i = x.get i) ∧ x'.get 15 = bv (d + n) := by
  by_cases hjn : j = n
  · subst hjn
    refine ⟨x.set 0 60#64, mem, ?_, hmem, hz, ?_, by simp [get_set_zero, h15]⟩
    · rw [Nat.sub_self]; lexec
    · frame_tac
  · have hstep : ∃ y, run 4 ⟨x, bv 52, mem, [], out, .running⟩ =
        ⟨y, bv 52, wr mem (d + j) (bv 0) 1, [], out, .running⟩ ∧
        (∀ i : Reg, i ∉ ([15] : List Reg) → y.get i = x.get i) ∧ y.get 15 = bv (d + j + 1) := by
      have h2 : run 2 ⟨x, bv 52, mem, [], out, .running⟩ =
          ⟨x.set 15 (bv (d + j + 1)), bv 64, mem, [], out, .running⟩ := by
        lexec
      refine ⟨(x.set 15 (bv (d + j + 1))).set 0 72#64, ?_, by frame_tac, by simp [Regs.get_set]⟩
      rw [show (4 : Nat) = 2 + (1 + 1) from rfl, run_add, h2, run, if_pos rfl,
        step64 _ mem out (d + j + 1) hmem (by simp [Regs.get_set]) (by omega) (by omega) hsz]
      rw [get_set_ne _ _ _ _ (by decide), h11, show d + j + 1 - 1 = d + j by omega]
      lexec
    obtain ⟨y, hrun1, hfr1, hy15⟩ := hstep
    have hpre : Prefix image (wr mem (d + j) (bv 0) 1) 1536 :=
      prefix_wr _ _ _ hmem (by omega) (by omega)
    have hz' : Zeroed mem0 (wr mem (d + j) (bv 0) 1) d (j + 1) := by
      refine ⟨by rw [wr_size, hz.size_eq], ?_, ?_⟩
      · intro i h1 h2
        by_cases hi : i = d + j
        · subst hi; rw [wr_byte_get _ _ _ (by omega)]; rfl
        · rw [wr_get _ _ _ _ (by omega) _ (by omega)]; exact hz.zero i h1 (by omega)
      · intro i hi
        rw [wr_get _ _ _ _ (by omega) _ (by omega)]; exact hz.frame i (by omega)
    obtain ⟨x', mem', hrun, hp', hz'', hfr, h15'⟩ := memset_loop y mem0
      (wr mem (d + j) (bv 0) 1) out d n (j + 1) R hpre (by rw [wr_size, hsz])
      (by rw [hy15, ← Nat.add_assoc]) (by rw [hfr1 12 (by decide), h12]) (by rw [hfr1 11 (by decide), h11])
      (by rw [hfr1 1 (by decide), h1]) hR hR' hd hdn (by omega) hz' hsz0
    refine ⟨x', mem', ?_, hp', hz'', ?_, h15'⟩
    · rw [show 4 * (n - j) + 2 = 4 + (4 * (n - (j + 1)) + 2) by omega, run_add, hrun1, hrun]
    · intro i hi
      rw [hfr i hi, hfr1 i hi]
termination_by n - j

/-- `memset(a0, 0, a2)` from its entry at address 44, returning to `ra`. -/
theorem memset (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (d n R : Nat)
    (hmem : Prefix image mem 1536) (hsz : mem.size = 4194304)
    (h10 : x.get 10 = bv d) (h12 : x.get 12 = bv n) (h11 : x.get 11 = bv 0)
    (h1 : x.get 1 = bv R) (hR : R % 2 = 0) (hR' : R < 4194304)
    (hd : 1536 ≤ d) (hdn : d + n ≤ 4194304) :
    ∃ x' mem', run (4 * n + 4) ⟨x, bv 44, mem, [], out, .running⟩ =
        ⟨x', bv R, mem', [], out, .running⟩ ∧ Prefix image mem' 1536 ∧ Zeroed mem mem' d n ∧
      (∀ i : Reg, i ∉ ([12, 15] : List Reg) → x'.get i = x.get i) := by
  obtain ⟨y, hrun1, hfr1, hy12, hy15⟩ : ∃ y, run 2 ⟨x, bv 44, mem, [], out, .running⟩ =
      ⟨y, bv 52, mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([12, 15] : List Reg) → y.get i = x.get i) ∧
      y.get 12 = bv (d + n) ∧ y.get 15 = bv d :=
    ⟨(x.set 12 (bv (d + n))).set 15 (bv d), by lexec, by frame_tac, by simp [Regs.get_set],
      by simp [Regs.get_set]⟩
  obtain ⟨x', mem', hrun, hp', hz, hfr, _⟩ := memset_loop y mem mem out d n 0 R hmem hsz
    (by rw [hy15, Nat.add_zero]) hy12 (by rw [hfr1 11 (by decide), h11]) (by rw [hfr1 1 (by decide), h1])
    hR hR' hd hdn (by omega) ⟨rfl, fun i h1 h2 => by omega, fun _ _ => rfl⟩ hsz
  refine ⟨x', mem', ?_, hp', hz, ?_⟩
  · rw [show 4 * n + 4 = 2 + (4 * (n - 0) + 2) by omega, run_add, hrun1, hrun]
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hfr i (by simp; exact hi.2), hfr1 i (by simp; exact hi)]

end TinyFive.LphaBinary
