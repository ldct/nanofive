import ZjyBinary.Tactic
import GrumpyBinary.Memset

/-! The runtime of the zjy2008 image: `memset(d, 0, n)` at address 508, and the
`vector<int>(n)` constructor at 1428, which takes memory from the heap cursor (1512) and zeroes
it with a tail call to `memset`. Ported from the grumpygordon proof. -/
namespace TinyFive.ZjyBinary
open SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

set_option linter.unusedVariables false

theorem step528 (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (a : Nat)
    (hmem : Prefix image mem 1480) (h15 : x.get 15 = bv a) (ha : 1 ≤ a) (hs : a ≤ mem.size) (hsz : mem.size = 4194304) :
    step ⟨x, bv 528, mem, [], out, .running⟩ =
      ⟨x, bv 532, wr mem (a - 1) (x.get 11) 1, [], out, .running⟩ := by
  rw [step_at x 528 mem out .running hmem (by decide) (by decide), instrAt_528,
    exec_store_at _ _ _ _ x _ mem [] out .running (a - 1)
      (by rw [h15, sext_12_4095]; exact addr_neg1 a ha (by omega)) (by simp only [Width.bytes]; omega)]
  simp only [Width.bytes]
  rfl

theorem memset_loop (x : Regs 64) (mem0 mem : Array (BitVec 8)) (out : String) (d n j R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h15 : x.get 15 = bv (d + j)) (h12 : x.get 12 = bv (d + n)) (h11 : x.get 11 = bv 0)
    (h1 : x.get 1 = bv R) (hR : R % 2 = 0) (hR' : R < 4194304)
    (hd : 1480 ≤ d) (hdn : d + n ≤ 4194304) (hj : j ≤ n)
    (hz : Zeroed mem0 mem d j) (hsz0 : mem0.size = 4194304) :
    ∃ x' mem', run (4 * (n - j) + 2) ⟨x, bv 516, mem, [], out, .running⟩ =
        ⟨x', bv R, mem', [], out, .running⟩ ∧ Prefix image mem' 1480 ∧
      Zeroed mem0 mem' d n ∧
      (∀ i : Reg, i ∉ ([15] : List Reg) → x'.get i = x.get i) ∧ x'.get 15 = bv (d + n) := by
  by_cases hjn : j = n
  · subst hjn
    refine ⟨x.set 0 524#64, mem, ?_, hmem, hz, ?_, by simp [get_set_zero, h15]⟩
    · rw [Nat.sub_self]; zexec
    · frame_tac
  · have hstep : ∃ y, run 4 ⟨x, bv 516, mem, [], out, .running⟩ =
        ⟨y, bv 516, wr mem (d + j) (bv 0) 1, [], out, .running⟩ ∧
        (∀ i : Reg, i ∉ ([15] : List Reg) → y.get i = x.get i) ∧ y.get 15 = bv (d + j + 1) := by
      have h2 : run 2 ⟨x, bv 516, mem, [], out, .running⟩ =
          ⟨x.set 15 (bv (d + j + 1)), bv 528, mem, [], out, .running⟩ := by
        zexec
      refine ⟨(x.set 15 (bv (d + j + 1))).set 0 536#64, ?_, by frame_tac, by simp [Regs.get_set]⟩
      rw [show (4 : Nat) = 2 + (1 + 1) from rfl, run_add, h2, run, if_pos rfl,
        step528 _ mem out (d + j + 1) hmem (by simp [Regs.get_set]) (by omega) (by omega) hsz]
      rw [get_set_ne _ _ _ _ (by decide), h11, show d + j + 1 - 1 = d + j by omega]
      zexec
    obtain ⟨y, hrun1, hfr1, hy15⟩ := hstep
    have hpre : Prefix image (wr mem (d + j) (bv 0) 1) 1480 :=
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

/-- `memset(a0, 0, a2)` from its entry at address 508, returning to `ra`. -/
theorem memset (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (d n R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h10 : x.get 10 = bv d) (h12 : x.get 12 = bv n) (h11 : x.get 11 = bv 0)
    (h1 : x.get 1 = bv R) (hR : R % 2 = 0) (hR' : R < 4194304)
    (hd : 1480 ≤ d) (hdn : d + n ≤ 4194304) :
    ∃ x' mem', run (4 * n + 4) ⟨x, bv 508, mem, [], out, .running⟩ =
        ⟨x', bv R, mem', [], out, .running⟩ ∧ Prefix image mem' 1480 ∧ Zeroed mem mem' d n ∧
      (∀ i : Reg, i ∉ ([12, 15] : List Reg) → x'.get i = x.get i) := by
  obtain ⟨y, hrun1, hfr1, hy12, hy15⟩ : ∃ y, run 2 ⟨x, bv 508, mem, [], out, .running⟩ =
      ⟨y, bv 516, mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([12, 15] : List Reg) → y.get i = x.get i) ∧
      y.get 12 = bv (d + n) ∧ y.get 15 = bv d :=
    ⟨(x.set 12 (bv (d + n))).set 15 (bv d), by zexec, by frame_tac, by simp [Regs.get_set],
      by simp [Regs.get_set]⟩
  obtain ⟨x', mem', hrun, hp', hz, hfr, _⟩ := memset_loop y mem mem out d n 0 R hmem hsz
    (by rw [hy15, Nat.add_zero]) hy12 (by rw [hfr1 11 (by decide), h11]) (by rw [hfr1 1 (by decide), h1])
    hR hR' hd hdn (by omega) ⟨rfl, fun i h1 h2 => by omega, fun _ _ => rfl⟩ hsz
  refine ⟨x', mem', ?_, hp', hz, ?_⟩
  · rw [show 4 * n + 4 = 2 + (4 * (n - 0) + 2) by omega, run_add, hrun1, hrun]
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hfr i (by simp; exact hi.2), hfr1 i (by simp; exact hi)]

/-- The heap cursor `heap`, at address 1512. -/
abbrev heapAddr : Nat := 1512

/-- `vector<int>(n)` constructing at object address `o` (address 1428): takes `4n` bytes from
the 8-aligned heap cursor, zeroes them and stores their address at `o`. -/
theorem vec_ctor (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (o n H R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h10 : x.get 10 = bv o) (h11 : x.get 11 = bv n) (h1 : x.get 1 = bv R)
    (hR : R % 2 = 0) (hR' : R < 4194304)
    (hheap : readBytes mem heapAddr 8 = some (bv H)) (hH : 1520 ≤ H)
    (hfit : (H + 7) / 8 * 8 + 4 * n ≤ o) (ho : o + 8 ≤ 4194304) :
    ∃ x' mem', run (13 + (4 * (4 * n) + 4)) ⟨x, bv 1428, mem, [], out, .running⟩ =
        ⟨x', bv R, mem', [], out, .running⟩ ∧ Prefix image mem' 1480 ∧
      Zeroed (wr (wr mem o (bv ((H + 7) / 8 * 8)) 8) heapAddr (bv ((H + 7) / 8 * 8 + 4 * n)) 8)
        mem' ((H + 7) / 8 * 8) (4 * n) ∧
      x'.get 10 = bv ((H + 7) / 8 * 8) ∧
      (∀ i : Reg, i ∉ ([6, 10, 11, 12, 13, 14, 15] : List Reg) → x'.get i = x.get i) := by
  have hrun := run_add 13 (4 * (4 * n) + 4) ⟨x, bv 1428, mem, [], out, .running⟩
  obtain ⟨y, h13, hy10, hy11, hy12, hy1, hfy⟩ : ∃ y, run 13 ⟨x, bv 1428, mem, [], out, .running⟩ =
      ⟨y, bv 508, wr (wr mem o (bv ((H + 7) / 8 * 8)) 8) 1512 (bv ((H + 7) / 8 * 8 + n * 4)) 8, [],
        out, .running⟩ ∧ y.get 10 = bv ((H + 7) / 8 * 8) ∧ y.get 11 = bv 0 ∧ y.get 12 = bv (n * 4) ∧
      y.get 1 = bv R ∧
      (∀ i : Reg, i ∉ ([6, 10, 11, 12, 13, 14, 15] : List Reg) → y.get i = x.get i) :=
    ⟨((((((((((x.set 14 1428#64).set 14 1512#64).set 15 (bv H)).set 12 (bv (n * 4))).set 11 0#64).set
      15 (bv (H + 7))).set 15 (bv ((H + 7) / 8 * 8))).set 13 (bv ((H + 7) / 8 * 8 + n * 4))).set
      10 (bv ((H + 7) / 8 * 8))).set 6 1472#64).set 0 1480#64, by zexec, by simp [Regs.get_set],
      by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set, h1], by frame_tac⟩
  rw [h13] at hrun
  have hp2 : Prefix image (wr (wr mem o (bv ((H + 7) / 8 * 8)) 8) 1512
      (bv ((H + 7) / 8 * 8 + n * 4)) 8) 1480 :=
    prefix_wr _ _ _ (prefix_wr _ _ _ hmem (by omega) (by omega)) (by simp; omega) (by omega)
  obtain ⟨x', mem', hr, hp', hz, hfr⟩ := memset y _ out ((H + 7) / 8 * 8) (4 * n) R hp2
    (by simp [hsz]) hy10 (by rw [hy12, Nat.mul_comm]) hy11 hy1 hR hR' (by omega) (by omega)
  refine ⟨x', mem', by rw [hrun, hr], hp', ?_, ?_, ?_⟩
  · rw [show heapAddr = 1512 from rfl, show 4 * n = n * 4 by omega] at *; exact hz
  · rw [hfr 10 (by decide), hy10]
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hfr i (by simp [hi.2.2.2.1, hi.2.2.2.2.2.2]), hfy i (by simp [hi])]
end TinyFive.ZjyBinary
