import OddWheelFive
namespace TinyFive.CountingPrimesOddWheel
open SieveMemory
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Exact execution of k+1 iterations, where the last one exits. -/
theorem five_loop (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (cap a E k : Nat) (hm : Layout image 328 cap mem)
    (ha : 512+a+20*k+13 < cap) (ha64 : 512+a+20*(k+1) < 2^64)
    (hE : E < 2^64) (hcont : k = 0 ∨ a+20*k < E)
    (hstop : E ≤ a+20*(k+1))
    (h11 : x.get 11 = BitVec.ofNat 64 a) (h7 : x.get 7 = 16777217)
    (h5 : x.get 5 = BitVec.ofNat 64 E) :
    run (4*(k+1)) ⟨x, 72, mem, [], out, .running⟩ =
      ⟨x.set 11 (BitVec.ofNat 64 (a+20*(k+1))), 88,
        fiveMemory mem a (k+1), [], out, .running⟩ := by
  induction k generalizing x mem a with
  | zero =>
    have hi := five_iteration x mem out cap a E hm (by omega) (by omega) hE h11 h7 h5
    change run 4 ⟨x, 72, mem, [], out, .running⟩ =
      ⟨x.set 11 (BitVec.ofNat 64 (a+20)), 88,
        fiveWord (fiveWord mem (512+a)) (512+a+10), [], out, .running⟩
    simpa only [show ¬ a+20 < E by omega, if_false] using hi
  | succ k ih =>
    have hi := five_iteration x mem out cap a E hm (by omega) (by omega) hE h11 h7 h5
    have hb : a+20 < E := by omega
    simp only [hb, if_true] at hi
    have hm1 : Layout image 328 cap (fiveWord (fiveWord mem (512+a)) (512+a+10)) := by
      unfold fiveWord
      exact (((((((hm.update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)
    have ht := ih (x.set 11 (BitVec.ofNat 64 (a+20))) _ (a+20) hm1 (by omega) (by omega) (by omega) (by omega) (by simp [Regs.get_set]) (by simp [Regs.get_set, h7]) (by simp [Regs.get_set, h5])
    rw [show 4*(k+1+1) = 4+4*(k+1) by omega, run_add, hi, ht]
    have heq : a+20+20*(k+1) = a+20*(k+1+1) := by omega
    rw [heq]
    conv =>
      rhs
      rw [fiveMemory_succ]
    have hr : (x.set 11 (BitVec.ofNat 64 (a+20))).set 11 (BitVec.ofNat 64 (a+20*(k+1+1))) =
        x.set 11 (BitVec.ofNat 64 (a+20*(k+1+1))) := by
      cases x
      simp only [Regs.set, Vector.set_set]
    rw [hr]


end TinyFive.CountingPrimesOddWheel
