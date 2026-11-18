import CountingPrimesOddWheelMachine
import OddSieveMath
import Std.Tactic.BVDecide

namespace TinyFive.CountingPrimesOddWheel
open SieveMemory OddSieveMath
set_option maxRecDepth 4096

/-- A word load of four flag bytes, each 0 or 1, is their little-endian sum. -/
private theorem read_word (mem : Array (BitVec 8)) (a f0 f1 f2 f3 : Nat)
    (h0 : mem[a]? = some (BitVec.ofNat 8 f0)) (h1 : mem[a+1]? = some (BitVec.ofNat 8 f1))
    (h2 : mem[a+2]? = some (BitVec.ofNat 8 f2)) (h3 : mem[a+3]? = some (BitVec.ofNat 8 f3))
    (b0 : f0 ≤ 1) (b1 : f1 ≤ 1) (b2 : f2 ≤ 1) (b3 : f3 ≤ 1) :
    (readBytes mem a 4).map (BitVec.signExtend 64) =
      some (BitVec.ofNat 64 (f0 + 256*f1 + 65536*f2 + 16777216*f3)) := by
  have h2' : mem[a+1+1]? = some (BitVec.ofNat 8 f2) := h2
  have h3' : mem[a+1+1+1]? = some (BitVec.ofNat 8 f3) := h3
  have c0 : f0 = 0 ∨ f0 = 1 := by omega
  have c1 : f1 = 0 ∨ f1 = 1 := by omega
  have c2 : f2 = 0 ∨ f2 = 1 := by omega
  have c3 : f3 = 0 ∨ f3 = 1 := by omega
  simp only [readBytes, h0, h1, h2', h3']
  rcases c0 with rfl | rfl <;> rcases c1 with rfl | rfl <;> rcases c2 with rfl | rfl <;>
    rcases c3 with rfl | rfl <;> decide

/-- The two-step fold of four byte lanes, none above 124. -/
private theorem fold_lanes (l0 l1 l2 l3 : Nat) (h0 : l0 ≤ 124) (h1 : l1 ≤ 124) (h2 : l2 ≤ 124)
    (h3 : l3 ≤ 124) (t : BitVec 64)
    (ht : t = BitVec.ofNat 64 (l0 + 256*l1 + 65536*l2 + 16777216*l3)) :
    (t + t >>> 16) &&& 255#64 = BitVec.ofNat 64 (l0 + l2) ∧
    ((t + t >>> 16) >>> 8) &&& 255#64 = BitVec.ofNat 64 (l1 + l3) := by
  subst t
  have hm : ∀ a : Nat, a &&& 255 = a % 256 := fun a => Nat.and_two_pow_sub_one_eq_mod a 8
  obtain ⟨w, hw⟩ : ∃ w, w = l0 + 256*l1 + 65536*l2 + 16777216*l3 := ⟨_, rfl⟩
  rw [← hw]
  have e1 : w % 2^64 = w := by omega
  have e2 : w / 2^16 = l2 + 256*l3 := by omega
  have e3 : (w + (l2 + 256*l3)) % 2^64 = w + (l2 + 256*l3) := by omega
  have e4 : (w + (l2 + 256*l3)) / 2^8 = l1 + l3 + 256*l2 + 65536*l3 := by omega
  have e5 : (l1 + l3 + 256*l2 + 65536*l3) % 256 = l1 + l3 := by omega
  have e6 : (l1 + l3) % 2^64 = l1 + l3 := by omega
  have e7 : (w + (l2 + 256*l3)) % 256 = l0 + l2 := by omega
  have e8 : (l0 + l2) % 2^64 = l0 + l2 := by omega
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, hm, e1, e2, e3, e4, e5, e6, e7, e8]

/-- The 16 zero bytes preceding the flag array, indexed from address 496. -/
def paddedFlag (f : Nat → Nat) (i : Nat) : Nat := if i < 16 then 0 else f (i-16)

theorem paddedFlag_le_one (f : Nat → Nat) (hf : ∀ i, f i ≤ 1) (i : Nat) :
    paddedFlag f i ≤ 1 := by
  unfold paddedFlag
  split <;> simp_all

theorem padded_csum (f : Nat → Nat) (k : Nat) :
    csum (paddedFlag f) (16+k) = csum f k := by
  induction k with
  | zero => simp [csum, paddedFlag]
  | succ k ih =>
      rw [show 16+(k+1) = (16+k)+1 by omega, csum_succ, csum_succ, ih]
      simp [paddedFlag, show ¬ 16+k < 16 by omega]

private theorem padded_prefix_zero (f : Nat → Nat) (k : Nat) (hk : k ≤ 16) :
    csum (paddedFlag f) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [csum_succ, ih (by omega)]
      simp [paddedFlag, show k < 16 by omega]

private theorem signed_sub (q k : Nat) (hq : q < 2^37) (hk : k ≤ 496) :
    (BitVec.ofNat 64 q - BitVec.ofNat 64 k).toInt = (q : Int) - (k : Int) := by
  have he : BitVec.ofNat 64 q - BitVec.ofNat 64 k =
      BitVec.ofInt 64 ((q : Int) - (k : Int)) := by
    simp [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
  rw [he, BitVec.toInt_ofInt_eq_self (by omega)]
  all_goals omega

private theorem signed_nat (q : Nat) (hq : q < 2^37) :
    (BitVec.ofNat 64 q).toInt = (q : Int) := by
  have h := signed_sub q 0 hq (by omega)
  simpa using h

theorem padded_byte (E i : Nat) (f : Nat → Nat) (mem : Array (BitVec 8))
    (hi : i < E+16)
    (flags : ∀ j, j < E → mem[512+j]? = some (BitVec.ofNat 8 (f j)))
    (pad : ∀ a, 496 ≤ a → a < 512 → mem[a]? = some 0) :
    mem[496+i]? = some (BitVec.ofNat 8 (paddedFlag f i)) := by
  by_cases h : i < 16
  · simpa [paddedFlag, h] using pad (496+i) (by omega) (by omega)
  · have he : 496+i = 512+(i-16) := by omega
    simpa [paddedFlag, h, he] using flags (i-16) (by omega)

/-- A reverse word load can straddle the start of the flag array. -/
theorem padded_word (E i : Nat) (f : Nat → Nat) (mem : Array (BitVec 8))
    (hi : i+4 ≤ E+16) (hf : ∀ j, f j ≤ 1)
    (flags : ∀ j, j < E → mem[512+j]? = some (BitVec.ofNat 8 (f j)))
    (pad : ∀ a, 496 ≤ a → a < 512 → mem[a]? = some 0) :
    (readBytes mem (496+i) 4).map (BitVec.signExtend 64) =
      some (BitVec.ofNat 64 (paddedFlag f i + 256*paddedFlag f (i+1) +
        65536*paddedFlag f (i+2) + 16777216*paddedFlag f (i+3))) := by
  apply read_word
  · exact padded_byte E i f mem (by omega) flags pad
  · simpa [Nat.add_assoc] using padded_byte E (i+1) f mem (by omega) flags pad
  · simpa [Nat.add_assoc] using padded_byte E (i+2) f mem (by omega) flags pad
  · simpa [Nat.add_assoc] using padded_byte E (i+3) f mem (by omega) flags pad
  all_goals exact paddedFlag_le_one f hf _

private theorem code200 : code[50]?.getD .ecall = .opImm .add 10 5 1 := by decide
private theorem code204 : code[51]?.getD .ecall = .opImm .add 6 5 (-496) := by decide
private theorem code208 : code[52]?.getD .ecall = .branch .bge 6 0 8 := by decide
private theorem code212 : code[53]?.getD .ecall = .opImm .add 6 0 0 := by decide
private theorem code216 : code[54]?.getD .ecall = .opImm .add 28 0 0 := by decide
private theorem code220 : code[55]?.getD .ecall = .load .word true 29 5 508 := by decide
private theorem code224 : code[56]?.getD .ecall = .load .word true 30 5 504 := by decide
private theorem code228 : code[57]?.getD .ecall = .load .word true 31 5 500 := by decide
private theorem code232 : code[58]?.getD .ecall = .load .word true 17 5 496 := by decide
private theorem code236 : code[59]?.getD .ecall = .op .add 28 28 29 := by decide
private theorem code240 : code[60]?.getD .ecall = .op .add 28 28 30 := by decide
private theorem code244 : code[61]?.getD .ecall = .op .add 28 28 31 := by decide
private theorem code248 : code[62]?.getD .ecall = .op .add 28 28 17 := by decide
private theorem code252 : code[63]?.getD .ecall = .opImm .add 5 5 (-16) := by decide
private theorem code256 : code[64]?.getD .ecall = .branch .blt 6 5 (-36) := by decide
private theorem code260 : code[65]?.getD .ecall = .opImm .srl 29 28 16 := by decide
private theorem code264 : code[66]?.getD .ecall = .op .add 28 28 29 := by decide
private theorem code268 : code[67]?.getD .ecall = .opImm .and 29 28 255 := by decide
private theorem code272 : code[68]?.getD .ecall = .op .sub 10 10 29 := by decide
private theorem code276 : code[69]?.getD .ecall = .opImm .srl 28 28 8 := by decide
private theorem code280 : code[70]?.getD .ecall = .opImm .and 28 28 255 := by decide
private theorem code284 : code[71]?.getD .ecall = .op .sub 10 10 28 := by decide
private theorem code288 : code[72]?.getD .ecall = .branch .blt 0 5 (-84) := by decide

macro "wheel_count_exec" : tactic =>
  `(tactic| simp [run, step_image, code200, code204, code208, code212, code216,
      code220, code224, code228, code232, code236,
      code240, code244, code248, code252, code256, code260, code264, code268, code272, code276,
      code280, code284, code288, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, ecall, Width.bytes, Regs.get_set, BranchOp.taken, *])

/-- The counting phase starts by including the two even-wheel exceptions. -/
theorem count_entry (E : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 328) (h5 : x.get 5 = BitVec.ofNat 64 E) :
    ∃ y, y.get 10 = BitVec.ofNat 64 (E+1) ∧ y.get 5 = BitVec.ofNat 64 E ∧
      run 1 ⟨x, 200, mem, [], out, .running⟩ = ⟨y, 204, mem, [], out, .running⟩ := by
  refine ⟨x.set 10 (BitVec.ofNat 64 (E+1)), ?_, ?_, ?_⟩
  · simp [Regs.get_set]
  · simp [Regs.get_set, h5]
  · wheel_count_exec
    simp [← BitVec.ofNat_add]

/-- The chunk threshold is clamped at signed zero. -/
theorem count_block_head (e : BitVec 64) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 328) (h5 : x.get 5 = e) :
    ∃ fuel y, fuel ≤ 4 ∧ y.get 5 = e ∧ y.get 10 = x.get 10 ∧ y.get 28 = 0 ∧
      y.get 6 = (if (e - 496#64).slt 0#64 then 0 else e - 496#64) ∧
      run fuel ⟨x, 204, mem, [], out, .running⟩ = ⟨y, 220, mem, [], out, .running⟩ := by
  have he : e + 18446744073709551120#64 = e - 496#64 := by bv_decide
  by_cases hb : (e - 496#64).slt 0#64
  · refine ⟨4, ((x.set 6 (e-496#64)).set 6 0).set 28 0, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Regs.get_set, h5]
    · simp [Regs.get_set]
    · simp [Regs.get_set]
    · simp [Regs.get_set, hb]
    · wheel_count_exec
  · refine ⟨3, (x.set 6 (e-496#64)).set 28 0, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Regs.get_set, h5]
    · simp [Regs.get_set]
    · simp [Regs.get_set]
    · simp [Regs.get_set, hb]
    · wheel_count_exec

/-- One reverse round loads four words before decrementing the signed cursor. -/
theorem count_round (e stop acc w0 w1 w2 w3 : BitVec 64)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 328)
    (h5 : x.get 5 = e) (h6 : x.get 6 = stop) (h28 : x.get 28 = acc)
    (r0 : (readBytes mem ((e.toNat + 508) % 2^64) 4).map (BitVec.signExtend 64) = some w0)
    (r1 : (readBytes mem ((e.toNat + 504) % 2^64) 4).map (BitVec.signExtend 64) = some w1)
    (r2 : (readBytes mem ((e.toNat + 500) % 2^64) 4).map (BitVec.signExtend 64) = some w2)
    (r3 : (readBytes mem ((e.toNat + 496) % 2^64) 4).map (BitVec.signExtend 64) = some w3) :
    ∃ y, y.get 5 = e - 16#64 ∧ y.get 6 = stop ∧
      y.get 28 = acc + w0 + w1 + w2 + w3 ∧ y.get 10 = x.get 10 ∧
      run 10 ⟨x, 220, mem, [], out, .running⟩ =
        ⟨y, if stop.slt (e - 16#64) then 220 else 260, mem, [], out, .running⟩ := by
  obtain ⟨v0, hv0, hs0⟩ := Option.map_eq_some_iff.mp r0
  obtain ⟨v1, hv1, hs1⟩ := Option.map_eq_some_iff.mp r1
  obtain ⟨v2, hv2, hs2⟩ := Option.map_eq_some_iff.mp r2
  obtain ⟨v3, hv3, hs3⟩ := Option.map_eq_some_iff.mp r3
  have he : e + 18446744073709551600#64 = e - 16#64 := by bv_decide
  refine ⟨(((((((((x.set 29 w0).set 30 w1).set 31 w2).set 17 w3).set 28
    (acc+w0)).set 28 (acc+w0+w1)).set 28 (acc+w0+w1+w2)).set 28
    (acc+w0+w1+w2+w3)).set 5 (e-16#64)), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Regs.get_set]
  · simp [Regs.get_set, h6]
  · simp [Regs.get_set]
  · simp [Regs.get_set]
  · by_cases hb : stop.slt (e - 16#64)
    · simp only [hb, ite_true]
      wheel_count_exec
    · simp only [hb]
      wheel_count_exec

/-- A round at a positive cursor, expressed in terms of the padded flag array. -/
theorem count_round_flags (E q : Nat) (f : Nat → Nat) (stop a : BitVec 64)
    (l0 l1 l2 l3 : Nat) (hq : 0 < q) (hqE : q ≤ E) (hE : E < 2^37)
    (hf : ∀ j, f j ≤ 1)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 328)
    (flags : ∀ j, j < E → mem[512+j]? = some (BitVec.ofNat 8 (f j)))
    (pad : ∀ j, 496 ≤ j → j < 512 → mem[j]? = some 0)
    (h5 : x.get 5 = BitVec.ofNat 64 q) (h6 : x.get 6 = stop) (h10 : x.get 10 = a)
    (h28 : x.get 28 = BitVec.ofNat 64 (l0+256*l1+65536*l2+16777216*l3)) :
    ∃ y, y.get 5 = BitVec.ofNat 64 q - 16#64 ∧ y.get 6 = stop ∧ y.get 10 = a ∧
      y.get 28 = BitVec.ofNat 64
        ((l0+paddedFlag f q+paddedFlag f (q+4)+paddedFlag f (q+8)+paddedFlag f (q+12)) +
        256*(l1+paddedFlag f (q+1)+paddedFlag f (q+5)+paddedFlag f (q+9)+paddedFlag f (q+13)) +
        65536*(l2+paddedFlag f (q+2)+paddedFlag f (q+6)+paddedFlag f (q+10)+paddedFlag f (q+14)) +
        16777216*(l3+paddedFlag f (q+3)+paddedFlag f (q+7)+paddedFlag f (q+11)+paddedFlag f (q+15))) ∧
      run 10 ⟨x, 220, mem, [], out, .running⟩ =
        ⟨y, if stop.slt (BitVec.ofNat 64 q - 16#64) then 220 else 260, mem, [], out, .running⟩ := by
  let g := paddedFlag f
  have hq64 : q % 2^64 = q := by omega
  have h508 : (q+508) % 2^64 = q+508 := by omega
  have h504 : (q+504) % 2^64 = q+504 := by omega
  have h500 : (q+500) % 2^64 = q+500 := by omega
  have h496 : (q+496) % 2^64 = q+496 := by omega
  have r0 := padded_word E (q+12) f mem (by omega) hf flags pad
  have r1 := padded_word E (q+8) f mem (by omega) hf flags pad
  have r2 := padded_word E (q+4) f mem (by omega) hf flags pad
  have r3 := padded_word E q f mem (by omega) hf flags pad

  have w0 : (readBytes mem (q+508) 4).map (BitVec.signExtend 64) =
      some (BitVec.ofNat 64 (g (q+12)+256*g (q+13)+65536*g (q+14)+16777216*g (q+15))) := by
    simpa [g, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r0
  have w1 : (readBytes mem (q+504) 4).map (BitVec.signExtend 64) =
      some (BitVec.ofNat 64 (g (q+8)+256*g (q+9)+65536*g (q+10)+16777216*g (q+11))) := by
    simpa [g, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r1
  have w2 : (readBytes mem (q+500) 4).map (BitVec.signExtend 64) =
      some (BitVec.ofNat 64 (g (q+4)+256*g (q+5)+65536*g (q+6)+16777216*g (q+7))) := by
    simpa [g, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r2
  have w3 : (readBytes mem (q+496) 4).map (BitVec.signExtend 64) =
      some (BitVec.ofNat 64 (g q+256*g (q+1)+65536*g (q+2)+16777216*g (q+3))) := by
    simpa [g, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r3
  obtain ⟨y, hy5, hy6, hy28, hy10, hr⟩ := count_round (BitVec.ofNat 64 q) stop
    (BitVec.ofNat 64 (l0+256*l1+65536*l2+16777216*l3))
    (BitVec.ofNat 64 (g (q+12)+256*g (q+13)+65536*g (q+14)+16777216*g (q+15)))
    (BitVec.ofNat 64 (g (q+8)+256*g (q+9)+65536*g (q+10)+16777216*g (q+11)))
    (BitVec.ofNat 64 (g (q+4)+256*g (q+5)+65536*g (q+6)+16777216*g (q+7)))
    (BitVec.ofNat 64 (g q+256*g (q+1)+65536*g (q+2)+16777216*g (q+3)))
    x mem out hmem h5 h6 h28
    (by simpa [BitVec.toNat_ofNat, hq64, h508] using w0)
    (by simpa [BitVec.toNat_ofNat, hq64, h504] using w1)
    (by simpa [BitVec.toNat_ofNat, hq64, h500] using w2)
    (by simpa [BitVec.toNat_ofNat, hq64, h496] using w3)
  refine ⟨y, hy5, hy6, by simpa [h10] using hy10, ?_, hr⟩
  rw [hy28, ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  dsimp only [g]
  omega

/-- Reverse rounds within one 496-byte chunk. -/
private theorem count_inner (E q0 q stop l0 l1 l2 l3 : Nat) (f : Nat → Nat) (a : BitVec 64)
    (hE : E < 2^37) (hq0 : q0 ≤ E) (hq : 0 < q) (hqq : q ≤ q0)
    (hstop : stop ≤ q) (hstop0 : q0 ≤ stop+496) (hmod : (q0-q)%16 = 0)
    (hd : q0-q ≤ 480)
    (hl0 : 4*l0 ≤ q0-q) (hl1 : 4*l1 ≤ q0-q)
    (hl2 : 4*l2 ≤ q0-q) (hl3 : 4*l3 ≤ q0-q)
    (hf : ∀ j, f j ≤ 1)
    (hsum : csum (paddedFlag f) (q+16) + (l0+l1+l2+l3) =
      csum (paddedFlag f) (q0+16))
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 328)
    (flags : ∀ j, j < E → mem[512+j]? = some (BitVec.ofNat 8 (f j)))
    (pad : ∀ j, 496 ≤ j → j < 512 → mem[j]? = some 0)
    (h5 : x.get 5 = BitVec.ofNat 64 q) (h6 : x.get 6 = BitVec.ofNat 64 stop)
    (h10 : x.get 10 = a)
    (h28 : x.get 28 = BitVec.ofNat 64 (l0+256*l1+65536*l2+16777216*l3)) :
    ∃ fuel q' m0 m1 m2 m3 y,
      fuel + 10*((q0-q)/16) ≤ 310 ∧ q' < q ∧ q' ≤ stop ∧ q0 ≤ q'+496 ∧
      m0 ≤ 124 ∧ m1 ≤ 124 ∧ m2 ≤ 124 ∧ m3 ≤ 124 ∧
      csum (paddedFlag f) (q'+16) + (m0+m1+m2+m3) =
        csum (paddedFlag f) (q0+16) ∧
      y.get 10 = a ∧ (q' > 0 → y.get 5 = BitVec.ofNat 64 q') ∧
      y.get 28 = BitVec.ofNat 64 (m0+256*m1+65536*m2+16777216*m3) ∧
      ((0#64).slt (y.get 5) = decide (q' > 0)) ∧
      run fuel ⟨x, 220, mem, [], out, .running⟩ = ⟨y, 260, mem, [], out, .running⟩ := by
  let g := paddedFlag f
  let m0 := l0+g q+g (q+4)+g (q+8)+g (q+12)
  let m1 := l1+g (q+1)+g (q+5)+g (q+9)+g (q+13)
  let m2 := l2+g (q+2)+g (q+6)+g (q+10)+g (q+14)
  let m3 := l3+g (q+3)+g (q+7)+g (q+11)+g (q+15)
  have hg : ∀ i, g i ≤ 1 := paddedFlag_le_one f hf
  have b0 := hg q; have b1 := hg (q+1); have b2 := hg (q+2); have b3 := hg (q+3)
  have b4 := hg (q+4); have b5 := hg (q+5); have b6 := hg (q+6); have b7 := hg (q+7)
  have b8 := hg (q+8); have b9 := hg (q+9); have b10 := hg (q+10); have b11 := hg (q+11)
  have b12 := hg (q+12); have b13 := hg (q+13); have b14 := hg (q+14); have b15 := hg (q+15)
  have hcs := csum_add16 g q
  have hm : csum g q + (m0+m1+m2+m3) = csum g (q0+16) := by
    dsimp only [m0, m1, m2, m3]
    change csum g (q+16) + (l0+l1+l2+l3) = csum g (q0+16) at hsum
    omega
  have hm0 : 4*m0 ≤ q0-q+16 := by dsimp [m0]; omega
  have hm1 : 4*m1 ≤ q0-q+16 := by dsimp [m1]; omega
  have hm2 : 4*m2 ≤ q0-q+16 := by dsimp [m2]; omega
  have hm3 : 4*m3 ≤ q0-q+16 := by dsimp [m3]; omega
  obtain ⟨y, hy5, hy6, hy10, hy28, hr⟩ :=
    count_round_flags E q f (BitVec.ofNat 64 stop) a l0 l1 l2 l3 hq (by omega) hE hf
      x mem out hmem flags pad h5 h6 h10 h28
  change y.get 28 = BitVec.ofNat 64 (m0+256*m1+65536*m2+16777216*m3) at hy28
  have hcmp : (BitVec.ofNat 64 stop).slt (BitVec.ofNat 64 q - 16#64) =
      decide (stop+16 < q) := by
    rw [BitVec.slt_eq_decide, signed_nat stop (by omega), signed_sub q 16 (by omega) (by omega)]
    by_cases hh : stop+16 < q <;> simp [hh] <;> omega
  rw [hcmp] at hr
  by_cases hb : stop+16 < q
  · simp only [hb, decide_true, ite_true] at hr
    have he : BitVec.ofNat 64 q - 16#64 = BitVec.ofNat 64 (q-16) := by
      apply BitVec.eq_of_toInt_eq
      rw [signed_sub q 16 (by omega) (by omega), signed_nat (q-16) (by omega)]
      omega
    rw [he] at hy5
    obtain ⟨fuel, q', n0, n1, n2, n3, z, hfu, hq', hstop', hspan, hn0, hn1, hn2, hn3,
      hsum', hz10, hz5, hz28, hzsign, ht⟩ :=
      count_inner E q0 (q-16) stop m0 m1 m2 m3 f a hE hq0 (by omega) (by omega) (by omega)
        hstop0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        hf (by
          have he : q-16+16 = q := by omega
          simpa [he] using hm)
        y mem out hmem flags pad hy5 hy6 hy10 hy28
    refine ⟨10+fuel, q', n0, n1, n2, n3, z, by omega, by omega, hstop', hspan,
      hn0, hn1, hn2, hn3, hsum', hz10, hz5, hz28, hzsign, ?_⟩
    rw [run_add, hr, ht]
  · simp only [hb, decide_false, Bool.false_eq_true, ite_false] at hr
    have hq' : q-16 ≤ stop := by omega
    have hsum' : csum g ((q-16)+16) + (m0+m1+m2+m3) = csum g (q0+16) := by
      by_cases h16 : 16 ≤ q
      · have he : q-16+16 = q := by omega
        simpa [he] using hm
      · have hz : csum g q = 0 := padded_prefix_zero f q (by omega)
        have hz' : csum g ((q-16)+16) = 0 := by
          have : q-16 = 0 := by omega
          simpa [this, g] using padded_prefix_zero f 16 (by omega)
        omega
    have hpositive : (0#64).slt (y.get 5) = decide (q-16 > 0) := by
      rw [hy5, BitVec.slt_eq_decide, BitVec.toInt_zero,
        signed_sub q 16 (by omega) (by omega)]
      by_cases hh : q-16 > 0 <;> simp [hh] <;> omega
    have hpos : q-16 > 0 → y.get 5 = BitVec.ofNat 64 (q-16) := by
      intro hp
      rw [hy5]
      apply BitVec.eq_of_toInt_eq
      rw [signed_sub q 16 (by omega) (by omega), signed_nat (q-16) (by omega)]
      omega
    refine ⟨10, q-16, m0, m1, m2, m3, y, by omega, by omega, hq', by omega,
      by omega, by omega, by omega, by omega, hsum', hy10, hpos, hy28, hpositive, hr⟩
termination_by q

/-- One completed chunk is folded without carries and subtracted from the count. -/
theorem count_fold (l0 l1 l2 l3 : Nat) (h0 : l0 ≤ 124) (h1 : l1 ≤ 124)
    (h2 : l2 ≤ 124) (h3 : l3 ≤ 124) (a e : BitVec 64)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 328)
    (h10 : x.get 10 = a) (h5 : x.get 5 = e)
    (h28 : x.get 28 = BitVec.ofNat 64 (l0 + 256*l1 + 65536*l2 + 16777216*l3)) :
    ∃ y, y.get 10 = a - BitVec.ofNat 64 (l0+l2) - BitVec.ofNat 64 (l1+l3) ∧
      y.get 5 = e ∧ run 8 ⟨x, 260, mem, [], out, .running⟩ =
        ⟨y, if (0#64).slt e then 204 else 292, mem, [], out, .running⟩ := by
  let t := BitVec.ofNat 64 (l0 + 256*l1 + 65536*l2 + 16777216*l3)
  have ht : x.get 28 = t := h28
  obtain ⟨hA, hB⟩ := fold_lanes l0 l1 l2 l3 h0 h1 h2 h3 t rfl
  refine ⟨((((((x.set 29 (t >>> 16)).set 28 (t + t >>> 16)).set 29
    (BitVec.ofNat 64 (l0+l2))).set 10 (a - BitVec.ofNat 64 (l0+l2))).set 28
    ((t + t >>> 16) >>> 8)).set 28 (BitVec.ofNat 64 (l1+l3))).set 10
    (a - BitVec.ofNat 64 (l0+l2) - BitVec.ofNat 64 (l1+l3)), ?_, ?_, ?_⟩
  · simp [Regs.get_set]
  · simp [Regs.get_set, h5]
  · by_cases hb : (0#64).slt e
    · simp only [hb, ite_true]
      wheel_count_exec
      dsimp only [t] at hA hB
      rw [hA, hB]
    · simp only [hb]
      wheel_count_exec
      dsimp only [t] at hA hB
      rw [hA, hB]

/-- One chunk, including the clamped header, reverse rounds and lane fold. -/
theorem count_chunk (E q : Nat) (f : Nat → Nat) (a : BitVec 64)
    (hE : E < 2^37) (hq : 0 < q) (hqE : q ≤ E) (hf : ∀ j, f j ≤ 1)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 328)
    (flags : ∀ j, j < E → mem[512+j]? = some (BitVec.ofNat 8 (f j)))
    (pad : ∀ j, 496 ≤ j → j < 512 → mem[j]? = some 0)
    (h5 : x.get 5 = BitVec.ofNat 64 q) (h10 : x.get 10 = a) :
    ∃ fuel q' y, fuel ≤ 322 ∧ q' < q ∧ q-496 ≤ q' ∧ (q' = 0 ∨ q'+480 ≤ q) ∧
      y.get 10 = a - BitVec.ofNat 64 (csum f q - csum f q') ∧
      (q' > 0 → y.get 5 = BitVec.ofNat 64 q') ∧
      run fuel ⟨x, 204, mem, [], out, .running⟩ =
        ⟨y, if q' = 0 then 292 else 204, mem, [], out, .running⟩ := by
  have hthreshold :
      (if (BitVec.ofNat 64 q - 496#64).slt 0#64 then 0 else BitVec.ofNat 64 q - 496#64) =
        BitVec.ofNat 64 (q-496) := by
    by_cases hh : q < 496
    · have hs : (BitVec.ofNat 64 q - 496#64).slt 0#64 = true := by
        rw [BitVec.slt_iff_toInt_lt, signed_sub q 496 (by omega) (by omega), BitVec.toInt_zero]
        omega
      have hz : q-496 = 0 := by omega
      simp [hs, hz]
    · have hs : (BitVec.ofNat 64 q - 496#64).slt 0#64 = false := by
        apply Bool.eq_false_iff.mpr
        intro hn
        have hn' := BitVec.slt_iff_toInt_lt.mp hn
        rw [signed_sub q 496 (by omega) (by omega), BitVec.toInt_zero] at hn'
        omega
      simp only [hs, Bool.false_eq_true, ite_false]
      apply BitVec.eq_of_toInt_eq
      rw [signed_sub q 496 (by omega) (by omega), signed_nat (q-496) (by omega)]
      omega
  obtain ⟨fh, u, hfh, hu5, hu10, hu28, hu6, hh⟩ :=
    count_block_head (BitVec.ofNat 64 q) x mem out hmem h5
  rw [hthreshold] at hu6
  obtain ⟨fi, q', m0, m1, m2, m3, v, hfi, hq', hstop, hspan, hm0, hm1, hm2, hm3,
    hsum, hv10, hv5, hv28, hvsign, hi⟩ :=
    count_inner E q q (q-496) 0 0 0 0 f a hE hqE hq (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hf (by simp)
      u mem out hmem flags pad hu5 hu6 (by simpa [h10] using hu10) (by simpa using hu28)
  obtain ⟨z, hz10, hz5, hz⟩ :=
    count_fold m0 m1 m2 m3 hm0 hm1 hm2 hm3 a (v.get 5) v mem out hmem hv10 rfl hv28
  have hsum' : csum f q' + (m0+m1+m2+m3) = csum f q := by
    rw [show q'+16=16+q' by omega, show q+16=16+q by omega, padded_csum, padded_csum] at hsum
    exact hsum
  have hsub : a - BitVec.ofNat 64 (m0+m2) - BitVec.ofNat 64 (m1+m3) =
      a - BitVec.ofNat 64 (csum f q - csum f q') := by
    have hn : (m0+m2)+(m1+m3) = csum f q - csum f q' := by omega
    rw [← hn, BitVec.sub_sub]
    simp only [BitVec.ofNat_add]
  rw [hsub] at hz10
  have hz' : run 8 ⟨v, 260, mem, [], out, .running⟩ =
      ⟨z, if q' = 0 then 292 else 204, mem, [], out, .running⟩ := by
    by_cases he : q' = 0
    · simpa [he, hvsign] using hz
    · have hp : q' > 0 := by omega
      simpa [he, hvsign, hp] using hz
  refine ⟨fh+fi+8, q', z, by omega, hq', by omega, ?_, hz10, ?_, ?_⟩
  · by_cases he : q' = 0
    · exact Or.inl he
    · exact Or.inr (by omega)
  · intro hp
    rw [hz5]
    exact hv5 hp
  · rw [run_add, run_add, hh, hi, hz']

end TinyFive.CountingPrimesOddWheel
