import DecNumber.Image
import TinyFive.SieveMemory

/-! Bounded, exact calls to the pinned binary. These use the actual linked
entry points, including the comparator's internal helper calls. -/
namespace DecNumber.Bounded
open TinyFive Replay

-- Fixed, disjoint, naturally aligned regions in the 1 MiB NanoFive address space.
def capacity : Nat := 0x100000
def dest : Nat := 0x80000
def lhs : Nat := 0x80020
def rhs : Nat := 0x80040
def ctx : Nat := 0x80060
def sp : Nat := 0x90000
def returnPC : BitVec 64 := 0x100

def writable (frameSize a : Nat) : Bool :=
  decide (dest ≤ a ∧ a < dest + 12 ∧ a ≠ dest + 9 ∨ sp - frameSize ≤ a ∧ a < sp)

def abi (compare : Bool) : Regs 64 :=
  ⟨Vector.ofFn fun r => match r.val with
    | 1 => returnPC
    | 2 => BitVec.ofNat 64 sp
    | 10 => BitVec.ofNat 64 dest
    | 11 => BitVec.ofNat 64 lhs
    | 12 => BitVec.ofNat 64 (if compare then rhs else ctx)
    | 13 => BitVec.ofNat 64 ctx
    | _ => 0x000000013753ab00 + BitVec.ofNat 64 r.val⟩

/-- The relevant layout of a finite, single-unit decNumber (DECDPUN=3).
`digits` counts significant coefficient digits, with one digit for zero. -/
structure Decimal where
  digits : Nat
  exponent : Int
  negative : Bool
  coefficient : Nat

def signByte (negative : Bool) : BitVec 8 := if negative then 128 else 0

def Decimal.at (n : Decimal) (mem : Array (BitVec 8)) (ptr : Nat) : Prop :=
  readBytes mem ptr 4 = some (BitVec.ofNat 32 n.digits) ∧
  readBytes mem (ptr + 4) 4 = some (BitVec.ofInt 32 n.exponent) ∧
  mem[ptr + 8]? = some (signByte n.negative) ∧
  readBytes mem (ptr + 10) 2 = some (BitVec.ofNat 16 n.coefficient)

def Decimal.value (n : Decimal) : Rat :=
  let c := if n.negative then -(n.coefficient : Int) else (n.coefficient : Int)
  if n.exponent < 0 then mkRat c (10 ^ n.exponent.natAbs)
  else (c * (10 : Int) ^ n.exponent.natAbs : Int)

private def Decimal.known (n : Decimal) (mem : Bytes) (ptr : Nat) : Bytes :=
  let mem := write mem ptr (BitVec.ofNat 32 n.digits) 4
  let mem := write mem (ptr + 4) (BitVec.ofInt 32 n.exponent) 4
  let mem := put mem (ptr + 8) (signByte n.negative)
  write mem (ptr + 10) (BitVec.ofNat 16 n.coefficient) 2

private def Decimal.check (n : Decimal) (mem : Bytes) : Bool :=
  read mem dest 4 == some (BitVec.ofNat 32 n.digits) &&
  read mem (dest + 4) 4 == some (BitVec.ofInt 32 n.exponent) &&
  mem (dest + 8) == some (signByte n.negative) &&
  read mem (dest + 10) 2 == some (BitVec.ofNat 16 n.coefficient)

private theorem Decimal.check_sound (n : Decimal) {s : State} {m : Machine 64}
    (hm : Related s m) (h : n.check s.bytes = true) : n.at m.mem dest := by
  simp only [Decimal.check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hd, he⟩, hn⟩, hc⟩ := h
  exact ⟨read_agrees hm.2.2.2 hd, read_agrees hm.2.2.2 he,
    hm.2.2.2 _ _ hn, read_agrees hm.2.2.2 hc⟩

/-- jq's literal context: precision 147483648, maximum exponent range,
    round half up, no traps/status, no clamp. -/
def imageAndContext : Bytes :=
  let m := write Image.bytes ctx (147483648 : BitVec 32) 4
  let m := write m (ctx + 4) (999999999 : BitVec 32) 4
  let m := write m (ctx + 8) (-999999999 : BitVec 32) 4
  let m := write m (ctx + 12) (2 : BitVec 32) 4
  write m (ctx + 16) (0 : BitVec 72) 9

private def preserved : List Reg := [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

private def checked (n : Decimal) (frameSize fuel : Nat) (s : State) : Bool :=
  match untilReturn (writable frameSize) capacity returnPC fuel s with
  | none => false
  | some (_, r) => n.check r.bytes && r.x.get 10 == BitVec.ofNat 64 dest &&
      preserved.all (fun i => r.x.get i == s.x.get i) && read r.bytes (ctx + 20) 4 == some 0

/-- `run` counts instructions, not a C-language evaluation. No other instruction
    after returning to the caller is executed. -/
def Returns (n : Decimal) (frameSize fuel : Nat) (m : Machine 64) : Prop :=
  ∃ steps, steps ≤ fuel ∧ let r := run steps m
    r.pc = returnPC ∧ r.status = .running ∧ r.x.get 10 = BitVec.ofNat 64 dest ∧
    (∀ i ∈ preserved, r.x.get i = m.x.get i) ∧
    n.at r.mem dest ∧ readBytes r.mem (ctx + 20) 4 = some 0 ∧ Frame (writable frameSize) m r

private theorem checked_sound {n : Decimal} {frameSize fuel : Nat} {s : State} {m : Machine 64}
    (ha : Related s m) (hc : m.mem.size = capacity) (h : checked n frameSize fuel s = true) :
    Returns n frameSize fuel m := by
  unfold checked at h
  cases hr : untilReturn (writable frameSize) capacity returnPC fuel s with
  | none => simp [hr] at h
  | some sr =>
    rcases sr with ⟨steps, final⟩
    simp only [hr, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, hret⟩, hsave⟩, hstat⟩ := h
    obtain ⟨hout, hframe, hp, hsteps⟩ := untilReturn_sound ha hc hr
    refine ⟨steps, hsteps, hout.2.1.trans hp, hout.2.2.1, ?_, ?_,
      n.check_sound hout hn, read_agrees hout.2.2.2 hstat, hframe⟩
    · rw [hout.1, hret]
    · intro i hi
      rw [hout.1, ha.1]
      exact beq_iff_eq.mp (List.all_eq_true.mp hsave i hi)

/-- A single integer digit, optionally followed by a decimal point and one
    fractional digit. Both forms allow an initial minus, including negative zero. -/
def literal (negative : Bool) (whole : Fin 10) (fraction : Option (Fin 10)) : List (BitVec 8) :=
  (if negative then [45] else []) ++ [BitVec.ofNat 8 (48 + whole.val)] ++
    (match fraction with | none => [] | some f => [46, BitVec.ofNat 8 (48 + f.val)]) ++ [0]

def exact (negative : Bool) (whole : Fin 10) (fraction : Option (Fin 10)) : Decimal :=
  match fraction with
  | none => ⟨1, 0, negative, whole.val⟩
  | some f => ⟨if whole.val = 0 then 1 else 2, -1, negative, 10 * whole.val + f.val⟩

/-- The value of the generated JSON token, independently of decNumber's fields. -/
def literalValue (negative : Bool) (whole : Fin 10) (fraction : Option (Fin 10)) : Rat :=
  let sign (i : Int) : Int := if negative then -i else i
  match fraction with
  | none => sign whole.val
  | some f => mkRat (sign (10 * whole.val + f.val : Nat)) 10

theorem exact_value (negative : Bool) (whole : Fin 10) (fraction : Option (Fin 10)) :
    (exact negative whole fraction).value = literalValue negative whole fraction := by
  cases fraction with
  | none => simp [exact, Decimal.value, literalValue] <;> rfl
  | some _ => rfl

private def putList : Bytes → Nat → List (BitVec 8) → Bytes
  | m, _, [] => m
  | m, pos, b :: more => putList (put m pos b) (pos + 1) more

def parseStart (negative : Bool) (whole : Fin 10) (fraction : Option (Fin 10)) : State :=
  ⟨abi false, BitVec.ofNat 64 Image.parseEntry, putList imageAndContext lhs (literal negative whole fraction)⟩

private def parseCheck (negative : Bool) (whole : Fin 10) (fraction : Option (Fin 10)) : Bool :=
  checked (exact negative whole fraction) 144 160 (parseStart negative whole fraction)

private def fractions : List (Option (Fin 10)) := none :: (List.finRange 10).map some

private theorem fractions_complete (fraction : Option (Fin 10)) : fraction ∈ fractions := by
  cases fraction <;> simp [fractions, List.mem_finRange]

-- These two exhaustive decisions use Lean's native evaluator. The replay soundness and the
-- reduction from arbitrary initial memory to the exhaustive checks are kernel proofs.
private theorem parseExhaustive : ([false, true] : List Bool).all (fun neg => (List.finRange 10).all
    (fun w => fractions.all (parseCheck neg w))) = true := by native_decide

/-- All 220 signed one-digit integer and one-decimal-place spellings parse exactly. -/
theorem parse_exact (negative : Bool) (whole : Fin 10) (fraction : Option (Fin 10)) (m : Machine 64)
    (h : Related (parseStart negative whole fraction) m) (hc : m.mem.size = capacity) :
    Returns (exact negative whole fraction) 144 160 m := by
  exact checked_sound h hc (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp parseExhaustive negative (by cases negative <;> simp))
    whole (List.mem_finRange whole)) fraction (fractions_complete fraction))

/-- Integer subset whose parsed representation is also the compare ABI's input. -/
def integer (negative : Bool) (d : Fin 10) : Decimal := exact negative d none

/-- Exact mathematical comparison; rational equality identifies signed zeros. -/
def ordering (a b : Decimal) : Decimal :=
  ⟨1, 0, a.value < b.value, if a.value = b.value then 0 else 1⟩

def compareStart (aNeg : Bool) (a : Fin 10) (bNeg : Bool) (b : Fin 10) : State :=
  ⟨abi true, BitVec.ofNat 64 Image.compareEntry,
    (integer bNeg b).known ((integer aNeg a).known imageAndContext lhs) rhs⟩

private def compareCheck (aNeg : Bool) (a : Fin 10) (bNeg : Bool) (b : Fin 10) : Bool :=
  checked (ordering (integer aNeg a) (integer bNeg b)) 168 153 (compareStart aNeg a bNeg b)

private def integers : List (Bool × Fin 10) :=
  ([false, true] : List Bool).flatMap fun neg => (List.finRange 10).map (fun d => (neg, d))

private theorem integers_complete (neg : Bool) (d : Fin 10) : (neg, d) ∈ integers := by
  cases neg <;> simp [integers, List.mem_finRange]

private theorem compareExhaustive : integers.all (fun (an, a) =>
    integers.all fun (bn, b) => compareCheck an a bn b) = true := by native_decide

/-- The linked public comparator returns the exact ordering for all 400 pairs
    of signed digits (including both spellings of zero). -/
theorem compare_exact (aNeg : Bool) (a : Fin 10) (bNeg : Bool) (b : Fin 10) (m : Machine 64)
    (h : Related (compareStart aNeg a bNeg b) m) (hc : m.mem.size = capacity) :
    Returns (ordering (integer aNeg a) (integer bNeg b)) 168 153 m := by
  exact checked_sound h hc (List.all_eq_true.mp
    (List.all_eq_true.mp compareExhaustive (aNeg, a) (integers_complete aNeg a))
    (bNeg, b) (integers_complete bNeg b))

end DecNumber.Bounded
