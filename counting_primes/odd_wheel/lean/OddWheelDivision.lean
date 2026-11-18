import TinyFive.Primes

namespace TinyFive.OddWheelDivision

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- All intermediate additions and left shifts used to construct the reciprocal
    fit in an unsigned 64-bit register, for the supported input range. -/
theorem intermediate_bounds (n : Nat) (hn : n < 10^11) :
    let m := (n+3)/2
    let y := 21845*m
    1 ≤ m ∧ m ≤ 50000000001 ∧
    n+3 < 2^64 ∧ 4*m < 2^64 ∧ 5*m < 2^64 ∧
    80*m < 2^64 ∧ 85*m < 2^64 ∧ 21760*m < 2^64 ∧
    y < 2^64 ∧ y+y/65536 < 2^64 ∧
    y+(y+y/65536)/65536 < 2^64 := by
  dsimp only
  have hm : 1 ≤ (n+3)/2 ∧ (n+3)/2 ≤ 50000000001 := by omega
  have h₁ := Nat.div_le_self (21845*((n+3)/2)) 65536
  have h₂ := Nat.div_le_self
    (21845*((n+3)/2) + 21845*((n+3)/2)/65536) 65536
  omega

/-- The two reciprocal refinements compute `ceil (2*m/3) - 1` exactly. -/
theorem division_correct (n : Nat) (hn : n < 10^11) :
    let m := (n+3)/2
    let y := 21845*m
    (y+(y+y/65536)/65536)/32768 = (2*m-1)/3 := by
  dsimp only
  have hm : 1 ≤ (n+3)/2 ∧ (n+3)/2 ≤ 50000000001 := by omega
  let m := (n+3)/2
  let y := 21845*m
  let a := y/65536
  let b := (y+a)/65536
  have ha := Nat.div_add_mod y 65536
  have har := Nat.mod_lt y (by decide : 0 < 65536)
  have hb := Nat.div_add_mod (y+a) 65536
  have hbr := Nat.mod_lt (y+a) (by decide : 0 < 65536)
  have hlow : 65536*m < 3*(y+b)+32768 := by dsimp [a,b,y] at *; omega
  have hhigh : 3*(y+b) < 65536*m := by dsimp [a,b,y] at *; omega
  have he := Nat.div_add_mod (y+b) 32768
  have her := Nat.mod_lt (y+b) (by decide : 0 < 32768)
  have hq := Nat.div_add_mod (2*m-1) 3
  have hqr := Nat.mod_lt (2*m-1) (by decide : 0 < 3)
  change (y+b)/32768 = (2*m-1)/3
  omega
end TinyFive.OddWheelDivision
