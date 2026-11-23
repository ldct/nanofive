import ZjyBinary.FinishRun

/-! `pi`'s outer loop: `calc(3)` if `9 ≤ R`, `calc(5)` if `25 ≤ R`, then the mod-30 wheel
`p = 7, 11, 13, ...` while `p ≤ isqrt R`, calling `calc(p)` when `skip[p]` is clear. The wheel
visits every prime from 7 on, and `skip[p]` is clear exactly for primes, so the rounds are
grumpygordon's: one per odd prime `p` with `p⁴ ≤ N`. -/
namespace TinyFive.ZjyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

/-! ## The wheel -/

/-- The gaps `4, 2, 4, 2, 4, 6, 2, 6` of the wheel table at 1480. -/
def wheel (c : Nat) : Nat :=
  match c % 8 with
  | 0 => 4 | 1 => 2 | 2 => 4 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 2 | _ => 6

/-- The residue mod 30 of the `c`-th wheel value: `7, 11, 13, 17, 19, 23, 29, 31`. -/
def wres (c : Nat) : Nat :=
  match c % 8 with
  | 0 => 7 | 1 => 11 | 2 => 13 | 3 => 17 | 4 => 19 | 5 => 23 | 6 => 29 | _ => 1

theorem not_prime_dvd (r d : Nat) (hd : r % d = 0) (h1 : 2 ≤ d) (h2 : d < r) : ¬ Prime r := fun hp =>
  ((prime_iff r).mp hp).2 d h1 h2 hd

theorem wheel_step (c p : Nat) (h : p % 30 = wres c) (hp : 7 ≤ p) :
    (p + wheel c) % 30 = wres (c + 1) ∧ p % 2 = 1 ∧ wheel c ≤ 6 ∧ 2 ≤ wheel c ∧
      ∀ r, p < r → r < p + wheel c → ¬ Prime r := by
  have nd : ∀ r, p < r → (r % 2 = 0 ∨ r % 3 = 0 ∨ r % 5 = 0) → ¬ Prime r := fun r hr h => by
    rcases h with h | h | h
    · exact not_prime_dvd r 2 h (by decide) (by omega)
    · exact not_prime_dvd r 3 h (by decide) (by omega)
    · exact not_prime_dvd r 5 h (by decide) (by omega)
  rcases (by omega : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨
    c % 8 = 6 ∨ c % 8 = 7) with hk | hk | hk | hk | hk | hk | hk | hk <;>
  · have hk1 : (c + 1) % 8 = (c % 8 + 1) % 8 := by omega
    simp only [wheel, wres, hk1, hk] at h ⊢
    refine ⟨by omega, by omega, by decide, by decide, fun r h1 h2 => nd r h1 ?_⟩
    rcases (by omega : r = p + 1 ∨ r = p + 2 ∨ r = p + 3 ∨ r = p + 4 ∨ r = p + 5) with
      rfl | rfl | rfl | rfl | rfl <;> omega

theorem wheel_read (mem : Array (BitVec 8)) (hw : Prefix image mem 1512) (c : Nat) :
    readBytes mem (1480 + c % 8 * 4) 4 = some (BitVec.ofNat 32 (wheel c)) := by
  have hc := Nat.mod_lt c (show 8 > 0 by decide)
  rw [readBytes_congr mem image _ 4 (fun j h1 h2 => hw j (by omega))]
  rcases (by omega : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨
    c % 8 = 6 ∨ c % 8 = 7) with hk | hk | hk | hk | hk | hk | hk | hk <;>
  · simp only [wheel, hk]; decide +kernel

/-! ## Moving the stage past non-primes -/

/-- A composite odd `p`: the memory at stage `p` is the memory at stage `p + 2`. -/
theorem zmem_skip {N p : Nat} {mem : Array (BitVec 8)} (h : ZMem N p mem) (hn : ¬ Prime p) :
    ZMem N (p + 2) mem := by
  have hRL := RL_skip N p h.hp3 h.hpo hn
  have hC := C_skip2 p h.hp3 h.hpo hn
  refine ⟨h.hN7, h.hN, by have := h.hp3; omega, by have := h.hpo; omega, ?_, h.size, h.pre, h.wh, h.ra,
    ?_, h.sm.ext (fun i _ => by rw [hC]), by rw [hRL]; exact h.ro,
    by rw [hRL]; exact h.la.ext (fun i _ => by rw [hC]), h.sk.ext (fun i _ => by
      simp only [show SkipMarked (p + 2) i ↔ SkipMarked p i from
        skip_step_composite p i h.hp3 h.hpo hn])⟩
  · intro r h3 hr hpr
    by_cases hrp : r < p
    · exact h.hpr r h3 hrp hpr
    · by_cases hre : r = p
      · subst hre; exact absurd hpr hn
      · exact absurd hpr (by rw [show r = p + 1 by omega]; exact not_prime_even p h.hp3 h.hpo)
  · rw [hRL, C_pc_skip p h.hp3 h.hpo hn]; exact h.sl

/-- No primes in `[p, q)`, both odd: stage `p` is stage `q`. -/
theorem zmem_adv {N p : Nat} (q : Nat) {mem : Array (BitVec 8)} (h : ZMem N p mem) (hpq : p ≤ q)
    (hq : q % 2 = 1) (hn : ∀ r, p ≤ r → r < q → ¬ Prime r) : ZMem N q mem := by
  by_cases hpq' : p = q
  · subst hpq'; exact h
  · have h2 := zmem_skip h (hn p (Nat.le_refl p) (by omega))
    have := h.hpo
    exact zmem_adv q h2 (by omega) hq (fun r h1 h2 => hn r (by omega) h2)
termination_by q - p

/-! ## The wheel loop at 1296 -/

theorem alu_and7 (c : Nat) (hc : c < 2 ^ 64) : alu .and (bv c) 7#64 = bv (c % 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [alu, BitVec.toNat_and, BitVec.toNat_ofNat]
  have h7 : (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 := by decide
  rw [h7, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The registers of the wheel loop. -/
structure WRegs (x : Regs 64) (N p c : Nat) : Prop where
  h19 : x.get 19 = bv (isqrt (isqrt N))
  h20 : x.get 20 = bv p
  h21 : x.get 21 = bv c
  h22 : x.get 22 = bv 4194160
  h23 : x.get 23 = bv 1480
  h2 : x.get 2 = bv 4194096
  h8 : x.get 8 = bv 1520
  h9 : x.get 9 = bv (ZB ((isqrt N + 1) / 2))
  h18 : x.get 18 = bv (ZC ((isqrt N + 1) / 2) (isqrt N))

theorem wl_exit (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N p c : Nat)
    (hmem : Prefix image mem 1480) (hx : WRegs x N p c) (hp : isqrt (isqrt N) < p) (hp' : p < 2 ^ 30) :
    run 1 ⟨x, bv 1296, mem, [], out, .running⟩ = ⟨x, bv 956, mem, [], out, .running⟩ := by
  obtain ⟨h19, h20, h21, h22, h23, h2, h8, h9, h18⟩ := hx
  zexec

theorem wl_skip (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N p c D : Nat)
    (hmem : Prefix image mem 1480) (hx : WRegs x N p c) (hp : p ≤ isqrt (isqrt N)) (hp' : p < 2 ^ 30) (hsq : isqrt (isqrt N) < 2 ^ 30)
    (hD : D + p < 4194000) (ssk : readBytes mem 4194144 8 = some (bv D))
    (hS : readBytes mem (D + p) 1 = some (BitVec.ofNat 8 1)) :
    ∃ y, run 5 ⟨x, bv 1296, mem, [], out, .running⟩ = ⟨y, bv 1332, mem, [], out, .running⟩ ∧
      (∀ r : Reg, r ∉ ([15] : List Reg) → y.get r = x.get r) := by
  obtain ⟨h19, h20, h21, h22, h23, h2, h8, h9, h18⟩ := hx
  exact ⟨_, by zexec; rfl, by frame_tac⟩

theorem wl_call (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N p c D : Nat)
    (hmem : Prefix image mem 1480) (hx : WRegs x N p c) (hp : p ≤ isqrt (isqrt N)) (hp' : p < 2 ^ 30) (hsq : isqrt (isqrt N) < 2 ^ 30)
    (hD : D + p < 4194000) (ssk : readBytes mem 4194144 8 = some (bv D))
    (hS : readBytes mem (D + p) 1 = some (BitVec.ofNat 8 0)) :
    ∃ y, run 9 ⟨x, bv 1296, mem, [], out, .running⟩ = ⟨y, bv 36, mem, [], out, .running⟩ ∧
      y.get 10 = bv 4194160 ∧ y.get 11 = bv p ∧ y.get 1 = bv 1332 ∧
      (∀ r : Reg, r ∉ ([1, 10, 11, 15] : List Reg) → y.get r = x.get r) := by
  obtain ⟨h19, h20, h21, h22, h23, h2, h8, h9, h18⟩ := hx
  exact ⟨_, by zexec; rfl, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
    by frame_tac⟩

theorem wl_adv (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (N p c : Nat)
    (hmem : Prefix image mem 1480) (hx : WRegs x N p c) (hp' : p < 2 ^ 30) (hc : c < 2 ^ 30)
    (hw : readBytes mem (1480 + c % 8 * 4) 4 = some (BitVec.ofNat 32 (wheel c))) (hwb : wheel c ≤ 6) :
    ∃ y, run 7 ⟨x, bv 1332, mem, [], out, .running⟩ = ⟨y, bv 1296, mem, [], out, .running⟩ ∧
      WRegs y N (p + wheel c) (c + 1) ∧
      (∀ r : Reg, r ∉ ([15, 20, 21] : List Reg) → y.get r = x.get r) := by
  obtain ⟨h19, h20, h21, h22, h23, h2, h8, h9, h18⟩ := hx
  have := alu_and7
  have hc8 := Nat.mod_lt c (show 8 > 0 by decide)
  refine ⟨_, by zexec; rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by frame_tac⟩ <;>
    simp [Regs.get_set, h19, h22, h23, h2, h8, h9, h18, Nat.add_comm]

theorem WRegs.frame {x y : Regs 64} {N p c : Nat} (h : WRegs x N p c) (l : List Reg)
    (hl : ∀ r ∈ [19, 20, 21, 22, 23, 2, 8, 9, 18], r ∉ l)
    (hf : ∀ r : Reg, r ∉ l → y.get r = x.get r) : WRegs y N p c :=
  ⟨by rw [hf 19 (hl 19 (by decide)), h.h19], by rw [hf 20 (hl 20 (by decide)), h.h20],
   by rw [hf 21 (hl 21 (by decide)), h.h21], by rw [hf 22 (hl 22 (by decide)), h.h22],
   by rw [hf 23 (hl 23 (by decide)), h.h23], by rw [hf 2 (hl 2 (by decide)), h.h2],
   by rw [hf 8 (hl 8 (by decide)), h.h8], by rw [hf 9 (hl 9 (by decide)), h.h9],
   by rw [hf 18 (hl 18 (by decide)), h.h18]⟩

theorem sq4_of_lt {N p : Nat} (h : isqrt (isqrt N) < p) : N < p * p * (p * p) := by
  have h1 := (isqrt_spec (isqrt N)).2
  have h2 := (isqrt_spec N).2
  have h3 : isqrt N + 1 ≤ p * p := by
    have := Nat.mul_le_mul (show isqrt (isqrt N) + 1 ≤ p by omega) (show isqrt (isqrt N) + 1 ≤ p by omega)
    omega
  have := Nat.mul_le_mul h3 h3
  omega

theorem sq4_of_le {N p : Nat} (h : p ≤ isqrt (isqrt N)) : p * p * (p * p) ≤ N := by
  have h1 := (isqrt_spec (isqrt N)).1
  have h2 := (isqrt_spec N).1
  have h3 : p * p ≤ isqrt N := Nat.le_trans (Nat.mul_le_mul h h) h1
  exact Nat.le_trans (Nat.mul_le_mul h3 h3) h2

theorem isqrt4_small {N : Nat} (hN : N < 100000000000) : isqrt (isqrt N) ≤ 562 := by
  apply Decidable.byContradiction; intro hc
  have h1 := sq4_of_le (show 563 ≤ isqrt (isqrt N) by omega)
  have h2 : 563 * 563 * (563 * 563) = 100469346961 := by decide
  omega

/-- The wheel loop, from the wheel value `p` (the `c`-th) to the finish at 956, at a stage `a`
with `N < a⁴`. -/
theorem wheel_loop (N p c : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h : ZMem N p mem) (hx : WRegs x N p c) (hres : p % 30 = wres c) (hp7 : 7 ≤ p) (hcp : c < p)
    (hpb : p ≤ isqrt (isqrt N) + 6) :
    ∃ n a y mem', run n ⟨x, bv 1296, mem, [], out, .running⟩ = ⟨y, bv 956, mem', [], out, .running⟩ ∧
      ZMem N a mem' ∧ N < a * a * (a * a) ∧ y.get 2 = bv 4194096 ∧ y.get 8 = bv 1520 ∧
      y.get 9 = bv (ZB ((isqrt N + 1) / 2)) ∧ y.get 18 = bv (ZC ((isqrt N + 1) / 2) (isqrt N)) := by
  have hsq := isqrt4_small h.hN
  obtain ⟨hvb, hCe⟩ := zmem_bounds h
  have hlay := zlayout ((isqrt N + 1) / 2) (isqrt N)
  obtain ⟨hres', hpo, hw6, hw2, hgap⟩ := wheel_step c p hres hp7
  have hpo' := (wheel_step (c + 1) (p + wheel c) hres' (by omega)).2.1
  by_cases hpq : isqrt (isqrt N) < p
  · exact ⟨1, p, x, mem, wl_exit x mem out N p c h.pre hx hpq (by omega), h, sq4_of_lt hpq,
      hx.h2, hx.h8, hx.h9, hx.h18⟩
  have hq := sq4_of_le (show p ≤ isqrt (isqrt N) by omega)
  have hpv : p ≤ isqrt N := Nat.le_trans (by omega) (Nat.le_trans (Nat.le_mul_self _) (isqrt_spec (isqrt N)).1)
  have hsk := h.sk p (by omega)
  dsimp only at hsk
  have hw := wheel_read mem h.wh c
  by_cases hprime : Prime p
  · rw [if_neg (show ¬ SkipMarked p p from fun hs => (skip_self_iff p h.hp3 hpo).mp hs hprime)] at hsk
    obtain ⟨y1, hr1, y10, y11, y1r, g1⟩ := wl_call x mem out N p c (ZD ((isqrt N + 1) / 2)) h.pre hx
      (by omega) (by omega) (by omega) (by omega) h.sl.sk hsk
    have hx1 := hx.frame _ (by decide) g1
    obtain ⟨n2, y2, mem2, hr2, h2, y28, y22, g2⟩ := calc_prime N p y1 mem out 1520 1332 h hprime hq
      y10 y11 hx1.h2 hx1.h8 y1r (by decide) (by decide)
    have hx2 : WRegs y2 N p c := ⟨by rw [g2 19 (by decide), hx1.h19], by rw [g2 20 (by decide), hx1.h20],
      by rw [g2 21 (by decide), hx1.h21], by rw [g2 22 (by decide), hx1.h22],
      by rw [g2 23 (by decide), hx1.h23], y22, y28, by rw [g2 9 (by decide), hx1.h9],
      by rw [g2 18 (by decide), hx1.h18]⟩
    obtain ⟨y3, hr3, hx3, g3⟩ := wl_adv y2 mem2 out N p c h2.pre hx2 (by omega) (by omega)
      (wheel_read mem2 h2.wh c) hw6
    have h3 := zmem_adv (p + wheel c) h2 (by omega) (by omega)
      (fun r h1 h2 => hgap r (by omega) h2)
    obtain ⟨n4, a, y4, mem4, hr4, h4, hc4, z2, z8, z9, z18⟩ := wheel_loop N (p + wheel c) (c + 1) y3
      mem2 out h3 hx3 hres' (by omega) (by omega) (by omega)
    exact ⟨9 + n2 + 7 + n4, a, y4, mem4, by rw [run_add, run_add, run_add, hr1, hr2, hr3, hr4], h4,
      hc4, z2, z8, z9, z18⟩
  · rw [if_pos ((skip_self_iff p h.hp3 hpo).mpr hprime)] at hsk
    obtain ⟨y1, hr1, g1⟩ := wl_skip x mem out N p c (ZD ((isqrt N + 1) / 2)) h.pre hx
      (by omega) (by omega) (by omega) (by omega) h.sl.sk hsk
    have hx1 := hx.frame _ (by decide) g1
    obtain ⟨y3, hr3, hx3, g3⟩ := wl_adv y1 mem out N p c h.pre hx1 (by omega) (by omega) hw hw6
    have h3 := zmem_adv (p + wheel c) h (by omega) (by omega)
      (fun r h1 h2 => by
        by_cases hr : r = p
        · subst hr; exact hprime
        · exact hgap r (by omega) h2)
    obtain ⟨n4, a, y4, mem4, hr4, h4, hc4, z2, z8, z9, z18⟩ := wheel_loop N (p + wheel c) (c + 1) y3
      mem out h3 hx3 hres' (by omega) (by omega) (by omega)
    exact ⟨5 + 7 + n4, a, y4, mem4, by rw [run_add, run_add, hr1, hr3, hr4], h4, hc4, z2, z8, z9, z18⟩
termination_by isqrt (isqrt N) + 1 - p
decreasing_by all_goals omega

end TinyFive.ZjyBinary
