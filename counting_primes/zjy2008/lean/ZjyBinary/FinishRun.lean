import ZjyBinary.Finish

/-! From the end of the sieve (956) to the exit: the finish, `pi`'s return to the driver, and
the driver's printing. -/
namespace TinyFive.ZjyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64
local notation "iv" => BitVec.ofInt 64

/-- `return z`, then the driver prints it with a newline and exits with code 0. -/
theorem fin_ret (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (R : Nat)
    (hmem : Prefix image mem 1480) (hsz : mem.size = 4194304)
    (h10 : x.get 10 = bv R) (h2 : x.get 2 = bv 4194096) (hR : R < 2 ^ 40)
    (hra : readBytes mem 4194296 8 = some (bv 8)) :
    is_exited_with_output (run 18 ⟨x, bv 620, mem, [], out, .running⟩) (out ++ toString R ++ "\n") := by
  obtain ⟨w1, hw1⟩ := readBytes_some mem 4194288 8 (by omega)
  obtain ⟨w2, hw2⟩ := readBytes_some mem 4194280 8 (by omega)
  obtain ⟨w3, hw3⟩ := readBytes_some mem 4194272 8 (by omega)
  obtain ⟨w4, hw4⟩ := readBytes_some mem 4194264 8 (by omega)
  obtain ⟨w5, hw5⟩ := readBytes_some mem 4194256 8 (by omega)
  obtain ⟨w6, hw6⟩ := readBytes_some mem 4194248 8 (by omega)
  obtain ⟨w7, hw7⟩ := readBytes_some mem 4194240 8 (by omega)
  obtain ⟨w8, hw8⟩ := readBytes_some mem 4194232 8 (by omega)
  have := out_eq out R (by omega)
  zexec
  exact ⟨rfl, rfl⟩

/-- The finish's table facts, from the memory invariant at the cutoff. -/
theorem zmem_FH {N a : Nat} {mem : Array (BitVec 8)} (h : ZMem N a mem) (hc : Cut N a) :
    ZFH mem 1520 (ZB ((isqrt N + 1) / 2)) N (RL N a).length (C a (a - 1))
      (isqrt N) (fun i => C a (2 * i + 1)) (qq N a) := by
  obtain ⟨hvb, hDb⟩ := zmem_bounds h
  have hlay := zlayout ((isqrt N + 1) / 2) (isqrt N)
  have hv1 : 1 ≤ isqrt N := le_isqrt (by have := h.hN7; omega)
  have hlen := RL_len N a h.hp3 hv1
  have ha564 : a ≤ 564 := by
    apply Decidable.byContradiction; intro hc
    have := h.hpr 563 (by decide) (by omega) prime_563
    have := h.hN
    omega
  have hpc : C a (a - 1) ≤ a - 1 := C_le a _
  exact {
    hs := by omega
    hpc := by omega
    hN := by have := h.hN; omega
    hA := by omega
    hB := by omega
    pre := h.pre
    ro := fun k hk1 hk => by
      obtain ⟨hak, hkv, _⟩ := hc.qq_range k hk1 hk
      exact ⟨h.ro k hk, by have := hc.ha; omega, by omega⟩
    smr := fun d hd1 hdv => by
      refine ⟨h.sm ((d - 1) / 2) (by omega), by omega, ?_⟩
      rw [smd_C a d hc.ha hd1]
      have := C_le a d
      omega
    dl := fun l hl1 hl => by
      obtain ⟨hal, hlv, _⟩ := hc.qq_range l hl1 hl
      exact hc.div2 _ _ hal hal hlv hlv
    dk := fun l k hl1 hlk hk => by
      obtain ⟨hal, hlv, _⟩ := hc.qq_range l hl1 (by omega)
      obtain ⟨hak, hkv, _⟩ := hc.qq_range k (by omega) hk
      exact hc.div2 _ _ hal hak hlv hkv
    el := fun l hl1 hl => by
      obtain ⟨hal, hlv, _⟩ := hc.qq_range l hl1 hl
      obtain ⟨hX1, hXv⟩ := hc.div2 _ _ hal hal hlv hlv
      rw [smd_C a _ hc.ha hX1]
      have := C_mono a hXv
      have := C_isqrt N a hc.ha (by omega)
      omega }

/-- From the end of the sieve at the cutoff stage `a` to the exit, having printed `π(N)`. -/
theorem finish_run (N a : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h : ZMem N a mem) (hcut : N < a * a * (a * a))
    (h2 : x.get 2 = bv 4194096) (h18 : x.get 18 = bv (ZC ((isqrt N + 1) / 2) (isqrt N)))
    (h8 : x.get 8 = bv 1520) (h9 : x.get 9 = bv (ZB ((isqrt N + 1) / 2))) :
    ∃ n, is_exited_with_output (run n ⟨x, bv 956, mem, [], out, .running⟩)
      (out ++ toString (countPrimes N) ++ "\n") := by
  have hc : Cut N a := ⟨by have := h.hN7; omega, h.hN, h.hp3, hcut⟩
  have hF := zmem_FH h hc
  obtain ⟨hvb, hDb⟩ := zmem_bounds h
  have hlay := zlayout ((isqrt N + 1) / 2) (isqrt N)
  have hv1 : 1 ≤ isqrt N := le_isqrt (by have := h.hN7; omega)
  have hlen := RL_len N a h.hp3 hv1
  have hs1 : 1 ≤ (RL N a).length := by simp [RL]
  have hs := hF.hs
  have hpc := hF.hpc
  have hsz := h.size
  -- the triangular term
  have hL0 : readBytes mem (ZC ((isqrt N + 1) / 2) (isqrt N)) 8 = some (bv (C a (N / qq N a 0))) := by
    have := h.la 0 hs1; simpa using this
  have hL0b : C a (N / qq N a 0) < 2 ^ 40 := by
    have := C_le a (N / qq N a 0); have := h.hN; have := Nat.div_le_self N (qq N a 0); omega
  obtain ⟨y1, hr1, y10, y15, y13, y12, g1⟩ := fin_pro x mem out (ZC ((isqrt N + 1) / 2) (isqrt N))
    (RL N a).length (C a (a - 1)) (C a (N / qq N a 0)) h.pre h2 h18 h.sl.V h.sl.C hs1 hs hpc
    (by omega) hL0 hL0b
  -- subtracting the large counts
  obtain ⟨n2, y2, hr2, z10, g2⟩ := fin_loop1 y1 mem out (ZC ((isqrt N + 1) / 2) (isqrt N))
    (RL N a).length 0 (fun k => C a (N / qq N a k))
    ((tri (RL N a).length (C a (a - 1)) + (C a (N / qq N a 0) + 1) : Nat) : Int) h.pre
    (by rw [y10, iv_nat]) y15 y13 (by rw [g1 18 (by decide), h18]) hs1 hs (by omega) (by omega)
    (fun j hj1 hj => h.la j hj)
  have f2 : ∀ r : Reg, r ∉ ([10, 12, 13, 14, 15] : List Reg) → y2.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g2 r (by simp [hr]), g1 r (by simp [hr])]
  obtain ⟨y3, hr3, z28, z6, z11, g3⟩ := tri_enter y2 mem out N (C a (a - 1)) h.pre
    (by rw [f2 2 (by decide), h2]) (by rw [g2 12 (by decide), y12]) h.sl.n
  -- the triple correction
  obtain ⟨n4, y4, hr4, z4, g4⟩ := tri_loop y3 mem out 1520 (ZB ((isqrt N + 1) / 2)) N
    (RL N a).length (C a (a - 1)) (isqrt N) 1 (fun i => C a (2 * i + 1)) (qq N a) _ hF z11
    (by rw [g3 13 (by decide), g2 13 (by decide), y13]) z28
    (by rw [g3 9 (by decide), f2 9 (by decide), h9]) (by rw [g3 8 (by decide), f2 8 (by decide), h8])
    (by rw [g3 12 (by decide), g2 12 (by decide), y12]) (by rw [z6]; congr 1)
    (by rw [g3 10 (by decide), z10]) (Nat.le_refl 1) hs1
  -- the value
  have hval := finish_value hc
  have hcpN : countPrimes N ≤ N := countPrimes_le N
  have hR : y4.get 10 = bv (countPrimes N) := by
    rw [z4, ← iv_nat]; congr 1; push_cast at hval ⊢; omega
  have hret := fin_ret y4 mem out (countPrimes N) h.pre hsz hR
    (by rw [g4 2 (by decide), g3 2 (by decide), f2 2 (by decide), h2]) (by have := h.hN; omega) h.ra
  refine ⟨13 + n2 + 3 + n4 + 18, ?_⟩
  rw [run_add, run_add, run_add, run_add, hr1, hr2, hr3, hr4]
  exact hret

end TinyFive.ZjyBinary
