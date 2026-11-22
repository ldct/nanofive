import GrumpyBinary.FinishMath

/-! From the end of the sieve (396) to the exit: the finish, the return to the driver, and the
driver's printing. -/
namespace TinyFive.GrumpyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory

local notation "bv" => BitVec.ofNat 64
local notation "iv" => BitVec.ofInt 64

theorem out_eq (out : String) (k : Nat) (hk : k < 2 ^ 63) :
    (out ++ (bv k).toInt.repr).push (Char.ofNat 10) = out ++ toString k ++ "\n" := by
  have h1 : (bv k).toInt = k := by
    rw [BitVec.toInt_eq_toNat_of_msb (msb_bv k (by omega))]; simp; omega
  rw [h1]
  show (out ++ Int.repr (Int.ofNat k)).push _ = _
  simp only [Int.repr]
  rfl

/-- `return larges[0] + 1`, then the driver prints it with a newline and exits with code 0. -/
theorem fin_ret (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (Cb R : Nat)
    (hmem : Prefix image mem 1236) (hsz : mem.size = 4194304)
    (h8 : x.get 8 = bv Cb) (h2 : x.get 2 = bv 4194192) (hC : 1248 ≤ Cb) (hC' : Cb + 8 ≤ 4194192)
    (hR : R < 2 ^ 40)
    (hL : readBytes mem Cb 8 = some (bv R)) (hra : readBytes mem 4194296 8 = some (bv 8)) :
    is_exited_with_output (run 22 ⟨x, bv 468, mem, [], out, .running⟩) (out ++ toString (R + 1) ++ "\n") := by
  obtain ⟨w1, hw1⟩ := readBytes_some mem 4194288 8 (by omega)
  obtain ⟨w2, hw2⟩ := readBytes_some mem 4194280 8 (by omega)
  obtain ⟨w3, hw3⟩ := readBytes_some mem 4194272 8 (by omega)
  obtain ⟨w4, hw4⟩ := readBytes_some mem 4194264 8 (by omega)
  obtain ⟨w5, hw5⟩ := readBytes_some mem 4194256 8 (by omega)
  obtain ⟨w6, hw6⟩ := readBytes_some mem 4194248 8 (by omega)
  obtain ⟨w7, hw7⟩ := readBytes_some mem 4194240 8 (by omega)
  obtain ⟨w8, hw8⟩ := readBytes_some mem 4194232 8 (by omega)
  obtain ⟨w9, hw9⟩ := readBytes_some mem 4194224 8 (by omega)
  obtain ⟨w10, hw10⟩ := readBytes_some mem 4194216 8 (by omega)
  have := out_eq out (R + 1) (by omega)
  gexec
  exact ⟨rfl, rfl⟩

/-- The finish's table facts, from the sieve invariant at the cutoff. -/
theorem inv_FH {N a : Nat} {x : Regs 64} {mem : Array (BitVec 8)} (h : Inv N a x mem) (hc : Cut N a) :
    FH mem 1248 (LB ((isqrt N + 1) / 2)) (LC ((isqrt N + 1) / 2)) N (RL N a).length (C a (a - 1))
      (isqrt N) (fun i => C a (2 * i + 1)) (qq N a) := by
  obtain ⟨hvb, hDb⟩ := inv_bounds h
  have hlay := layout ((isqrt N + 1) / 2)
  have hLD : LD ((isqrt N + 1) / 2) = LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 := rfl
  have hv1 : 1 ≤ isqrt N := le_isqrt (by have := h.hN3; omega)
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
    hA := Nat.le_refl _
    hB := by omega
    hCb := by omega
    hC := by omega
    size := h.size
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
    (h : Inv N a x mem) (hcut : N < a * a * (a * a)) :
    ∃ n, is_exited_with_output (run n ⟨x, bv 396, mem, [], out, .running⟩)
      (out ++ toString (countPrimes N) ++ "\n") := by
  have hc : Cut N a := ⟨h.hN3, h.hN, h.hp3, hcut⟩
  have hF := inv_FH h hc
  obtain ⟨hvb, hDb⟩ := inv_bounds h
  have hlay := layout ((isqrt N + 1) / 2)
  have hLD : LD ((isqrt N + 1) / 2) = LC ((isqrt N + 1) / 2) + (isqrt N + 1) / 2 * 8 := rfl
  have hv1 : 1 ≤ isqrt N := le_isqrt (by have := h.hN3; omega)
  have hlen := RL_len N a h.hp3 hv1
  have hs1 : 1 ≤ (RL N a).length := by simp [RL]
  have hs := hF.hs
  have hpc := hF.hpc
  have hsz := h.size
  -- the triangular term
  have hL0 : readBytes mem (LC ((isqrt N + 1) / 2)) 8 = some (bv (C a (N / qq N a 0))) := by
    have := h.la 0 hs1; simpa using this
  obtain ⟨y1, hr1, y13, y15, g1⟩ := fin_pro x mem out (LC ((isqrt N + 1) / 2)) (RL N a).length
    (C a (a - 1)) (C a (N / qq N a 0)) h.pre h.size h.x14 h.x9 h.x8 hs1 hs hpc (by omega) hL0
  have hS1 : Same mem (wr mem (LC ((isqrt N + 1) / 2))
      (bv (tri (RL N a).length (C a (a - 1)) + C a (N / qq N a 0))) 8)
      (LC ((isqrt N + 1) / 2)) (LC ((isqrt N + 1) / 2) + 8) :=
    Same.wr _ _ _ _ _ _ (by omega) (by omega) (by omega)
  -- subtracting the large counts
  obtain ⟨n2, y2, mem2, hr2, hS2, hZ2, y12, y16, g2⟩ := fin_loop1 y1 _ out (LC ((isqrt N + 1) / 2))
    (RL N a).length 1 (C a (a - 1)) (fun k => C a (N / qq N a k))
    ((tri (RL N a).length (C a (a - 1)) + C a (N / qq N a 0) : Nat) : Int)
    (hS1.prefix h.pre (by omega)) (by rw [hS1.size_eq, h.size])
    (by rw [y15, iv_nat]) y13 (by rw [g1 9 (by decide), h.x9]) (by rw [g1 8 (by decide), h.x8])
    (by rw [g1 14 (by decide), h.x14]) (Nat.le_refl 1) hs1 hs (by omega) (by omega)
    (fun j hj1 hj => hS1.read (h.la j hj) (by omega))
    (by rw [read_wr_same _ _ _ _ (by omega), iv_nat]; simp)
  have f2 : ∀ r : Reg, r ∉ ([12, 13, 15, 16] : List Reg) → y2.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g2 r (by simp [hr]), g1 r (by simp [hr])]
  -- the triple correction
  have hS12 := hS1.trans hS2
  obtain ⟨n3, y3, mem3, hr3, hS3, hZ3, g3⟩ := tri_loop y2 mem2 out 1248 (LB ((isqrt N + 1) / 2))
    (LC ((isqrt N + 1) / 2)) N (RL N a).length (C a (a - 1)) (isqrt N) 1 (fun i => C a (2 * i + 1))
    (qq N a) _ (hF.same hS12) y12
    (by rw [f2 9 (by decide), h.x9]) (by rw [f2 19 (by decide), h.x19])
    (by rw [f2 21 (by decide), h.x21]) (by rw [f2 20 (by decide), h.x20])
    (by rw [f2 14 (by decide), h.x14]) (by rw [f2 8 (by decide), h.x8])
    (by rw [y16]; congr 1) (Nat.le_refl 1) hs1 hZ2
  have f3 : ∀ r : Reg, r ∉ ([0, 6, 10, 11, 12, 13, 15, 16, 17, 28] : List Reg) → y3.get r = x.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3 r (by simp [hr]), f2 r (by simp [hr])]
  have hS := hS12.trans hS3
  -- the value
  have hval := finish_value hc
  have hcp : countPrimes 3 ≤ countPrimes N := countPrimes_mono h.hN3
  have h3 : countPrimes 3 = 2 := by decide
  have hcpN : countPrimes N ≤ N := countPrimes_le N
  have hR : readBytes mem3 (LC ((isqrt N + 1) / 2)) 8 = some (bv (countPrimes N - 1)) := by
    rw [hZ3, ← iv_nat]; congr 2; omega
  have hret := fin_ret y3 mem3 out (LC ((isqrt N + 1) / 2)) (countPrimes N - 1)
    (hS.prefix h.pre (by omega)) (by rw [hS.size_eq, h.size]) (by rw [f3 8 (by decide), h.x8])
    (by rw [f3 2 (by decide), h.x2]) (by omega) (by omega) (by have := h.hN; omega) hR
    (hS.read h.ra (by omega))
  refine ⟨12 + n2 + n3 + 22, ?_⟩
  rw [run_add, run_add, run_add, hr1, hr2, hr3, show countPrimes N = countPrimes N - 1 + 1 by omega]
  exact hret

end TinyFive.GrumpyBinary
