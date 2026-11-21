import TinyFive.Machine

/-!
# Padding memory with zero bytes

`run_pad`: padding memory with zero bytes does not change a run that never faults, because
every access that succeeds in the smaller memory reads or writes the same bytes in the larger
one. `load_eq_pad`: loading into a large memory is loading into a small one and padding.
-/
namespace TinyFive

/-- Append `k` zero bytes to memory. -/
def Machine.pad {w : Nat} (m : Machine w) (k : Nat) : Machine w :=
  { m with mem := m.mem ++ Array.replicate k 0 }

private theorem readBytes_append (mem z : Array (BitVec 8)) :
    ∀ (n addr : Nat) (v : BitVec (8 * n)), readBytes mem addr n = some v →
      readBytes (mem ++ z) addr n = some v
  | 0, _, _, h => h
  | n + 1, addr, v, h => by
    simp only [readBytes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨lo, hlo, hi, hhi, hv⟩ := h
    have hlt : addr < mem.size := by
      rcases Nat.lt_or_ge addr mem.size with hlt | hge
      · exact hlt
      · rw [Array.getElem?_eq_none hge] at hlo
        cases hlo
    exact ⟨lo, by rw [Array.getElem?_append_left hlt]; exact hlo, hi,
      readBytes_append mem z n (addr+1) hi hhi, hv⟩

private theorem writeBytes_append {k : Nat} (z : Array (BitVec 8)) :
    ∀ (n : Nat) (mem mem' : Array (BitVec 8)) (addr : Nat) (v : BitVec k),
      writeBytes mem addr v n = some mem' → writeBytes (mem ++ z) addr v n = some (mem' ++ z)
  | 0, _, _, _, _, h => by simp_all [writeBytes]
  | n + 1, mem, mem', addr, v, h => by
    simp only [writeBytes] at h ⊢
    split at h
    · rename_i hlt
      rw [ite_eq_left (by simp; omega), Array.setIfInBounds_append_left hlt]
      exact writeBytes_append z n _ _ _ _ h
    · cases h

private theorem readBytes_none_append {mem : Array (BitVec 8)} {addr n : Nat}
    (h : readBytes mem addr n ≠ none) (z : Array (BitVec 8)) :
    readBytes (mem ++ z) addr n = readBytes mem addr n := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  rw [hv, readBytes_append mem z n addr v hv]

/-- One step commutes with padding unless it faults. -/
theorem step_pad {w : Nat} (m : Machine w) (k : Nat) (h : (step m).status ≠ .fault) :
    step (m.pad k) = (step m).pad k := by
  have hfetch : readBytes m.mem m.pc.toNat 4 ≠ none := by
    intro hn
    simp [step, hn, Machine.fail] at h
  simp only [step, Machine.pad] at h ⊢
  rw [readBytes_none_append hfetch]
  cases hd : (readBytes m.mem m.pc.toNat 4).bind (decode w) with
  | none => simp [hd, Machine.fail] at h
  | some i =>
    simp only [hd] at h ⊢
    cases i with
    | load width signed rd rs1 imm =>
      simp only [exec] at h ⊢
      split at h
      · rename_i v hv
        rw [readBytes_append _ _ _ _ _ hv]
        rfl
      · simp [Machine.fail] at h
    | store width rs2 rs1 imm =>
      simp only [exec] at h ⊢
      split at h
      · rename_i mem' hw
        rw [writeBytes_append _ _ _ _ _ _ hw]
        rfl
      · simp [Machine.fail] at h
    | ecall =>
      simp only [exec, ecall] at h ⊢
      split <;> (try split) <;> rfl
    | branch op rs1 rs2 imm =>
      simp only [exec]
      split <;> rfl
    | _ => rfl

theorem status_pad {w : Nat} (m : Machine w) (k : Nat) : (m.pad k).status = m.status := rfl

/-- Padding memory with zero bytes does not change a run that never faults. -/
theorem run_pad {w : Nat} (fuel : Nat) (m : Machine w) (k : Nat)
    (h : (run fuel m).status ≠ .fault) : run fuel (m.pad k) = (run fuel m).pad k := by
  induction fuel generalizing m with
  | zero => rfl
  | succ f ih =>
    by_cases hr : m.status = .running
    · have hpr : (m.pad k).status = .running := hr
      simp only [run, hr, ↓reduceIte] at h
      have hs : (step m).status ≠ .fault := by
        intro hf
        rw [run_stopped _ _ (by rw [hf]; decide), hf] at h
        exact h rfl
      simp only [run, hr, hpr, ↓reduceIte, step_pad m k hs]
      exact ih _ h
    · have hpr : ¬(m.pad k).status = .running := hr
      simp only [run, hr, hpr, ↓reduceIte]

/-! ## Loading into a larger memory -/

private theorem load_bytes_length (words : List (BitVec 32)) :
    (words.flatMap fun (x : BitVec 32) =>
      (List.range 4).map fun k => (x >>> (8 * k)).setWidth 8).length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons w ws ih => simp_all [List.flatMap_cons]; omega

/-- Loading into `large` bytes is loading into `small` bytes and padding the rest. -/
theorem load_eq_pad (words : List (BitVec 32)) (small large : Nat)
    (hw : 4 * words.length ≤ small) (hs : small ≤ large) :
    load 64 words large [] = (load 64 words small []).pad (large - small) := by
  simp only [Machine.pad, load, Machine.mk.injEq, and_true, true_and]
  apply Array.toList_inj.mp
  simp only [load_bytes_length, Array.toList_append,
    Array.toList_replicate, List.append_assoc, List.replicate_append_replicate]
  congr 2
  omega


end TinyFive
