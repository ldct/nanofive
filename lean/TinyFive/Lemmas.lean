import TinyFive.Machine

/-!
# General facts about the machine model

Facts used by the correctness proofs of more than one program: composing runs, and how memory
reads relate to memory writes and to the image that `load` builds.
-/

namespace TinyFive

theorem run_add {w : Nat} (a b : Nat) (m : Machine w) : run (a + b) m = run b (run a m) := by
  induction a generalizing m with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.add_right_comm, run, run]
    split
    · exact ih _
    · cases b <;> simp [run, *]

/-- The bytes of a word, least significant first, as `load` lays them out. -/
def wordBytes (x : BitVec 32) : List (BitVec 8) :=
  (List.range 4).map fun k => (x >>> (8 * k)).setWidth 8

/-! ## Reading memory -/

/-- A read depends only on the bytes it reads. -/
theorem readBytes_congr {mem mem' : Array (BitVec 8)} {addr n : Nat}
    (h : ∀ i, addr ≤ i → i < addr + n → mem[i]? = mem'[i]?) :
    readBytes mem addr n = readBytes mem' addr n := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    simp only [readBytes]
    rw [h addr (Nat.le_refl _) (by omega), ih (fun i h1 h2 => h i (by omega) (by omega))]

theorem readBytes_one {mem : Array (BitVec 8)} {addr : Nat} {b : BitVec 8}
    (h : mem[addr]? = some b) : readBytes mem addr 1 = some (b.cast (by omega)) := by
  simp only [readBytes, h, Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
  rw [BitVec.zero_width_append]
  rfl

theorem readBytes_four {mem : Array (BitVec 8)} {addr : Nat} {x : BitVec 32}
    (h : ∀ k < 4, mem[addr + k]? = some ((x >>> (8 * k)).setWidth 8)) :
    readBytes mem addr 4 = some x := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [readBytes, h0, h1, h2, h3, Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_setWidth]
  repeat' split
  all_goals simp only [BitVec.getLsbD_ushiftRight, ← BitVec.getLsbD_eq_getElem]
  all_goals first | omega | (congr 1; omega)

/-! ## Writing memory -/

theorem writeBytes_size {k : Nat} {mem mem' : Array (BitVec 8)} {addr n : Nat} {v : BitVec k}
    (h : writeBytes mem addr v n = some mem') : mem'.size = mem.size := by
  induction n generalizing mem addr v with
  | zero => simp [writeBytes] at h; subst h; rfl
  | succ n ih =>
    simp only [writeBytes] at h
    split at h
    · rw [ih h, Array.size_setIfInBounds]
    · simp at h

/-- A write leaves the bytes outside it alone. -/
theorem writeBytes_frame {k : Nat} {mem mem' : Array (BitVec 8)} {addr n : Nat} {v : BitVec k}
    (h : writeBytes mem addr v n = some mem') (i : Nat) (hi : i < addr ∨ addr + n ≤ i) :
    mem'[i]? = mem[i]? := by
  induction n generalizing mem addr v with
  | zero => simp [writeBytes] at h; subst h; rfl
  | succ n ih =>
    simp only [writeBytes] at h
    split at h
    · rw [ih h (by omega), Array.getElem?_setIfInBounds_ne (by omega)]
    · simp at h

/-- What a write puts in the bytes it writes. -/
theorem writeBytes_written {k : Nat} {mem mem' : Array (BitVec 8)} {addr n : Nat} {v : BitVec k}
    (h : writeBytes mem addr v n = some mem') (j : Nat) (hj : j < n) :
    mem'[addr + j]? = some ((v >>> (8 * j)).setWidth 8) := by
  induction n generalizing mem addr v j with
  | zero => omega
  | succ n ih =>
    simp only [writeBytes] at h
    split at h
    · rename_i ha
      cases j with
      | zero =>
        rw [writeBytes_frame h _ (by omega)]
        simp [ha]
      | succ j =>
        rw [show addr + (j + 1) = addr + 1 + j by omega, ih h j (by omega)]
        rw [← BitVec.shiftRight_add, show 8 + 8 * j = 8 * (j + 1) by omega]
    · simp at h

theorem writeBytes_isSome {k : Nat} {mem : Array (BitVec 8)} {addr n : Nat} (v : BitVec k)
    (h : addr + n ≤ mem.size) : ∃ mem', writeBytes mem addr v n = some mem' := by
  induction n generalizing mem addr v with
  | zero => exact ⟨mem, rfl⟩
  | succ n ih =>
    simp only [writeBytes, show addr < mem.size by omega, ite_true]
    exact ih _ (by simp; omega)

/-! ## Loading -/

/-- The bytes of `words`, laid out from `base` in `mem` as `load` lays them out. -/
def WordsAt (mem : Array (BitVec 8)) (base : Nat) (words : List (BitVec 32)) : Prop :=
  ∀ k (hk : k < words.length), ∀ j < 4,
    mem[base + 4 * k + j]? = some ((words[k] >>> (8 * j)).setWidth 8)

theorem WordsAt.read {mem : Array (BitVec 8)} {base : Nat} {words : List (BitVec 32)}
    (h : WordsAt mem base words) (k : Nat) (hk : k < words.length) :
    readBytes mem (base + 4 * k) 4 = some words[k] :=
  readBytes_four (h k hk)

theorem flatMap_wordBytes_getElem? (words : List (BitVec 32)) (k : Nat) (hk : k < words.length)
    (j : Nat) (hj : j < 4) :
    (words.flatMap wordBytes)[4 * k + j]? = some ((words[k] >>> (8 * j)).setWidth 8) := by
  induction words generalizing k with
  | nil => simp at hk
  | cons x ws ih =>
    have hlen : (wordBytes x).length = 4 := by simp [wordBytes]
    rw [List.flatMap_cons]
    cases k with
    | zero =>
      rw [List.getElem?_append_left (by omega)]
      simp [wordBytes, hj]
    | succ k =>
      rw [List.getElem?_append_right (by omega), hlen,
        show 4 * (k + 1) + j - 4 = 4 * k + j by omega, ih k (by simp at hk; omega)]
      simp

theorem load_wordsAt (w : Nat) (words : List (BitVec 32)) (memSize : Nat) (input : List Char) :
    WordsAt (load w words memSize input).mem 0 words := by
  intro k hk j hj
  have e := flatMap_wordBytes_getElem? words k hk j hj
  simp only [load, Nat.zero_add, List.getElem?_toArray]
  change (words.flatMap wordBytes ++ _)[4 * k + j]? = _
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp e).1]
  exact e

theorem length_flatMap_wordBytes (words : List (BitVec 32)) :
    (words.flatMap wordBytes).length = 4 * words.length := by
  induction words with
  | nil => simp
  | cons x ws ih =>
    simp only [List.flatMap_cons, List.length_append, ih, wordBytes, List.length_map,
      List.length_range, List.length_cons]
    omega

theorem load_size (w : Nat) (words : List (BitVec 32)) (memSize : Nat) (input : List Char)
    (h : 4 * words.length ≤ memSize) : (load w words memSize input).mem.size = memSize := by
  have := length_flatMap_wordBytes words
  change (words.flatMap wordBytes ++ List.replicate (memSize - (words.flatMap wordBytes).length)
    0).toArray.size = memSize
  simp only [List.size_toArray, List.length_append, List.length_replicate]
  omega

end TinyFive
