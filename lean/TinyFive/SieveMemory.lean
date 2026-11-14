import TinyFive.Machine

/-!
# Memory lemmas for an in-place byte sieve

These lemmas concern the actual arrays, byte loads/stores and instruction fetch of
`TinyFive.Machine`. Code occupies a protected prefix; sieve flags can be updated
above that prefix without changing instruction fetch. No connection to an external
emulator or assembler is assumed or asserted here.
-/
namespace TinyFive.SieveMemory

/-- Agreement with a reference code image on a protected prefix. -/
def Prefix (image mem : Array (BitVec 8)) (boundary : Nat) : Prop :=
  ∀ i, i < boundary → mem[i]? = image[i]?

/-- Fixed memory capacity together with preservation of the code prefix. -/
structure Layout (image : Array (BitVec 8)) (boundary capacity : Nat)
    (mem : Array (BitVec 8)) : Prop where
  size_eq : mem.size = capacity
  code_eq : Prefix image mem boundary

@[simp] theorem prefix_refl (image : Array (BitVec 8)) (boundary : Nat) :
    Prefix image image boundary := fun _ _ => rfl

theorem Prefix.mono {image mem : Array (BitVec 8)} {small large : Nat}
    (h : Prefix image mem large) (hle : small ≤ large) : Prefix image mem small :=
  fun i hi => h i (by omega)

/-- An in-bounds byte store is exactly an array point update. -/
theorem writeBytes_byte {k : Nat} (mem : Array (BitVec 8)) (addr : Nat)
    (v : BitVec k) (h : addr < mem.size) :
    writeBytes mem addr v 1 = some (mem.setIfInBounds addr (v.setWidth 8)) := by
  simp [writeBytes, h]

/-- A byte load returns the byte itself, rather than a differently sized encoding. -/
@[simp] theorem readBytes_byte (mem : Array (BitVec 8)) (addr : Nat) :
    readBytes mem addr 1 = mem[addr]? := by
  simp only [readBytes]
  cases mem[addr]? with
  | none => rfl
  | some v =>
    change some (0#0 ++ v) = some v
    rw [BitVec.zero_width_append]
    rfl

/-- Point updates preserve capacity, including out-of-bounds no-op updates. -/
@[simp] theorem size_update (mem : Array (BitVec 8)) (addr : Nat) (v : BitVec 8) :
    (mem.setIfInBounds addr v).size = mem.size := Array.size_setIfInBounds

@[simp] theorem read_update_same (mem : Array (BitVec 8)) (addr : Nat)
    (v : BitVec 8) (h : addr < mem.size) :
    readBytes (mem.setIfInBounds addr v) addr 1 = some v := by
  simp [Array.getElem?_setIfInBounds_self_of_lt h]

@[simp] theorem read_update_other (mem : Array (BitVec 8)) (addr query : Nat)
    (v : BitVec 8) (h : addr ≠ query) :
    readBytes (mem.setIfInBounds addr v) query 1 = readBytes mem query 1 := by
  simp [Array.getElem?_setIfInBounds_ne h]

/-- A flag store changes exactly the addressed flag. -/
theorem read_update (mem : Array (BitVec 8)) (addr query : Nat) (v : BitVec 8)
    (h : addr < mem.size) :
    readBytes (mem.setIfInBounds addr v) query 1 =
      if addr = query then some v else readBytes mem query 1 := by
  by_cases he : addr = query
  · subst query
    simp [h]
  · simp [he]

/-- Reads depend only on the bytes in their requested interval. -/
theorem readBytes_congr (mem₁ mem₂ : Array (BitVec 8)) (addr n : Nat)
    (h : ∀ i, addr ≤ i → i < addr + n → mem₁[i]? = mem₂[i]?) :
    readBytes mem₁ addr n = readBytes mem₂ addr n := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    simp only [readBytes, h addr (by omega) (by omega)]
    rw [ih (addr + 1) (by
      intro i hlo hhi
      exact h i (by omega) (by omega))]

/-- A byte update outside an interval cannot affect a read of that interval. -/
theorem readBytes_update_disjoint (mem : Array (BitVec 8)) (addr n store : Nat)
    (v : BitVec 8) (h : store < addr ∨ addr + n ≤ store) :
    readBytes (mem.setIfInBounds store v) addr n = readBytes mem addr n := by
  apply readBytes_congr
  intro i hlo hhi
  apply Array.getElem?_setIfInBounds_ne
  omega

/-- Agreement on the code prefix suffices to preserve a complete instruction fetch. -/
theorem readBytes_prefix {image mem : Array (BitVec 8)} {boundary : Nat}
    (h : Prefix image mem boundary) (addr n : Nat) (hfit : addr + n ≤ boundary) :
    readBytes mem addr n = readBytes image addr n := by
  apply readBytes_congr
  intro i _ hhi
  exact h i (by omega)

/-- Stores at or above the boundary preserve the code-prefix invariant. -/
theorem prefix_update {image mem : Array (BitVec 8)} {boundary : Nat}
    (h : Prefix image mem boundary) (addr : Nat) (v : BitVec 8)
    (haddr : boundary ≤ addr) :
    Prefix image (mem.setIfInBounds addr v) boundary := by
  intro i hi
  rw [Array.getElem?_setIfInBounds_ne (by omega)]
  exact h i hi

/-- The complete memory invariant is stable under a data-byte update. -/
theorem Layout.update {image mem : Array (BitVec 8)} {boundary capacity : Nat}
    (h : Layout image boundary capacity mem) (addr : Nat) (v : BitVec 8)
    (haddr : boundary ≤ addr) :
    Layout image boundary capacity (mem.setIfInBounds addr v) :=
  ⟨by simpa using h.size_eq, prefix_update h.code_eq addr v haddr⟩

/-- A successful data-byte store preserves both memory capacity and all code bytes. -/
theorem Layout.write_byte {image mem : Array (BitVec 8)} {boundary capacity : Nat}
    (h : Layout image boundary capacity mem) (addr : Nat) {k : Nat} (v : BitVec k)
    (hlo : boundary ≤ addr) (hhi : addr < capacity) :
    writeBytes mem addr v 1 = some (mem.setIfInBounds addr (v.setWidth 8)) ∧
      Layout image boundary capacity (mem.setIfInBounds addr (v.setWidth 8)) := by
  exact ⟨writeBytes_byte mem addr v (by rw [h.size_eq]; exact hhi),
    h.update addr _ hlo⟩

/-- Decode the unchanged instruction in a machine whose data memory has evolved. -/
theorem step_of_prefix {w : Nat} (m : Machine w) (image : Array (BitVec 8))
    (boundary : Nat) (h : Prefix image m.mem boundary)
    (hfit : m.pc.toNat + 4 ≤ boundary) (i : Instr)
    (hfetch : (readBytes image m.pc.toNat 4).bind (decode w) = some i) :
    step m = exec i m := by
  simp only [step, readBytes_prefix h _ _ hfit, hfetch]

/-- The exact byte encoding used by `TinyFive.load`. -/
def programBytes (words : List (BitVec 32)) : List (BitVec 8) :=
  words.flatMap fun (x : BitVec 32) => (List.range 4).map fun k => (x >>> (8 * k)).setWidth 8

@[simp] theorem programBytes_length (words : List (BitVec 32)) :
    (programBytes words).length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons x xs ih =>
    simp only [programBytes, List.flatMap_cons, List.length_append,
      List.length_map, List.length_range] at *
    simp only [List.length_cons]
    omega

theorem load_mem_eq (w : Nat) (words : List (BitVec 32)) (capacity : Nat)
    (input : List Char) :
    (load w words capacity input).mem =
      (programBytes words ++ List.replicate (capacity - 4 * words.length) 0).toArray := by
  change (programBytes words ++
    List.replicate (capacity - (programBytes words).length) 0).toArray = _
  rw [programBytes_length]

/-- Loading a fitting program allocates precisely the requested capacity. -/
theorem load_mem_size (w : Nat) (words : List (BitVec 32)) (capacity : Nat)
    (input : List Char) (h : 4 * words.length ≤ capacity) :
    (load w words capacity input).mem.size = capacity := by
  rw [load_mem_eq]
  simp only [List.size_toArray, List.length_append, programBytes_length,
    List.length_replicate]
  omega

/-- The instruction bytes of a loaded image are independent of memory capacity. -/
theorem load_mem_code (w : Nat) (words : List (BitVec 32)) (capacity : Nat)
    (input : List Char) (i : Nat) (hi : i < 4 * words.length) :
    (load w words capacity input).mem[i]? = (programBytes words)[i]? := by
  rw [load_mem_eq, List.getElem?_toArray, List.getElem?_append_left]
  simpa only [programBytes_length] using hi

/-- Every allocated byte after the program starts at zero. -/
theorem load_mem_zero (w : Nat) (words : List (BitVec 32)) (capacity : Nat)
    (input : List Char) (i : Nat) (hlo : 4 * words.length ≤ i)
    (hhi : i < capacity) :
    (load w words capacity input).mem[i]? = some 0 := by
  rw [load_mem_eq, List.getElem?_toArray, List.getElem?_append_right]
  · simp only [programBytes_length]
    apply List.getElem?_replicate_of_lt
    omega
  · simpa only [programBytes_length] using hlo

/-- Increasing a fitting image's capacity preserves its whole original prefix. -/
theorem load_prefix (w : Nat) (words : List (BitVec 32)) (small large : Nat)
    (input₁ input₂ : List Char) (_hcode : 4 * words.length ≤ small)
    (hle : small ≤ large) :
    Prefix (load w words small input₁).mem (load w words large input₂).mem small := by
  intro i hi
  by_cases hc : i < 4 * words.length
  · rw [load_mem_code w words large input₂ i hc, load_mem_code w words small input₁ i hc]
  · rw [load_mem_zero w words large input₂ i (by omega) (by omega),
      load_mem_zero w words small input₁ i (by omega) hi]

/-- A larger freshly loaded image satisfies the fixed-capacity/code-prefix invariant. -/
theorem load_layout (w : Nat) (words : List (BitVec 32)) (small large : Nat)
    (input₁ input₂ : List Char) (hcode : 4 * words.length ≤ small)
    (hle : small ≤ large) :
    Layout (load w words small input₁).mem small large (load w words large input₂).mem :=
  ⟨load_mem_size w words large input₂ (by omega),
    load_prefix w words small large input₁ input₂ hcode hle⟩

/-- A code boundary may be smaller than the padded reference image. -/
theorem load_layout_boundary (w : Nat) (words : List (BitVec 32))
    (boundary small large : Nat) (input₁ input₂ : List Char)
    (hcode : 4 * words.length ≤ small) (hboundary : boundary ≤ small)
    (hle : small ≤ large) :
    Layout (load w words small input₁).mem boundary large
      (load w words large input₂).mem :=
  ⟨load_mem_size w words large input₂ (by omega),
    (load_prefix w words small large input₁ input₂ hcode hle).mono hboundary⟩

end TinyFive.SieveMemory
