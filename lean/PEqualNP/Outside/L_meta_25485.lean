import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25485 : ∀ (k : Nat) (u v : Fin (2 ^ k)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (r rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (r colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let h := (k + 1) / 2
  let graph : Nat → Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun r row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first r w row.val < 2 ^ (k - h)) && decide (second r w col.val < 2 ^ (k - h)))
  graph 0 u v = true ↔
    ∃ w < 2 ^ k, (rot 1 w ^^^ u.val) < 2 ^ (k - h) ∧ (rot 3 w ^^^ v.val) < 2 ^ (k - h) := by
  intro k u v rot step constant first second h graph
  simp only [graph, first, second, List.range_zero, List.foldl_nil, List.any_eq_true, List.mem_range, Bool.and_eq_true]
  constructor
  · rintro ⟨w, hw, h1, h2⟩; exact ⟨w, hw, of_decide_eq_true h1, of_decide_eq_true h2⟩
  · rintro ⟨w, hw, h1, h2⟩; exact ⟨w, hw, decide_eq_true h1, decide_eq_true h2⟩
