import Mathlib.Data.List.Basic

/-! ## ListHelpers: Helper lemmas for list operations (0 axioms)

**Purpose**: Provide helper lemmas for list operations on concatenated lists,
particularly for working with prefix/suffix patterns in BitEncoding.

**Key Lemmas**:
- getLast? on lists ending with two-element suffix
- head? on lists starting with prefix
- Extracting middle section via tail and dropLast operations

**Trust Boundary**: 0 axioms (pure lemmas from Mathlib.Data.List)
-/

namespace LStar.Complexity.ListHelpers

/-- getLast? of a list concatenated with a two-element suffix returns the last element -/
lemma List.getLast?_append_two {α : Type} (l : List α) (a b : α) :
    (l ++ [a, b]).getLast? = some b := by
  cases l with
  | nil => simp [List.getLast?]
  | cons hd tl =>
    rw [List.getLast?_append]; simp [List.getLast?]

/-- After removing last element, getLast? returns the second-to-last element -/
lemma List.getLast?_dropLast_append_two {α : Type} (l : List α) (a b : α) :
    (l ++ [a, b]).dropLast.getLast? = some a := by
  have h1 : (l ++ [a, b]).dropLast = l ++ [a] := by
    simp [List.dropLast_append_of_ne_nil]
  rw [h1]
  cases l with
  | nil => simp [List.getLast?]
  | cons hd tl =>
    rw [List.getLast?_append]; simp [List.getLast?]

/-- Extracting body from [pre] ++ body ++ [s1, s2] -/
lemma List.tail_dropLast_dropLast_extract {α : Type} (pre : α) (body : List α) (s1 s2 : α) :
    ([pre] ++ body ++ [s1, s2]).tail.dropLast.dropLast = body := by
  have h1 : ([pre] ++ body ++ [s1, s2]).tail = body ++ [s1, s2] := by simp
  rw [h1]
  have h2 : (body ++ [s1, s2]).dropLast = body ++ [s1] := by
    simp [List.dropLast_append_of_ne_nil]
  rw [h2]
  simp [List.dropLast_append_of_ne_nil]

/-- head? of list with cons and append -/
lemma List.head?_cons_append {α : Type} (a : α) (l1 l2 : List α) :
    (a :: (l1 ++ l2)).head? = some a := by simp

/-- If list ends with [a, b], it's non-empty -/
lemma List.ne_nil_of_append_two {α : Type} (l : List α) (a b : α) :
    l ++ [a, b] ≠ [] := by simp

/-- Length of list with two-element suffix -/
lemma List.length_append_two {α : Type} (l : List α) (a b : α) :
    (l ++ [a, b]).length = l.length + 2 := by simp


end LStar.Complexity.ListHelpers
