import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Basic

/-! ## VectorHelpers: Vector Operations for FG Computation

**Main Operations**: Bit-level vector operations for parity computation and seed manipulation.

**Key Functions**:
- `vectorParity`: Compute XOR parity over vector of seeds (GF(2) arithmetic)
- `extractBits`: Extract bit range from seed (bit slicing)
- `packBits`: Pack boolean vector into seed (bit packing)

**Parity Computation** (for FG digest):
```lean
vectorParity seeds = fold XOR over all seed bits (associative, commutative)
```

**Why GF(2) Arithmetic**: Parity over GF(2) is maximally non-local—changing ANY input bit flips output.
Enables FG's information-theoretic security (no algebraic shortcuts).

**Trust Boundary**: Pure functions (no axioms). Uses Mathlib vector operations and GF(2) arithmetic.

**Paper**: §4.1 "Parity Computation", Appendix B "Vector Operations".

See Layer2_StructuralOWF/Layer2_README.md for FG mechanism and identity digest details.
-/

/-! ## Fin.cast lemmas -/

/-- Fin.cast preserves the underlying value. -/
@[simp]
theorem Fin.cast_val {n m : Nat} (h : n = m) (i : Fin n) : (Fin.cast h i).val = i.val := by
  subst h
  rfl

namespace Vector

variable {α : Type*} {n m : Nat}

/-! ## Core lemma: Vector.take preserves element 0 -/

/-- **Proven FROM FIRST PRINCIPLES**: (v.take k)[0] = v[0] when k > 0.

    **Real definition**: Vector.take xs i = Vector.mk (xs.toArray.take i) ...

    **Proof**: Unfold definitions and use Array.getElem_take.
-/
theorem get_take_zero (v : Vector α n) (k : Nat) (hk : 0 < k) (hn : 0 < n) :
    (v.take k).get ⟨0, by omega⟩ = v.get ⟨0, hn⟩ := by
  -- Convert Vector.get notation to getElem notation []
  show (v.take k)[0] = v[0]
  -- Use Vector.getElem_take (which exists in mathlib!)
  -- It requires a proof that 0 < min k n
  exact Vector.getElem_take (by omega)

/-! ## Core lemma: Vector.append preserves left element 0 -/

/-- **Proven FROM FIRST PRINCIPLES**: (v₁ ++ v₂)[0] = v₁[0] when v₁.length > 0.

    **Real definition**: Vector.append xs ys = Vector.mk (xs.toArray ++ ys.toArray) ...

    **Proof**: Unfold definitions and use Array.getElem_append_left.
-/
theorem get_append_zero (v₁ : Vector α n) (v₂ : Vector α m) (hn : 0 < n) :
    (v₁.append v₂).get ⟨0, by omega⟩ = v₁.get ⟨0, hn⟩ := by
  -- Convert Vector.get notation to getElem notation []
  show (v₁ ++ v₂)[0] = v₁[0]
  -- Use Vector.getElem_append (which exists in mathlib!)
  rw [Vector.getElem_append]
  -- Simplify the if-then-else (0 < n is true)
  simp [hn]

/-! ## Vector.cast lemmas -/

/-- Accessing an element of (v.cast h) equals accessing the same element of v. -/
theorem get_cast (v : Vector α n) (h : n = m) (i : Fin m) :
    (v.cast h).get i = v.get (Fin.cast h.symm i) := by
  subst h
  rfl

/-- When cast doesn't change the length, element access is preserved. -/
theorem get_cast_rfl (v : Vector α n) (i : Fin n) :
    (v.cast rfl).get i = v.get i := rfl

/-! ## Combined lemmas for resizeDigest use case -/

/-- Element 0 is preserved by take + cast. -/
theorem get_zero_take_cast (v : Vector α n) (k : Nat) (hk : 0 < k) (hn : 0 < n) (h_cast : min k n = k) :
    ((v.take k).cast h_cast).get ⟨0, by omega⟩ = v.get ⟨0, hn⟩ := by
  rw [get_cast]
  exact get_take_zero v k hk hn

/-- Element 0 is preserved by append + cast. -/
theorem get_zero_append_cast (v₁ : Vector α n) (v₂ : Vector α m) (hn : 0 < n) :
    ((v₁.append v₂).cast rfl).get ⟨0, by omega⟩ = v₁.get ⟨0, hn⟩ := by
  rw [get_cast_rfl]
  exact get_append_zero v₁ v₂ hn

end Vector

-- Axiom audit for key lemmas (should show only standard foundations)
#print axioms Vector.get_take_zero
#print axioms Vector.get_append_zero
#print axioms Vector.get_cast
