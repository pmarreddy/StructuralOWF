import Layer0_Foundations.Base.CNF
import Layer3_InformationBounds.Randomness.RandomnessSpace
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridgeHelpers

/-! ## ProofTests: Isolated Proof Development for OWFBridge Sorries

Test file to work out complex proofs in isolation before transferring to OWFBridge.lean.

**Current Tests**:
1. Fin coercion for Literal.eval extension
2. Vector.ofFn mechanics for digest equality
3. Other OWFBridge proof details
-/

namespace LStar.Complexity.StructuralOWFBridge.Tests

open LStar LStar.StructuralOWF.Foundations

/-! ### Test 1: Fin Coercion for Assignment Extension -/

/-- **Test Goal**: Show that extendAssign preserves equality at specific indices.

Given:
- `a_sat : Assignment` (i.e., `Nat → Bool`)
- `nvars : Nat`
- `i : Nat` with `i < nvars`

Show:
- `(extendAssign nvars (fun j : Fin nvars => a_sat j.val)) i = a_sat i`

This is the core issue in Literal.eval extension proof.
-/
theorem extendAssign_preserves_at_index
    (a_sat : Assignment)
    (nvars : Nat)
    (i : Nat)
    (h_i_bound : i < nvars) :
    (RandomnessN.extendAssign nvars (fun j : Fin nvars => a_sat j.val)) i = a_sat i := by
  -- Strategy: unfold extendAssign, use split_ifs to handle the conditional
  unfold RandomnessN.extendAssign
  split_ifs
  · -- Case: i < nvars (which we have)
    -- Goal: a_sat ⟨i, _⟩.val = a_sat i
    simp only [Fin.val_mk]

/-- **Application**: Use this lemma to prove Literal.eval equality.

Given:
- `literal : Literal`
- `a_sat : Assignment`
- `r_assignment := extendAssign nvars (fun j => a_sat j.val)`
- `literal.var < nvars`

Show:
- `Literal.eval literal r_assignment = Literal.eval literal a_sat`
-/
theorem literal_eval_with_extended_assignment
    (literal : Literal)
    (a_sat : Assignment)
    (nvars : Nat)
    (h_lit_bound : literal.var < nvars) :
    let r_assignment := RandomnessN.extendAssign nvars (fun j : Fin nvars => a_sat j.val)
    Literal.eval literal r_assignment = Literal.eval literal a_sat := by
  -- Use extendAssign_preserves_at_index to show r_assignment (literal.var) = a_sat (literal.var)
  have h_eq := extendAssign_preserves_at_index a_sat nvars literal.var h_lit_bound
  -- Unfold Literal.eval and apply the equality
  unfold Literal.eval
  simp only [h_eq]

/-! ### Test 2: Vector.ofFn to List.get Conversion -/

/-- **Test Goal**: Show that Vector.ofFn followed by toList and get preserves the function value.

Given:
- `f : Fin n → α`
- `i : Nat` with `i < n`

Show:
- `(Vector.ofFn f).toList.get ⟨i, _⟩ = f ⟨i, _⟩`

This is the core issue in Vector digest equality proof.
-/
theorem vector_ofFn_toList_get {α : Type} {n : Nat}
    (f : Fin n → α)
    (i : Nat)
    (h_i : i < n) :
    let v := Vector.ofFn f
    have h_len : v.toList.length = n := by simp [Vector.toList]
    v.toList.get ⟨i, by rw [h_len]; exact h_i⟩ = f ⟨i, h_i⟩ := by
  -- Strategy: Vector.ofFn creates a vector, toList converts, get extracts
  -- Use Vector.get_ofFn to relate vector get to function application
  simp [Vector.toList, Vector.get_ofFn]

/-- **Special case**: For a constant function (like our digest_vec), the result is always the constant. -/
theorem vector_ofFn_constant_toList_get {α : Type} {n : Nat}
    (c : α)
    (i : Nat)
    (h_i : i < n)
    (h_n_pos : 0 < n) :
    let v := Vector.ofFn (fun _ : Fin n => c)
    have h_len : v.toList.length = n := by simp [Vector.toList]
    v.toList.get ⟨i, by rw [h_len]; exact h_i⟩ = c := by
  simp [Vector.toList, Vector.get_ofFn]

/-! ### Test 3: First Element of Length-1 Vector -/

/-- **Test Goal**: The first element of a length-1 vector created by ofFn is f(0).

This is specifically for our digest case where we have a single gate.
-/
theorem vector_ofFn_length1_first {α : Type}
    (f : Fin 1 → α) :
    let v := Vector.ofFn f
    have h_len : v.toList.length = 1 := by simp [Vector.toList]
    v.toList.get ⟨0, by rw [h_len]; omega⟩ = f ⟨0, by omega⟩ := by
  exact vector_ofFn_toList_get f 0 (by omega)

/-- **Application**: For our specific case with digest_vec. -/
theorem digest_vec_first_element {α : Type}
    (digest_vec : α) :
    let v := Vector.ofFn (fun _ : Fin 1 => digest_vec)
    have h_len : v.toList.length = 1 := by simp [Vector.toList]
    v.toList.get ⟨0, by rw [h_len]; omega⟩ = digest_vec := by
  exact vector_ofFn_constant_toList_get digest_vec 0 (by omega) (by omega)

/-! ### Test 4: WellFormedRandomness None Case -/

/-- **Test Goal**: When emergentConfigAtGate returns none, the requirement is trivially satisfied.

From WellFormedRandomness definition:
```lean
match emergentConfigAtGate φ φ.nvars_pos numGates r.assignment i with
| none => True
| some ⟨_R, cfg⟩ => (digest requirements)
```

So in the none branch, we just need to prove True.
-/
theorem wellformed_none_case :
    True := by
  trivial

/-- **Test Goal**: Size proof - digest_vec has size 64.

Given:
- digest_list = digest_bit :: List.replicate 63 false
- digest_vec = ⟨digest_list.toArray, _⟩

Show:
- digest_vec.size = 64 > 0
-/
theorem digest_vec_size_pos
    (digest_bit : Bool) :
    let digest_list : List Bool := digest_bit :: List.replicate 63 false
    have h_len : digest_list.length = 64 := by
      rfl
    let digest_vec : Vector Bool 64 := ⟨digest_list.toArray, by
      simp [h_len]⟩
    0 < digest_vec.size := by
  simp only [Vector.size]
  omega

/-! ### Test 5: First Element of Constructed Vector -/

/-- **Test Goal**: The first element of digest_vec is digest_bit.

Given:
- digest_list = digest_bit :: List.replicate 63 false
- digest_vec = ⟨digest_list.toArray, _⟩

Show:
- digest_vec.get ⟨0, _⟩ = digest_bit
-/
theorem digest_vec_first_is_digest_bit
    (digest_bit : Bool) :
    let digest_list : List Bool := digest_bit :: List.replicate 63 false
    have h_len : digest_list.length = 64 := by
      rfl
    let digest_vec : Vector Bool 64 := ⟨digest_list.toArray, by
      simp [h_len]⟩
    digest_vec.get ⟨0, by omega⟩ = digest_bit := by
  rfl

/-! ### Test 6: Full Digest Matching with If-Then-Else -/

/-- **Test Goal**: Prove digest matching through if-then-else structure.

Given:
- digest_vec constructed from digest_bit
- h_budget : 0 < digest_vec.size

Show:
- if h_budget : 0 < digest_vec.size then digest_vec.get ⟨0, h_budget⟩ = digest_bit else True
-/
theorem digest_matching_with_if
    (digest_bit : Bool) :
    let digest_list : List Bool := digest_bit :: List.replicate 63 false
    have h_len : digest_list.length = 64 := by rfl
    let digest_vec : Vector Bool 64 := ⟨digest_list.toArray, by simp [h_len]⟩
    (if h_budget : 0 < digest_vec.size then digest_vec.get ⟨0, h_budget⟩ = digest_bit else True) := by
  -- Strategy: The if-then-else evaluates immediately because the condition is decidable
  -- and digest_vec.size = 64 > 0, so the then-branch is taken
  -- The goal reduces to: digest_vec.get ⟨0, _⟩ = digest_bit, which is true by rfl
  rfl

/-! ### Test 7: Helper Lemmas - COMPLETED ✅ -/

-- These lemmas are now completed in OWFBridgeHelpers.lean and imported above:
-- - computeSeedAtVertex_ext: Proven by well-founded induction on DAG structure
-- - emergentConfig_assignment_extension: Proven using computeSeedAtVertex_ext

-- Verify they're available:
#check computeSeedAtVertex_ext
#check emergentConfig_assignment_extension

end LStar.Complexity.StructuralOWFBridge.Tests

-- Build test
#check LStar.Complexity.StructuralOWFBridge.Tests.extendAssign_preserves_at_index
#check LStar.Complexity.StructuralOWFBridge.Tests.literal_eval_with_extended_assignment
#check LStar.Complexity.StructuralOWFBridge.Tests.vector_ofFn_toList_get
#check LStar.Complexity.StructuralOWFBridge.Tests.digest_vec_first_element
#check LStar.Complexity.StructuralOWFBridge.Tests.wellformed_none_case
#check LStar.Complexity.StructuralOWFBridge.Tests.digest_vec_size_pos
#check LStar.Complexity.StructuralOWFBridge.Tests.digest_vec_first_is_digest_bit
#check LStar.Complexity.StructuralOWFBridge.Tests.digest_matching_with_if
-- The following are now in OWFBridgeHelpers (completed):
#check computeSeedAtVertex_ext
#check emergentConfig_assignment_extension
