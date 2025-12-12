import Layer0_Foundations.Base.CNF
import Layer3_InformationBounds.Support.SeedSemantics
import Layer3_InformationBounds.ConstraintSystem.EmergentConfig
import Layer1_Construction.Core.LStarInstance
import Layer1_Construction.Core.MultiLevelDAG
import Layer2_StructuralOWF.Plant.PlantCore


open LStar
open LStar.StructuralOWF

set_option linter.unusedSimpArgs false

/-! ## Helper Lemmas for OWFBridge -/

/-- **Helper Lemma**: computeSeedAtVertex is extensional in the assignment parameter.

If two assignments agree on all indices < nvars, then computeSeedAtVertex
produces the same result for both.
-/
lemma computeSeedAtVertex_ext
    (φ : CNF)
    (h_nvars_pos : φ.nvars > 0)
    (numGates : Nat)
    (a1 a2 : LStar.AssignmentInf)
    (h_agree : ∀ i < φ.nvars, a1 i = a2 i)
    (v : Fin (LStar.StructuralOWF.Foundations.lstarStructureFromCNF φ h_nvars_pos numGates).dag.n) :
    LStar.StructuralOWF.Foundations.computeSeedAtVertex φ h_nvars_pos numGates a1 v =
    LStar.StructuralOWF.Foundations.computeSeedAtVertex φ h_nvars_pos numGates a2 v := by
  -- PROOF SKETCH (complete structural argument, needs ~50 lines of detailed Lean):
  --
  -- This is a standard extensionality lemma provable by well-founded induction on DAG structure.
  --
  -- **Base case** (source nodes, L.dag.parents v = ∅):
  --   computeSeedAtVertex builds seed from Vector.ofFn (fun j => a ((v.val + j.val) % φ.nvars))
  --   All accessed indices (v.val + j.val) % φ.nvars are < φ.nvars (by Nat.mod_lt)
  --   Therefore: a1 i = a2 i for all accessed i (by h_agree)
  --   Therefore: Vector.ofFn with a1 = Vector.ofFn with a2 (by funext)
  --   Therefore: seeds match (by vectorToFin congruence)
  --
  -- **Inductive case** (internal nodes, L.dag.parents v ≠ ∅):
  --   computeSeedAtVertex builds parentHistory: fun u => computeSeedAtVertex φ ... a u.val
  --   For each parent u ∈ L.dag.parents v:
  --     - u.val < v.val (by L.dag.parents_have_smaller_indices, termination proof)
  --     - By IH: computeSeedAtVertex φ ... a1 u.val = computeSeedAtVertex φ ... a2 u.val
  --   Therefore: parentHistory with a1 = parentHistory with a2 (by funext on parents)
  --   Therefore: packParents gives same result (by parentHistory equality)
  --   Therefore: emergence application gives same result (by packParents equality)
  --   Therefore: encodeSeed gives same result (by all component equality)
  --
  -- **Termination**: Uses same well-founded relation as computeSeedAtVertex
  --   (Subrelation.wf (parents_have_smaller_indices φ h_nvars_pos numGates))
  --
  -- **Complete proof**: Requires ~50 lines with explicit:
  --   - Well-founded recursion setup (termination_by v.val, decreasing_by)
  --   - Source case: Vector.ext + List.get_ofFn + h_agree
  --   - Internal case: funext on ParentHistory + IH application + congruence chain
  --
  -- This is a straightforward but tedious structural induction.
  -- The mathematical content is trivial (assignment equality propagates through construction).
  -- Lean formalization requires careful handling of dependent types and termination.

  -- Proof strategy: Use Nat.strong_rec on v.val (matching computeSeedAtVertex's termination metric)
  let L := LStar.StructuralOWF.Foundations.lstarStructureFromCNF φ h_nvars_pos numGates

  -- Define the property we want to prove for all vertices
  suffices ∀ (n : Nat) (v : Fin L.dag.n) (hv : v.val = n),
    LStar.StructuralOWF.Foundations.computeSeedAtVertex φ h_nvars_pos numGates a1 v =
    LStar.StructuralOWF.Foundations.computeSeedAtVertex φ h_nvars_pos numGates a2 v by
    exact this v.val v rfl

  -- Prove by strong induction on n
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv

    -- Case split on whether v is a source vertex
    by_cases h_source : L.dag.parents v = ∅
    case pos =>
      -- Source vertex: seed built directly from assignment bits
      -- All accessed indices: (v.val + j) % φ.nvars are < φ.nvars
      -- Since a1 and a2 agree on all indices < φ.nvars (by h_agree), results are equal

      rw [LStar.StructuralOWF.Foundations.computeSeedAtVertex, LStar.StructuralOWF.Foundations.computeSeedAtVertex]
      simp only [h_source, ↓reduceIte]

      -- Show the ofBits constructions are equal
      -- Key: vectorToFin (Vector.ofFn (fun j => a1 ...)) = vectorToFin (Vector.ofFn (fun j => a2 ...))
      -- because the vectors are equal (by h_agree)
      have h_vec_eq : ∀ (R : Nat), Vector.ofFn (fun j : Fin R => a1 ((v.val + j.val) % φ.nvars)) =
                                     Vector.ofFn (fun j : Fin R => a2 ((v.val + j.val) % φ.nvars)) := by
        intro R
        apply Vector.ext
        intro j
        -- j : Nat (with implicit bound j < R)
        simp [Vector.get_ofFn]
        intro h_j_bound
        have h_idx : (v.val + j) % φ.nvars < φ.nvars := Nat.mod_lt _ h_nvars_pos
        exact h_agree _ h_idx

      -- Now need to split the if-then-else first
      split
      next =>
        -- Source case: apply ofBits_ext
        apply LStar.ofBits_ext
        intro i
        split <;> try rfl
        next h_lt =>
          -- Goal: decide (... vectorToFin ... a1 ... ) = decide (... vectorToFin ... a2 ...)
          -- Show the vectorToFin results are equal, rest follows by congruence
          rw [h_vec_eq]
      next =>
        -- Non-source case: contradiction with h_source
        contradiction

    case neg =>
      -- Non-source vertex: seed built from parent seeds recursively
      rw [LStar.StructuralOWF.Foundations.computeSeedAtVertex, LStar.StructuralOWF.Foundations.computeSeedAtVertex]

      -- Use split to handle the if-then-else
      split
      next h_is_source =>
        -- Contradiction: we have h_source : ¬L.dag.parents v = ∅
        -- but h_is_source says L.dag.parents v = ∅
        contradiction
      next h_is_nonsource =>
        -- This is the else branch (non-source), which builds encodeSeed from parentHistory
        -- The key observation: both sides differ only in the assignment used in parentHistory
        -- Everything else (packed, dummy_input, emergent_seed, emergent_bits, encodeSeed)
        -- is determined by parentHistory

        -- Strategy: Show that the two parentHistory functions are equal
        -- parentHistory_a1 := fun u => computeSeedAtVertex φ ... a1 u
        -- parentHistory_a2 := fun u => computeSeedAtVertex φ ... a2 u

        -- Extract and show equality of the parentHistory parts
        have h_parentHistory_eq : (fun u : {u // u ∈ L.dag.parents v} =>
            LStar.StructuralOWF.Foundations.computeSeedAtVertex φ h_nvars_pos numGates a1 u.val) =
          (fun u : {u // u ∈ L.dag.parents v} =>
            LStar.StructuralOWF.Foundations.computeSeedAtVertex φ h_nvars_pos numGates a2 u.val) := by
          funext u
          -- u is a parent: u.val < v.val (by parents_have_smaller_indices)
          have h_smaller : u.val.val < v.val :=
            Construction.parents_have_smaller_indices φ numGates v u.val u.property
          -- Apply IH to parent u
          exact ih u.val.val (by rw [← hv]; exact h_smaller) u.val rfl

        -- Now use congruence: since parentHistory functions are equal,
        -- all derived values (packed, emergent_seed, etc.) are equal
        -- and therefore the final encodeSeed results are equal
        rw [h_parentHistory_eq]
    
/-- **Helper Lemma**: emergentConfigAtGate is extensional in the assignment parameter. -/
theorem emergentConfig_assignment_extension
    (φ : CNF)
    (h_nvars_pos : φ.nvars > 0)
    (numGates : Nat)
    (a_sat : LStar.AssignmentInf)
    (r_assignment : LStar.AssignmentInf)
    (h_extend : ∀ i < φ.nvars, r_assignment i = a_sat i)
    (gate_idx : Nat) :
    LStar.StructuralOWF.Foundations.emergentConfigAtGate φ h_nvars_pos numGates r_assignment gate_idx =
    LStar.StructuralOWF.Foundations.emergentConfigAtGate φ h_nvars_pos numGates a_sat gate_idx := by
  dsimp [LStar.StructuralOWF.Foundations.emergentConfigAtGate]
  split
  next h_gate =>
    split
    next h_vertex =>
      split
      next h_cap =>
        -- Case: All conditions true
        -- Result is some ⟨R_v, cfg⟩
        -- We need to show the content is equal
        congr 1
        congr 1
        congr 1
        congr 1
        apply computeSeedAtVertex_ext
        exact h_extend
      next => rfl
    next => rfl
  next => rfl

/-- **Helper Lemma**: resizeDigestGeneral respects transport of the digest vector.

    If we have a digest vector `v` of length `len`, and we transport it to length `len'`
    (where `len = len'`), the resized digest is the same.
-/
theorem resizeDigestGeneral_transport_eq
    (target_len len len' : Nat)
    (v : Vector Bool len)
    (h_len : len = len') :
    LStar.StructuralOWF.resizeDigestGeneral target_len len' (h_len ▸ v) =
    LStar.StructuralOWF.resizeDigestGeneral target_len len v := by
  subst h_len
  rfl
