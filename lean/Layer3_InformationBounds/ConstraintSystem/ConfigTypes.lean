import Layer2_StructuralOWF.Plant.PlantCore
import Layer1_Construction.Core.InstanceOps
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic

/-! ## ConfigTypes: Configuration Space Core Types

**Main Definitions**:
- `ConfigSpace L C`: Emergent config assignments at cut C
- `KeyednessProperty L C bound`: Injective mapping configs → states
- `liftKeyedness`: Lift keyedness from smaller to larger bound

**ConfigSpace Structure**:
```lean
ConfigSpace L C = (v : InCut L C) → Fin (2^(L.R v.val))
Cardinality: |ConfigSpace L C| = 2^(Σ_{v∈C} R_v)
```

**Why extracted**: Breaks circular dependencies (WitnessAlgorithm ↔ StateConfigCorrespondence).
Core types imported by both without creating cycles.

**Keyedness**: Injective config→state mapping ensures distinct configurations remain
distinguishable. Crucial for SCL information-theoretic bottleneck.

**Trust Boundary**: Axiom-free (pure type definitions, Fintype instances).

**Paper**: §7.2 "Configuration Space", §6 "Emergent Configurations", Appendix C.1-C.2 "State-Config Correspondence"

See Layer3_InformationBounds/Layer3_README.md for keyedness, configuration spaces, and SCL information bottleneck.
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF

/-- Algorithm state during L* witness-finding. Modeled abstractly as Nat. -/
abbrev AlgorithmState := Nat

/-- Type of nodes in a cut. -/
abbrev InCut (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :=
  {v : Fin L.dag.n // v ∈ C}

/-- Configuration space: Emergent config assignments at a cut.

    **Interpretation**: A configuration assigns a value in Fin (2^(R_v)) to each
    cut node v. This represents one possible "world" that could contain the witness.

    **Paper connection**: Appendix C.2 discusses how FG forces 2^λ such configurations
    at the min-cut, each requiring different seed values.

    **Type**: Dependent function from cut nodes to their value spaces.
    For a cut C with nodes {v₁,...,vₖ}, a config assigns vᵢ ↦ value ∈ Fin (2^(R_vᵢ)).

    **Cardinality**: |ConfigSpace L C| = ∏_{v∈C} 2^(R_v) = 2^(Σ_{v∈C} R_v).
    For singleton cut {v}, this simplifies to 2^(R_v).

    **Example**: At FG gate v with R_v = λ bits, there are 2^λ possible configs. -/
def ConfigSpace (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) : Type :=
  (v : InCut L C) → Fin (2^(L.R v.val))

/-- Finite instance for InCut. -/
noncomputable instance instFinite_InCut (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
  Finite (InCut L C) :=
  Finset.finite_toSet C

/-- Finite instance for ConfigSpace (dependent Pi from Finite to Finite). -/
noncomputable instance instFinite_ConfigSpace (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
  Finite (ConfigSpace L C) := by
  classical
  show Finite ((v : InCut L C) → Fin (2^(L.R v.val)))
  have _ : Finite (InCut L C) := instFinite_InCut L C
  have _ : ∀ v : InCut L C, Finite (Fin (2^(L.R v.val))) := fun _ => inferInstance
  infer_instance

/-- Fintype instance for ConfigSpace. -/
noncomputable instance instFintype_ConfigSpace (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
  Fintype (ConfigSpace L C) :=
  Fintype.ofFinite _

/-! ## Keyedness Property

The keyedness property captures the information-theoretic necessity that different
seed configurations require different algorithm states. This is the formalization
of A2 (injectivity) at the operational level.
-/

/-- Keyedness: Different seed configurations require different algorithm states.

    **Paper justification** (Appendix C.2):
    - Seeds deterministically encode parent information (A4: closure)
    - Different seeds → different parseable content (A2: injectivity)
    - Algorithm must maintain seed-specific state to track which config it's exploring
    - Can't merge configs without resolving their difference (would lose information)

    **Formalization**: We model this as an injective map from configurations to states.
    This captures the idea that each config needs its own state representation.

    **Why injection**: If cfg1 ≠ cfg2 mapped to the same state, the algorithm couldn't
    distinguish them, violating correctness (would give wrong answer on one of them).

    **Example**: In DP, this means different seed configs need different memoization keys.
    In backtracking, different configs correspond to different search tree nodes.

    **Cardinality consequence**: If there are 2^λ configs and the map is injective,
    then there must be ≥ 2^λ distinct states in the image (pigeonhole principle). -/
structure KeyednessProperty (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) (bound : Nat) where
  /-- Map from cut-scoped configurations to bounded algorithm states.

      **Interpretation**: Given a configuration (values on the cut only), what state
      must the algorithm be in to correctly explore that configuration?

      **Example**: In DP, different configs → different memoization keys.
      In backtracking, different configs → different search tree nodes.

      **Domain**: Uses `ConfigSpace L C` = `(v : InCut L C) → Fin (2^(L.R v))`,
      which is the natural "semantic" representation of configurations.

      **Codomain**: Uses `Fin bound` to ensure all mapped states are < bound.
      This eliminates the need for separate boundedness axioms - the bound is
      built into the type. Typically bound = haltTime for TM-based witness finders. -/
  configToState : ConfigSpace L C → Fin bound

  /-- Injectivity: Different configs map to different states.

      **This is the formalization of keyedness**: If you're exploring config1,
      your algorithm state must differ from when you're exploring config2.
      Otherwise you can't maintain the distinction needed for correctness.

      **Information-theoretic content**: Injection from N-element set (configs)
      to Fin bound means the image has N elements. So 2^λ configs → ≥ 2^λ states.

      **Proof simplicity**: Since ConfigSpace only contains cut values, extensional
      equality is straightforward - no out-of-cut complications. -/
  h_injective : Function.Injective configToState

/-- Lift a keyedness function from smaller bound to larger bound.

    **Use case**: When we have keyedness with bound = N but need bound = M where N ≤ M.
    For example, canonicalKeyedness has bound = Fintype.card (ConfigSpace L C),
    but TMAdapter needs bound = haltTime.

    **Preservation**: Maintains injectivity and all semantic properties.
    Only changes the codomain type from Fin N to Fin M. -/
def liftKeyedness {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    {bound1 bound2 : Nat} (h_le : bound1 ≤ bound2)
    (k : KeyednessProperty L C bound1) :
    KeyednessProperty L C bound2 := {
  configToState := fun cfg =>
    ⟨(k.configToState cfg).val,
     Nat.lt_of_lt_of_le (k.configToState cfg).isLt h_le⟩
  h_injective := by
    intro cfg1 cfg2 h_eq
    apply k.h_injective
    apply Fin.ext
    -- h_eq : ⟨(k.configToState cfg1).val, _⟩ = ⟨(k.configToState cfg2).val, _⟩
    -- Need: (k.configToState cfg1).val = (k.configToState cfg2).val
    injection h_eq
}

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms ConfigSpace
#print axioms KeyednessProperty
#print axioms liftKeyedness

end LStar.StructuralOWF.Foundations
