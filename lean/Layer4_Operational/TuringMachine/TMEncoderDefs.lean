import Layer4_Operational.TuringMachine.TuringMachineSemantics  -- LocalEncoder, TuringMachine, TMConfig
import Layer3_InformationBounds.Keyedness.PlantedInstanceConsistency  -- emergentConfigAtGate
import Layer2_StructuralOWF.Plant.PlantCore  -- WellFormedRandomness (also brings Randomness, Witness types)
import Layer2_StructuralOWF.Plant.PlantExponential  -- plant_flat
import Layer2_StructuralOWF.FrontierGate.FrontierGate  -- LStarInstanceFG

/-! ## TMEncoderDefs: TM Configuration Encoders (0 axioms)

**Purpose**: TM-specific encoding functions (output extraction, emergent config encoding).

**Key definitions**:
- tmOutputWitness: Extract witness from final TM configuration
- tmEmergentEncoder: Map TM configs → emergent values (for planted instances)
- Planted instance extractors: planted_φ, planted_r, planted_n

**Circular dependency resolution**: Extracted from TMAdapter.lean to allow both TMToExecutionPrefix and TMAdapter to import encoders without circular dependencies.

**Trust boundary**: 0 axioms (pure definitions, noncomputable extractors via Classical.choose)

See Layer4_Operational/Layer4_README.md §TuringMachine/TMEncoderDefs.
-/

namespace LStar.StructuralOWF.Foundations

open Classical

variable {k : Nat} {states alphabet : Type}
variable [Fintype states] [DecidableEq states]
variable [Fintype alphabet] [DecidableEq alphabet]
variable (L : LStarInstanceFG)

/-! ## Planted Instance Extractors

For hypothesis `h : ∃ n φ r h_nvars h_aligned, L = plant_flat n φ r h_nvars h_aligned ∧ WellFormedRandomness φ r`,
we provide extractors to get n, φ, r, and the equality.

These use Classical.choose to extract witnesses noncomputably.
-/

/-- Planted instance hypothesis type alias for cleaner signatures. -/
abbrev PlantedHyp (L : LStarInstanceFG) :=
  ∃ (n : Nat) (φ : CNF) (r : Randomness φ.nvars) (h_nvars : φ.nvars ≥ 4)
    (h_aligned : AlignedCNFConstraints φ),
    L = plant_flat n φ r h_nvars h_aligned ∧ WellFormedRandomness φ r

/-- Extract φ from planted instance hypothesis (noncomputable).

    **Extraction path**:
    - h : ∃ n φ r h_nvars h_aligned, L = plant_flat n φ r h_nvars h_aligned ∧ WellFormedRandomness φ r
    - This is syntactic sugar for: ∃ n, (∃ φ, (∃ r, ...))
    - First choose: Classical.choose h extracts n
    - Classical.choose_spec h : ∃ φ r, L = plant_flat n φ r ... ∧ ...
    - Second choose: Classical.choose (Classical.choose_spec h) extracts φ -/
noncomputable def planted_φ {L : LStarInstanceFG} (h : PlantedHyp L) : CNF :=
  Classical.choose (Classical.choose_spec h)

/-- Extract r from planted instance hypothesis (noncomputable). -/
noncomputable def planted_r {L : LStarInstanceFG} (h : PlantedHyp L) : Randomness (planted_φ h).nvars :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec h))

/-- Extract n from planted instance hypothesis (noncomputable). -/
noncomputable def planted_n {L : LStarInstanceFG} (h : PlantedHyp L) : Nat :=
  Classical.choose h

/-- Extract h_nvars from planted instance hypothesis. -/
noncomputable def planted_h_nvars {L : LStarInstanceFG} (h : PlantedHyp L) : (planted_φ h).nvars ≥ 4 :=
  let spec1 := Classical.choose_spec h
  let spec2 := Classical.choose_spec spec1
  let spec3 := Classical.choose_spec spec2
  Classical.choose spec3

/-- Extract h_aligned from planted instance hypothesis. -/
noncomputable def planted_h_aligned {L : LStarInstanceFG} (h : PlantedHyp L) :
    AlignedCNFConstraints (planted_φ h) :=
  let spec1 := Classical.choose_spec h
  let spec2 := Classical.choose_spec spec1
  let spec3 := Classical.choose_spec spec2
  let spec4 := Classical.choose_spec spec3
  Classical.choose spec4

/-- Extract L = plant_flat equality from planted instance hypothesis. -/
lemma planted_L_eq {L : LStarInstanceFG} (h : PlantedHyp L) :
    L = plant_flat (planted_n h) (planted_φ h) (planted_r h) (planted_h_nvars h) (planted_h_aligned h) :=
  let spec1 := Classical.choose_spec h
  let spec2 := Classical.choose_spec spec1
  let spec3 := Classical.choose_spec spec2
  let spec4 := Classical.choose_spec spec3
  let spec5 := Classical.choose_spec spec4
  spec5.1

/-! ## TM Output Witness

Extracts witness from final TM configuration.
-/

/-- Extract witness from final TM configuration.

    **Design**: Runs TM to haltTime and applies extractWitness to final config.

    **Usage**: Used by SegmentSequentiality.lean and TMAdapter.lean. -/
noncomputable def tmOutputWitness {nvars : Nat}
    (M : TuringMachine k states alphabet)
    (haltTime : Nat)
    (extractWitness : TMConfig M → Witness nvars) : Witness nvars :=
  let finalCfg := TMConfig.run M haltTime
  extractWitness finalCfg

/-! ## TM Emergent Encoder

Maps TM configurations to emergent configuration values for planted instances.
-/

/-- **LOCAL ENCODER**: Extract emergent configuration value from TM state.

    For planted instances, the emergent config at gate v is determined by the
    assignment. We define an encoder that extracts this value from the TM's
    current configuration (via extractWitness).

    **Design**: Maps TMConfig → emergent value (Nat) by:
    1. Apply extractWitness to get current assignment hypothesis
    2. Compute emergent config value for that assignment
    3. Return as Nat (in range 0..2^R_v-1)

    **Instance-specific**: Requires extractWitness parameter (caller provides). -/
noncomputable def tmEmergentEncoder {nvars : Nat}
    (M : TuringMachine k states alphabet)
    (v : {v // L.fg.gateReq v})
    (extractWitness : TMConfig M → Witness nvars)
    (h_planted : PlantedHyp L) :
    LocalEncoder M L v :=
  { encode := fun cfg =>
      -- Extract assignment from current config (convert to infinite for emergentConfigAtGate)
      let assignmentInf := (extractWitness cfg).assignmentInf

      -- For planted instances, compute emergent config using the pure function
      let φ := planted_φ h_planted
      let r := planted_r h_planted

      -- Derive h_pos from planted instance
      have h_pos : φ.nvars > 0 := by
        have spec1 := Classical.choose_spec h_planted
        have spec2 := Classical.choose_spec spec1
        obtain ⟨r', h_nvars, _, _⟩ := spec2
        unfold φ planted_φ
        omega

      -- Number of gates = r.gateDigests.length
      let numGates := r.gateDigests.length

      -- Convert absolute vertex index to gate-relative index
      let clause_start := 1 + φ.nvars
      let gateIndex := v.val - clause_start

      -- Call the pure emergent config function
      match emergentConfigAtGate φ h_pos numGates assignmentInf gateIndex with
      | some ⟨R_v, cfg⟩ => cfg.val
      | none => 0  -- Fallback (should never happen for valid gates)
  }

-- Axiom Audits: Trust Boundary Transparency
#print axioms planted_φ
#print axioms planted_r
#print axioms planted_n
#print axioms planted_h_nvars
#print axioms planted_h_dgLen
#print axioms tmOutputWitness
#print axioms tmEmergentEncoder

end LStar.StructuralOWF.Foundations
