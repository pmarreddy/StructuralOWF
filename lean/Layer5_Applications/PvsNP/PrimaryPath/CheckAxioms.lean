import Layer5_Applications.PvsNP.PrimaryPath.MainTheorems

/-! ## CheckAxioms: Axiom Audit for Main Theorems

This file prints the axiom dependencies of key theorems for trust boundary verification.

**Main Entry Point**: `MainTheorems.lean` collects all results.

**Two proof paths to P ≠ NP:**
1. `P_ne_NP` (StructuralOWFBridge.lean): Abstract type formulation
2. `exists_language_in_NP_not_in_P_clean` (BitstringOWF.lean): Explicit L ⊆ {0,1}*

Both paths share the same axiom dependencies.
-/

/-! ### Path 1: Abstract P ≠ NP (StructuralOWFBridge.lean) -/

-- Helper lemmas
#print axioms LStar.Complexity.StructuralOWFBridge.randomness_encoding_plant_equiv

-- FP ≠ FNP from OWF
#print axioms LStar.Complexity.StructuralOWFBridge.structural_owf_implies_fpnefnp

-- P ≠ NP (parametric version)
#print axioms LStar.Complexity.StructuralOWFBridge.pnenp

-- P ≠ NP (classical version)
#print axioms LStar.Complexity.StructuralOWFBridge.pnenp_classical

-- Main theorem: P ≠ NP
#print axioms LStar.Complexity.StructuralOWFBridge.P_ne_NP

/-! ### Path 2: Bitstring Interface (BitstringOWF.lean) — Paper §10.6 Equivalent

These theorems provide the explicit bitstring witness, mirroring paper §10.6:
- `PrefixLangBits_in_NP` ↔ Corollary 10.6.6 (NP membership)
- `PrefixLangBits_not_in_P` ↔ Corollary 10.6.7 (hardness via OWF)
- `exists_language_in_NP_not_in_P_clean` ↔ Corollary 10.6.8 (P ≠ NP)
-/

-- NP membership transfers (Corollary 10.6.6)
#print axioms LStar.Encoding.BitstringOWF.PrefixLangBits_in_NP

-- Hardness transfers via OWF (Corollary 10.6.7)
#print axioms LStar.Encoding.BitstringOWF.PrefixLangBits_not_in_P

-- Combined: explicit NP \ P witness
#print axioms LStar.Encoding.BitstringOWF.PrefixLangBits_in_NP_not_in_P

-- Main bitstring theorem: ∃ L ⊆ {0,1}*, L ∈ NP ∧ L ∉ P (Corollary 10.6.8)
#print axioms LStar.Encoding.BitstringOWF.exists_language_in_NP_not_in_P_clean

/-! ### Main Entry Point (MainTheorems.lean)

These are the official combined results, re-exported from MainTheorems.lean.
-/

-- Main theorem (abstract form)
#print axioms MainTheorems.P_ne_NP

-- Main theorem (explicit bitstring witness)
#print axioms MainTheorems.explicit_NP_not_P_witness

-- Paper §10.6 Corollaries
#print axioms MainTheorems.Corollary_10_6_6
#print axioms MainTheorems.Corollary_10_6_7
#print axioms MainTheorems.Corollary_10_6_8

-- Combined result (both forms)
#print axioms MainTheorems.P_ne_NP_complete
