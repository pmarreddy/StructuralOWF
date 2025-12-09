import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge

/-! ## CheckAxioms: Axiom Audit for Main Theorems

This file prints the axiom dependencies of key theorems in OWFBridge.lean
for trust boundary verification.
-/

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
