import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
import Layer5_Applications.PvsNP.ComplexityClasses.Encoding.BitstringOWF

/-! # Main Theorems: P ≠ NP

This file is the official endpoint of the proof path, collecting all main results.

## Two Equivalent Formulations

**Path 1 (Abstract)**: `P_ne_NP` from StructuralOWFBridge.lean
- Statement: ¬PeqNP_classical
- Uses abstract types for L* instances

**Path 2 (Bitstring)**: `exists_language_in_NP_not_in_P_clean` from BitstringOWF.lean
- Statement: ∃ L ⊆ {0,1}*, InNP L ∧ ¬InP L
- Explicit bitstring language (paper §10.6 equivalent)

Both paths share the same axiom dependencies (2 custom axioms).

## Paper §10.6 Correspondence

The bitstring interface mirrors paper §10.6 "Bitstring Interface for L*":
- Corollary 10.6.6 (NP Membership) ↔ `Corollary_10_6_6`
- Corollary 10.6.7 (Hardness) ↔ `Corollary_10_6_7`
- Corollary 10.6.8 (P ≠ NP) ↔ `Corollary_10_6_8`
-/

namespace MainTheorems

open LStar.Complexity
open LStar.Complexity.StructuralOWFBridge
open LStar.Encoding.BitstringOWF

/-! ## Main Results -/

/-- **Main Theorem (Abstract Form)**: P ≠ NP.

    From StructuralOWFBridge.lean via OWF ⇒ FP ≠ FNP ⇒ P ≠ NP bridge. -/
theorem P_ne_NP : ¬PeqNP_classical := pnenp_classical

/-- **Main Theorem (Bitstring Form)**: There exists L ⊆ {0,1}* in NP \ P.

    From BitstringOWF.lean via prefix-language encoding. -/
theorem explicit_NP_not_P_witness : ∃ (L : Lang (List Bool)), InNP L ∧ ¬InP L :=
  exists_language_in_NP_not_in_P_clean

/-- **Named Witness**: PrefixLangBits is in NP and not in P. -/
theorem PrefixLangBits_separation : InNP PrefixLangBits ∧ ¬InP PrefixLangBits :=
  PrefixLangBits_in_NP_not_in_P

/-! ## Paper §10.6 Corollaries -/

/-- **Corollary 10.6.6**: L* ⊆ {0,1}* ∈ NP.

    Paper: NP membership transfers via encoding lemmas E1-E4.
    Lean: Via `np_transfer` from `PrefixLangSigma_in_NP`. -/
theorem Corollary_10_6_6 : InNP PrefixLangBits := Corollary_10_6_6_NP_Membership

/-- **Corollary 10.6.7**: L* ⊆ {0,1}* ∉ P.

    Paper: OWF security implies hardness via coin-fixing.
    Lean: Via `hardness_transfer` from `PrefixLangSigma_not_in_P`. -/
theorem Corollary_10_6_7 : ¬InP PrefixLangBits := Corollary_10_6_7_Hardness

/-- **Corollary 10.6.8**: P ≠ NP (explicit bitstring witness).

    Paper: Classical bridge OWF ⇒ FP ≠ FNP ⇒ P ≠ NP.
    Lean: Explicit witness `PrefixLangBits` with `InNP ∧ ¬InP`. -/
theorem Corollary_10_6_8 : ∃ (L : Lang (List Bool)), InNP L ∧ ¬InP L :=
  Corollary_10_6_8_P_ne_NP

/-! ## Combined Result -/

/-- **P ≠ NP (Both Forms)**: Abstract and bitstring formulations.

    This theorem connects both proof paths, showing they derive from
    the same OWF construction and share the same axiom dependencies. -/
theorem P_ne_NP_complete :
    (¬PeqNP_classical) ∧ (∃ (L : Lang (List Bool)), InNP L ∧ ¬InP L) :=
  ⟨P_ne_NP, explicit_NP_not_P_witness⟩

/-! ## Axiom Audit -/

#print axioms P_ne_NP
#print axioms explicit_NP_not_P_witness
#print axioms PrefixLangBits_separation
#print axioms Corollary_10_6_6
#print axioms Corollary_10_6_7
#print axioms Corollary_10_6_8
#print axioms P_ne_NP_complete

end MainTheorems
