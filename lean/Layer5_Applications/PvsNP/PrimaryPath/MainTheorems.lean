import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
import Layer5_Applications.PvsNP.PrimaryPath.OWFExistence
import Layer5_Applications.PvsNP.PrimaryPath.UniformPPTEmbedding
import Layer5_Applications.PvsNP.ComplexityClasses.Encoding.BitstringOWF

/-! # Main Theorems: P ≠ NP

This file is the official endpoint of the proof path, collecting all main results.

## Two-Stage Proof Architecture

The proof proceeds in two clean stages:

**Stage 1: Structured Proofs (Layers 0-4)**
Work with abstract type X* (structured overlay instances). Prove:
- L*_struct construction with A1-A5 (Layer1_Construction/)
- A1-A5 → keyedness → SCL bound (Layer1_Construction/Bridge/LStarToNodeData.lean)
- Per-instance deterministic lower bounds (Layer3_InformationBounds/)
- Structural OWF construction (Layer2_StructuralOWF/Security/StructuralOWFExponential.lean)
- NP membership and classical bridge (StructuralOWFBridge.lean)

**Stage 2: Encoding Transfer (LStarEncoding.lean, BitstringOWF.lean)**
Transfer all results to L* ⊆ {0,1}* via:
- Injective encoding: `Encodable.encode_injective`, `PolytimeEncoding`
- Transfer theorems: `np_transfer`, `p_backward_transfer`, `hardness_transfer`
- Bitstring witness: `PrefixLangBits_in_NP_not_in_P`

## Two Equivalent Formulations

**Path 1 (Abstract)**: `P_ne_NP` from StructuralOWFBridge.lean
- Statement: ¬PeqNP_classical
- General type-theoretic formulation (works over any decidable type)

**Path 2 (Bitstring)**: `exists_language_in_NP_not_in_P_clean` from BitstringOWF.lean
- Statement: ∃ L ⊆ {0,1}*, InNP L ∧ ¬InP L
- Matches standard complexity theory (L ⊆ {0,1}*, aligns with paper §10.6)

Both paths share the same axiom dependencies (2 custom axioms).

## Key Theorems

- `Corollary_10_6_6` — NP membership via `np_transfer`
- `Corollary_10_6_7` — Hardness via `hardness_transfer`
- `Corollary_10_6_8` — P ≠ NP (explicit witness)
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

/-! ## Bitstring Transfer Corollaries -/

/-- **NP Membership**: the explicit bitstring witness language is in NP.

    Via `np_transfer` (LStarEncoding.lean) from `PrefixLangSigma_in_NP`. -/
theorem Corollary_10_6_6 : InNP PrefixLangBits := Corollary_10_6_6_NP_Membership

/-- **Hardness**: the explicit bitstring witness language is not in P.

    Via `hardness_transfer` (LStarEncoding.lean) from `PrefixLangSigma_not_in_P`. -/
theorem Corollary_10_6_7 : ¬InP PrefixLangBits := Corollary_10_6_7_Hardness

/-- **P ≠ NP** (explicit bitstring witness).

    Combines NP membership + hardness for explicit witness `PrefixLangBits`. -/
theorem Corollary_10_6_8 : ∃ (L : Lang (List Bool)), InNP L ∧ ¬InP L :=
  Corollary_10_6_8_P_ne_NP

/-! ## Combined Result -/

/-- **P ≠ NP (Both Forms)**: Abstract and bitstring formulations.

    This theorem connects both proof paths, showing they derive from
    the same OWF construction and share the same axiom dependencies. -/
theorem P_ne_NP_complete :
    (¬PeqNP_classical) ∧ (∃ (L : Lang (List Bool)), InNP L ∧ ¬InP L) :=
  ⟨P_ne_NP, explicit_NP_not_P_witness⟩

/-! ## OWF Existence (Cryptographic Form)

This section exports the OWF existence theorem in two forms:

**Form 1 (Family-Quantified)**: `∃ Φ, IsOneWayPlantFlat Φ`
- `SecurityProperty` quantifies over adversary families with poly bounds

**Form 2 (Textbook)**: `∃ Φ prec, TextbookOWFSecurity Φ prec`
- Standard textbook definition: ∀ uniform PPT A, Pr[A inverts] ≤ negl(n)
- `UniformPPTEmbedding.lean` proves `SecurityProperty → TextbookOWFSecurity`

**Trust Boundary**: 1 custom axiom (subset of P≠NP's 2 axioms).
-/

open LStar.StructuralOWF.OWFExistence
open LStar.StructuralOWF.UniformEmbedding

/-- **OWF Existence (Family Form)**: There exists a CNF family with one-way plant_flat.

    Uses family-quantified `SecurityProperty`.
    Uses 1 custom axiom (tm_correctness_implies_realizesAllValuesFrom_flat_encoded). -/
theorem OWF_exists_main : ∃ Φ : LStar.StructuralOWF.Theorems.CNFFamily,
    IsOneWayPlantFlat Φ :=
  OWF_exists

/-- **OWF Existence (Textbook Form)**: There exists Φ with textbook OWF security.

    Standard form: "∃ f, ∀ uniform PPT A, Pr[A inverts f] ≤ negl(n)"
    Proven via `security_implies_textbook` from `UniformPPTEmbedding.lean`. -/
theorem OWF_exists_textbook_main :
    ∃ (Φ : LStar.StructuralOWF.Theorems.CNFFamily) (prec : CNFPreconditions Φ),
      TextbookOWFSecurity Φ prec :=
  OWF_exists_textbook

/-! ## Axiom Audit -/

-- P ≠ NP theorems (2 custom axioms)
#print axioms P_ne_NP
#print axioms explicit_NP_not_P_witness
#print axioms PrefixLangBits_separation
#print axioms Corollary_10_6_6
#print axioms Corollary_10_6_7
#print axioms Corollary_10_6_8
#print axioms P_ne_NP_complete

-- OWF existence (1 custom axiom)
#print axioms OWF_exists_main
#print axioms OWF_exists_textbook_main

end MainTheorems
