-- Constraint System (world semantics)
import Layer3_InformationBounds.ConstraintSystem.ConstraintSystem
import Layer3_InformationBounds.ConstraintSystem.ConstraintExtraction
import Layer3_InformationBounds.ConstraintSystem.ConfigTypes
import Layer3_InformationBounds.ConstraintSystem.EmergentConfig
import Layer3_InformationBounds.ConstraintSystem.NormalForm

-- WorldCommit (WC-1 elimination)
import Layer3_InformationBounds.WorldCommit.WorldCommit
import Layer3_InformationBounds.WorldCommit.ExecutionHistory
import Layer3_InformationBounds.WorldCommit.CutWorlds
import Layer3_InformationBounds.WorldCommit.CutProduct
import Layer3_InformationBounds.WorldCommit.AppendixJBridge
import Layer3_InformationBounds.WorldCommit.FGPathSetSizing
import Layer3_InformationBounds.WorldCommit.FGIndistinguishability
import Layer3_InformationBounds.WorldCommit.CDT_Lemmas

-- SegmentReduction (main theorem: refutationCount ≥ 2^(ρ-s))
import Layer3_InformationBounds.SegmentReduction.SegmentReduction
import Layer3_InformationBounds.SegmentReduction.SegmentCounting
import Layer3_InformationBounds.SegmentReduction.SegmentBoundaries
import Layer3_InformationBounds.SegmentReduction.SegmentInjection
-- SegmentSequentiality (experimental file, not in active proof chain) requires Mathlib API migration
-- (List.Chain' → List.IsChain, cons → cons_cons, Chain'.tail field notation)
-- import Layer3_InformationBounds.SegmentReduction.SegmentSequentiality
import Layer3_InformationBounds.SegmentReduction.WorkLowerBounds
import Layer3_InformationBounds.SegmentReduction.StructuralLowerBound
import Layer3_InformationBounds.SegmentReduction.CanonicalKeyednessBounds

-- Keyedness (planted instance uniqueness)
import Layer3_InformationBounds.Keyedness.KeyednessFromA2
import Layer3_InformationBounds.Keyedness.KeyednessBounds
import Layer3_InformationBounds.Keyedness.AcceptanceUniqueness
import Layer3_InformationBounds.Keyedness.PlantedInstanceConsistency
import Layer3_InformationBounds.Keyedness.PlantedFGDiversity
import Layer3_InformationBounds.Keyedness.StateConfigCorrespondence
import Layer3_InformationBounds.Keyedness.LaneDefinitions
import Layer3_InformationBounds.Keyedness.NoBackdoorTheorem

-- Randomness (R profiles: Core and Exponential)
import Layer3_InformationBounds.Randomness.RandomnessSpace
import Layer3_InformationBounds.Randomness.RanksCore
import Layer3_InformationBounds.Randomness.RanksExponential

-- Support (infrastructure for information bounds)
import Layer3_InformationBounds.Support.Probability
import Layer3_InformationBounds.Support.ObservationModel
import Layer3_InformationBounds.Support.SeedSemantics
import Layer3_InformationBounds.Support.TimingModel
import Layer3_InformationBounds.Support.SemanticNormalForm
import Layer3_InformationBounds.Support.OperationalModel
import Layer3_InformationBounds.Support.LaneDichotomy
import Layer3_InformationBounds.Support.ExecutionSemanticsAdapter
import Layer3_InformationBounds.Support.ComputationalModel
import Layer3_InformationBounds.Support.FinsetExtraction
import Layer3_InformationBounds.Support.SquareLePowProven

-- Theorems (parametric CNF family properties)
import Layer3_InformationBounds.Theorems.AlignedFamily
import Layer3_InformationBounds.Theorems.Quantitative

-- Decision (L* in NP)
import Layer3_InformationBounds.Decision.LStarNP

/-! # Layer 3: Information Bounds

Exports all Layer 3 modules: Exponential lower bounds via Semantic Conservation Law.
-/
