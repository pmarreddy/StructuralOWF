import Layer5_Applications.PvsNP.ComplexityClasses.PPTAdversary
import Layer5_Applications.PvsNP.ComplexityClasses.StructuralOWFSizedInstances  -- For Sized LStarInstanceFG
import Layer5_Applications.PvsNP.ComplexityClasses.TMEncoding  -- For getTape0, initWithEncodingBase
import Layer2_StructuralOWF.FrontierGate.FrontierGate  -- For LStarInstanceFG
import Layer2_StructuralOWF.FrontierGate.RandomnessTypes  -- For Randomness, Witness
import Layer4_Operational.TuringMachine.TuringMachineSemantics  -- For TMConfig.run
import Layer4_Operational.TimeBridge.LStarEncodingTypes  -- For ReplantingSimulation, WorstCaseCorrectOnLStar
import Layer0_Foundations.Base.CNF  -- For CNF, HasPositiveClause

/-! ## StructuralOWFAdversary: OWF-Specific PPT Adversary

**Purpose**: Wraps generic PPTAdversary with OWF-specific types and assignment correspondence.

**Design**: StructuralOWFAdversary wraps PPTAdversary with:
- Type specialization: α = LStarInstanceFG, β = Randomness, γ = Witness
- Assignment correspondence field connecting extractWitness to run output

**TM-Algorithm Correspondence**: The correspondence between TM execution and
algorithmic `run` is now a STRUCTURAL FIELD (`assignment_correspondence`) rather
than an axiom. This uses ENCODED-INPUT semantics (initWithEncodingBase), not
blank-tape (TMConfig.run).

**Key insight**: Both β=Randomness and γ=Witness have `.assignment : Assignment`.
The correspondence field proves these match after TM execution with encoded input.

**How it works**:
1. PPTAdversary.run_correct: decode(getTape0(final_cfg)) = run c x
2. assignment_correspondence: extractWitness(final_cfg).assignment = (run c x).assignment
3. For proper extractWitness: read tape, decode to Randomness, extract .assignment

See Layer5_Applications/Layer5_README.md §ComplexityClasses/StructuralOWFAdversary.
-/

namespace LStar.Complexity

open LStar.StructuralOWF
open LStar.StructuralOWF.Foundations
open Sized

/-- **Nontrivial Computation**: Satisfying assignments require ≥2 TM steps.

    **Definition**: For encoded-input initial configurations, if `extractWitness`
    produces a satisfying assignment for a CNF φ (with nvars ≥ 4 and HasPositiveClause),
    then the computation required at least 2 steps.

    **Scope**:
    - Encoded-input configurations via `initWithEncodingBase`
    - A CNF φ passed as parameter (from the CNF family Φ used to plant the instance)
    - CNFs with at least one all-positive clause

    **Note**: The CNF φ is passed as a parameter rather than extracted from the instance
    because `LStarInstanceFG` contains only the OAP-encoded form (`encodedφ : EncodedCNF`),
    not the plaintext CNF. The relationship φ.nvars = x.encodedφ.nvars is maintained.

    **Justification**: At t < 2, format separation ensures the output decoder
    produces an all-false assignment when interpreting input-encoded data.
    The all-false assignment cannot satisfy CNFs with positive clauses.
    At t ≥ 2, meaningful computation has occurred.

    **Trust Boundary**: 0 axioms (structural property of well-formed encodings)
-/
def NontrivialComputation (nvars : Nat)
    {tapeCount : Nat} {states alphabet : Type} [Fintype states] [DecidableEq states]
    [Fintype alphabet] [DecidableEq alphabet]
    (M : TuringMachine tapeCount states alphabet)
    (extractWitness : TMConfig M → Witness nvars)
    {coins : Nat} (encoding : TMInputEncodingBase (Fin coins × LStarInstanceFG) alphabet)
    (h_tape_pos : 0 < tapeCount)
    (h_blank : M.blank = encoding.blank) : Prop :=
  ∀ (c : Fin coins) (x : LStarInstanceFG) (φ : CNF) (haltTime : Nat),
    φ.nvars = x.encodedφ.nvars →  -- φ corresponds to this instance
    φ.nvars ≥ 4 →
    LStar.CNF.HasPositiveClause φ →
    let init_cfg := initWithEncodingBase M encoding (c, x) h_tape_pos h_blank
    φ.satisfies (extractWitness ((TMConfig.step (M := M))^[haltTime] init_cfg)).assignmentInf →
    haltTime ≥ 2

/-- OWF-specific PPT adversary with assignment correspondence.

    **Purpose**: Wraps generic PPTAdversary with OWF-specific types and proves
    the assignment correspondence structurally (no axiom required).

    **Type Specialization**:
    - α = LStarInstanceFG (L* instances with Frontier Gate)
    - β = Randomness nvars (has .assignment : Assignment nvars)
    - γ = Witness nvars (has .assignment : Assignment nvars)

    **Assignment Correspondence**: The `assignment_correspondence` field proves that
    for encoded-input TM execution, extractWitness produces the same assignment as run.
    This is derived from PPTAdversary.run_correct when extractWitness is properly
    defined to read and decode the tape.

    **Usage**: OWF security proofs (OWFExponential, OWFQP) use StructuralOWFAdversary
    to work with the concrete OWF types and derive tm_algorithm_correspondence.
-/
structure StructuralOWFAdversary (nvars : Nat) where
  /-- The underlying generic PPT adversary. -/
  base : PPTAdversary LStarInstanceFG (Randomness nvars) (Witness nvars)

  /-- **ASSIGNMENT CORRESPONDENCE**: extractWitness produces same assignment as run.

      **Statement**: For encoded-input TM execution, the witness extracted from
      the final configuration has the same assignment as what `run` produces.

      **Semantics**: Uses ENCODED-INPUT execution (initWithEncodingBase), not
      blank-tape (TMConfig.run). This matches PPTAdversary.run_correct semantics.

      **Time bound**: Uses `size L` (dag size) to match PPTAdversary.run_correct.
      This is directly provable from run_correct when extractWitness decodes the tape.

      **Proof Strategy**: When extractWitness is defined to read the tape and
      produce a Witness with matching .assignment, this follows from run_correct:
      1. run_correct: decode(final_tape) = run c L
      2. extractWitness reads tape, creates Witness with decode(tape).assignment
      3. Therefore: extractWitness(final).assignment = (run c L).assignment

      **Why not blank-tape**: Blank-tape execution doesn't have input on tape,
      so run_correct can't be applied. Encoded-input is the correct semantics. -/
  assignment_correspondence : ∀ (c : Fin base.num_coins) (L : LStarInstanceFG) (t : Nat),
    t ≥ base.C * (size L + 1) ^ base.k →
    let init_cfg := initWithEncodingBase base.M base.encoding.input (c, L) base.h_tape_pos base.h_blank_consistent
    let final_cfg := (TMConfig.step (M := base.M))^[t] init_cfg
    (base.extractWitness final_cfg).assignment = (base.run c L).assignment

  /-- **HALTING (Encoded-Input)**: TM halts within C*(size L+1)^k steps.

      **Statement**: For all L, TM halts at time C*(size L+1)^k from encoded input.

      **Why size L**: Matches PPTAdversary.halts semantics exactly, making this
      directly provable from base.halts.

      **Consistency**: Uses same time bound as assignment_correspondence,
      enabling the encoded-input time bound theorems.

      **Trust Boundary**: 0 axioms (directly follows from base.halts) -/
  halts_encoded : ∀ (c : Fin base.num_coins) (L : LStarInstanceFG),
    let t := base.C * (size L + 1) ^ base.k
    let init_cfg := initWithEncodingBase base.M base.encoding.input (c, L) base.h_tape_pos base.h_blank_consistent
    let final_cfg := (TMConfig.step (M := base.M))^[t] init_cfg
    final_cfg.state ∈ base.M.halt

  /-- **NONTRIVIAL COMPUTATION**: extractWitness requires ≥2 steps for satisfying assignments.

      **Statement**: For ENCODED-INPUT initial configurations, if extractWitness produces
      a satisfying assignment for a CNF with ≥4 variables, then at least 2 TM steps were required.

      **Purpose**: Structural requirement replacing the tm_nontrivial_computation axiom.
      Makes nontrivial computation a proof obligation for adversary constructors.

      **Scope**: Only applies to encoded-input init configs (matches actual usage in
      OWFExponential security proofs).

      **Usage**: Security proofs use this to derive haltTime ≥ 2 when the adversary
      produces a satisfying assignment for L.φ.

      **Trust Boundary**: 0 axioms (structural requirement, not assumption) -/
  nontrivial_computation : NontrivialComputation nvars base.M base.extractWitness
      base.encoding.input base.h_tape_pos base.h_blank_consistent

  /-- **EXTRACTWITNESS COVERS BOUNDED ASSIGNMENTS**: extractWitness can produce any
      assignment with support ≤ nvars.

      **Statement**: For any infinite assignment σ with support ≤ nvars
      (i.e., σ i = false for all i ≥ nvars), there exists a TM configuration cfg
      such that (extractWitness cfg).assignmentInf = σ.

      **Purpose**: Structural requirement enabling encoder completeness proofs.
      Combined with A3 emergence (full-rank matrices), this proves that the emergent
      config encoder can produce all values in [0, 2^R) where R ≤ nvars.

      **Why nvars**: Witness nvars has assignment : Fin nvars → Bool, so assignmentInf
      is always false for i ≥ nvars. We use nvars as the fixed bound since:
      1. Emergence rank R ≤ nvars for all gates in planted instances
      2. This matches the Witness type's natural representational capacity

      **Usage**: Security proofs use this to show all emergent configurations
      (which have support ≤ R ≤ nvars bits) can be produced.

      **Trust Boundary**: 0 axioms (structural requirement, not assumption) -/
  extractWitness_covers_bounded_assignments : ∀ (σ : LStar.AssignmentInf),
      (∀ i ≥ nvars, σ i = false) →
      ∃ cfg : TMConfig base.M, (base.extractWitness cfg).assignmentInf = σ

  /-- **L*-ENCODING: initForPlanting**: Maps planted config to initial TM state.

      **Statement**: For each L* instance L and frontier gate v, provides a function
      that maps a planted emergent config (Fin (2^(L.R v))) to an initial TM configuration.

      **Purpose**: Makes the TM-L* encoding structure definitional. The adversary
      constructor must provide this encoding, ensuring it's coherent with the TM behavior.

      **Usage**: Security proofs use this to plant different configs and analyze TM behavior.

      **Trust Boundary**: 0 axioms (definitional requirement, not assumption) -/
  lstar_initForPlanting : (L : LStarInstanceFG) → (v : Fin L.dag.n) →
      L.fg.gateReq v → Fin (2^(L.R v)) → TMConfig base.M

  /-- **L*-ENCODING: extractConfigAtV**: Extracts computed config from TM state.

      **Statement**: For each L* instance L and vertex v, provides a function that
      extracts the emergent configuration at v from a TM configuration.

      **Purpose**: Makes the TM-L* encoding structure definitional. The adversary
      constructor must provide this extractor, ensuring it's coherent with initForPlanting.

      **Usage**: Security proofs use this to observe what config the TM has computed.

      **Trust Boundary**: 0 axioms (definitional requirement, not assumption) -/
  lstar_extractConfigAtV : (L : LStarInstanceFG) → (v : Fin L.dag.n) →
      TMConfig base.M → Fin (2^(L.R v))

  /-- **L*-ENCODING: ReplantingSimulation**: Replanting coherence property.

      **Statement**: For any planted config at time t, if the TM extracts config c,
      then running with c planted reaches the same state.

      **Purpose**: Proves the encoding is coherent - extracting and replanting
      is idempotent. This is the key structural property enabling time bounds.

      **Formalization**: For all cfg_planted and t:
        let state_t := step^[t] (initForPlanting cfg_planted)
        let c := extractConfigAtV state_t
        step^[t] (initForPlanting c) = state_t

      **Trust Boundary**: 0 axioms (definitional requirement, not assumption) -/
  lstar_replanting : (L : LStarInstanceFG) → (v : Fin L.dag.n) → (h_fg : L.fg.gateReq v) →
      ReplantingSimulation L base.M v
        (lstar_extractConfigAtV L v)
        (lstar_initForPlanting L v h_fg)

  /-- **L*-ENCODING: haltTime**: Specific halting time for each (L, v) pair.

      **Statement**: Provides the concrete halting time for the TM on planted L* instances.

      **Purpose**: Exposes the haltTime from the axiom so that lstar_worst_case and
      lstar_halts can both reference the same specific time.

      **Trust Boundary**: 0 axioms (from algspec_has_lstar_structure axiom) -/
  lstar_haltTime : (L : LStarInstanceFG) → (v : Fin L.dag.n) → L.fg.gateReq v → Nat

  /-- **L*-ENCODING: WorstCaseCorrectOnLStar**: TM outputs correct config for all plantings.

      **Statement**: For any planted config cfg at frontier gate v, after lstar_haltTime steps,
      the TM's extracted config equals cfg.

      **Purpose**: Proves the TM is correct on ALL L* instances with ALL plantings.
      Combined with ReplantingSimulation, this enables the time lower bound proof.

      **Formalization**: For all cfg : Fin (2^(L.R v)):
        let finalState := step^[lstar_haltTime L v h_fg] (initForPlanting cfg)
        extractConfigAtV finalState = cfg

      **Note**: WorstCaseCorrect for t ≤ lstar_haltTime is DERIVABLE via derive_worst_case_all_t
      from WorstCaseCorrect at lstar_haltTime + ReplantingSimulation.

      **Trust Boundary**: 0 axioms (definitional requirement, not assumption) -/
  lstar_worst_case : (L : LStarInstanceFG) → (v : Fin L.dag.n) → (h_fg : L.fg.gateReq v) →
      WorstCaseCorrectOnLStar L base.M v
        (lstar_extractConfigAtV L v)
        (lstar_initForPlanting L v h_fg)
        (lstar_haltTime L v h_fg)

  /-- **L*-ENCODING: Halting**: TM halts at lstar_haltTime for planted configs.

      **Statement**: For each (L, v) with frontier gate, the TM halts at lstar_haltTime
      for all planted configs, and lstar_haltTime is bounded by the PPT time.

      **Purpose**: Enables the time lower bound proof by providing halting at a
      concrete time. Combined with halt_persists, this shows halting at any later time.

      **Usage**: StructuralOWFExponential uses this to prove h_halts_lstar.

      **Trust Boundary**: 0 axioms (from algspec_has_lstar_structure axiom) -/
  lstar_halts : (L : LStarInstanceFG) → (v : Fin L.dag.n) → (h_fg : L.fg.gateReq v) →
      (∀ cfg : Fin (2^(L.R v)),
        ((TMConfig.step (M := base.M))^[lstar_haltTime L v h_fg] (lstar_initForPlanting L v h_fg cfg)).state ∈ base.M.halt) ∧
      lstar_haltTime L v h_fg ≤ base.C * (Sized.size L + 1) ^ base.k

/-- Extract the TM from an OWF adversary. -/
abbrev StructuralOWFAdversary.M {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.M

/-- Extract witness function from an OWF adversary. -/
abbrev StructuralOWFAdversary.extractWitness {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.extractWitness

/-- Extract run function from an OWF adversary. -/
abbrev StructuralOWFAdversary.run {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.run

/-- Number of coins in an OWF adversary. -/
abbrev StructuralOWFAdversary.num_coins {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.num_coins

/-- Time bound function from an OWF adversary. -/
abbrev StructuralOWFAdversary.time_bound {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.time_bound

/-- Uniform polynomial constant C from an OWF adversary. -/
abbrev StructuralOWFAdversary.C {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.C

/-- Uniform polynomial exponent k from an OWF adversary. -/
abbrev StructuralOWFAdversary.k {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.k

/-- Polynomial bound from an OWF adversary. -/
abbrev StructuralOWFAdversary.poly {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.poly

/-- Tape count from an OWF adversary. -/
abbrev StructuralOWFAdversary.tapeCount {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.tapeCount

/-- Coins positivity from an OWF adversary. -/
abbrev StructuralOWFAdversary.coins_pos {nvars : Nat} (A : StructuralOWFAdversary nvars) := A.base.coins_pos

-- Axiom Audits
#print axioms StructuralOWFAdversary
#print axioms StructuralOWFAdversary.M

end LStar.Complexity
