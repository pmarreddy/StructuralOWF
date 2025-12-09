import Layer1_Construction.Core.InstanceOps
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer0_Foundations.Base.FiniteEncoding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic

/-! ## ObservationModel: FG Gate Observation Tracking

**Purpose**: Lightweight model tracking which emergent bit positions a computation observes at FG gate vertex.

**Design philosophy** (§6, Appendix C):
- Local, not global: Scoped to single FG gate
- Minimal interface: Just enough to prove FG indistinguishability
- No WitnessFinder changes: Layer sits between FG structure and correctness

**Key insight**: FG digest = parity over emergent bits → computing parity correctly requires reading ALL bits (decision tree complexity) → correct witness finding at FG gate requires complete observation → must visit all 2^{R_v} states.

**Usage**: Observation structure tracks observed positions → prove isComplete → conclude all configs visited.

**Main definitions**: Observation (structure), isIncomplete/isComplete (predicates), configs_agree_on_obs (agreement)

**References**: FrontierGate.lean (FG structure), StructuralLowerBound.lean (parity requires all bits), FGIndistinguishability.lean (uses this)

**Trust boundary**: 0 axioms, 0 sorries - pure definitions

See Layer3_InformationBounds/Layer3_README.md §Support Infrastructure.
-/

namespace LStar.StructuralOWF.Foundations

open LStar

/-! ## Core Observation Structure -/

/-- Record of which emergent bit positions were observed at a gate vertex.

    **Interpretation**: `obs.read_positions` contains indices `i` where the
    computation read bit `i` of the emergent slice at node `v`.

    **Why emergent slice**: FG digest is specifically wired into emergent bits
    (the last `R_v` bits of the seed, which come from the emergence matrix).

    **Scope**: Local to a single FG gate. Each gate has its own observation record.

    **Example**: If algorithm reads bits 0, 2, 5 at gate v with R_v = 8:
    ```
    obs.read_positions = {0, 2, 5}  -- Finset (Fin 8)
    ```

    **Connection to seeds**: These positions correspond to bits in the emergent
    component of the seed at node v. See SeedChain.lean for seed structure. -/
structure Observation (L : LStarInstanceFull) (v : Fin L.dag.n) where
  /-- Set of emergent bit positions that were observed/read.

      **Type**: `Finset (Fin (L.R v))` - subset of emergent positions.

      **Invariant**: Elements are valid emergent indices (0 ≤ i < R_v).
      This is enforced by the Fin type. -/
  read_positions : Finset (Fin (L.R v))
  deriving DecidableEq

/-! ## Completeness Predicates -/

/-- An observation is complete if all emergent positions were observed.

    **Definition**: `card = R_v` means every position was read.

    **Interpretation**: The computation has "looked at" every bit of the
    emergent information at this gate. By FG design, this means it can
    correctly compute the digest (which is parity over these bits).

    **Example**: For R_v = 8, complete means read_positions = {0,1,2,3,4,5,6,7}.

    **Usage**: Correctness of FG witness finding will require complete observation. -/
def Observation.isComplete {L : LStarInstanceFull} {v : Fin L.dag.n}
    (obs : Observation L v) : Prop :=
  obs.read_positions.card = L.R v

/-- An observation is incomplete if some emergent positions weren't read.

    **Definition**: `card < R_v` means at least one position was skipped.

    **Key property**: Incomplete observation → cannot correctly compute FG digest
    for all possible inputs (by parity lower bound, Stage 2).

    **Example**: For R_v = 8, if read_positions = {0,1,5}, then incomplete
    (missing positions 2,3,4,6,7).

    **Usage**: FG indistinguishability theorem assumes incomplete observation
    to derive contradictory configs. -/
def Observation.isIncomplete {L : LStarInstanceFull} {v : Fin L.dag.n}
    (obs : Observation L v) : Prop :=
  obs.read_positions.card < L.R v

/-- Helper: Completeness and incompleteness are mutually exclusive and exhaustive. -/
lemma observation_complete_or_incomplete {L : LStarInstanceFull} {v : Fin L.dag.n}
    (obs : Observation L v) :
    obs.isComplete ∨ obs.isIncomplete := by
  unfold Observation.isComplete Observation.isIncomplete
  -- Either card = R_v (complete) or card < R_v (incomplete)
  have h_le : obs.read_positions.card ≤ L.R v := by
    calc obs.read_positions.card
        ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = L.R v := Finset.card_fin _
  cases Nat.lt_or_eq_of_le h_le with
  | inl h => right; exact h
  | inr h => left; exact h

/-! ## Configuration Agreement -/

/-- Extract bit i from configuration (treating config as bit vector).

    **Encoding**: Config is natural number, bits extracted via division/mod.

    **Example**: For cfg = 13 = 0b1101:
    - bit 0 = 1 (least significant)
    - bit 1 = 0
    - bit 2 = 1
    - bit 3 = 1 (most significant)

    **Implementation**: `(cfg / 2^i) % 2` extracts bit at position i. -/
def getBit (cfg : Nat) (i : Nat) : Nat :=
  (cfg / 2^i) % 2

/-- Two configurations agree on observed positions if they have identical
    bit values at all observed indices.

    **Interpretation**: From the computation's perspective (seeing only
    `obs.read_positions`), cfg1 and cfg2 are indistinguishable - they produce
    the same sequence of observed bits.

    **Information-theoretic foundation**: Uses exact bit equality (getBit = getBit),
    corresponding to Hartley entropy (zero-error regime). This models deterministic
    binary observations, not probabilistic or partial information. Each observed
    position reveals exactly 1 bit of information.

    **Example**:
    - cfg1 = 0b10110, cfg2 = 0b10010
    - obs.read_positions = {1, 2, 4}
    - Bits at observed positions:
      - Position 1: cfg1 has 1, cfg2 has 1 ✓
      - Position 2: cfg1 has 1, cfg2 has 0 ✗
    - Result: NOT indistinguishable (differ at position 2)

    **Key property**: If algorithm only reads observed positions, it cannot
    distinguish cfg1 from cfg2 when they agree on those positions.

    **This is the formal definition of "indistinguishable from observation"!** -/
def Observation.configsAgree {L : LStarInstanceFull} {v : Fin L.dag.n}
    (obs : Observation L v)
    (cfg1 cfg2 : Fin (2^(L.R v))) : Prop :=
  ∀ (i : Fin (L.R v)), i ∈ obs.read_positions →
    getBit cfg1.val i.val = getBit cfg2.val i.val

/-! ## Helper Lemmas -/

/-- If observation is complete, read_positions covers all emergent indices. -/
lemma complete_observation_covers_all {L : LStarInstanceFull} {v : Fin L.dag.n}
    (obs : Observation L v)
    (h_complete : obs.isComplete) :
    ∀ (i : Fin (L.R v)), i ∈ obs.read_positions := by
  unfold Observation.isComplete at h_complete
  intro i
  -- Since card = R_v and elements are in Fin (R_v), must contain all
  by_contra h_not
  -- If i ∉ read_positions, then card < R_v (contradicts h_complete)
  have h_univ : Finset.univ.card = L.R v := Finset.card_fin _
  have h_subset : obs.read_positions ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · exact Finset.subset_univ _
    · intro h_eq
      -- If obs.read_positions = Finset.univ, then i ∈ obs.read_positions
      have : i ∈ obs.read_positions := h_eq ▸ Finset.mem_univ i
      exact h_not this
  have h_lt : obs.read_positions.card < L.R v := by
    calc obs.read_positions.card
        < (@Finset.univ (Fin (L.R v)) _).card := Finset.card_lt_card h_subset
      _ = L.R v := h_univ
  -- h_complete says card = R_v, but h_lt says card < R_v
  rw [h_complete] at h_lt
  exact Nat.lt_irrefl _ h_lt

/-- If two configs agree on all positions, they're identical. -/
lemma configs_agree_on_all_positions_are_equal
    {L : LStarInstanceFull} {v : Fin L.dag.n}
    (cfg1 cfg2 : Fin (2^(L.R v)))
    (h_agree : ∀ (i : Fin (L.R v)), getBit cfg1.val i.val = getBit cfg2.val i.val) :
    cfg1 = cfg2 := by
  -- Reduce to equality of seeds via bit extensionality
  -- Use the extensionality from finite encodings: equality iff all bits equal
  -- Convert `Nat`-valued bits to Boolean testBit via the bridge lemma
  -- Then apply `LStar.Seed.ext`.
  -- Treat cfg1,cfg2 as `Seed (L.R v)` (definally equal to `Fin (2^(L.R v))`).
  -- Strengthen the hypothesis to a Nat-indexed version for recursion
  have h_all : ∀ i : Nat, i < L.R v → getBit cfg1.val i = getBit cfg2.val i := by
    intro i hi; exact h_agree ⟨i, hi⟩
  -- Prove by induction on n = L.R v that two numbers < 2^n are determined by their bits < n
  have rec_eq : ∀ n a b, a < 2^n → b < 2^n → (∀ i < n, getBit a i = getBit b i) → a = b := by
    intro n; induction n with
    | zero =>
        intro a b ha hb _
        have ha0 : a = 0 := Nat.le_antisymm (Nat.le_of_lt_succ (by simpa [Nat.pow_zero] using ha)) (Nat.zero_le _)
        have hb0 : b = 0 := Nat.le_antisymm (Nat.le_of_lt_succ (by simpa [Nat.pow_zero] using hb)) (Nat.zero_le _)
        simp [ha0, hb0]
    | succ n ih =>
        intro a b ha hb hbits
        -- Compare LSBs
        have h_lsb : a % 2 = b % 2 := by
          -- i = 0
          have := hbits 0 (Nat.succ_pos _)
          simpa [getBit] using this
        -- Compare higher bits by dividing by 2
        have ha' : a / 2 < 2^n := by
          -- Borrow the pattern from FiniteEncoding.ext
          calc a / 2
              < 2^(n+1) / 2 := Nat.div_lt_div_of_lt_of_dvd (by omega) ha
            _ = 2^n := by rw [pow_succ]; omega
        have hb' : b / 2 < 2^n := by
          calc b / 2
              < 2^(n+1) / 2 := Nat.div_lt_div_of_lt_of_dvd (by omega) hb
            _ = 2^n := by rw [pow_succ]; omega
        have hbits' : ∀ i < n, getBit (a / 2) i = getBit (b / 2) i := by
          intro i hi
          have := hbits (i.succ) (Nat.succ_lt_succ hi)
          -- getBit (x) (i+1) = ((x / 2) / 2^i) % 2 = getBit (x/2) i
          simpa [getBit, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_div_eq_div_mul] using this
        have h_high : a / 2 = b / 2 := ih (a / 2) (b / 2) ha' hb' hbits'
        -- Reconstruct a and b from halves and LSB
        calc a
            = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
          _ = 2 * (b / 2) + b % 2 := by simp [h_high, h_lsb]
          _ = b := (Nat.div_add_mod b 2)
  -- Apply the recursion at n = L.R v
  apply Fin.ext
  exact rec_eq (L.R v) cfg1.val cfg2.val cfg1.isLt cfg2.isLt (by
    intro i hi; exact h_all i hi)

/-- Complete observation + agreement → configs are equal.

    **This connects completeness to distinguishability!**

    **Contrapositive**: Different configs → incomplete observation OR disagree.
    This is key for FG indistinguishability: if observation incomplete,
    can have different configs that look the same. -/
theorem complete_observation_implies_distinguishable
    {L : LStarInstanceFull} {v : Fin L.dag.n}
    (obs : Observation L v)
    (h_complete : obs.isComplete)
    (cfg1 cfg2 : Fin (2^(L.R v)))
    (h_agree : obs.configsAgree cfg1 cfg2) :
    cfg1 = cfg2 := by
  apply configs_agree_on_all_positions_are_equal
  intro i
  -- Since complete, i is observed
  have h_obs : i ∈ obs.read_positions :=
    complete_observation_covers_all obs h_complete i
  -- Apply agreement
  exact h_agree i h_obs

/-! ## Construction Helpers -/

/-- Empty observation: nothing has been read yet.

    **Use case**: Initial state before any computation. -/
def Observation.empty (L : LStarInstanceFull) (v : Fin L.dag.n) :
    Observation L v :=
  { read_positions := ∅ }

/-- Full observation: everything has been read.

    **Use case**: After exhaustive exploration of emergent slice. -/
def Observation.full (L : LStarInstanceFull) (v : Fin L.dag.n) :
    Observation L v :=
  { read_positions := Finset.univ }

/-- Full observation is complete (by definition). -/
lemma full_observation_is_complete {L : LStarInstanceFull} {v : Fin L.dag.n} :
    (Observation.full L v).isComplete := by
  unfold Observation.full Observation.isComplete
  simp only [Finset.card_univ, Fintype.card_fin]

/-- Empty observation is incomplete (unless R_v = 0, which doesn't occur). -/
lemma empty_observation_is_incomplete {L : LStarInstanceFull} {v : Fin L.dag.n}
    (h_pos : L.R v > 0) :
    (Observation.empty L v).isIncomplete := by
  unfold Observation.empty Observation.isIncomplete
  simp [h_pos]

/-! ## Module Summary

**Core definitions**:
- Observation structure (lightweight, local to FG gate)
- Completeness predicates (isComplete, isIncomplete)
- Configuration agreement (configsAgree)
- Helper lemmas (complete → covers all, agreement + complete → equal)
- Construction helpers (empty, full observations)

**Key theorem**: `complete_observation_implies_distinguishable` - Complete observation
plus agreement on observed positions implies configs are equal. This connects
completeness to distinguishability, enabling the FG indistinguishability proof.

**Dependencies**:
- LStarInstanceFull (existing infrastructure)
- Finset, Fin (mathlib standard library)

**Usage**: This module provides the observation abstraction for StructuralLowerBound.lean,
which proves that parity computation requires reading all bits.
-/


/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

end LStar.StructuralOWF.Foundations
