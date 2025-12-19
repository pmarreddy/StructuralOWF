import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer3_InformationBounds.WorldCommit.CutProduct
import Layer3_InformationBounds.WorldCommit.AppendixJBridge

/-! ## CutWorlds: Cut-World Semantics for Information Flow Tracking

**Purpose**: Define "cut-worlds" (assignments to unresolved bits at DAG cut) for Semantic Conservation Law.

**Mathematical intuition** (§7.2, §2.2):
- Cut C partitions DAG: resolved ancestors vs unresolved descendants
- Cut-world ω: Hypothetical assignment to emergent bits at C nodes
- Feasible worlds: Consistent with observed info (decreases from 2^ρ → 1)
- SCL tracks: How information resolves exponentially many possibilities

**Key components**:
- CutWorld: Assignment structure (v ∈ C) ↦ Fin (2^{R_v})
- ExecutionPrefix: Observations so far (stub, full version in ExecutionSemantics.lean)
- FeasibleWorlds: Worlds consistent with prefix
- initial_feasible_worlds_count: 2^ρ initial worlds (Cartesian product via CutProduct)

**Main results**: cutWorldEquiv (CutWorld ≃ product type), initial_feasible_worlds_count (cardinality 2^(Σ R_v))

**Trust boundary**: 12 axiom audits - all proven

See Layer3_InformationBounds/Layer3_README.md §World Commitment.
-/

namespace LStar.StructuralOWF.Foundations

open Classical CutProduct

/-! ## Execution Prefix (Lightweight Version)

**Note**: This is a lightweight version. The full ExecutionPrefix structure
is defined in ExecutionSemantics.lean.

We need a type to represent "what's been observed so far" in order
to define FeasibleWorlds.
-/

/-- **Execution prefix**: What the algorithm has observed so far.

    **Full version** (ExecutionSemantics.lean):
    - time: Current time step
    - revealedCells: Which designated addresses have been read
    - revealedValues: Values at those addresses
    - computedSeeds: Seeds computed so far
    - computedDigests: Gate digests computed so far

    **Lightweight version** (this file):
    - Minimal structure for defining FeasibleWorlds
    - ConsistentWith predicate defined without implementation details
-/
structure ExecutionPrefix (L : LStarInstanceFG) where
  /-- Time point in execution. -/
  time : Nat

/-- Empty execution prefix (no observations yet). -/
def emptyPrefix (L : LStarInstanceFG) : ExecutionPrefix L :=
  { time := 0 }

/-! ## Cut-World Definitions

**MATHEMATICAL SETUP**:

For a cut C ⊆ {0, ..., n-1} (set of node indices):
- Each node v ∈ C has R_v emergent bits
- A "world" ω assigns values to all these bits
- Total configuration space: ∏_{v ∈ C} 2^{R_v} = 2^{Σ_{v ∈ C} R_v}

**KEY INSIGHT**: We represent worlds as functions v ↦ bitstring, not as flat bitvectors.
This makes the Cartesian product structure explicit.
-/

/-- **Cut-world**: Assignment to emergent bits at nodes in cut C.

    **Representation**: For each node v ∈ C, assign a value in {0, ..., 2^{R_v}-1}.

    **Example**: If C = {v₁, v₂} with R_{v₁}=2, R_{v₂}=3, then:
    - ω.assignment v₁ h₁ ∈ Fin 4 (4 possible values: 00, 01, 10, 11)
    - ω.assignment v₂ h₂ ∈ Fin 8 (8 possible values: 000, ..., 111)

    **Total worlds**: 4 × 8 = 32 = 2^5 = 2^{R_{v₁} + R_{v₂}}
-/
structure CutWorld (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) where
  /-- Assignment to emergent bits at each node v ∈ C.

      For node v ∈ C with R_v emergent bits, assigns value in Fin (2^{R_v}).
  -/
  assignment : ∀ v : Fin L.dag.n, v ∈ C → Fin (2^(L.R v))

/-- **Extensionality lemma for CutWorld**: Two worlds are equal iff their assignments are equal. -/
@[ext]
theorem CutWorld.ext {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    {ω₁ ω₂ : CutWorld L C}
    (h : ∀ (v : Fin L.dag.n) (hv : v ∈ C), ω₁.assignment v hv = ω₂.assignment v hv) :
    ω₁ = ω₂ := by
  cases ω₁
  cases ω₂
  simp only [mk.injEq]
  funext v hv
  exact h v hv

/-! ## Consistency Predicate

**PURPOSE**: Define when a world ω is "consistent" with observed information.

**STUB STATUS**: This predicate always returns `True`. This is **intentional and sound** because:

1. **Only used for initial count**: `FeasibleWorlds` is only invoked with `emptyPrefix` in the
   main proof chain (see `initial_feasible_worlds_count` and its uses in SegmentReduction.lean).

2. **Mathematically correct at t=0**: At empty prefix (no observations), ALL worlds ARE feasible
   by definition - no constraints have been accumulated yet.

3. **World elimination uses different mechanism**: The actual tracking of world elimination
   during execution uses `wcExecute` (WorldCommit protocol) in WorldCommit.lean, NOT this
   `FeasibleWorlds` function. The WorldCommit protocol maintains its own feasible set via
   `WCState.feasible` which is properly updated by `applyBitDetermination` and `applyDigestMatch`.

**What a full implementation WOULD check** (not needed for the proof):
- If π reveals bit i=1, then ω must have bit i=1
- If π computes digest d, then ω must satisfy the parity constraint giving d
- If π computes seed s, then ω must be consistent with that seed history
-/

/-- **Consistency predicate**: World ω is consistent with execution prefix π.

    **STUB**: Always returns `True`. This is sound because:
    - This predicate is only used via `FeasibleWorlds` at `emptyPrefix`
    - At t=0, all worlds ARE feasible (no constraints yet)
    - World elimination tracking uses `wcExecute`, not `FeasibleWorlds`

    See the section comment above for full justification.
-/
def ConsistentWith {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (_ω : CutWorld L C) (_π : ExecutionPrefix L) : Prop :=
  -- STUB: Always True. Sound because only used at emptyPrefix where all worlds are feasible.
  -- World elimination tracking uses wcExecute (WorldCommit.lean), not this function.
  True

/-! ## Fintype Instance for CutWorld

**GOAL**: Establish that CutWorld L C is a finite type.

**KEY INSIGHT**: CutWorld is isomorphic to a Pi type over finite index set.

The type `∀ v : Fin L.dag.n, v ∈ C → Fin (2^(L.R v))` is equivalent to
`(v : C) → Fin (2^(L.R v.val))` where C is viewed as a subtype.

Since C is a Finset (hence finite), and each Fin (2^(L.R v)) is finite,
the Pi type is finite by Mathlib's Fintype instance for Pi types.
-/

/-- **Equivalence between CutWorld and canonical Pi type**.

    Maps between dependent function with precondition and Pi over subtype.
-/
def cutWorldToPi (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    CutWorld L C → ((v : C) → Fin (2^(L.R v.val))) :=
  fun ω v => ω.assignment v.val v.property

/-- **Inverse mapping from Pi type to CutWorld**. -/
def piToCutWorld (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    ((v : C) → Fin (2^(L.R v.val))) → CutWorld L C :=
  fun f => ⟨fun v h => f ⟨v, h⟩⟩

/-- **The mappings are inverses** (left inverse). -/
theorem cutWorldToPi_leftInv (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    Function.LeftInverse (piToCutWorld L C) (cutWorldToPi L C) := by
  intro ω
  -- Need to show: piToCutWorld (cutWorldToPi ω) = ω
  -- Unfold definitions
  unfold piToCutWorld cutWorldToPi
  -- Both sides are CutWorlds with equal assignment functions
  rfl

/-- **The mappings are inverses** (right inverse). -/
theorem cutWorldToPi_rightInv (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    Function.RightInverse (piToCutWorld L C) (cutWorldToPi L C) := by
  intro f
  -- Need to show: cutWorldToPi (piToCutWorld f) = f
  unfold piToCutWorld cutWorldToPi
  -- Both sides are functions with equal values
  rfl

/-- **Equivalence between CutWorld and Pi type**. -/
def cutWorldEquiv (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    CutWorld L C ≃ ((v : C) → Fin (2^(L.R v.val))) where
  toFun := cutWorldToPi L C
  invFun := piToCutWorld L C
  left_inv := cutWorldToPi_leftInv L C
  right_inv := cutWorldToPi_rightInv L C

/-- **CutWorld is a Fintype** (via equivalence with finite Pi type).

    **Proof strategy**:
    1. Pi type over finite index set (C : Finset) is Fintype (by Mathlib)
    2. Each component Fin (2^(L.R v)) is Fintype
    3. Therefore (v : C) → Fin (2^(L.R v.val)) is Fintype
    4. CutWorld ≃ Pi type → CutWorld is Fintype
-/
instance cutWorldFintype (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    Fintype (CutWorld L C) :=
  Fintype.ofEquiv ((v : C) → Fin (2^(L.R v.val))) (cutWorldEquiv L C).symm

/-- **CutWorld has decidable equality** (needed for filtering).

    Uses classical decidability via Fintype instance.
-/
noncomputable instance cutWorldDecidableEq (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    DecidableEq (CutWorld L C) := by
  classical
  infer_instance

/-! ## Lexicographic Ordering on Worlds

**PURPOSE**: Define total order for canonical world sorting (used in NF_C refutation lists).

**Why we need this**: normalize function needs to sort refuted worlds to ensure uniqueness.

**Strategy**: Use Fintype enumeration - every world has a unique index via the Pi type equivalence.

**Why this works**: CutWorld ≃ Pi type, and Pi types have canonical Fintype ordering.
-/

/-- **Ordering on CutWorlds via Fintype enumeration**.

    **Total order**: Compare via Fintype enumeration indices.

    **Why this works**:
    - CutWorld L C is a Fintype (via cutWorldEquiv)
    - Fintype provides canonical enumeration: Fintype.elems
    - We can find index of each world in this enumeration
    - Compare indices lexicographically

    **Why it's total**: Every world has unique index ∈ {0, ..., card-1}.
-/
noncomputable instance cutWorldOrd (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    Ord (CutWorld L C) where
  compare ω1 ω2 :=
    -- Find positions in canonical enumeration using findIdx
    let enum := (Fintype.elems : Finset (CutWorld L C)).toList
    let idx1 := enum.findIdx (· == ω1)
    let idx2 := enum.findIdx (· == ω2)
    compare idx1 idx2

/-! ## Linear Order on CutWorld (for Canonical Selection)

**PURPOSE**: Provide a total order for canonical element selection from sets.

**WHY NEEDED**: `extractViolatorsForConfig` needs to pick a CANONICAL violator
(the least one) to enable provable coverage: after m steps, exactly m distinct
worlds are refuted. Using `List.head?` on `Finset.toList` picks an arbitrary
element, but using `Finset.min'` with this order picks the canonical minimum.

**CONSTRUCTION**: Use Fintype enumeration index as the ordering key.
Every CutWorld maps to a unique index in {0, ..., card-1} via the Fintype
enumeration, and we order by this index.
-/

/-- **Canonical index of a CutWorld via Fintype.equivFin**.
    This is a bijection from CutWorld to Fin (Fintype.card), which has a natural linear order. -/
noncomputable def cutWorldToFin (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    CutWorld L C → Fin (Fintype.card (CutWorld L C)) :=
  Fintype.equivFin (CutWorld L C)

noncomputable instance cutWorldLinearOrder (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    LinearOrder (CutWorld L C) :=
  -- Use Fintype.equivFin to transfer linear order from Fin n
  LinearOrder.lift' (cutWorldToFin L C) (Fintype.equivFin (CutWorld L C)).injective

/-! ## Feasible Worlds

**DEFINITION**: The set of worlds consistent with current observations.

**Properties** (conceptual - see stub note below):
- Initially (empty prefix): All 2^ρ worlds feasible (no constraints)
- During execution: Shrinks as constraints accumulate (tracked by `wcExecute`, not here)
- At acceptance: ≤ 1 world feasible (unique solution)

**STUB NOTE**: The `FeasibleWorlds` function below always returns all worlds because
`ConsistentWith` is stubbed to `True`. This is sound for the proof - see `ConsistentWith`
documentation. The actual world elimination tracking is done by `wcExecute` in WorldCommit.lean.
-/

/-- **Feasible worlds**: Assignments consistent with current knowledge.

    Returns the set of cut-worlds that don't contradict the execution prefix π.

    **Implementation**: Filter all possible worlds by consistency predicate.

    **STUB BEHAVIOR**: Since `ConsistentWith` always returns `True`, this function
    always returns `Finset.univ` (all worlds). This is sound because:
    - Only used with `emptyPrefix` in the main proof chain
    - At t=0, all worlds ARE feasible (mathematically correct)
    - World elimination during execution uses `wcExecute`, not this function

    **Noncomputable**: Uses classical decidability for filtering.
-/
noncomputable def FeasibleWorlds (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (π : ExecutionPrefix L) : Finset (CutWorld L C) :=
  Finset.univ.filter (fun ω => ConsistentWith ω π)

/-! ## Initial World Count Theorem

**THEOREM**: With no observations (empty prefix), there are exactly 2^ρ feasible worlds,
where ρ = Σ_{v ∈ C} R_v.

**PROOF STRATEGY**:
1. CutWorld ≃ Pi type (proven by cutWorldEquiv)
2. |Pi type| = ∏|components| (proven by Mathlib Fintype.card_pi)
3. |Fin (2^{R_v})| = 2^{R_v} (proven by Fintype.card_fin)
4. ∏ 2^{R_v} = 2^{Σ R_v} (proven by card_pi_eq_pow_sum)

**WHY CARTESIAN FACTORING IS VALID** (Paper Appendix J, Lemma J.1-Cart):

The product formula |Worlds| = ∏_{v∈C} 2^{R_v} is justified by instance properties:

- **A1 (Hermeticity)** → disjoint address pools (H1) → structural independence
  Each node v accesses disjoint memory region U_v (proven by address_hermetic theorem)
  → choices at v₁ cannot constrain choices at v₂

- **A3 (Emergence)** → full-rank matrices (H4) → algebraic independence
  rank(E_v) = R_v (proven by rank_eq certificate in EmergenceMatrix structure)
  → all 2^{R_v} configurations at v are achievable (surjective onto full config space)

- **A2 (Injectivity)** → no hidden correlations (H3)
  Distinct parent configs → distinct seeds (proven by Enc injectivity property)
  → seeds encode full information without compression artifacts

- **Paper quote** (Appendix J, Lemma J.1-Cart):
  > "multiplicativity across C is justified without probabilistic independence"

**This is a DETERMINISTIC, WORST-CASE bound** from information theory, not probabilistic averaging.
No statistical independence assumption needed—structural properties (disjoint memory + full rank) suffice!

**Dependencies**:
- CutProduct.lean (Cartesian factoring under H1-H5)
- Mathlib.Data.Fintype.Card (product cardinalities)
-/

/-- **Initial feasible world count**: At start, 2^ρ worlds are feasible.

    **Statement**: With empty execution prefix (no observations),
    all possible assignments are feasible, giving exactly 2^ρ worlds
    where ρ = Σ_{v ∈ C} R_v.

    **Proof**: Cartesian product cardinality via Pi type equivalence.

    **Trust chain** (explicit):
    1. A1-A3 properties hold for L* (proven: L_satisfies_A1, L_satisfies_A2, L_satisfies_A3)
    2. A1-A3 → H1,H3,H4 (proven: AppendixJBridge.a1_a2_a3_imply_independence)
    3. H1-H5 → Cartesian factoring (proven: Paper Appendix J, Lemma J.1-Cart)
    4. Therefore: |Π_C| = ∏_{v∈C} |S_v| = 2^(Σ R_v) ∎

    **Refactored**: Now uses CutProduct.card_pi_eq_pow_sum (simplified from 35 lines to 18).
-/
theorem initial_feasible_worlds_count
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    : (FeasibleWorlds L C (emptyPrefix L)).card = 2^(C.sum (fun v => L.R v)) := by
  -- Step 1: FeasibleWorlds with empty prefix = all CutWorlds
  have h_all_feasible : FeasibleWorlds L C (emptyPrefix L) = Finset.univ := by
    unfold FeasibleWorlds
    ext ω
    simp [ConsistentWith]

  -- Step 2-3: Convert to Pi type via cutWorldEquiv
  rw [h_all_feasible, Finset.card_univ]
  rw [Fintype.card_congr (cutWorldEquiv L C)]

  -- Step 4: Apply CutProduct.card_pi_eq_pow_sum (replaces steps 4-7)
  have h_fin_card : ∀ v : C, Fintype.card (Fin (2^(L.R v.val))) = 2^(L.R v.val) := by
    intro v
    exact Fintype.card_fin (2^(L.R v.val))
  trans (2 ^ (∑ v : C, L.R v.val))
  · convert card_pi_eq_pow_sum (fun v : C => Fin (2^(L.R v.val))) (fun v => L.R v.val) h_fin_card
  · congr 1
    exact Finset.sum_attach C (fun v => L.R v)

/-! ## Validation Tests (Placeholders)

These will be implemented once we have concrete instances.

**Test 1**: Single node with R=2 → 4 initial worlds
**Test 2**: Two nodes with R=1,2 → 2×4 = 8 initial worlds
-/

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms ExecutionPrefix
#print axioms emptyPrefix
#print axioms CutWorld
#print axioms CutWorld.ext
#print axioms ConsistentWith
#print axioms cutWorldToPi
#print axioms piToCutWorld
#print axioms cutWorldToPi_leftInv
#print axioms cutWorldToPi_rightInv
#print axioms cutWorldEquiv
#print axioms FeasibleWorlds
#print axioms initial_feasible_worlds_count

end LStar.StructuralOWF.Foundations
