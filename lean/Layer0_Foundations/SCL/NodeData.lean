import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-! ## NodeData: SCL Framework Data Structures

**Purpose**: Core abstractions for information-theoretic state bounds.

**Main Definitions**:
- `NodeData`: Computational node with Known context, Unknown assignments, and observable States
- `Assign v`: Assignment space (2^λ possible assignments to λ unknown bits)
- `lambda v`: Residual λ = number of unresolved bits (drives exponential bound)
- `keyed v`: Injective assignment→state mapping (distinct assignments → distinct states)

**Key Insight**: `keyed` property prevents state compression. Combined with counting:
```
2^λ distinct assignments + keyed (injective) → need ≥ 2^λ distinct states (pigeonhole)
```

**Information-Theoretic Foundation (Rényi-0 / Hartley Entropy)**:

SCL corresponds to Hartley entropy, which equals Rényi entropy at α=0:
- **Hartley/Rényi-0**: H₀(X) = log₂|X| (log of support cardinality)
- **SCL's Φ**: Φ = log₂|State| = log₂(Alt_v)

These are identical—both measure log₂ of the number of distinguishable elements.

**Why Rényi-0 (not Shannon/Rényi-1)?**
- **Zero-error**: Must distinguish ALL 2^λ cases, not on average
- **Worst-case**: Per-instance bounds, no probabilistic averaging
- **Counting-based**: Pure cardinality, no distribution assumptions

Shannon entropy (Rényi-1) averages over distributions: H₁ = -Σ p(x) log p(x).
This gives weaker average-case bounds, unsuitable for worst-case correctness.

**Derivation**: The bound is proven via pigeonhole (pure counting), then recognized
as equivalent to Hartley entropy. We don't "apply" Rényi-0 formulas—we derive the
same result from first principles, and note the correspondence.

**Type Parameters**:
- `Known`: Resolved information (corresponds to q designated reads in paper)
- `UnknownIdx`: Unresolved λ binary coordinates (λ = R - q residual bits)
- `State`: Observable computational artifacts (Alt_v in paper, Φ_v = log₂|State|)

**Trust Boundary**: Pure definitions (no axioms). Uses Fintype for constructive cardinality.

**Paper**: §7.0.1 (abstract setup), Lemma 7.I (injectivity → exponential bound), §1.6 (Rényi spectrum).
-/

/-- A node in the SCL framework represents a point in computation.

    **Mathematical Structure**:
    Formalizes the paper's abstract node framework (§7.0.1) where computation at node v
    depends on both resolved information (Known) and unresolved coordinates (UnknownIdx).

    **Type Parameters**:
    - `Known`: Information explicitly available to the algorithm (corresponds to q_v context)
    - `UnknownIdx`: Hidden binary coordinates that determine computational state (R_v - q_v bits)
    - `State`: Observable computational artifacts (Alt_v equivalence classes in paper)

    **Typeclass Requirements**:
    All types must support:
    - Decidable equality (enables constructive reasoning about state distinctness)
    - Finiteness (enables cardinality bounds via |State| ≥ 2^λ)
    - Known must be inhabited (ensures non-empty context for keyedness)

    **Core Mapping**:
    - `state`: (k, a) ↦ s maps (known context, hidden assignment) to observable state
    - Paper notation: given k (resolved q_v bits) and a (assignment to R_v - q_v unknowns),
      produces observable state s ∈ Alt_v

    **Design Rationale**:
    The structure is parametric over types to achieve model-independence—the same abstract
    framework applies whether State represents memory contents, tree branches, table keys,
    or BDD nodes. This generality enables SCL to articulate a common pattern across diverse lower bound techniques.
-/
structure NodeData where
  Known : Type
  UnknownIdx : Type
  State : Type

  -- Decidability: Required for constructive equality tests on state distinctness
  [dec_K : DecidableEq Known]
  [inh_K : Inhabited Known]  -- Non-empty context for keyedness definition
  [dec_I : DecidableEq UnknownIdx]
  [dec_S : DecidableEq State]

  -- Finiteness: Required for cardinality reasoning (|State|, 2^λ bounds)
  [fin_K : Fintype Known]
  [fin_I : Fintype UnknownIdx]
  [fin_S : Fintype State]

  /-- Core state mapping: (known context, hidden assignment) ↦ observable state.
      Paper: Given resolution prefix (q_v bits) and assignment to unresolved coordinates,
      produce the observable computational artifact (element of Alt_v). -/
  state : Known × (UnknownIdx → Bool) → State

namespace NodeData

/-- Typeclass instance exports for dependent types.

    **Purpose**: Expose structure-level typeclass fields (dec_K, fin_K, etc.) as global
    instances for the dependent types v.Known, v.UnknownIdx, v.State. This enables Lean's
    typeclass inference system to automatically find decidability and finiteness instances
    when reasoning about node-specific types.

    **Technical Detail**: Without these exports, Lean cannot infer that v.Known is decidable
    even though NodeData carries [dec_K : DecidableEq Known]. The exports make dependent
    types "first-class" for typeclass resolution.
-/
instance instDecidableEqKnown (v : NodeData) : DecidableEq v.Known := v.dec_K
instance instInhabitedKnown (v : NodeData) : Inhabited v.Known := v.inh_K
instance instDecidableEqUnknownIdx (v : NodeData) : DecidableEq v.UnknownIdx := v.dec_I
instance instDecidableEqState (v : NodeData) : DecidableEq v.State := v.dec_S
instance instFintypeKnown (v : NodeData) : Fintype v.Known := v.fin_K
instance instFintypeUnknownIdx (v : NodeData) : Fintype v.UnknownIdx := v.fin_I
instance instFintypeState (v : NodeData) : Fintype v.State := v.fin_S

/-- Assignment space: Functions from unknown binary coordinates to Boolean values.

    **Mathematical Content**:
    - Type: UnknownIdx → Bool (assignment of truth values to unresolved bits)
    - Cardinality: |Assign v| = 2^λ where λ = |UnknownIdx| (exponential in residual)

    **Paper Correspondence**:
    Represents the 2^{R_v - q_v} distinct computational histories that remain feasible
    at node v after resolving q_v bits. Lemma 7.I ("Unresolved worlds") states:
    "there are exactly 2^{s_v} feasible worlds consistent with the current transcript."

    **Why Exponential Matters**:
    This exponential size is the source of lower bounds in the SCL framework. When an algorithm
    maintains keyedness (distinct assignments → distinct states), it must explicitly represent
    all 2^λ possibilities, yielding the bound |State| ≥ 2^λ. For λ = Ω(n), this forces
    exponential or quasi-polynomial complexity.
-/
def Assign (v : NodeData) : Type := v.UnknownIdx → Bool

/-- Lambda (λ): The residual complexity measure at node v.

    **Definition**: λ_v = |UnknownIdx| = number of unresolved binary coordinates.

    **Paper Correspondence**:
    - Paper notation: s_v = R_v - q_v (residual at node v)
    - Min-cut residual: λ(A,x) = min_C Σ_{v∈C}(R_v - q_v) (bottleneck measure)
    - Our λ_v corresponds to local residual s_v when q_v is implicit in Known

    **Complexity Regimes** (from paper §3):
    - λ = O(log n): Polynomial complexity (P problems)
    - λ = Θ(log² n): Quasi-polynomial (QP-sharp profile for L*)
    - λ = Θ(n): Exponential (Exponential profile for L*)

    **Mathematical Role**:
    The residual λ directly controls computational cost via SCL. When λ remains large
    (cannot be reduced by polynomial-time inference), the bound |State| ≥ 2^λ forces
    super-polynomial resource requirements.

    **Implementation**: Uses Fintype.card to compute cardinality constructively, enabling
    `decide` tactics for concrete verification of specific instances.
-/
def lambda (v : NodeData) : Nat := by
  let _ := v.fin_I
  exact Fintype.card v.UnknownIdx

/-- Keyedness: Injectivity of the state mapping in its assignment argument.

    **Mathematical Definition**: For all fixed contexts k, the partial function
    `a ↦ state(k,a)` is injective on the assignment space—distinct assignments
    produce distinguishable observable states.

    **Computational Verification**: For |UnknownIdx| = λ, checking keyedness requires
    verifying (2^λ choose 2) ≈ 2^{2λ-1} distinctness checks. For λ=256 (Exponential profile),
    this is 2^511 ≈ 10^154 checks—physically impossible. Keyedness is proven mathematically
    for the construction but cannot be verified computationally for realistic parameters.

    **Paper Correspondence**:
    Corresponds to A2 (Injectivity) and the keyedness property from Lemma 7.I:
    - "By A2 (Injectivity), distinct assignments to unresolved coordinates induce
      distinct Seed_v values"
    - "By Keyedness, designated addresses are computed as F_overlay(Seed_v; j,ℓ),
      so if Seed_v differs then designated access patterns differ"
    - Result: 2^{s_v} worlds induce pairwise distinct designated access patterns

    **Information-Theoretic Interpretation**:
    Keyedness captures why algorithms cannot "compress away" uncertainty. If the state
    function were not injective, multiple computational histories (assignments) would
    collapse to the same observable state, allowing the algorithm to merge possibilities
    without resolving the underlying information. By preventing such compression,
    keyedness forces explicit representation of all 2^λ distinct computational histories.

    **Consequence**: Combined with cardinality counting (pigeonhole principle), keyedness
    immediately implies |State| ≥ |Assign| = 2^λ. This is the content of Lemma 7.I
    and theorem SCL_node. See SCLNode.lean for the formal derivation.

    **Correctness vs Performance (Proven for L*, Not Universal)**:
    In the abstract SCL framework, keyedness is a **hypothesis** (not a definitional requirement).
    For L* specifically, keyedness is **proven necessary for correctness** via A2 (Injectivity)
    in Layer 1 (see LStarToNodeData.lean, theorem `NodeDataFull_keyed`).

    For systems satisfying keyedness (like L*), violating the property allows state collisions,
    producing wrong outputs, not just slower computation. This is why SCL is a correctness
    constraint for L*: "Violating q + Φ ≥ R yields wrong outputs, not slower computation—a
    correctness requirement, not a performance heuristic."

    **Key Distinction**:
    - **Abstract framework (Layer 0)**: `keyed` is a *hypothesis* in theorem SCL_node
    - **Concrete construction (Layer 1)**: `keyed` is a *proven property* for L* (via A2)
    - **Result**: L* satisfies the abstract framework's requirements (not by assumption, by proof)

    **Formal Property**: ∀k ∈ Known, ∀a₁ a₂ ∈ Assign, a₁ ≠ a₂ → state(k,a₁) ≠ state(k,a₂)
-/
def keyed (v : NodeData) : Prop :=
  ∀ (k : v.Known) (a₁ a₂ : Assign v),
    a₁ ≠ a₂ → v.state (k, a₁) ≠ v.state (k, a₂)

/- Axiom audit: Core definitions rely only on Lean's type theory and
   standard Mathlib Fintype infrastructure. -/
#print axioms NodeData
#print axioms Assign
#print axioms lambda
#print axioms keyed

end NodeData
