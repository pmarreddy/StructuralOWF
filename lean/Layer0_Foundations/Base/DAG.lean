import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-! ## DAG: Directed Acyclic Graphs (L* Dependency Structure)

**Purpose**: Minimal DAG structure for L* dependency tracking (Property A5).

**Main Definitions**:
- `DAG`: Vertices V = Fin n, parent relation (edges)
- `hasTopoOrder`: Parents numbered before children (valid evaluation order)
- `isAcyclic`: DEFINED as ∃ topological order (not "no cycles")

**Why Definitional Acyclicity?**: Makes `exists_topo_order_of_acyclic` trivial (witness is in definition). Equivalent to standard "no cycles" definition but simpler for L* (only needs existence, not algorithm).

**Minimalism**: Only parent relation + topo order predicate + acyclicity. No graph algorithms (BFS/DFS), no transitive closure, no reachability. L* only needs to VERIFY acyclicity by exhibiting order.

**Property A5**: L* satisfies "Seed_v depends on Seed_u → u is parent of v" (well-founded computation).

**Applications**: Layer 1 (L* structure), Layer 3 (cut-level SCL bounds), Layer 5 (sequential evaluation).

**Paper**: §6 "L* Construction A5", §4.2 "Min-cut framework".
-/

namespace LStar

/-- **DAG Structure**: Directed acyclic graph with finite indexed vertices.

    **Mathematical Structure**:
    A DAG G = (V, E) with:
    - Vertex set V = Fin n (indexed vertices 0, 1, ..., n-1)
    - Edge set E represented implicitly via parent function
    - Edge (u, v) exists ⟺ u ∈ parents(v)

    **Structure Fields**:
    - `n : Nat`: Number of vertices in the graph
    - `parents : Fin n → Finset (Fin n)`: Parent relation mapping each vertex to
      its set of immediate predecessors

    **Edge Representation**:
    We use parent sets rather than explicit edge lists because:
    1. **Natural for dependencies**: "node v depends on nodes parents(v)" is direct
    2. **Efficient membership**: u ∈ parents(v) is O(log |parents(v)|) lookup
    3. **Compact for sparse graphs**: L* DAGs typically have few parents per node

    **Acyclicity Enforcement** (two-stage verification):
    Acyclicity IS enforced for L* instances through Property A5 (Dependency), which
    requires a topological ordering proof (`isAcyclic`). The structure definition
    allows general directed graphs to enable modular verification.

    **How enforcement works**:
    - Structure level: Permits general directed graphs (flexible construction)
    - Instance level: **Property A5 requires and verifies acyclicity** (enforcement)
    - Result: Every L* instance used in the proof has a proven acyclicity certificate

    **Design benefits**:
    - Modular verification: Acyclicity proven when constructing L* instances (Layer 1)
    - Type flexibility: Enables testing with non-acyclic graphs as counterexamples
    - Dependent-type best practice: Structure + property separation

    **Theoretical alignment**: Equivalent to textbook DAG definitions (Cormen et al.)
    with acyclicity as a proven property rather than a type constraint.

    **Example**: For dependency graph with edges (0→2), (1→2), (2→3):
    ```lean
    { n := 4,
      parents := fun v => match v with
        | 0 => ∅           -- Node 0 has no parents (source node)
        | 1 => ∅           -- Node 1 has no parents (source node)
        | 2 => {0, 1}      -- Node 2 depends on nodes 0 and 1
        | 3 => {2}         -- Node 3 depends on node 2
    }
    ```

    **L* Application**:
    In L* construction, vertices represent computational nodes and edges represent
    seed dependencies. If Seed_v is computed using Seed_u, then u ∈ parents(v).
    Property A5 ensures this dependency structure forms a valid DAG.

    **Design Note**: No invariants enforced at construction time (acyclicity is a
    separate predicate, not a structural constraint). This allows flexible graph
    construction followed by acyclicity verification.
-/
structure DAG where
  /-- Number of vertices in the graph -/
  n : Nat
  /-- Parent relation: parents v is the set of immediate predecessors of vertex v.
      Edge (u, v) exists in the graph ⟺ u ∈ parents v -/
  parents : Fin n → Finset (Fin n)

namespace DAG

variable {G : DAG}

/-- **Topological Ordering**: Vertex numbering respecting dependency order.

    **Definition**: A function order : Fin n → ℕ is a topological ordering if every
    edge (u, v) in the graph satisfies order(u) < order(v). In other words, parents
    are numbered strictly before their children.

    **Mathematical Content**:
    ```
    hasTopoOrder G order ≡ ∀(u, v) ∈ E, order(u) < order(v)
    ```

    Equivalently (contrapositive): No "backward edges" relative to the numbering—
    you never have v numbered before u when u is a dependency of v.

    **Intuition - Why This Matters**:
    Topological orderings enable sequential evaluation strategies:
    - Process vertices in increasing order number: order⁻¹(0), order⁻¹(1), ...
    - When processing vertex v, all parents u ∈ parents(v) have already been processed
      (because order(u) < order(v))
    - Result: Valid computation order respecting all dependencies

    **Example**: For DAG with edges (0→2), (1→2), (2→3):
    - Valid topo order: order(0) = 0, order(1) = 1, order(2) = 2, order(3) = 3
    - Also valid: order(0) = 5, order(1) = 7, order(2) = 10, order(3) = 20
      (Ordering only needs to PRESERVE edge direction, not be consecutive)
    - Invalid: order(0) = 0, order(1) = 1, order(2) = 3, order(3) = 2
      (Violates edge 2→3 since order(3) < order(2))

    **Classical Graph Theory**:
    Kahn's theorem (1962): Finite directed graph admits topological ordering ⟺ acyclic.
    Our formalization uses this equivalence definitionally (see `isAcyclic` below).

    **L* Application**:
    L* instances use topological ordering to prove Property A5 (dependency closure).
    The ordering witnesses well-foundedness: compute seeds in increasing order to
    ensure all dependencies are satisfied.

    **Non-Uniqueness**: Topological orderings are NOT unique in general. A DAG may
    have exponentially many distinct topological orderings (e.g., complete bipartite
    graph K_{n,m} has n!·m! orderings). We only need existence, not uniqueness.
-/
def hasTopoOrder (G : DAG) (order : Fin G.n → Nat) : Prop :=
  ∀ v u, u ∈ G.parents v → order u < order v

/-- **Acyclicity**: Characterized by existence of a topological ordering.

    **Definition**: A graph G is acyclic if there exists a topological ordering on
    its vertices. This is the constructive characterization of DAGs.

    **Mathematical Content**:
    ```
    isAcyclic G ≡ ∃ order : V → ℕ, hasTopoOrder G order
    ```

    **Classical Graph Theory Equivalence** (Kahn's theorem, 1962):
    For finite directed graphs:
    - G is acyclic (no directed cycles) ⟺ G admits a topological ordering

    Our definition uses the topological ordering characterization directly rather
    than defining "no cycles" and proving the equivalence. Both are mathematically
    correct—we chose the constructive characterization for pragmatic reasons (see below).

    **Design Rationale - Why Definitional Acyclicity**:

    **Our approach** (USED): Define isAcyclic ≡ ∃ topo order
    - ✓ **Verification friendly**: Prove acyclicity by exhibiting explicit ordering
    - ✓ **Minimal implementation**: No cycle detection algorithms needed
    - ✓ **Sufficient for L***: Construction only needs to certify well-foundedness
    - ✓ **Makes theorem trivial**: exists_topo_order_of_acyclic is definitional

    **Alternative** (NOT used): Define isAcyclic ≡ no directed cycles, prove ∃ topo order
    - ✗ Requires formalizing cycle detection (Tarjan's or DFS-based)
    - ✗ More complex proof burden (prove Kahn's theorem constructively)
    - ✗ Over-engineered for L* needs (don't need algorithmic cycle checking)

    **Mathematical Equivalence**: Both approaches define the same concept. We chose
    the simpler formalization because L* instances prove acyclicity constructively
    anyway (by providing explicit orderings via Property A5 verification).

    **Example - Proving Acyclicity**:
    For DAG with edges (0→2), (1→2), (2→3), exhibit ordering:
    ```lean
    have h_acyclic : isAcyclic G := by
      use (fun v => v.val)  -- Use vertex indices as ordering
      intro v u hu
      -- Prove order(u) < order(v) for all edges...
    ```

    **Paper Reference**: §6 "L* Construction" - Property A5 ensures dependency
    structure forms valid DAG (acyclic by construction). No explicit acyclicity
    proofs needed—topological ordering witnessing well-foundedness is implicit
    in the layer-by-layer construction.
-/
def isAcyclic (G : DAG) : Prop := ∃ order : Fin G.n → Nat, hasTopoOrder G order

/-- **Acyclic graphs have topological orderings** (definitional witness extraction).

    **Theorem Statement**:
    ```lean
    isAcyclic G → ∃ order, hasTopoOrder G order
    ```

    **Mathematical Content**:
    If G is acyclic (has a topological ordering), then G has a topological ordering.
    This appears tautological—and it is by design! The proof is trivial (h itself
    is the witness) because we DEFINED acyclicity as existence of topo order.

    **Why This Theorem Exists**:
    Despite being definitionally true, this theorem serves important roles:

    1. **API clarity**: Separates definition (what acyclicity means) from usage
       (extracting the witness ordering). Users can write `exists_topo_order_of_acyclic h`
       instead of manually unpacking `h : isAcyclic`.

    2. **Documentation**: Explicitly states the key property of acyclic graphs in
       theorem form, making the implication searchable and discoverable.

    3. **Stability**: The theorem statement is robust to alternative definitions
       of acyclicity (proof may change, but statement remains valid).

    **Proof**: Immediate—definitional extraction of existential witness.
    ```lean
    h : isAcyclic G ≡ ∃ order, hasTopoOrder G order
    Goal: ∃ order, hasTopoOrder G order
    Proof: h  (exact same type) ∎
    ```

    **Classical Graph Theory**:
    In standard graph theory, this would be Kahn's theorem (1962): "Every DAG admits
    a topological ordering." Our formalization makes this definitional rather than
    requiring algorithmic proof via DFS or Kahn's algorithm.

    **Usage in L***:
    L* proofs use this theorem to extract ordering witnesses from acyclicity hypotheses.
    Property A5 verification typically provides explicit ordering (Layer 1), which
    this theorem can then extract for use in sequential evaluation arguments (Layer 4).
-/
theorem exists_topo_order_of_acyclic (G : DAG) (h : isAcyclic G) :
  ∃ order, hasTopoOrder G order := h

/-- **Parent-based ordering**: u < v if u is a parent of v.
    Used for well-founded recursion over DAG structure. -/
def lt (G : DAG) (u v : Fin G.n) : Prop := u ∈ G.parents v

/-- **Well-foundedness of parent ordering for acyclic DAGs**.

    For an acyclic DAG, the parent relation is well-founded: there are no
    infinite descending chains u₁ ∈ parents(u₂) ∈ parents(u₃) ∈ ...

    This enables well-founded recursion for seed computation. -/
theorem lt_wf (G : DAG) (h_acyclic : isAcyclic G) : WellFounded (G.lt) := by
  -- Extract topological ordering from acyclicity
  obtain ⟨order, h_order⟩ := h_acyclic
  -- Key insight: If u is a parent of v, then order(u) < order(v).
  -- So G.lt is a sub-relation of (InvImage Nat.lt order).
  -- Since Nat.lt is well-founded, InvImage Nat.lt order is well-founded,
  -- and any sub-relation of a well-founded relation is well-founded.
  have h_sub : Subrelation G.lt (InvImage (· < ·) order) := by
    intro a b h_lt
    -- h_lt : G.lt a b means a ∈ G.parents b
    -- Need to show: order a < order b (InvImage (· < ·) order a b)
    -- h_order : hasTopoOrder G order, i.e., ∀ v u, u ∈ G.parents v → order u < order v
    exact h_order b a h_lt
  have h_inv_wf : WellFounded (InvImage (· < ·) order) :=
    InvImage.wf order Nat.lt_wfRel.wf
  exact Subrelation.wf h_sub h_inv_wf

/- **Axiom Audit**: Trust boundary verification for DAG definitions and theorem.

   **Expected Result**: All definitions and the theorem should rely only on standard
   Lean foundations (propext, Quot.sound, Classical.choice at most).

   **DAG structure**: Pure type definition—defines record type with two fields (n, parents).
   No computational content, just type-theoretic structure. Should have minimal axioms.

   **hasTopoOrder**: Pure predicate definition—defines proposition about orderings.
   Universal quantification over finite types. Should rely on standard foundations.

   **isAcyclic**: Existential proposition—states existence of topological ordering.
   Uses existential quantification (∃). Should rely on standard foundations.

   **exists_topo_order_of_acyclic**: Trivial theorem—proof is identity function (h itself).
   Should have same axioms as `isAcyclic` definition since proof is definitional.

   **Verification**: Running #print axioms below confirms trust boundary. -/
#print axioms DAG
#print axioms hasTopoOrder
#print axioms isAcyclic
#print axioms exists_topo_order_of_acyclic
#print axioms lt
#print axioms lt_wf

end DAG

end LStar
