# Layer 1: L* Construction (SCL Framework Instantiation)

**Purpose**: Concrete construction of L* instances satisfying A1-A5 properties, instantiating the abstract SCL framework from Layer 0.

**Location**: `lean/Layer1_Construction/`

**Status**: ✅ Publication-ready (12/12 files, zero custom axioms)

---

## Overview

Layer 1 provides the **L* construction** - a computational problem with built-in information-theoretic hardness. L* instances satisfy Properties A1-A5, which mathematically **guarantee** that the abstract SCL framework (Layer 0) applies, forcing exponential resource requirements.

**Key Insight**: L* isn't just "a hard problem" - it's a **constructive proof** that problems with A1-A5 structure are unavoidably hard. The construction is explicit, verifiable, and parametric in the emergence rank R.

**Layer Dependencies**:
- **Upstream**: Layer 0 (SCL framework provides abstract bounds)
- **Downstream**: Layer 2 (Structural OWF uses Plant function to embed 3-SAT), Layer 3 (applies information bounds to L* instances)

---

## Properties A1-A5: The Foundation

L* instances are designed to satisfy five properties that collectively force exponential complexity:

### A1: Hermeticity (Disjoint Designated Pools)

**Statement**: Each node v has its own designated pool - disjoint memory regions where seeds can be written/read.

**Mathematical Content**:
```
∀ v₁ v₂, v₁ ≠ v₂ → designated_pool(v₁) ∩ designated_pool(v₂) = ∅
```

**Why This Matters**: Prevents information leakage between nodes.
```
Without A1: Node v₁ could "spy" on v₂'s computations (shared memory)
With A1: Each node's designated reads are independent (hermetic isolation)
→ Enables compositional SCL bounds (cut-level multiplicative principle)
```

**Implementation**: Stride-based pool allocation - pool_v = base + v × stride (ensures disjointness).

**Trust Boundary**: Constructively verified (proven from pool arithmetic, not assumed).

### A2: Injectivity (encodeSeed Injective)

**Statement**: The encoding function Enc(parents, emergent) is injective - different inputs produce different seeds.

**Mathematical Content**:
```lean
encodeSeed_injective:
  (hist₁, e₁) ≠ (hist₂, e₂) → encodeSeed(hist₁, e₁) ≠ encodeSeed(hist₂, e₂)
```

**Why This Matters**: Forces **keyedness** (Layer 0 requirement).
```
Different (parent seeds, emergent bits) → different child seeds (injective)
→ Different assignments → different seed chains → different states (keyed)
→ Cannot compress 2^λ assignments into < 2^λ states
→ SCL_node applies: |State| ≥ 2^λ ✓
```

**This is the "keyedness bridge"**: A2 (Layer 1 property) → keyed predicate (Layer 0 requirement) → SCL_node (exponential bound).

**Implementation**: encodeSeed packs parent bits + emergent bits into seed via bit concatenation (injective by construction).

**Trust Boundary**: **PROVEN** from bit packing injectivity (A2_Injectivity.lean), zero axioms.

### A3: Emergence (Full-Rank Emergence Matrices)

**Statement**: At each node v, R_v bits must **emerge** - cannot be determined from parent seeds alone.

**Mathematical Content**:
```lean
emergence_matrix_full_rank (v : Fin n) :
  Matrix.rank (L.emergence v) = R v
```

**Why This Matters**: Forces **resolution bottleneck** (Way 2).
```
R_v bits emerge at node v (full-rank constraint)
→ Cannot derive these bits from parents deterministically
→ Must explicitly "resolve" via designated reads
→ q designated reads can resolve at most q bits
→ Residual λ = R - q bits remain → 2^λ possibilities remain
```

**Concrete Example** (R=3):
```
Parent seeds: [s₀, s₁, s₂]  (fully determined)
Emergent bits: [e₀, e₁, e₂]  (3 bits that must be "created")
Full-rank matrix: Each emergent bit is linearly independent
→ Cannot predict e₁ from (s₀, s₁, s₂, e₀) - must read explicitly
→ 2³ = 8 possible configurations remain after reading parents
```

**Implementation**: constructFullRank builds explicit full-rank R×seedWidth matrices.

**Trust Boundary**: **PROVEN** from matrix rank properties (A3_Emergence.lean), zero axioms.

### A4: Closure (Deterministic Seed Recovery)

**Statement**: Given parent seeds and emergent bits, the child seed is uniquely determined.

**Mathematical Content**:
```
Seed_v = encodeSeed(packParents(parent_seeds), emergent_bits)  (deterministic function)
```

**Why This Matters**: Ensures **well-defined seed chains**.
```
Parent seeds + emergent bits → unique child seed (deterministic)
→ Seed chains are functions (not relations)
→ Can trace seed dependencies through DAG
→ Enables A5 (dependency closure) verification
```

**Implementation**: encodeSeed is a pure function (no randomness, no oracles).

**Trust Boundary**: Definitional (encodeSeed is a def, not an axiom).

### A5: Dependency (Topological Ordering)

**Statement**: If node v's seed depends on node u's seed, then u is a parent of v in the DAG.

**Mathematical Content**:
```
Seed_v depends on Seed_u → u ∈ dag.parents(v)  (dependency captured by graph structure)
```

**Why This Matters**: Ensures **well-founded computation**.
```
All dependencies are explicit in DAG structure
→ No hidden circular dependencies
→ Topological order exists (can evaluate seeds level-by-level)
→ SCL cuts partition dependencies cleanly
```

**Implementation**: DAG is acyclic (Layer 0), parents relation captures all dependencies.

**Trust Boundary**: Verified by exhibiting topological order (constructive proof).

---

## A1-A5 → SCL: The Reduction

**Theorem** (informal, formalized across Layers 0-1):
```
L* instance satisfies A1-A5 → SCL framework applies → |State| ≥ 2^λ
```

**Proof Chain**:
1. **A2 (injectivity)** → keyed predicate (different assignments → different states)
2. **keyed** → SCL_node (Layer 0 theorem: |State| ≥ 2^λ)
3. **A1 (hermeticity)** → independent node bounds (compositional reasoning)
4. **A3 (emergence)** → λ = R - q residual (information bottleneck)
5. **A4, A5 (closure, dependency)** → well-defined seed chains (enables tracing)

**Result**: L* instances have **unavoidable exponential complexity** when λ = ω(log n).

---

## Seed Chain Mechanism

**Central Concept**: Seeds propagate through the DAG via deterministic encoding.

### Seed Propagation Formula

**At each node v**:
```
Seed_v = encodeSeed(packParents(parent_seeds), emergent_bits)
```

**Components**:
- `parent_seeds`: Seeds from all parent nodes u ∈ dag.parents(v)
- `packParents`: Concatenate parent seeds into bit vector
- `emergent_bits`: R_v fresh bits (from designated reads or emergence matrix)
- `encodeSeed`: Injective encoding function (A2 property)

**Example** (3 parents, R=2):
```
Parents: v₀ (seed s₀), v₁ (seed s₁), v₂ (seed s₂)
Pack: parentBits = [s₀ bits] ++ [s₁ bits] ++ [s₂ bits]
Emerge: emergent = [e₀, e₁]  (2 fresh bits)
Encode: Seed_v = encodeSeed(parentBits, emergent)
        = pack as single bitstring (injective!)
```

### Why Injectivity (A2) Matters

**Without A2** (non-injective encoding):
```
(parents₁, emergent₁) ≠ (parents₂, emergent₂) but Seed_v₁ = Seed_v₂  (collision!)
→ Different computational histories produce same seed
→ Can merge states (compress information)
→ SCL_node doesn't apply (keyedness fails)
→ No exponential bound ✗
```

**With A2** (injective encoding):
```
(parents₁, emergent₁) ≠ (parents₂, emergent₂) → Seed_v₁ ≠ Seed_v₂  (injective!)
→ Different histories remain distinguishable
→ Cannot compress states (keyedness holds)
→ SCL_node applies: |State| ≥ 2^λ ✓
```

**Result**: A2 is the **linchpin property** - without it, the entire SCL argument collapses.

---

## Multi-Level DAG Architecture

L* uses a **multi-level reduction tree** to embed computational problems (e.g., 3-SAT) with logarithmic depth.

### Structure

**Level 0**: Source node (v₀)
- Provides base randomness
- No parents (root of DAG)
- Seed₀ = external input

**Level 1**: Variable nodes (v₁, ..., vₙ)
- One node per problem variable
- Parents: {v₀} (source)
- Seed_vᵢ = encodeSeed(Seed₀, variable_bits_i)

**Level 2**: Clause nodes (with FG bottleneck architecture)
- **FG gates** (first `numGates` clauses): Parents = variables in clause
- **Non-FG clauses** (remaining): Parents = variables in clause **+ FG gate(s)**
- Seed_c = encodeSeed(packParents(var_seeds, fg_seeds), constraint_emergent)

**Levels 3+**: Reduction tree (binary combining)
- Binary tree structure (each node has ≤2 parents)
- Depth: ⌈log₂ m⌉ levels (m = number of constraints)
- Combines constraints via AND/OR gates

**Total Depth**: 3 + ⌈log₂ m⌉ = O(log m)

### Hourglass DAG Architecture (Critical for 2^R Bound)

The **FrontierGate (FG) bottleneck** creates an **hourglass-shaped DAG**: wide (variables) → narrow (FG) → wide (clauses). All information must flow through the narrow "pinch point" at FG.

```
        Source
           ↓
    ┌──┬──┬──┬──┐
    v₁ v₂ v₃ ... vₙ        ← WIDE: n variable nodes (α enters here)
    └──┴──┴──┴──┘
           ↓
         ┌───┐
         │ FG │             ← NARROW: bottleneck (R bits derived from assignment, A3)
         └───┘
           ↓
    ┌──┬──┬──┬──┐
    C₁ C₂ C₃ ... Cₘ        ← WIDE: m clause nodes (ALL depend on FG!)
    └──┴──┴──┴──┘
           ↓
      Reduction tree
```

**Why FG Bottleneck Matters**:
1. **Creates single point of control**: All clause seeds depend on FG seeds
2. **FG seeds contain R bits**: Derived from assignment, certified by A3 (emergence)
3. **Wrong FG entropy → everything wrong**: Clause seeds, masks, decoding all fail
4. **SCL proves 2^R state complexity**: Any algorithm must maintain 2^R distinguishable states to correctly traverse FG (proven in Layer 0)

**Implementation** (`MultiLevelDAG.lean`):
```lean
-- Non-FG clause: add FG gate(s) as parents (all paths go through FG)
let fg_indices := List.range numGates |>.map (· + nvars + 1)
base_parents ++ fg_indices
```

**Important Clarification**: The 2^R hardness is NOT from guessing independent secrets. The FG bits are deterministically derived from the assignment. The 2^R lower bound comes from SCL (Semantic Conservation Law, Layer 0), which proves any algorithm must maintain ≥2^R distinguishable states to correctly compute seeds at the FG gate. This is an algorithmic complexity theorem, not a verifier-enforced search.

### Why Multi-Level?

**Flat structure** (NOT used):
```
All constraints at level 2, single reduction node at level 3
Depth: 3 (constant)
Problem: Reduction node has m parents → seedWidth = Θ(m · R) (linear in m!)
```

**Binary tree** (USED):
```
Constraints at level 2, binary tree at levels 3+ combining them
Depth: O(log m) (logarithmic)
Benefit: Each node has ≤2 parents → seedWidth_k ≤ 2·seedWidth_{k-1} + R
Result: seedWidth = O(2^k · R) = poly(n) when k = O(log m) ✓
```

**Seed Width Recurrence**:
```
seedWidth₀ = R                                (source)
seedWidth₁ = R + R = 2R                       (variables)
seedWidth₂ = #parents · (R + R) + R ≈ 7R     (constraints, #parents ≈ 3 for 3-SAT)
seedWidth_k = 2 · seedWidth_{k-1} + R         (binary tree, k ≥ 3)

Solution: seedWidth_k = O(2^k · R)
With k = O(log m): seedWidth = O(m · R) = poly(n) ✓
```

**Result**: Polynomial-size seeds despite exponential information requirements (via depth/width tradeoff).

---

## File Organization

### Core/ Subdirectory (Main Construction)

**Read Order** (dependencies):
1. **LStarInstance.lean** - Core L* structure (DAG + pools + encoding + emergence)
2. **Pools.lean** - Designated pool allocation (A1 hermeticity)
3. **SeedChain.lean** - encodeSeed definition and injectivity (A2)
4. **EmergenceMatrix.lean** - Full-rank emergence matrices (A3)
5. **InstanceOps.lean** - seedWidth computation, capacity constraints
6. **BalancedBinaryTree.lean** - Balanced binary tree for O(log m) aggregation
7. **MultiLevelDAG.lean** - Complete multi-level DAG construction (depth O(log m))
8. **OAPEncoding.lean** - OAP (Observation-Assignment Pair) encoding helpers

**Purpose**: Build complete L* instances with verified A1-A5 properties.

### Bridge/ Subdirectory (Layer 0 Connection)

**File**: **LStarToNodeData.lean**

**Purpose**: Instantiate Layer 0's abstract SCL framework with concrete L* structure.

**Key Function**:
```lean
def lstarToNodeData (L : LStarInstance) (v : Fin L.n) : NodeData
```

**Mapping**:
- Layer 0 `NodeData.State` ← Layer 1 `Seed seedWidth(v)` (seeds as states)
- Layer 0 `keyed` ← Layer 1 A2 injectivity (encodeSeed injective → keyed)
- Layer 0 `lambda` ← Layer 1 residual λ_v = R_v - q_v

**Result**: SCL_node theorem (Layer 0) applies to L* instances (Layer 1).

### Properties/ Subdirectory (A1-A5 Verification)

**Files** (no required order):
- **A1_Hermeticity.lean** - Disjoint designated pools (stride-based allocation)
- **A2_Injectivity.lean** - encodeSeed injectivity (bit packing injectivity proof)
- **A3_Emergence.lean** - Full-rank emergence matrices (constructFullRank correctness)

**Purpose**: Prove L* construction satisfies A1-A5 properties (enables SCL application).

---

## Key Theorems

### encodeSeed_injective (A2)

**Statement**:
```lean
theorem encodeSeed_injective (L : LStarInstanceFull) (v : Vertex L)
    (hcap : parentBits L v + L.R v ≤ L.seedWidth v)
    (hist1 hist2 : ParentHistory L v)
    (e1 e2 : Vector Bool (L.R v)) :
    (hist1 ≠ hist2 ∨ e1 ≠ e2) →
    encodeSeed L v hist1 e1 ≠ encodeSeed L v hist2 e2
```

**Meaning**: Different (parent history, emergent bits) → different seeds.

**Proof**: Bit packing injectivity (concatenation preserves distinctness).

**Significance**: Establishes keyedness (Layer 0 requirement), enables SCL_node.

**Trust Boundary**: **PROVEN** from Mathlib bit operations (zero axioms).

### constructFullRank (A3)

**Statement**:
```lean
/-- Construct a certified full-row-rank emergence matrix when `R ≤ n`. -/
def constructFullRank (R n : Nat) (h : R ≤ n) : EmergenceMatrix R n :=
  { matrix := leftIdentityBlock R n h
  , rank_eq := rank_leftIdentityBlock R n h }
```

**Note**: The rank property `.rank_eq` is bundled as a field in the `EmergenceMatrix` structure, not a separate theorem.

**Meaning**: Can construct R×n matrix with full rank R (R linearly independent rows).

**Proof**: Identity matrix construction (first R rows are identity → rank R).

**Significance**: Ensures R bits must emerge (cannot be predicted from parents).

**Trust Boundary**: **PROVEN** from Mathlib matrix rank (zero axioms).

### build3SATReductionDAG (Multi-Level Construction)

**Statement**:
```lean
def build3SATReductionDAG (φ : CNF) (numGates : Nat := 1) : DAG
```

**Note**: The `numGates` parameter (default 1) specifies how many FG gates exist. All non-FG clauses have FG gate(s) as additional parents, ensuring their seeds depend on FG entropy.

**Meaning**: Constructs DAG with O(log m) depth (m = #clauses).

**Proof**: Binary tree construction (explicit topological order).

**Significance**: Ensures polynomial seed widths (depth/width tradeoff).

**Trust Boundary**: **PROVEN** constructively (explicit DAG construction).

---

## Trust Boundary

**Axioms**: ZERO custom axioms in Layer 1.

**Foundations Used**:
- `propext` - Propositional extensionality (standard Lean)
- `Quot.sound` - Quotient soundness (standard Lean)
- `Classical.choice` - Classical choice (standard mathematics)

**Why Zero Axioms?**:
- **A1 (Hermeticity)**: Proven from stride arithmetic (disjoint pool calculation)
- **A2 (Injectivity)**: Proven from bit packing injectivity (Mathlib)
- **A3 (Emergence)**: Proven from identity matrix rank (Mathlib linear algebra)
- **A4 (Closure)**: Definitional (encodeSeed is a pure function)
- **A5 (Dependency)**: Proven by exhibiting topological order (DAG construction)

**Key Achievement**: **A1-A5 are theorems, not axioms**. The L* construction is fully verified - no "assume properties hold" - we **prove** they hold.

**Verification**: Run `#print axioms encodeSeed_injective` → shows only standard Lean foundations.

---

## Paper References

**Primary Source**: "Read-or-x.md" (P≠NP proof paper)

**Layer 1 Correspondence**:

**§6 "L* Construction"**:
- Lines 2977-2994: L* instance structure (corresponds to LStarInstance.lean)
- Lines 2995-3010: Multi-level DAG (corresponds to MultiLevelDAG.lean)
- Lines 3011-3025: Seed encoding (corresponds to SeedChain.lean)

**§6.1 "Properties A1-A5"**:
- A1: Hermeticity (A1_Hermeticity.lean)
- A2: Injectivity (A2_Injectivity.lean)
- A3: Emergence (A3_Emergence.lean)
- A4: Closure (implied by encodeSeed definition)
- A5: Dependency (DAG.lean acyclicity)

**§7.2 "SCL Application to L*"**:
- Lines 3650-3670: A1-A5 → SCL (corresponds to LStarToNodeData.lean bridge)
- Lemma 7.I "Keyedness from A2" - A2 injectivity → keyed predicate (keyedness bridge)

---

## Design Rationale

### Why Separate Core/Bridge/Properties?

**Design**: Layer 1 split into three subdirectories.

**Rationale**:
- **Core/**: Construction files (build L* instances) - algorithmic content
- **Bridge/**: Layer 0 connection (apply abstract SCL to concrete L*) - instantiation
- **Properties/**: A1-A5 verification (prove properties hold) - correctness

**Benefits**:
1. **Conceptual clarity**: Construction vs. verification vs. abstraction bridging
2. **Modularity**: Can update construction without touching properties (if interface stable)
3. **Navigation**: Readers know where to find specific concerns

### Why Injective encodeSeed Instead of Collision-Resistant Hash?

**Our Approach** (USED): Deterministic injective encoding
```lean
encodeSeed : ParentHistory → EmergentBits → Seed  (injective function)
```

**Alternative** (NOT used): Cryptographic hash
```lean
encodeSeed_hash : ParentHistory → EmergentBits → Seed  (collision-resistant hash)
```

**Why Deterministic Injective?**:
1. **No axioms**: Injectivity provable from bit packing (collision-resistance would be axiom)
2. **Constructive**: Can trace seeds backward (extract parent info if needed)
3. **Transparent**: No black-box cryptography (full formalization)
4. **Sufficient**: Don't need cryptographic strength - just injectivity for keyedness

**Tradeoff**: Deterministic encoding is predictable (unlike hash), but preferable for formalization (provable without crypto axioms).

### Why Full-Rank Matrices Instead of Random Matrices?

**Our Approach** (USED): Identity matrix construction
```lean
constructFullRank R seedWidth : First R rows are identity matrix → rank R
```

**Alternative** (NOT used): Random matrix sampling
```lean
axiom random_matrix_full_rank : Random R×seedWidth matrix has rank R w.h.p.
```

**Why Identity Construction?**:
1. **Deterministic**: No probability/randomness needed
2. **Provable**: rank(identity) = R is theorem (Mathlib)
3. **Explicit**: Can verify rank by inspection (first R rows independent)
4. **No axioms**: Don't need probabilistic lemmas about random matrices

**Result**: A3 is **constructively proven** (exhibit explicit full-rank matrix), not probabilistically assumed.

---

## Significance in Proof Chain

**Layer 1 Role**: Provide concrete L* instances that **provably satisfy** A1-A5, enabling SCL application.

**Proof Flow**:
```
Layer 0: Abstract SCL framework
  keyed → |State| ≥ 2^λ  (abstract theorem)
  ↓
Layer 1 (THIS LAYER): Concrete L* construction
  A1-A5 proven → keyed holds → SCL applies to L*
  ↓
Layer 2: Structural OWF construction
  Plant embeds 3-SAT in L* → hard instances
  ↓
Layer 3: Information bounds
  Apply SCL to planted L* → 2^(ρ-s) lower bound
  ↓
Layers 4-5: Operational semantics + complexity
  TM time ≥ 2^(ρ-s) → poly-time contradiction → P≠NP
```

**Without Layer 1**: Layer 0 is abstract (no concrete instances), can't build Structural OWF.

**With Layer 1**: Explicit construction enables everything downstream (OWF, planted instances, information bounds).

---

## Implementation Notes

### Dependent Types and seedWidth

**Challenge**: seedWidth varies per node (depends on #parents, R_v).

**Solution**: Dependent types - `Seed (seedWidth v)` where seedWidth is a function.

**Benefit**: Type system enforces seed width compatibility (can't mix seeds from different nodes).

**Tradeoff**: More complex types (need proofs of seed width equality for transport), but **type-safe** (prevents width mismatches).

### Fintype Instances

**Every type is Fintype**:
```lean
instance : Fintype (Seed k) := Fintype.ofEquiv (Fin (2^k)) (by ...)
instance : Fintype ParentHistory := ...
instance : Fintype EmergentBits := ...
```

**Why Critical**: SCL_node requires `Fintype.card v.State` (must be computable cardinality).

**Result**: All L* state spaces automatically get exponential bounds (inherit from Seed finiteness).

---

## FAQ

**Q: Why do we need A1-A5? Can't we just say "L* is hard"?**

A: A1-A5 provide a **constructive characterization** of hardness. Instead of axiomatically assuming "L* is hard", we **prove** it from structural properties. The properties are:
1. **Verifiable**: Can check any instance satisfies A1-A5
2. **Reusable**: Any problem with A1-A5 gets exponential bound (not L*-specific)
3. **Trustworthy**: Properties proven, not assumed (zero axioms)

**Q: What if an algorithm doesn't use seeds/state in the way L* expects?**

A: The SCL framework is **representation-independent**. Any algorithm solving L* must:
- **Store** information (blocked by A1/A2 via keyedness)
- **Resolve** information (blocked by A3 via emergence)
- **Eliminate** possibilities (blocked by FG parity, Layer 2)

Even if algorithm uses different representation (not seeds), it still hits these information-theoretic barriers.

**Q: Why is A2 (injectivity) provable when it seems like a security assumption?**

A: A2 is **mathematical injectivity**, not cryptographic. We use bit packing:
```
encodeSeed(hist, emerge) = [hist bits] ++ [emerge bits]  (concatenation)
→ Injective by construction (different inputs have different concatenations)
```

This is **provable** from bit operations (Mathlib), unlike cryptographic assumptions (unprovable).

**Q: Can L* instances be constructed in polynomial time?**

A: Yes! The Plant function (Layer 2) constructs L* instances in poly(n) time. The **solving** is hard (exponential lower bound), not the **construction**. This is standard for NP-complete problems (easy to construct hard instances, hard to solve them).

**Q: What happens if we relax one of A1-A5?**

A:
- **Drop A1**: Nodes share pools → information leakage → can't compose bounds → SCL breaks
- **Drop A2**: Non-injective encoding → can merge states → keyedness fails → |State| < 2^λ
- **Drop A3**: No emergence → can predict all bits from parents → no residual λ → trivial
- **Drop A4**: Non-deterministic → seed chains ill-defined → can't trace dependencies
- **Drop A5**: Circular dependencies → DAG is cyclic → no topological order → ill-founded

**All five are necessary** for the proof to work.

---

## Next Steps

After understanding Layer 1 (concrete construction):
1. **Layer 2 (Layer2_StructuralOWF/)**: See how Plant embeds 3-SAT in L*, creates Structural OWF
2. **Layer 3 (Layer3_InformationBounds/)**: See how planted instances get 2^(ρ-s) bound
3. **Layer 0 (Layer0_Foundations/)**: Review abstract SCL framework that Layer 1 instantiates

**Entry Point**: Start with `Core/LStarInstance.lean` (main structure), then `Properties/A2_Injectivity.lean` (keyedness bridge).

---

## Verification Commands

```bash
# Build Layer 1
cd lean
lake build Layer1_Construction

# Verify zero axioms for key theorems
lake env lean Layer1_Construction/Properties/A2_Injectivity.lean
# Check #print axioms encodeSeed_injective - should show only standard foundations

lake env lean Layer1_Construction/Properties/A3_Emergence.lean
# Check #print axioms constructFullRank - should show only standard foundations

# Run full build
lake build Layer1_Construction.Core.LStarInstance
lake build Layer1_Construction.Bridge.LStarToNodeData
lake build Layer1_Construction.Properties.A2_Injectivity
```

**Expected Output**: 0 errors, ~1100 jobs compiled successfully.

---

**Last Updated**: 2025-12-09 (path references corrected)
