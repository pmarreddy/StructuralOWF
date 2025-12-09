# Layer 0: Semantic Conservation Law (SCL) Framework

**Purpose**: Abstract information-theoretic framework proving exponential state requirements independent of computational model.

**Location**: `lean/Layer0_Foundations/`

**Status**: ✅ Publication-ready (10/10 core files, zero custom axioms)

---

## Overview

Layer 0 provides the **model-independent foundation** for the P≠NP proof via information conservation. The Semantic Conservation Law (SCL) establishes that resolving computational problems with emergence rank R requires maintaining ≥ 2^λ distinguishable states, where λ (residual) = R - q (designated reads).

**Key Insight**: Information must be STORED (Way 1), RESOLVED (Way 2), or ELIMINATED (Way 3). The SCL framework blocks all three "Ways" simultaneously via A1-A5 properties, forcing exponential resource consumption.

**Layer Dependencies**:
- **Upstream**: Mathlib only (no custom dependencies)
- **Downstream**: Layer 1 (L* construction instantiates SCL), Layer 3 (information bounds apply SCL)

---

## Three Ways Framework

The proof works by exhaustively constraining ALL possible algorithmic strategies:

### Way 1: Storage (Blocked by A2 - Injectivity/Keyedness)

**Strategy**: "Store partial results and reuse them."

**Example**: Dynamic programming caches intermediate values to avoid recomputation.

**SCL Constraint**: Keyedness (A2) forces distinct assignments → distinct states.
```
Different assignments produce different seeds (encodeSeed injective)
→ Cannot merge computational states without losing information
→ Must maintain ≥ 2^λ distinct states simultaneously
→ Exponential space requirement
```

**Theorem**: `SCL_node` (SCLNode.lean) - If keyed, then |State| ≥ 2^λ.

**Why It Works**: Pigeonhole principle - 2^λ assignments need ≥ 2^λ storage locations.

### Way 2: Resolution (Blocked by A3 - Emergence)

**Strategy**: "Resolve bits incrementally through computation."

**Example**: SAT solver learns clauses gradually, reducing search space.

**SCL Constraint**: Emergence (A3) enforces R fresh bits per node must appear.
```
R bits emerge per node (cannot be derived from parents deterministically)
→ Must explicitly "create" these bits through designated reads
→ q designated reads can resolve at most q bits
→ Residual λ = R - q bits remain unresolved
→ 2^λ possibilities remain after q reads
```

**Theorem**: `SCL_node` (SCLNode.lean) - λ = R - q unresolved bits require 2^λ states.

**Why It Works**: Information theory - can't resolve R bits with only q < R reads.

### Way 3: Elimination (Blocked by FG - Frontier-Gate)

**Strategy**: "Prune search space via constraints."

**Example**: SAT solver uses unit propagation to eliminate incompatible assignments in bulk.

**SCL Constraint**: FG identity digest prevents cascading elimination.
```
Without FG: Single elimination cascades (prune one assignment → prune exponentially many)
With FG: Identity digest depends on ALL emergent bits globally (non-cascading constraint)
→ Cannot prune assignments in bulk (parity coupling prevents independence)
→ Must check each of 2^λ possibilities individually
```

**Mechanism**: FrontierGate.lean (Layer 2) - digest = parity(emergent bits) wired into seeds.

**Why It Works**: Global parity constraint couples all emergent bits → no local elimination possible.

---

## SCL Formula: q + Φ ≥ R

**Informal Statement**:
```
Bits resolved (q) + Log₂(simultaneously distinguishable artifacts) ≥ Emergence rank (R)
```

**Lean Formalization** (exponential form):
```lean
Fintype.card v.State ≥ 2 ^ lambda v    where lambda v = R v - q v
```

**Mathematical Equivalence**:
```
Paper:  q + log₂(Φ) ≥ R    (logarithmic inequality)
        ⟺  log₂(Φ) ≥ R - q
        ⟺  Φ ≥ 2^(R - q)

Lean:   |State| ≥ 2^λ      (cardinality inequality)
        where λ = R - q
```

**Why Exponential Form?**:
- **Constructive**: `Fintype.card` provides concrete counting via typeclass instances
- **Computational**: Enables `decide` tactics for verification
- **Direct**: Avoids real number encodings (log₂) - work with natural numbers
- **Pigeonhole**: Makes pigeonhole principle application explicit

**Variables**:
- **q (designated reads)**: Bits explicitly resolved by algorithm (e.g., reading input variables)
- **Φ (artifacts)**: Simultaneously distinguishable computational states (|State| in Lean)
- **R (emergence rank)**: Fresh bits that must emerge per node (full-rank emergence matrices)
- **λ (residual)**: Unresolved bits = R - q (drives exponential lower bound)

---

## SCL as Structural Parallel: Theoretical Precedents

**Why measure "bits resolved" instead of "steps taken"?**

This approach has strong theoretical pedigree. Multiple fields independently discovered that measuring **information acquired** yields valid lower bounds:

**Prior Lower Bound Techniques (1970s-1990s):**

- **Decision Trees**: Input queries (Wegener 1987)
- **Communication Complexity**: Bits exchanged (Yao 1979, Kushilevitz-Nisan 1997)
- **Pebbling Games**: Pebble placements (Lengauer-Tarjan 1982)
- **Branching Programs**: Path length (Barrington-Straubing 1991)
- **Resolution**: Clause width (Ben-Sasson-Wigderson 2001)

**SCL as Structural Parallel**: These techniques share a common pattern captured by SCL (q + Φ ≥ R). These are **structural parallels**, not derived instances:

| Technique | q | Φ | R |
|-----------|---|---|---|
| Decision trees | queries | log₂(tree nodes) | log₂(distinguishable inputs) |
| Pebbling | placements | pebble count | DAG complexity |
| Branching programs | path length | log₂(width) | log₂(input classes) |
| Communication | bits exchanged | log₂(rectangles) | log₂(partition number) |
| Resolution | proof length | clause width | log₂(search space) |
| TM observation | bits observed | log₂(configs) | emergence R_v [FORMALIZED] |

**This Work's Contribution:**

1. **Articulates common structure** across 5 prior techniques via SCL (q + Φ ≥ R)
   - This is **conceptual unification**—identifying shared intuition
   - We do NOT claim SCL formally subsumes prior techniques

2. **Formalizes TM observation paradigm**: bits observed = q, configs visited = 2^Φ
   - Bridges SCL to state compression bounds (keyedness, parity lower bounds)
   - Connects abstract bounds → concrete TM time complexity
   - Enables unconditional P≠NP via Structural OWF construction
   - **This is the only paradigm with mechanized Lean proofs**

**Summary:**

- **Observation principle**: Not novel — established 1970s-80s
- **SCL as structural parallel**: Novel — articulates common pattern across techniques
- **TM formalization**: Novel — mechanically verified SCL→TM bridge
- **Application to P≠NP**: Novel — unconditional TM bounds via OWF

**Implementation**: TM observation paradigm is implemented in `Layer4_Operational/TimeBridge/TMToExecutionPrefix.lean`:
- `ExecutionPrefixReal.revealedBits` → q (bits observed)
- `ExecutionPrefixReal.computedConfigs` → 2^Φ (configs visited)
- `tmExecutionToPrefix` → extracts observations from TM trace

See `TuringMachineSemantics.lean` for detailed references and proofs.

---

## File Organization

### SCL/ Subdirectory (Core Framework)

**Read Order**:
1. **NodeData.lean** - Node-level data structure (State, Assignment, keyed predicate)
2. **Helpers.lean** - Infrastructure lemmas (finite exponentiation, pigeonhole setup)
3. **SCLNode.lean** - Per-node bound (`SCL_node`: |State| ≥ 2^λ)
4. **SCLCut.lean** - Cut-level bound (`SCL_cut`: composition across DAG cuts)

**Purpose**: Prove exponential state requirement from keyedness (abstract framework).

**Key Theorem**: `SCL_node` - If `keyed v` then `Fintype.card v.State ≥ 2 ^ lambda v`.

**Proof Technique**: Pure counting (pigeonhole principle) - no axioms needed.

### Base/ Subdirectory (Foundational Definitions)

**Files** (no required read order):
- **CNF.lean** - CNF formulas, 3-SAT, satisfiability (target problem encoding)
- **DAG.lean** - Directed acyclic graphs (computational structure)
- **EncodedCNF.lean** - Encoded CNF representation with size bounds
- **FiniteEncoding.lean** - Fixed-width bitstring encodings (seed representation)
- **BoundedSecurityParam.lean** - Security parameter types (size indexing)
- **List/DedupRight.lean** - Transparent list deduplication (avoiding noncomputable helpers)

**Purpose**: Provide computational building blocks for L* construction (Layer 1).

---

## Key Concepts

### Keyedness (A2 Injectivity)

**Definition**: Different assignments produce distinguishable states for all known contexts.
```lean
def keyed (v : NodeData) : Prop :=
  ∀ (k : v.Known) (a₁ a₂ : Assign v),
    a₁ ≠ a₂ → v.state (k, a₁) ≠ v.state (k, a₂)
```

**Meaning**: Cannot merge computational histories without losing information.

**Consequence**: 2^λ assignments require ≥ 2^λ states (pigeonhole principle).

**Layer 1 Instantiation**: `encodeSeed` injectivity (A2_Injectivity.lean) - different (parents, emergent) → different seeds.

**Why Critical**: Blocks "Way 1: Storage" - cannot compress state space without errors.

### Emergence Rank (R)

**Definition**: Number of fresh bits that must emerge per node.

**Meaning**: Bits that cannot be deterministically computed from parent seeds alone.

**SCL Role**: Sets information requirement - must resolve R bits to fully determine node.

**Layer 1 Instantiation**: Emergence matrix rank (A3_Emergence.lean) - full-rank R×seedWidth matrices ensure R bits must be "created" via designated reads.

**Example**:
- R = 10 → 2^10 = 1024 possible emergent configurations per node
- Must resolve these 1024 possibilities to determine node's configuration

### Designated Reads (q)

**Definition**: Bits explicitly resolved by algorithm (e.g., reading input variables, querying oracles).

**Meaning**: Information acquired through explicit computational steps.

**SCL Role**: Upper bound on resolved information - can resolve at most q bits with q reads.

**Layer 3 Instantiation**: RWA (Receiving-Window Attribution) tracks designated reads per node (ConstraintSystem/ files).

**Residual**: λ = R - q bits remain unresolved → 2^λ possibilities remain.

### Residual (λ = R - q)

**Definition**: Unresolved bits = emergence rank minus designated reads.

**Meaning**: Information gap that cannot be closed via computation.

**SCL Bound**: 2^λ computational possibilities remain after q reads.

**Example**:
- R = 100 bits emergence
- q = 10 bits resolved via reads
- λ = 90 bits unresolved → 2^90 ≈ 1.24×10^27 states required

**Complexity Impact**: λ = Ω(n) → exponential bound, λ = Ω((log n)²) → quasi-polynomial bound.

---

## Trust Boundary

**Axioms**: ZERO custom axioms in Layer 0.

**Foundations Used**:
- `propext` - Propositional extensionality (standard Lean)
- `Quot.sound` - Quotient soundness (standard Lean)
- `Classical.choice` - Classical choice (standard Lean mathematics)

**Why Zero Axioms?**:
- **SCL_node**: Pure counting (pigeonhole principle from Mathlib)
- **SCL_cut**: Composition via cut properties (proven from node-level bound)
- **Helpers**: Infrastructure lemmas (finite arithmetic, proven from Mathlib)
- **Base definitions**: Constructive definitions (CNF, DAG, encodings)

**Axiom Eliminations** (vs. earlier drafts):
- `SecurityParam` arithmetic: Proven via bounded subtypes (not axiomatic)
- `ofBits_injective`: Proven from List injectivity (Mathlib)
- `normalize_semantically_faithful`: Proven via structural induction

**Verification**: Run `#print axioms SCL_node` → shows only standard Lean foundations.

---

## Paper References

**Primary Source**: "Read-or-x.md" (P≠NP proof paper)

**Layer 0 Correspondence**:

**§1.2 "Three Ways Framework"**:
- Lines 449-453: Way 1 (Storage) - corresponds to SCL_node with keyedness
- Lines 454-458: Way 2 (Resolution) - corresponds to residual λ = R - q
- Lines 459-463: Way 3 (Elimination) - blocked by FG (Layer 2), not Layer 0

**§7.2 "SCL Framework"**:
- Line 1840: q + Φ ≥ R inequality (corresponds to SCL_node exponential form)
- Line 1845: Per-node bound (SCLNode.lean)
- Line 1850: Cut composition (SCLCut.lean)

**§7.2.1 "Consolidated SCL Theorem"**:
- H1 (Hermeticity): Disjoint pools - instantiated in Layer 1 (A1_Hermeticity.lean)
- H3 (Keyedness): Enc injectivity - corresponds to `keyed` predicate (NodeData.lean)
- H4 (Emergence): Realizability - corresponds to emergence rank R (Layer 1 A3_Emergence.lean)

**§1.6 "Hartley Entropy"**:
- Φ_v = log₂|State| - Lean uses |State| directly (Fintype.card v.State)
- Zero-error, worst-case measure (not Shannon entropy)

---

## Design Rationale

### Why Layer 0 is Abstract

**Layer 0 Design**: Model-independent (no algorithms, no TM semantics, no operational details).

**Rationale**:
1. **Proof modularity**: SCL theorem proven once, instantiated many times (Layer 1 L* construction, future extensions)
2. **Trust minimization**: Core information-theoretic argument isolated from computational model details
3. **Generality**: Same framework applies to TM, RAM, circuit models (any model with state)

**Analogy**: Layer 0 is to P≠NP proof as linear algebra is to signal processing - foundational framework used everywhere, proven once.

### Why Exponential Form (vs. Logarithmic)

**Paper**: Uses q + log₂(Φ) ≥ R (logarithmic inequality).

**Lean**: Uses |State| ≥ 2^λ (exponential inequality).

**Why Different**?:
1. **Constructive counting**: `Fintype.card` provides computable cardinality (can run `decide` tactics)
2. **Avoid real numbers**: No Real.log encodings (purely natural number arithmetic)
3. **Direct pigeonhole**: 2^λ assignments fit into |State| states - pigeonhole principle is immediate
4. **Type-level guarantees**: Fintype ensures concrete finite representations (no infinite cardinalities)

**Mathematical Equivalence**: Taking log₂ of both sides recovers paper's form:
```
|State| ≥ 2^λ  ⟺  log₂|State| ≥ λ  ⟺  q + log₂|State| ≥ q + λ  ⟺  q + Φ ≥ R
```

### Why Separate SCL/ and Base/

**Design**: Layer 0 split into two subdirectories.

**Rationale**:
- **SCL/**: Pure abstract framework (NodeData, SCL theorems) - model-independent
- **Base/**: Computational primitives (CNF, DAG, encodings) - problem-specific but generic

**Benefits**:
1. **Conceptual clarity**: Separate information theory (SCL/) from data structures (Base/)
2. **Reusability**: Base/ primitives used throughout all layers (CNF, DAG ubiquitous)
3. **Modularity**: Could swap out Base/ implementations without affecting SCL theorems

---

## Significance in Proof Chain

**Layer 0 Role**: Establish that ANY algorithm satisfying A1-A5 properties requires ≥ 2^λ states.

**Proof Flow**:
```
Layer 0 (THIS LAYER): Abstract framework
  keyed v → |State| ≥ 2^λ  (pure counting)
  ↓
Layer 1: L* construction instantiates framework
  A1-A5 properties → keyed nodes (encodeSeed injective)
  ↓
Layer 2: Structural OWF construction
  Plant function f(r) = Plant(φ, r) with FG wiring
  ↓
Layer 3: Information bounds
  Apply SCL framework → solver requires ≥ 2^(ρ-s) operations
  ↓
Layer 4: Operational semantics
  TM steps ≥ information operations → time ≥ 2^(ρ-s)
  ↓
Layer 5: Complexity classes
  Poly-time < 2^(ρ-s) → contradiction → Structural OWF exists → P≠NP
```

**Without Layer 0**: Would need to prove exponential bound directly in operational model (entangles information theory with TM details, harder to verify).

**With Layer 0**: Clean separation - prove information bound abstractly (Layer 0), instantiate concretely (Layers 1-3), lift to operational semantics (Layer 4).

---

## Implementation Notes

### Fintype.card vs. Cardinality

**Choice**: Use `Fintype.card` (computable cardinality for finite types).

**Alternatives**:
- `Cardinal.mk` - Set-theoretic cardinality (works for infinite sets)
- Custom cardinality definition

**Why Fintype?**:
1. **Decidability**: Can run `decide` to verify finite cardinality claims
2. **Constructive**: Provides explicit bijections (not just existence)
3. **Type safety**: Fintype instance → guarantee of finiteness (no infinite surprises)
4. **Mathlib integration**: Rich API for finite type reasoning

### Keyed Predicate

**Definition**:
```lean
def keyed (v : NodeData) : Prop :=
  ∀ (a₁ a₂ : v.Assignment), a₁ ≠ a₂ → v.toState a₁ ≠ v.toState a₂
```

**Why This Form?**:
- **Injective mapping**: Encodes function injectivity (assignment → state is injective)
- **Contrapositive**: Can prove by contrapositive (equal states → equal assignments)
- **Layer 1 instantiation**: Corresponds to encodeSeed injectivity (A2)

---

## FAQ

**Q: Why is Layer 0 needed? Can't we prove bounds directly in Layer 3?**

A: Layer 0 provides **proof modularity**. The abstract SCL framework is proven once (with zero axioms), then instantiated in Layer 1 (L* construction). This separates information-theoretic reasoning (Layer 0) from construction details (Layer 1), making each layer simpler to verify. Additionally, Layer 0 could be reused for future constructions (different from L*) without reproving the core counting argument.

**Q: Why not use Shannon entropy instead of Hartley entropy (Φ = log₂|State|)?**

A: Shannon entropy is a probabilistic measure (average information). The SCL framework uses **Hartley entropy** (log₂ of support size), which is a **zero-error, worst-case** measure appropriate for deterministic lower bounds. We're proving that ALL algorithms (even the best one) require exponential resources, not that average-case algorithms do.

**Q: How does Layer 0 handle q (designated reads) if algorithms aren't specified yet?**

A: Layer 0 treats q as an **abstract parameter** (implicit in the `keyed` predicate via residual λ). The concrete q value is determined in Layer 3 (operational instantiation) where RWA tracks designated reads per algorithm execution. Layer 0's theorem is **parametric in q** - it holds for any q, with residual λ = R - q determining the bound.

**Q: What if an algorithm uses mixed strategies (partial storage + partial resolution + partial elimination)?**

A: The SCL framework handles **all strategies simultaneously** via the inequality q + Φ ≥ R. Any algorithm must either:
1. Store information (increasing Φ) - bounded by keyedness (Way 1)
2. Resolve information (increasing q) - bounded by emergence rank R (Way 2)
3. Eliminate possibilities (reducing Φ) - bounded by FG non-cascading constraint (Way 3)

The inequality ensures no "escape route" - must pay exponential cost via some dimension.

---

## Historical Notes

**Axiom Eliminations** (vs. earlier drafts):
1. `SecurityParam` axiomatization → proven via bounded subtypes (BoundedSecurityParam.lean)
2. `ofBits_injective` axiom → proven from List.map injectivity (FiniteEncoding.lean)
3. `normalize_semantically_faithful` axiom → proven via structural induction (CNF.lean)

**Design Evolution**:
1. Early drafts: SCL framework entangled with L* construction details (harder to verify)
2. Refactoring: Separated into Layer 0 (abstract) + Layer 1 (concrete instantiation)
3. Result: Zero axioms in Layer 0, cleaner trust boundary

---

## Next Steps

After understanding Layer 0 (abstract framework):
1. **Layer 1 (Layer1_Construction/)**: See how A1-A5 properties instantiate SCL framework in L* construction
2. **Layer 2 (Layer2_StructuralOWF/)**: See how FG wiring blocks "Way 3: Elimination"
3. **Layer 3 (Layer3_InformationBounds/)**: See how RWA operationalizes q (designated reads) for concrete algorithms

**Entry Point**: Start with `SCL/NodeData.lean` (data structures), then `SCL/SCLNode.lean` (main theorem).

---

## Verification Commands

```bash
# Build Layer 0
cd lean
lake build Layer0_Foundations

# Verify zero axioms
lake env lean Layer0_Foundations/SCL/SCLNode.lean
# Check #print axioms output - should show only propext, Quot.sound, Classical.choice

# Run tests
lake build Layer0_Foundations.SCL.SCLNode  # Builds and type-checks
```

**Expected Output**: 0 errors, ~400 jobs compiled successfully.

---

**Last Updated**: 2025-12-09 (path references corrected)
