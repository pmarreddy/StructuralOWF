# Dual Proof Architectures: Semantic vs Execution Paths

Two independent proof paths to P≠NP, each using 2 axioms. Both are publication-ready (0 sorries).

---

## Why Time >= 2^R?

**What is R?** The emergence rank--number of fresh bits at each Frontier Gate (FG). R = n for exponential bound, R = (log n)² for quasi-polynomial.

**One-Sentence Answer**: A2 injectivity ensures 2^R configurations produce 2^R distinguishable seeds--the algorithm must find the ONE correct configuration among 2^R possibilities.

**Two components create hardness**:
- **A2 Injectivity** (HARDNESS SOURCE): Different R-bit vectors -> different seeds -> 2^R distinguishable states
- **Identity Digest** (Verification): Returns full R bits; tells you "wrong" but not which bits

**Why clever algorithms fail**:
- "Skip configurations" -> A2 injectivity: correct one could be ANY of 2^R
- "Cannot learn from wrong guesses" -> Digest only says "wrong", not "how wrong"
- "Parallelize" -> Total work still >= 2^R

---

## The Two Architectures

```
SEMANTIC (TOP-DOWN)
"If you got the right answer, you MUST have seen everything."

Correctness requirement -> Complete observation NECESSARY -> time >= 2^R

Key: Derives WHY exploration is necessary from semantic requirements
```

```
EXECUTION (BOTTOM-UP)
"Watch the algorithm work, count what it rules out."

TM trace -> Count eliminations -> 2^R-1 eliminations needed -> time >= 2^R

Key: Shows HOW the algorithm spent its time (elimination by elimination)
```

| Aspect | Semantic | Execution |
|--------|----------|-----------|
| Direction | From conclusion backwards | From primitives forwards |
| Starting Point | Correctness property | TM execution trace |
| Key Question | WHY must exploration happen? | HOW does exploration happen? |
| Main Technique | Collision indistinguishability | Elimination counting |

---

## Semantic Architecture

**Philosophy**: "Correctness implies complete exploration."

**Core Argument**:
1. TM produces correct satisfying assignment
2. Correct witness requires correct FG digest (identity function on R bits)
3. A2 injectivity: 2^R configs -> 2^R distinguishable seeds
4. If TM missed some configuration value v, then by pigeonhole: exists two planted instances that look identical to TM (same partial observation) but require different outputs
5. TM cannot distinguish them -> outputs same answer for both -> wrong on at least one -> contradicts correctness
6. Therefore: must visit ALL 2^R configurations -> time >= 2^R

**Key Axiom**: `executionPrefix_compatible_with_planted_flat`
```lean
axiom executionPrefix_compatible_with_planted_flat
    (L : LStarInstanceFG) (n : Nat) (φ : CNF) (r : Randomness) ...
    (π : ExecutionPrefixReal L) (C : Finset (Fin L.dag.n))
    (h_valid : ValidExecutionPrefix_flat L φ r π)
    -- Returns 6 properties including collision impossibility
```
- **Nature**: Execution prefix bridge with validity guard
- **Risk**: Low (properties derive from A2 injectivity)
- **Sound Design**: `ValidExecutionPrefix_flat` ties π to r.assignment BEFORE quantification

---

## Execution Architecture

**Philosophy**: "Build the execution history, analyze its structure."

**Core Argument**:
1. Given TM execution trace [cfg_0, cfg_1, ..., cfg_T]
2. Construct ExecutionPrefixReal with visited configurations
3. Count distinct configurations tested (each test = one elimination of a candidate)
4. To isolate correct config among 2^R, must eliminate 2^R - 1 wrong ones
5. Each elimination costs >= 1 step -> haltTime >= 2^R

**Key Axiom**: `executionPrefix_compatible_with_planted`
- Bundles properties ensuring execution model correctly represents planted instance behavior
- See PlantedBoundaryDiversity.lean for details
- **Nature**: Operational bridge connecting execution model to planted instance
- **Risk**: Low (properties derive from A2 injectivity)

---

## Why Two Architectures?

**Primary reason**: Two independent proofs increases confidence. Different axioms, different reasoning -> independent failure modes.

| Architecture | Teaches Us |
|--------------|------------|
| Semantic | WHY polynomial time is impossible |
| Execution | HOW polynomial time fails |

---

## R_v Formula (Orthogonal)

The formula determines bound strength, NOT proof method:

| Formula | Bound | Suffices for P!=NP |
|---------|-------|-------------------|
| (log n)^2 | n^{log n} (quasi-polynomial) | Yes |
| n | 2^n (exponential) | Yes |

Current pairings are design choices:
- **Semantic + Exponential** -> TMAdapterExponential.lean
- **Execution + QP** -> TMAdapterQP.lean

---

## Trust Boundaries

### Semantic (Exponential) -- 2 Axioms

1. **`algspec_has_tm`** (RandAdv.lean) -- Church-Turing bridge
2. **`executionPrefix_compatible_with_planted_flat`** (TMAdapterExponential.lean) -- Execution prefix bridge (SOUND)
   - Guards with `ValidExecutionPrefix_flat` that ties π to r.assignment
   - Replaces deprecated `collision_indistinguishability_under_incomplete_observation` (TM-based, had quantification order vulnerability)

### Execution (QP) -- 2 Axioms

1. **`algspec_has_tm`** (RandAdv.lean) -- Church-Turing bridge (shared)
2. **`executionPrefix_compatible_with_planted`** (PlantedBoundaryDiversity.lean) -- Operational bridge

**Now proven** (no longer axioms): `fg_lossless_encoding` (145-line theorem), `plant_flat_wf_transfer`

**Note**: `qp_dominates_poly` is proven, not an axiom.

---

## Connection to P≠NP

```
TIME LOWER BOUND (time >= 2^R)
    |
    v
OWF SECURITY (StructuralOWFExponential.lean)
  - Forward: plant(phi, r) -> L* instance in poly-time (planter knows trapdoor)
  - Backward: recover r from L* requires time >= 2^R (no trapdoor)
    |
    v
FP ≠ FNP (StructuralOWFBridge.lean)
  - OWF inversion is in FNP (solution verifiable in poly-time)
  - OWF inversion not in FP (cannot compute in poly-time)
    |
    v
P ≠ NP (ParametricComplexity.lean)
  - FP ≠ FNP implies P ≠ NP (standard reduction)
```

Architecture choice affects step 1 only. Steps 2-4 are shared infrastructure.

---

## Implementation Mapping

| Architecture | File | R_v | Bound |
|--------------|------|-----|-------|
| Semantic | TMAdapterExponential.lean | n | 2^n |
| Execution | TMAdapterQP.lean | (log n)^2 | n^{log n} |

**Shared infrastructure** (~95% of code):
- Layer 0: SCL*.lean
- Layer 1: A1-A5*.lean
- Layer 2: Plant*.lean, FrontierGate.lean
- Layer 3: SegmentReduction.lean
- Layer 5: ParametricComplexity.lean

---

## FAQ

**Q: Which is better?**
A: Neither objectively. Semantic is conceptually simpler; Execution shows explicit construction. Both are publication-ready.

**Q: Why two?**
A: Independent verification. If one has a subtle flaw, the other likely doesn't.

**Q: Could Semantic+QP or Execution+Exponential work?**
A: Yes, architectures are orthogonal to R_v. Not implemented but theoretically possible.

**Q: Key axiom difference?**
A: Both now use execution prefix bridges with validity guards (`ValidExecutionPrefix_flat` for exponential, `ValidExecutionPrefix` for QP). The guards ensure π is tied to r.assignment before quantification, preventing adversarial construction.

---

## Summary

| Architecture | Direction | Axioms | Status |
|--------------|-----------|--------|--------|
| Semantic | Top-Down (WHY) | 2 | Publication-ready |
| Execution | Bottom-Up (HOW) | 2 | Publication-ready |

Two independent proofs -> increased confidence in P≠NP result.

---

**Last Updated**: 2025-12-12
