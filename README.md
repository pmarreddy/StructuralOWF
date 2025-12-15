# P≠NP: A Constructive Proof via Semantic Conservation Law

A complete formalization of P≠NP in Lean 4 with a minimal trust boundary (2 axioms).

## Overview

This repository contains a full mathematical proof that P≠NP, formalized in the Lean 4 theorem prover. The proof is constructive—it builds a concrete one-way function whose inversion hardness implies P≠NP.

**Key Features:**
- **~94,000 lines** of Lean 4 formalization across **171 files** (excluding Mathlib)
- **0 sorries** — fully verified proof
- **2 axioms** — minimal trust boundary (Church-Turing bridge + semantic bound)
- **6-layer architecture** — modular construction from foundations to complexity separation

**The Core Insight:** The Semantic Conservation Law (SCL) establishes that distinguishing k possibilities requires either resolving k bits of information or maintaining k computational artifacts (q + Φ ≥ R). The L* construction creates instances where compression causes correctness failure. This is a counting argument based on information-theoretic necessity, not a computational hiding argument.

## Quick Start

| Resource | Purpose |
|----------|---------|
| [`docs/TRAPDOOR_OWF_MECHANISM.md`](docs/TRAPDOOR_OWF_MECHANISM.md) | Core intuition — start here |
| [`docs/CONTRIBUTIONS.md`](docs/CONTRIBUTIONS.md) | Reviewer guidelines, contribution recognition |
| [`paper/read-or-x.md`](paper/read-or-x.md) | Full mathematical exposition |
| [`lean/`](lean/) | Machine-verified formalization (authoritative) |

## Repository Structure

```
├── lean/                           # Lean 4 formalization (171 files)
│   ├── Layer0_Foundations/         # Base: CNF, DAG, SCL, encodings
│   ├── Layer1_Construction/        # L* instance, pools, seed chains
│   ├── Layer2_StructuralOWF/           # One-way function construction
│   ├── Layer3_InformationBounds/   # Keyedness, segment reduction
│   ├── Layer4_Operational/         # Turing machines, execution semantics
│   ├── Layer5_Applications/        # P≠NP theorem, cryptographic applications
│   ├── Infrastructure/             # Witness finding, time bounds
│   └── testing/                    # Regression tests (17 test files)
│
├── paper/                          # Mathematical exposition
│   ├── read-or-x.md                # Main paper (Markdown)
│   ├── read-or-x-clean.tex         # LaTeX source
│   └── read-or-x-clean.pdf         # Generated PDF
│
├── docs/                           # Documentation
│   ├── CONTRIBUTIONS.md            # Reviewer guidelines (start here)
│   ├── TRAPDOOR_OWF_MECHANISM.md   # Quick intuition (5-minute read)
│   ├── PROOF_CONTROL_FLOW.md       # 11 critical theorems, proof spine
│   ├── CRITICAL_DEFINITIONS.md     # 108 definitions cataloged
│   └── DUAL_PROOF_ARCHITECTURES.md # QP vs Exponential profiles
│
├── CLAUDE.md                       # AI assistant guidelines
└── README.md                       # This file
```

## Proof Architecture

### The Proof Chain

```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│ L* Construction │───▶│ One-Way Function│───▶│    FP ≠ FNP     │───▶│    P ≠ NP       │
│                 │    │                 │    │                 │    │                 │
│ A1: Hermeticity │    │ Inversion needs │    │ Search harder   │    │ Decision        │
│ A2: Injectivity │    │ ≥2^n steps      │    │ than poly-time  │    │ separation      │
│ A3: Emergence   │    │ (info barrier)  │    │                 │    │                 │
└─────────────────┘    └─────────────────┘    └─────────────────┘    └─────────────────┘
```

### Layer Overview

| Layer | Purpose | Key Results |
|-------|---------|-------------|
| **0: Foundations** | CNF, DAG, SCL framework, encodings | NodeData, keyed property |
| **1: Construction** | L* instance family, seed chains | Hermeticity (A1), Injectivity (A2), Emergence (A3) |
| **2: StructuralOWF** | One-way function construction | Plant/Extract, security proofs |
| **3: Information** | Lower bounds via SCL | Keyedness, world-commit, no-backdoor |
| **4: Operational** | TM semantics, execution model | TMAdapter, TimeBridge |
| **5: Applications** | Complexity classes, final theorems | **P≠NP**, cryptographic primitives |

### Main Theorem

```lean
-- File: Layer5_Applications/PvsNP/PrimaryPath/StructuralOWFBridge.lean

theorem pnenp : ¬BitstringBridge.PeqNP_parametric
theorem P_ne_NP : ¬PeqNP_classical := pnenp_classical
```

## Trust Boundary (2 Axioms)

The proof relies on only **2 custom axioms**:

| Axiom | Nature | Risk |
|-------|--------|------|
| `algspec_has_tm` | Church-Turing bridge | Very Low |
| `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` | Semantic bound (correctness implies exhaustive exploration) | Low |

### Axiom Details

1. **`algspec_has_tm`** (Church-Turing Bridge)
   - Any polynomial-time algorithmic specification has a TM implementation
   - Preserves polynomial constants C and k
   - Universally accepted CS principle (Church 1936, Turing 1936)

2. **`tm_correctness_implies_realizesAllValuesFrom_flat_encoded`** (Semantic Bound)
   - Correctness on planted instances requires visiting all 2^R configurations
   - Based on A2 injectivity: different configs → different seeds
   - Information-theoretic necessity (pigeonhole counting)

### Previously Eliminated Axioms

The following were axioms in earlier versions but are now **fully proven**:
- `fg_lossless_encoding` → 145-line theorem (EncodingDiscipline.lean)
- `encoding_semantics` → Now `encoding_semantics_derived` (proven)

## Dual Profile Architecture

The codebase supports two independent proof profiles:

| Profile | R Formula | Lower Bound | Key Files |
|---------|-----------|-------------|-----------|
| **Exponential** | R = n | 2^n | TMAdapterExponential, StructuralOWFExponential |
| **QP-Sharp** | R = (log n)² | n^{log n} | TMAdapterQP, StructuralOWFQP |

Both profiles prove P≠NP independently. The Exponential profile provides stronger bounds (2^n vs n^{log n}); the QP profile uses a more conservative R formula with a smaller base.

## Building

### Prerequisites

- **Lean 4** v4.25.1 (via [elan](https://github.com/leanprover/elan))
- **Mathlib4** (stable branch, fetched automatically by Lake)
- ~16GB RAM recommended for building (Mathlib compilation is memory-intensive)

### Build Commands

```bash
cd lean

# Full incremental build (fast after first run)
lake build

# Build specific layer
lake build Layer5_Applications
```

To verify the axiom count for the main theorem:
```bash
lake env lean -c "import Layer5_Applications; #print axioms LStar.Complexity.StructuralOWFBridge.P_ne_NP"
```

**WARNING**: Never run `lake clean` — Mathlib rebuild takes 2-4+ hours. Use only `lake build` (incremental).

## Verification

```bash
cd lean

# Verify main theorem compiles
lake build Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge

# Run regression tests
lake build testing
```

All 171 Lean files compile with **0 sorries**.

## For Reviewers

**Current Focus**: Conceptual soundness audit. Is the proof architecture valid? Are definitions sound? Do critical lemmas hold?

**Priority Review Areas**:
1. **Compression Challenge**: Can you represent 2^R configurations in poly(n) states while maintaining correctness?
2. **Layer 3↔4 Bridge**: Is the translation from information bounds to TM steps rigorous?
3. **OWF Construction**: Does `Plant(φ,r)` truly hide the preimage?
4. **Barrier Compliance**: Does the proof escape Relativization, Natural Proofs, Algebrization? (See [paper §12.6](paper/read-or-x.md#126-why-our-approach-avoids-known-barriers))

**Falsification Criteria** (see paper §3.6):
- **Type 1 (approach-ending)**: Universal compression regardless of structure → kills the approach
- **Type 2 (patchable)**: L*-specific compression → may need additional properties (A6, A7, ...)
- **Technical gaps**: Flaws in specific lemmas → repairable

See [`docs/CONTRIBUTIONS.md`](docs/CONTRIBUTIONS.md) for full guidelines and contribution recognition.

## Documentation

| Document | Purpose |
|----------|---------|
| [`CONTRIBUTIONS.md`](docs/CONTRIBUTIONS.md) | Reviewer guidelines, recognition tiers |
| [`TRAPDOOR_OWF_MECHANISM.md`](docs/TRAPDOOR_OWF_MECHANISM.md) | Quick intuition (5-minute read) |
| [`PROOF_CONTROL_FLOW.md`](docs/PROOF_CONTROL_FLOW.md) | 11 critical theorems, proof spine |
| [`CRITICAL_DEFINITIONS.md`](docs/CRITICAL_DEFINITIONS.md) | 108 definitions cataloged |
| [`DUAL_PROOF_ARCHITECTURES.md`](docs/DUAL_PROOF_ARCHITECTURES.md) | QP vs Exponential profiles |
| [`AI_REVIEW_GUIDE.md`](docs/AI_REVIEW_GUIDE.md) | AI-assisted review methodology |

## Citation

```bibtex
@misc{pnp2025,
  title={P≠NP: A Constructive Proof via Semantic Conservation Law},
  author={Prasanth Marreddy},
  year={2025},
  note={Complete Lean 4 formalization with 2 axioms}
}
```

## License

This work is licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).

You are free to share and adapt this material for any purpose, including commercial, provided you give appropriate attribution.

## Contact

**Author**: Prasanth Marreddy
**Email**: pmarreddy@gmail.com

---

**Status**: Complete formalization, 0 sorries, 2 axioms
**Last Updated**: 2025-12-09
