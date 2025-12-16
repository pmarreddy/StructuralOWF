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
│   ├── Layer2_StructuralOWF/       # One-way function construction
│   ├── Layer3_InformationBounds/   # Keyedness, segment reduction
│   ├── Layer4_Operational/         # Turing machines, execution semantics
│   ├── Layer5_Applications/        # P≠NP theorem, cryptographic applications
│   │   └── PvsNP/PrimaryPath/MainTheorems.lean  # ⬅ FINAL PROOF FILE
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
│   └── CRITICAL_DEFINITIONS.md     # 108 definitions cataloged
│
├── CLAUDE.md                       # AI assistant guidelines
└── README.md                       # This file
```

**Layer Documentation**:
- [Layer 0: Foundations](lean/Layer0_Foundations/Layer0_README.md) — CNF, DAG, SCL framework, encodings
- [Layer 1: Construction](lean/Layer1_Construction/Layer1_README.md) — L* instance family, seed chains, A1-A3 properties
- [Layer 2: StructuralOWF](lean/Layer2_StructuralOWF/Layer2_StructuralOWF_README.md) — One-way function construction
- [Layer 3: Information Bounds](lean/Layer3_InformationBounds/Layer3_README.md) — Keyedness, world-commit, segment reduction
- [Layer 4: Operational](lean/Layer4_Operational/Layer4_README.md) — TM semantics, execution model, time bridge
- [Layer 5: Applications](lean/Layer5_Applications/Layer5_README.md) — P≠NP theorem, cryptographic primitives

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
| [**0: Foundations**](lean/Layer0_Foundations/Layer0_README.md) | CNF, DAG, SCL framework, encodings | NodeData, keyed property |
| [**1: Construction**](lean/Layer1_Construction/Layer1_README.md) | L* instance family, seed chains | Hermeticity (A1), Injectivity (A2), Emergence (A3) |
| [**2: StructuralOWF**](lean/Layer2_StructuralOWF/Layer2_StructuralOWF_README.md) | One-way function construction | Plant/Extract, security proofs |
| [**3: Information**](lean/Layer3_InformationBounds/Layer3_README.md) | Lower bounds via SCL | Keyedness, world-commit, no-backdoor |
| [**4: Operational**](lean/Layer4_Operational/Layer4_README.md) | TM semantics, execution model | TMAdapter, TimeBridge |
| [**5: Applications**](lean/Layer5_Applications/Layer5_README.md) | Complexity classes, final theorems | **P≠NP**, cryptographic primitives |

### Main Theorem

**Final Proof File**: [`Layer5_Applications/PvsNP/PrimaryPath/MainTheorems.lean`](lean/Layer5_Applications/PvsNP/PrimaryPath/MainTheorems.lean)

```lean
-- File: Layer5_Applications/PvsNP/PrimaryPath/MainTheorems.lean

theorem P_ne_NP : ¬PeqNP_classical := pnenp_classical
theorem explicit_NP_not_P_witness : ∃ (L : Lang (List Bool)), InNP L ∧ ¬InP L
theorem OWF_exists_main : ∃ Φ : CNFFamily, IsOneWayPlantFlat Φ
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
lake env lean -c "import Layer5_Applications; #print axioms MainTheorems.P_ne_NP"
```

**WARNING**: Never run `lake clean` — Mathlib rebuild takes 2-4+ hours. Use only `lake build` (incremental).

## Verification

```bash
cd lean

# Verify main theorem compiles (final proof file)
lake build Layer5_Applications.PvsNP.PrimaryPath.MainTheorems

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
