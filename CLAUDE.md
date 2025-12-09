# CLAUDE.md

Guidance for AI assistants working on P≠NP via Semantic Conservation Law formalization.

## Critical Warnings

**NEVER run `lake clean`** — Mathlib rebuild takes 2-4+ hours. Use only `lake build` (incremental).

**NEVER create documentation files** unless explicitly requested.

**NEVER use tables in `paper/read-or-x.md`** — Use lists instead. Tables are allowed in Lean documentation and README files.

**NEVER revert files** (backups, git checkout, git revert) unless explicitly asked. Commit to fixes, don't abandon progress.

---

## Project Overview

**Claim**: P≠NP via information-theoretic approach (Semantic Conservation Law)

**Status**: Publication-ready
- ~94,000 lines Lean 4 (171 files)
- 0 sorries, 2 axioms
- Full build passes

**Key Resources**:
- `paper/read-or-x.md` — Mathematical exposition
- `lean/` — Mechanized proof (authoritative)
- `CONTRIBUTIONS.md` — Reviewer guidelines
- `docs/AI_REVIEW_GUIDE.md` — AI-assisted review guide

---

## Directory Structure

```
lean/
├── Layer0_Foundations/   — SCL framework
├── Layer1_Construction/  — L* construction
├── Layer2_StructuralOWF/ — One-way function
├── Layer3_InformationBounds/ — Lower bounds
├── Layer4_Operational/   — TM semantics
└── Layer5_Applications/  — P≠NP theorem + Crypto

paper/                    — Paper sources
docs/                     — Documentation
```

---

## Build Commands

```bash
cd lean
lake build              # Incremental build (fast)
lake build LayerName    # Specific layer
```

**FORBIDDEN**: `lake clean` (causes multi-hour rebuild)

---

## Trust Boundary (2 Axioms)

1. **`algspec_has_tm`** — Church-Turing bridge (any AlgSpec has TM implementation)
2. **`collision_indistinguishability_under_incomplete_observation`** — Semantic bound (A2 injectivity)

All standard CS/information-theory principles. See `docs/AXIOM_FINAL_COUNT.md`.

Note: `fg_lossless_encoding` was previously an axiom but is now fully proven (145-line theorem).

---

## Proof Architecture

```
OWF construction → Information must flow (≥2^Ω(n)) → Flow costs time
→ Poly-time impossible → OWF exists → FP≠FNP → P≠NP
```

**Core insight**: Information-theoretic impossibility (q + Φ ≥ R), not algorithmic analysis.

---

## Key Documentation

- `docs/PROOF_CONTROL_FLOW.md` — 11 critical theorems, proof spine
- `docs/CRITICAL_DEFINITIONS.md` — 108 definitions cataloged
- `docs/AXIOM_FINAL_COUNT.md` — Trust boundary details
