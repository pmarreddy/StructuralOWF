# Contributing to the P≠NP Verification

## An Invitation to Peer Reviewers

This repository contains a fully mechanized Lean 4 formalization claiming to establish P≠NP via an information-theoretic approach called the Semantic Conservation Law (SCL). We invite rigorous peer review from the complexity theory, formal verification, and broader computer science communities. **Current focus: conceptual soundness** — is the proof architecture valid? Are definitions sound? Do critical lemmas hold? Let's first confirm we're heading in the right direction; once validated, we make it airtight. Detailed polish (missing cases, supporting lemmas, clarity, typos) is deferred until the core argument is validated.

**Three foundational shifts from current approaches** (see paper §1 and `docs/TRAPDOOR_OWF_MECHANISM.md`):
- *Structure, not algorithms*: Traditional asks "Can we invent a faster algorithm?" — we ask "What does problem structure require?"
- *Correctness, not speed*: Traditional proves "algorithms take too many steps" — we prove "correctness requires too many states"
- *Engineered, not natural*: Traditional analyzes messy natural problems (3-SAT, TSP) — we engineer L* to guarantee required properties by construction

**Three complementary resources**:
- **Quick intuition** (`docs/TRAPDOOR_OWF_MECHANISM.md`) — Start here for the core insight in 5 minutes
- **Paper** (`paper/read-or-x.md`) — Full mathematical exposition and proof narrative
- **Lean code** (`lean/`) — Machine-verified rigor (authoritative)

**Note on documentation**: We are actively refining documentation as issues are identified and resolved. Some docs may lag behind the Lean code. When in doubt, the Lean formalization is authoritative — it always reflects the current state of the proof.

**Why engage?** If this proof is correct, deep engagement positions you to:

- **Understand**: Master a new paradigm for complexity separations — be among the first to understand a resolution to the central open problem in theoretical CS

- **Extend**: Build on SCL/λ-parametric techniques across three major directions:

  - **Complexity Theory** — Apply to other open problems (open 50+ years):
    - Class separations: P vs BPP, NP vs PSPACE, NP vs coNP, PH collapse questions
    - Circuit lower bounds: Extend L* techniques to prove super-polynomial bounds
    - Fine-grained complexity: Characterize exact complexity via λ measurement
    - Derandomization: BPP = P via unconditional PRG from L* Structural OWF

  - **Cryptography** — Work with the first unconditional Structural OWF (all modern crypto follows from L*):
    - Minicrypt (12 primitives): PRG, PRF, PRP, MAC, Symmetric Encryption (CPA + AE), Commitment, Signatures (OTS + Merkle), Zero-Knowledge, Coin Flipping, MPC, UOWHF
    - Cryptomania (3 primitives): Public-Key Encryption, Key Exchange, Public-Key Signatures
    - Post-quantum: L* Structural OWF security is information-theoretic — resistant to quantum attacks

  - **Formal Methods** — Extend the mechanized verification:
    - Alternative provers: Port to Coq, Isabelle/HOL, Agda, F*
    - Axiom elimination: Prove the 2 remaining axioms from first principles
    - Proof automation: Develop tactics for SCL-style reasoning

- **Publish**: Write follow-on papers, surveys, tutorials, textbook chapters
- **Teach**: Develop courses on SCL methodology and information-theoretic complexity
- **Shape**: Influence research direction as an early expert in the paradigm
- **Contribute**: Earn recognition for review contributions (see Contribution Recognition below)

If correct, this would be one of the most significant results in theoretical computer science — proving both unconditional Structural OWF and P≠NP (a Clay Millennium Prize problem) together. It would also settle Impagliazzo's question: we live in **Cryptomania**.

**If this proof is flawed**, you will have contributed to the scientific process by identifying where information-theoretic approaches encounter obstacles.

Either outcome advances the field.

---

## Current Status & Priority

1. ✅ **Paper** — Mathematical exposition (`paper/read-or-x.md`)
2. ✅ **Mechanized** — Lean 4 formalization (~90K lines, 0 sorries, 2 axioms)
3. 🔍 **Community Audit** — Peer review: Stress-test definitions, axioms, and logic. Break it if you can. **← NOW**
4. 🔧 **Hardening** — Incorporate feedback, fix clarifications, prove axioms if possible, and strengthen arguments
5. 📝 **Formal Submission** — Submit to journal with community audit report

**Current priority**: Step 3 — conceptual soundness audit. Focus on: proof architecture, definitions, critical lemmas, axiom validity. Confirm the direction first; then we polish until airtight. Defer: missing cases, supporting lemmas, clarity, typos. Break the core argument first; polish later.

---

## About This Work

### What We Claim
A constructive proof establishing:
1. **Unconditional OWF**: The L* construction provides a one-way function without relying on unproven assumptions (factoring, discrete log, etc.)
2. **P≠NP**: Via the chain L* Structural OWF → FP≠FNP → P≠NP
3. **Explicit hard instances**: For all polynomials p(n), there exists n₀ such that for all n ≥ n₀, concrete instances require ≥2^Ω(n) steps — stronger than mere existence (∃L ∈ NP \ P)

### Impagliazzo's Five Worlds

Russell Impagliazzo (1995) identified five possible "worlds" based on cryptographic primitive existence:

| World | Condition | Cryptography |
|-------|-----------|--------------|
| **Algorithmica** | P = NP | Impossible |
| **Heuristica** | P ≠ NP, no OWF | None (worst ≠ average case) |
| **Pessiland** | Hard problems, no useful OWF | None (hard but unusable) |
| **Minicrypt** | OWF exist | Private-key crypto |
| **Cryptomania** | Structural OWF exist | Public-key crypto |

**This proof places us in Cryptomania**: L* provides both OWF (for Minicrypt) and Structural OWF (for public-key primitives). See `Layer5_Applications/Crypto/` for the complete cryptographic landscape derivable from L*.

### Proof Approach
1. **SCL Framework**: Information must be conserved — distinguishing k possibilities requires either resolving k bits or maintaining k artifacts (q + Φ ≥ R)
2. **L* Construction**: A language with planted structure requiring exponential information flow
3. **OWF Path**: L* → One-Way Function existence → FP≠FNP → P≠NP
4. **Cryptographic Applications**: L* Structural OWF → PRG → PRF → all of Minicrypt (12 primitives); L* Trapdoor Structural OWF → all of Cryptomania (3 primitives)
5. **Barrier Avoidance**: Explicitly designed to escape Relativization (via non-relativizing structure), Natural Proofs (via exponential sparsity), and Algebrization (via combinatorial counting). See **Section 12.6** of the paper.

### Why This Approach Works

**The key distinction: structural incompressibility vs computational hiding.**

Previous P≠NP attempts typically argue "algorithms can't find X" — a computational claim vulnerable to clever shortcuts. This proof argues "algorithms cannot compress 2^R configurations into fewer than 2^R states while maintaining correctness" — a structural counting argument.

| Approach | Example | Hardness type | Vulnerable to |
|----------|---------|---------------|---------------|
| **Hiding** | Factoring N=p×q | Computational | Shortcuts (Shor's algorithm) |
| **Structural incompressibility** | L* with collision indistinguishability | Counting (pigeonhole) | Nothing — compression causes correctness failure |

**How L* uses this:** The construction ensures 2^R configurations must map to distinct computational states (collision indistinguishability from A2 injectivity). Attempting to compress — using fewer states to represent more configurations — forces collisions where different inputs produce the same output, violating correctness. This is a pigeonhole argument, not an entropy bound.

**Why barriers don't apply:**
- **Natural Proofs**: Require properties useful against random functions. L* is sparse (exponentially few hard instances), so natural proof machinery doesn't engage.
- **Relativization**: Oracle arguments fail because L*'s hardness is structural (seed-determined addressing), not oracle-dependent.
- **Algebrization**: Algebraic extensions don't help because the bound comes from combinatorial counting (pigeonhole), not algebraic structure.

**The strategic path:** State compression impossibility → inversion hardness → OWF existence → FP≠FNP → P≠NP

See **§1** of the paper for the full development of this perspective.

### Verification Status (Current HEAD)
| Aspect | Status |
|--------|--------|
| Lines of Lean 4 code | ~90,000 |
| Custom axioms | 2 (all standard CS/counting principles) |
| Lean foundation axioms | Standard (propext, Classical.choice, Quot.sound) |
| Sorries (gaps) | 0 |
| Compilation | ✅ Full build passes |

### The 2 Custom Axioms (Trust Boundary)
1. **`algspec_has_tm`** (Church-Turing Bridge, Positive): Any algorithmic specification has a Turing machine implementation
2. **`tm_correctness_implies_realizesAllValuesFrom_flat_encoded`** (Church-Turing Bridge, Negative): Functional impossibility implies computational impossibility — TMs cannot bypass proven information-theoretic limits

Note: `fg_lossless_encoding` was previously an axiom but is now fully proven (145-line theorem). See `docs/AXIOM_FINAL_COUNT.md` for details.

Both axioms are standard computer science / information-theory principles, not novel assumptions. The proof also uses Lean's standard foundation axioms (propext, Classical.choice, Quot.sound), which are universally accepted in formalized mathematics.

### Falsification Criteria

**Three levels of critique** (see §3.6 in paper for formal definitions):

1. **Type 1 — Universal compression (approach-ending)**: Produce a compression that maps 2^R configurations to poly(n) states while preserving correctness, *regardless of what structural properties the construction satisfies*. This would show structural incompressibility fundamentally cannot deliver P≠NP—no set of properties can block compression. Implies P=NP.

2. **Type 2 — L*-specific compression (likely patchable)**: Compress L* itself by exploiting a loophole in this particular construction. This could motivate strengthening with additional properties (A6, A7, …) that block the compression. Does not imply P=NP.

3. **Repairable technical gaps**:
   - Show L* violates an A1-A5 property → refine construction or add properties
   - Find a gap in deriving SCL from A1-A5 → fortify the logical chain
   - Give a polynomial-time OWF inverter → adjust the Plant construction
   - Break the OWF → P≠NP reduction → repair the reduction

All critiques advance understanding; only Type 1 (universal compression) decisively kills the approach.

### Reviewer's Guide (Where to Focus)
If you want to break this proof efficiently, focus here:

1.  **The Compression Challenge**: Can you represent 2^R L* configurations in poly(n) states and still produce correct outputs? This is the core claim to attack.
2.  **The "Air Gap" (Layer 3 ↔ Layer 4)**: The connection between information-theoretic bounds (Layer 3) and the operational TM model (Layer 4) relies on `TimeBridge` and `TMAdapter`. Is the translation of "TM steps" to "information cost" rigorous?
3.  **The OWF Construction (Layer 2)**: Does `Plant(φ,r)` truly hide the preimage? If you can invert this function in polynomial time, the P≠NP claim falls.
4.  **Barrier Compliance (Section 12.6)**: We claim to escape Relativization, Natural Proofs, and Algebrization. Do we? Or is there a hidden oracle dependency?

**Key Documentation for Reviewers** (may not be fully up-to-date, but gives fast catchup):
- `docs/PROOF_CONTROL_FLOW.md` — Logical structure: 13 critical theorems forming the proof spine, how they compose to establish P≠NP
- `docs/CRITICAL_DEFINITIONS.md` — 108 definitions cataloged (46 core + 13 supporting + 49 moderate), organized by domain

---

## Why Your Review Matters

### Historical Context
Dozens of P≠NP proof attempts have failed over 50+ years. Common failure modes:
- Hidden non-standard definitions
- Gaps that compile but don't follow mathematically
- Incorrect complexity models
- Relativization/naturalization barriers violated unknowingly

### What Formal Verification Catches
- Type errors
- Logical inconsistencies within the formal system
- Missing cases in proofs

### What Formal Verification Does NOT Catch
- Whether definitions match standard complexity theory
- Whether the computational model is realistic
- Whether axioms are truly standard (vs disguised strong assumptions)
- Conceptual gaps that are technically well-typed

**This is why human review is essential.** The code compiling is necessary but not sufficient.

---

## We Remain Humble

Given the extraordinary nature of this claim and the history of failed attempts:

- We **believe** this proof is sound, but do not **assert** certainty
- We actively seek reviewers who will try to break it
- We prefer to be disproven (if wrong) quickly rather than slowly
- Finding an error is a scientific contribution, not an embarrassment

The worst outcome is a flawed proof that wastes the community's time. Help us avoid that.

---

## Contribution Recognition

Three levels based on scope and criticality:

1. **Co-Authorship** — Architectural (layer/framework rebuild) → Named author
2. **Special Thanks** — Critical lemma (must fix for proof to hold) → Named in paper with details
3. **Thanks** — Non-critical lemma, missing cases in a critical lemma, non-critical issues that must be addressed → Listed in general thanks

We err toward generosity for Special Thanks and Thanks, but remain stringent on Co-authorship.

**What counts**: These tiers recognize contributions to the Lean formalization — the mechanized proof. Paper exposition, documentation clarity, and presentation improvements are appreciated and acknowledged informally, but the formal recognition tiers above apply specifically to proof correctness. The paper provides intuition; for verification, use the Lean code.

### Co-Authorship
**Scope**: Architectural — requires layer-level or framework-level rebuild.

Without your contribution, the proof would be invalid. Examples: SCL framework unsound, OWF construction invertible, λ collapses to poly.

Co-authorship requires intellectual contribution comparable to original authorship.

**Process**: Co-authorship discussions occur only after: (1) issue confirmed as architectural, AND (2) fix merged into Lean codebase and paper.

### Special Thanks (Named in Paper)
**Scope**: Critical lemma — a lemma that must be fixed for the proof to hold.

Finding the issue earns Special Thanks even without implementing the fix.

Proving an axiom (eliminating it from the trust boundary) also earns Special Thanks.

Complete Tier-1 (publication-standard) review of the entire proof earns Special Thanks — single reviewer or team (first 3).

Independent reimplementation in another proof assistant (Coq, Isabelle, etc.) earns Special Thanks.

Detailed educational write-up that helps others understand the proof earns Special Thanks.

**Format**: "Special thanks to [Name] ([Affiliation]) for [specific contribution]"

### Thanks
**Scope**: Non-critical but needed.

Missing cases in a lemma, edge conditions, non-critical assumptions, build fixes.

Listed in a general "Thanks to reviewers" section.

### Duplicate Reports

When multiple reviewers independently find the same issue:

- **Credit goes to the first complete report** (timestamp of GitHub Issue or email)
- **"Complete"** means: clear description, location identified, explanation of why it's an error
- **Partial credit**: If reviewer A identifies the symptom and reviewer B identifies the root cause, both receive Special Thanks with their respective contributions noted
- **Good faith**: If you see an open issue discussing a problem, add to that thread rather than opening a duplicate

### Final Discretion

All recognition decisions are at the authors' final discretion. We commit to:
- Good faith evaluation of all contributions
- Transparent communication about decisions
- Erring toward generosity for Special Thanks and Thanks, but stringent on Co-authorship

We will not engage in disputes about credit allocation. Our decisions are final.

---

## Reporting Guidelines

### Before You Report an Issue

**Cross-check from multiple angles.** Before reporting, especially for potential proof-breaking issues:

1. **Verify in the Lean code** — Does the issue manifest in the mechanized proof, or only in your interpretation of the paper? The Lean code is authoritative; the paper provides intuition.
2. **Construct a counterexample** — Can you provide a concrete instance that breaks the claimed property? Vague concerns are harder to address than specific failures.
3. **Check the paper's explanation** — Have you read the relevant section in `paper/read-or-x.md`? The paper often addresses subtleties that aren't obvious from the Lean code alone.
4. **Cross-check with AI assistants** — Use multiple AI models (Claude Opus 4.5, ChatGPT 5.1, Gemini 3.0 Pro) to stress-test your finding. Don't take the first answer at face value — drill down with specific questions, ask for counterexamples, and verify the AI's reasoning. See `docs/AI_REVIEW_GUIDE.md` for recommended approach.
5. **Try to break your own objection** — Before reporting, spend 10 minutes trying to disprove your own finding. If you can't break it, it's more likely to be real.

We welcome reports even when uncertain, but thorough self-verification helps everyone. False alarms are fine; we'd rather hear "I think this might be wrong because X, Y, Z" than silence.

**In the age of AI, fixing issues is more or less straightforward — identifying them is the hard part.** Especially in a mechanized Lean formalization, the real intellectual contribution needed now is finding where the proof breaks. 

### Responsible Disclosure

For potential proof-breaking issues:
- **Private disclosure welcome**: Email if you prefer not to post publicly until confirmed
- **No embargo required**: You may discuss findings publicly at any time — we do not request silence
- **Coordination appreciated**: If you plan to publish a refutation paper, a heads-up allows us to respond or acknowledge in the same venue

### Response Expectations

As a single researcher with limited resources, I must prioritize. My primary goal is to prove or disprove this theory — everything else is secondary.

Expect at minimum one week for initial response. May vary based on:
- **Severity**: Critical issues get priority
- **Workload**: Resources are genuinely limited
- **Clarity**: If I can't understand the report, I can't respond — clear, specific reports get faster attention
- **Already resolved**: Duplicates or fixed issues may get brief responses or no response

I want to address every report and satisfy every reviewer, but in the real world that may not always be possible. I remain open to being convinced if I initially disagree.

### If the Proof Breaks

If a fatal, unfixable flaw is found:
- We will publicly acknowledge the error and credit the discoverer
- We will document what went wrong for the benefit of future attempts
- The repository will be updated to reflect the status
- This is a valid scientific outcome — better to know than not know

### Out of Scope

The following are **not** errors and won't receive issue responses:
- Stylistic preferences ("I would have structured this differently")
- Requests for alternative proof approaches ("Why not use X instead?")
- Philosophical objections to formalization ("Lean proofs aren't real math")
- Concerns already addressed in the paper or documentation

For now, we focus on **correctness**, not style or alternative approaches.

### Derivative Work

This work is open for academic use. You may:
- Build on these techniques for your own research
- Publish papers extending the methodology
- Fork and modify (with appropriate citation)

Standard academic citation norms apply. If you publish work substantially derived from this proof, citation is expected.

---

## What to Scrutinize

### Priority Review Areas

**Layer 0 — Foundations**
- Is `NodeData` a standard computational model?
- Does collision indistinguishability (injectivity) match standard definitions?
- Is the SCL conservation law a theorem or hidden assumption?

**Layer 1 — L* Construction**
- Do A1-A3 properties (Hermeticity, Injectivity, Emergence) hold?
- Is `encodeInjectivity` (seed encoding injective) proven correctly?
- Is the SeedChain/EmergenceMatrix construction sound?

**Layer 2 — OWF Construction**
- Does `Plant(φ,r)` constitute a valid one-way function?
- Is the FrontierGate mechanism sound?
- Does the Witness Extractor correctly recover witnesses from inversions?

**Layer 3 — Information Bounds**
- Is `R_of_flat` (emergence rank definition) correctly specified?
- Does SegmentReduction correctly establish 2^(ρ-s) bounds?
- Is the world-counting argument valid?

**Layer 4 — Operational**
- Is the TM model standard?
- Does TimeBridge correctly translate steps to information cost?
- Does `algspec_has_tm` (Church-Turing bridge) encode any hidden assumptions?

**Layer 5 — Complexity Separation**
- Does ParametricBitstringBridge correctly connect OWF to P≠NP?
- Are complexity class definitions standard (Arora-Barak, Sipser)?
- Does the final argument actually establish P≠NP?

**Layer 5 — Cryptographic Applications** (`Layer5_Applications/Crypto/`)
- Do the 20 reduction axioms (17 Minicrypt + 3 Cryptomania) correctly cite standard literature?
- Is the Structural OWF construction sound?
- Are the 15 cryptographic primitives correctly derived from L* Structural OWF?

**The 2 Custom Axioms** (`algspec_has_tm`, `tm_correctness_implies_realizesAllValuesFrom_flat_encoded`)
- Are these truly standard principles?
- Could any be encoding non-trivial assumptions?
- Are they necessary, or could they be proven?

### Suggested Review Path
```
1. paper/read-or-x.md          — Mathematical exposition
2. lean/Layer0_Foundations/    — Core definitions
3. lean/Layer5_Applications/   — Final theorem
4. Work backwards through layers as needed
```

---

## How to Contribute

### Reporting Issues
- **GitHub Issues**: Technical findings, questions, suggestions
- **Discussions**: Exploratory questions, clarification requests
- **Private**: Open a private security advisory on GitHub for sensitive disclosures

### Issue Format
```markdown
## Summary
[One sentence description]

## Commit Reviewed
[Output of `git rev-parse --short HEAD`, e.g., 2bb3560]

## Location
[File path and line numbers, or theorem name]

## Details
[Full explanation of the issue]

## Severity Assessment
- [ ] Proof-breaking (invalidates P≠NP)
- [ ] Significant (requires correction but not fatal)
- [ ] Minor (typo, clarity, style)

## Suggested Fix (if any)
[Your proposed solution]
```

**Why commit matters**: The codebase may evolve. Recording the commit ensures we can reproduce your findings and verify whether fixes have been applied.

### Review Discussions
We welcome:
- Questions about definitions and their standard equivalence
- Requests for clarification on proof steps
- Comparisons to other P≠NP attempts
- Discussion of potential extensions

---

## Timeline Considerations

This is an open review with no deadline. However:

**The intellectual incentive favors early engagement.**

If this proof is correct, the techniques generalize. The λ-parametric framework and SCL methodology could apply to:
- P vs BPP
- NP vs PSPACE
- Other long-standing separations

Researchers who deeply understand this approach early will be best positioned to:
- Extend these techniques to other problems
- Publish follow-on results
- Shape the research direction

Those who engage later may find the landscape already explored.

---

## Frequently Asked Questions

**Q: Why should I believe this attempt is different?**

A: **Don't believe — verify.** This attempt differs in specific, falsifiable ways:
- **Fully Mechanized**: The entire logical chain is machine-checked in Lean 4 (0 sorries).
- **Barrier-Aware**: It explicitly addresses why it escapes Relativization, Natural Proofs, and Algebrization (see §12.6).
- **Constructive**: It doesn't just prove separation; it provides the explicit hard instances.
- **Minimal Axioms**: It relies on only 2 custom axioms, both grounded in standard theory.

**Q: How long will review take?**

A: Depends on depth. Surface review: days. Deep verification: weeks to months. We recommend starting with the paper, then diving into Lean for areas of concern.

**Q: What if I find something but I'm not sure it's an error?**

A: Report it anyway. We prefer false alarms to missed issues. Open a Discussion thread if uncertain.

**Q: Can I review anonymously?**

A: Yes for the review process. Attribution in Special Thanks/Acknowledgments requires identification.

**Q: What background do I need?**

A: Ideal: complexity theory + Lean 4. Useful: either one. The paper (read-or-x.md) is accessible to complexity theorists without Lean knowledge.

---

## Building and Exploring

### Prerequisites
- Lean 4 v4.25.1 (via [elan](https://github.com/leanprover/elan))
- Mathlib4 (pinned to specific commit in `lake-manifest.json`; **do not update** dependencies manually)
- ~16GB RAM recommended (Mathlib is large)

See `lean/lean-toolchain` for the exact Lean version. Mathlib dependencies are cached; first build downloads ~2GB.

### Build Commands
```bash
cd lean                 # IMPORTANT: run from lean/ directory
lake build              # Full incremental build (fast after first run)
lake build LayerName    # Specific layer
```

**Warning**: **NEVER** run `lake clean` — Mathlib rebuild takes 2-4+ hours. Use only `lake build` (incremental).

### Key Files
```
paper/read-or-x.md                           — Main paper
lean/Layer5_Applications/PvsNP/PrimaryPath/  — P≠NP theorem
lean/Layer5_Applications/Crypto/             — Cryptographic applications (Minicrypt + Cryptomania)
lean/Layer0_Foundations/SCL/                 — Core framework
docs/AXIOM_FINAL_COUNT.md                    — Trust boundary details
```

---

## Final Note

We have done our best to produce a correct, verifiable proof — checked mechanically, reviewed manually, and stress-tested. But we are not infallible.

The history of P≠NP attempts teaches humility. Many brilliant researchers have believed they had proofs, only to find subtle errors. We may be in that category.

**Your job is to find out.**

If you find an error, you advance science. If you verify correctness, you witness history. Either way, your engagement matters.

Thank you for your time and rigor.

---

*This document will be updated as the review process evolves. Last updated: 2025-12-09*
