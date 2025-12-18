# Reviewing with AI Assistants

AI assistants can significantly accelerate your understanding of this proof. We have tested and found the following models capable of engaging meaningfully with the theory:

**Recommended Models** (as of late 2025):
- **OpenAI**: ChatGPT 5.1 (Pro, Thinking mode)
- **Anthropic**: Claude Opus 4.5, Claude Sonnet 4.5
- **Google**: Gemini 3.0 Pro (Thinking mode)

*Model recommendations evolve rapidly; any reasoning-capable frontier model should suffice.*

**Important: Web vs Code Environments**

- **Web interfaces** (ChatGPT, Claude, Gemini): Upload `read-or-x.md` for theory review. Cannot browse directories or navigate the full 90k-line codebase.
- **Code environments** (Claude Code, Cursor, Codex): Full access to both paper and Lean codebase. Required for serious Lean code review.
- **Tested**: Claude Code (used to formalise this proof in lean). Others (Cursor, Codex) may work but are untested.

These models can help you:
- Understand the SCL framework and λ-parametric approach
- Navigate the proof structure across layers
- Identify potential weaknesses or gaps
- Verify your interpretation of definitions against standard theory
- Generate counterexample candidates to stress-test claims

---

## How to Use AI Effectively

**Don't accept the first answer.** AI models can be confidently wrong — they may fabricate lemma names, misquote definitions, or invent plausible-sounding but nonexistent theorems. Always:

1. **Drill down** — If the AI says "this looks correct," ask: "What specific assumption makes this work? What would break if that assumption failed?"
2. **Request counterexamples** — "Can you construct a concrete case where this lemma would fail?"
3. **Challenge the reasoning** — "You said X implies Y. Walk me through each step. Where is the weakest link?"
4. **Cross-validate** — Ask the same question to multiple models. If they disagree, investigate why.
5. **Verify against source** — AI summaries can drift from the actual Lean code. Always check the file directly for critical claims.

---

## Example Queries

```
Explain the SCL conservation law (q + Φ ≥ R) and why it implies
exponential lower bounds when λ = ω(log n).

The proof claims L* escapes Natural Proofs via sparsity.
What exactly is the sparsity argument? Could it fail?

In Layer 4, TimeBridge translates TM steps to information cost.
What are the assumptions? Is there a gap between operational
semantics and information flow?

The tm_correctness_implies_realizesAllValuesFrom_flat_encoded axiom
is framed as a Church-Turing bridge: functional impossibility implies
computational impossibility. Is this standard? What would reject it?
```

---

## Why This Works

This proof is complex (~90,000 lines of Lean), but the core ideas are accessible. AI assistants excel at:
- **Rapid orientation** — Getting up to speed on unfamiliar frameworks
- **Pattern matching** — Recognizing common proof techniques and potential issues
- **Socratic dialogue** — Helping you articulate and test your intuitions

The combination of AI-assisted exploration + human judgment + Lean verification is the fastest path to understanding (and potentially breaking) this proof.

**A personal note**: In my experience, reviewers not using AI will be ~3-10x slower than those using it effectively. As a single researcher, I could not have completed this formalization without AI assistance — it accelerated every aspect of the work: proof development, documentation, debugging, and stress-testing arguments. Like any tool, you must understand it and use it effectively — but once you do, the productivity gain is substantial. I encourage you to leverage these tools fully.

---

*See also: [CONTRIBUTIONS.md](../CONTRIBUTIONS.md) for full reviewer guidelines.*
