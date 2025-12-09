import Layer4_Operational.TuringMachine.TuringMachineSemantics
import Layer4_Operational.TuringMachine.TMEncoderDefs
import Layer0_Foundations.Base.CNF

/-! ## TMSemanticProperties: Basic TM Operational Lemmas (0 axioms)

**Purpose**: Provide helper lemmas about TM operational semantics.

**Key lemmas**:
- tm_at_zero_is_init: TM at step 0 is in initial configuration
- tm_zero_steps_no_change: TM with haltTime=0 produces initial witness
- tm_nontrivial_computation_base: Output change requires ≥1 step

**Trust boundary**: 0 custom axioms (pure lemmas from TM operational semantics)

**Note**: The properties tm_nontrivial_computation and tm_overhead remain as
definitional axioms in TMAxioms.lean. They capture semantic constraints about
what "computational work" means, similar to the Church-Turing thesis.

See Layer4_Operational/Layer4_README.md §TuringMachine/TMSemanticProperties.
-/

namespace LStar.StructuralOWF.Foundations

open Classical

variable {k : Nat} {states alphabet : Type}
variable [Fintype states] [DecidableEq states]
variable [Fintype alphabet] [DecidableEq alphabet]

/-! ## Basic TM Operational Lemmas -/

/-- **Lemma**: TM at step 0 is in initial configuration.

    **Statement**: TMConfig.run M 0 = TMConfig.init M

    **Proof**: By definition of run (Function.iterate 0 = id).
-/
lemma tm_at_zero_is_init (M : TuringMachine k states alphabet) :
  TMConfig.run M 0 = TMConfig.init M := by
  unfold TMConfig.run
  simp [Function.iterate_zero]

/-- **Lemma**: TM that halts immediately (haltTime = 0) has done no work.

    **Statement**: tmOutputWitness M 0 extractWitness = extractWitness (TMConfig.init M)

    **Proof**: By definition of tmOutputWitness and tm_at_zero_is_init.
-/
lemma tm_zero_steps_no_change (M : TuringMachine k states alphabet)
    (extractWitness : TMConfig M → Witness) :
  tmOutputWitness M 0 extractWitness = extractWitness (TMConfig.init M) := by
  unfold tmOutputWitness
  rw [tm_at_zero_is_init]

/-- **Theorem**: Output change requires at least 1 step.

    **Statement**: For a TM to produce output different from the initial configuration,
    it must execute at least 1 step.

    **Proof**: By contradiction. If haltTime < 1, then haltTime = 0, which means
    the output equals the initial witness (by tm_zero_steps_no_change).

    **Usage**: This is a base lemma. The full properties (tm_nontrivial_computation,
    tm_overhead) remain as definitional axioms in TMAxioms.lean since they require
    semantic constraints about what "meaningful computation" means.
-/
theorem tm_nontrivial_computation_base
    (M : TuringMachine 1 states alphabet)
    (haltTime : Nat)
    (extractWitness : TMConfig M → Witness)
    (h_diff : tmOutputWitness M haltTime extractWitness ≠ extractWitness (TMConfig.init M))
    : haltTime ≥ 1 := by
  by_contra h_contra
  push_neg at h_contra
  -- haltTime < 1 means haltTime = 0
  interval_cases haltTime
  -- Case: haltTime = 0
  have : tmOutputWitness M 0 extractWitness = extractWitness (TMConfig.init M) :=
    tm_zero_steps_no_change M extractWitness
  contradiction

/-! ## Placeholder TM Halting Lemmas

For "placeholder" TMs that immediately transition to halt state, we prove halting
via a single reusable lemma. This is used when constructing RandAdv instances
where the TM is structural scaffolding (e.g., verifiers, encodings).
-/

/-- **Lemma**: A TM whose δ always returns a halt state halts after ≥1 steps.

    **Purpose**: Proves halting for placeholder TMs that immediately enter halt.

    **Design**: Parametric over any TM where δ always produces a halt state,
    regardless of current state or tape contents. This is the common pattern
    for "structural" TMs in RandAdv constructions.

    **Proof**:
    1. After 1 step: state = (δ _ syms).1 ∈ halt (by h_immediate)
    2. By halt_persists: stays in halt for remaining steps

    **Usage**: Apply to any TM with `δ := fun _s _syms => (halt_state, _, _)`
-/
theorem immediate_halt_tm_halts
    {k : Nat} {states alphabet : Type}
    [Fintype states] [DecidableEq states]
    [Fintype alphabet] [DecidableEq alphabet]
    (M : TuringMachine k states alphabet)
    (h_immediate : ∀ (s : states) (syms : Fin k → alphabet), (M.δ s syms).1 ∈ M.halt)
    (cfg : TMConfig M)
    (t : Nat)
    (h_t : t ≥ 1) :
    ((TMConfig.step)^[t] cfg).state ∈ M.halt := by
  -- Decompose t = 1 + (t - 1)
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h_t
  rw [Nat.add_comm] at hn
  subst hn
  -- After 1 step, we're in halt
  have h_one_step : (TMConfig.step cfg).state ∈ M.halt := by
    unfold TMConfig.step
    simp only
    exact h_immediate cfg.state (fun i => cfg.tapes i (cfg.heads i))
  -- Iterate n more times, staying in halt by halt_persists
  rw [Function.iterate_add_apply]
  simp only [Function.iterate_one]
  exact LStar.StructuralOWF.Foundations.halt_persists M (TMConfig.step cfg) n h_one_step

/-- **Corollary**: Placeholder TM with specific Fin states halts after ≥1 steps.

    **Purpose**: Specialized version for common case where states = Fin m
    and halt = {⟨halt_idx, _⟩}.

    **Usage**: For TMs like `δ := fun _s _syms => (⟨1, h⟩, _, _)` with `halt := {⟨1, h⟩}`.
-/
theorem immediate_halt_tm_halts_fin
    {k m : Nat} {alphabet : Type}
    [Fintype alphabet] [DecidableEq alphabet]
    (M : TuringMachine k (Fin m) alphabet)
    (halt_idx : Fin m)
    (h_halt_eq : M.halt = {halt_idx})
    (h_immediate : ∀ (s : Fin m) (syms : Fin k → alphabet), (M.δ s syms).1 = halt_idx)
    (cfg : TMConfig M)
    (t : Nat)
    (h_t : t ≥ 1) :
    ((TMConfig.step)^[t] cfg).state ∈ M.halt := by
  apply immediate_halt_tm_halts M _ cfg t h_t
  intro s syms
  rw [h_halt_eq, Finset.mem_singleton, h_immediate]

/-! ## Axiom Audits

These lemmas use only standard Lean axioms (propext, Classical.choice, Quot.sound).
No custom axioms required.
-/

#print axioms tm_at_zero_is_init
#print axioms tm_zero_steps_no_change
#print axioms tm_nontrivial_computation_base
#print axioms immediate_halt_tm_halts
#print axioms immediate_halt_tm_halts_fin

end LStar.StructuralOWF.Foundations
