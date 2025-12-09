import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! ## TimingModel: Runtime Model Scaffold (Axiom-Free)

**Purpose**: Lightweight datatypes for runs, segments, strategies without committing to specific machine model.

**Key structures** (§7, Appendix C):
- Strategy: Single-run vs restart lane classification
- Segment: Work unit with digestOperations counter
- DeterministicRun: Run skeleton (strategy, segmentCount, time)

**Design philosophy**: Axiom-free scaffold—proof obligations developed in Foundations layer to keep Security/FrontierGate modules clean.

**Main definitions**: Strategy (inductive), Segment (structure), DeterministicRun (structure)

**Trust boundary**: 0 axioms - pure definitions

See Layer3_InformationBounds/Layer3_README.md §Support Infrastructure.
-/

namespace LStar.StructuralOWF.Foundations

/-- Which lane a run uses, abstracted for the reduction. -/
inductive Strategy
  | singleRun
  | restart
  deriving DecidableEq, Repr

/-- A coarse segment of work within a deterministic run. -/
structure Segment where
  digestOperations : Nat := 0
  deriving DecidableEq, Repr

/-- Deterministic run skeleton for an algorithm `A` on input `X`. -/
structure DeterministicRun (A X : Type) where
  strategy : Strategy := .singleRun
  segmentCount : Nat := 0
  preFinalAgreement : Nat := 0
  time : Nat := 0
  deriving Repr

/-- Placeholders for algorithm classes; details live in Probability. -/
abbrev Algorithm := Unit
abbrev UniformAlgorithm := Unit

namespace TimingModel

/-!
Proof obligations to be developed here (no axioms):

- segment_count_lower_bound
- parity_cost_per_segment
- per_instance_deterministic_bound

These will depend on FrontierGate invariants and Phase 3’s SeedChain
bit layout; they are left as targets to implement in this module.
-/

open scoped BigOperators
open Finset
open Classical

/-- Number of digest units (work items) assigned to a segment `i` via an
assignment function `assign : Fin b → Fin run.segmentCount`. Each `k : Fin b`
represents one required unit of parity work. -/
def assignedCount
    {A X : Type} (run : DeterministicRun A X)
    (b : Nat) (assign : Fin b → Fin run.segmentCount)
    (i : Fin run.segmentCount) : Nat :=
  Fintype.card {k : Fin b // assign k = i}

/-- Sum of fiber cardinalities equals the domain cardinality. -/
theorem sum_assignedCount_eq
    {A X : Type} (run : DeterministicRun A X)
    (b : Nat) (assign : Fin b → Fin run.segmentCount) :
    (∑ i : Fin run.segmentCount, assignedCount run b assign i) = b := by
  classical
  -- Rephrase as a sigma-type cardinality over the fibers
  have : (∑ i : Fin run.segmentCount, Fintype.card {k : Fin b // assign k = i}) =
      Fintype.card (Sigma fun i : Fin run.segmentCount => {k : Fin b // assign k = i}) := by
    simp [Fintype.card_sigma]
  -- Construct an equivalence from the sigma of fibers to the domain `Fin b`
  let φ : (Sigma fun i : Fin run.segmentCount => {k : Fin b // assign k = i}) ≃ Fin b :=
    { toFun := (fun p => p.2.1)
    , invFun := (fun k => ⟨assign k, ⟨k, rfl⟩⟩)
    , left_inv := by
        intro p; cases p with
        | mk i hk =>
          cases hk with
          | mk k hk =>
            cases hk; rfl
      , right_inv := by
        intro k; rfl }
  -- Apply cardinality congruence
  have : (∑ i : Fin run.segmentCount, assignedCount run b assign i) = Fintype.card (Fin b) := by
    simpa [assignedCount] using this.trans (Fintype.card_congr φ)
  simpa using this

/-- From an assignment of `b` work units to segments and per-segment lower
bounds, the total parity operations across segments is at least `b`. -/
theorem total_parity_ops_ge_of_assignment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (b : Nat) (assign : Fin b → Fin run.segmentCount)
    (perSeg : ∀ i, assignedCount run b assign i ≤ (segments i).digestOperations) :
    (∑ i, (segments i).digestOperations) ≥ b := by
  classical
  -- Sum lower bound by per-segment bounds
  have hsum : (∑ i, assignedCount run b assign i) ≤ ∑ i, (segments i).digestOperations := by
    exact Finset.sum_le_sum (by intro i _; exact perSeg i)
  -- Replace LHS by `b` using fiber-cardinality identity
  simpa [sum_assignedCount_eq run b assign] using hsum

/-- If for every segment `i` the fiber `{k // assign k = i}` admits an
    injection into `Fin (segments i).digestOperations`, then the per-
    segment lower bounds needed by `total_parity_ops_ge_of_assignment`
    hold. This isolates the combinatorial core: per-bit distinct unit of
    work embeds into the segment’s parity operation budget. -/
theorem perSeg_from_injection
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (b : Nat) (assign : Fin b → Fin run.segmentCount)
    (i : Fin run.segmentCount)
    (inj : {k : Fin b // assign k = i} ↪ Fin (segments i).digestOperations) :
    assignedCount run b assign i ≤ (segments i).digestOperations := by
  classical
  -- Cardinality of a finite set injects into `Fin n` ⇒ size ≤ n
  have hcard : Fintype.card {k : Fin b // assign k = i} ≤
      Fintype.card (Fin (segments i).digestOperations) := by
    refine Fintype.card_le_of_injective (fun x => inj x) ?hInj
    intro a b h; exact inj.inj' h
  simpa [assignedCount, Fintype.card_fin] using hcard

/-- If there is an injection from a fiber `{k // assign k = i}` into `Fin (2^s)`,
    then the fiber size is at most `2^s`. This is the generic counting step
    used to derive per‑segment capacity `assignedCount ≤ 2^s` from a projection. -/
theorem assignedCount_le_two_pow_of_inj
    {A X : Type} (run : DeterministicRun A X)
    (rho s : Nat) (assign : Fin (2 ^ rho) → Fin run.segmentCount)
    (i : Fin run.segmentCount)
    (inj : {k : Fin (2 ^ rho) // assign k = i} ↪ Fin (2 ^ s)) :
    assignedCount run (2 ^ rho) assign i ≤ 2 ^ s := by
  classical
  have : Fintype.card {k : Fin (2 ^ rho) // assign k = i} ≤
         Fintype.card (Fin (2 ^ s)) := by
    exact Fintype.card_le_of_injective (fun x => inj x) (by intro a b h; exact inj.inj' h)
  simpa [assignedCount, Fintype.card_fin] using this

/-- A global injection of `b` work units into the disjoint union of
    per-segment budgets induces both an assignment function and fiberwise
    injections for each segment. -/
structure GlobalAssignmentInj
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment) (b : Nat) where
  inj : (Fin b) ↪ Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations)

/-- Build a `GlobalAssignmentInj` from any injective map assigning each
    work unit to a segment and an operation index in that segment. -/
def GlobalAssignmentInj.ofInjectiveMap
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment) (b : Nat)
    (m : Fin b → Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations))
    (hinj : Function.Injective m) :
    GlobalAssignmentInj run segments b :=
  { inj := ⟨m, hinj⟩ }

-- Note: legacy helper for building a global injection from fiber embeddings
-- has been removed (no current call sites).

/-- Canonical embedding `Fin t ↪ Fin n` when `t ≤ n`. -/
def finEmbeddingLe {t n : Nat} (hle : t ≤ n) : (Fin t) ↪ (Fin n) where
  toFun := fun k => ⟨(k : Nat), Nat.lt_of_lt_of_le k.isLt hle⟩
  inj' := by intro a b h; cases a; cases b; cases h; rfl

/-- If some segment has parity budget at least `b`, we can build a global
    injection of `b` work units by sending all units to that segment with
    distinct operation indices. -/
def GlobalAssignmentInj.ofBigSegment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment) (b : Nat)
    (i : Fin run.segmentCount) (hle : b ≤ (segments i).digestOperations) :
    GlobalAssignmentInj run segments b :=
  let emb := finEmbeddingLe hle
  let m : Fin b → Sigma (fun j : Fin run.segmentCount => Fin (segments j).digestOperations) :=
    fun k => ⟨i, emb k⟩
  GlobalAssignmentInj.ofInjectiveMap run segments b m (by
    intro ka kb h
    -- m ka = ⟨i, emb ka⟩ and m kb = ⟨i, emb kb⟩
    have hmk :
        @Sigma.mk (Fin run.segmentCount)
                  (fun j : Fin run.segmentCount => Fin (segments j).digestOperations)
                  i (emb ka)
      = @Sigma.mk (Fin run.segmentCount)
                  (fun j : Fin run.segmentCount => Fin (segments j).digestOperations)
                  i (emb kb) := by
      simpa [m] using h
    -- Project equality of second components under constant index `i`
    have hheq : HEq (emb ka) (emb kb) := (Sigma.mk.inj_iff.mp hmk).2
    have h_eq : emb ka = emb kb := by simpa [heq_eq_eq] using hheq
    exact emb.inj' h_eq)

/- From a global injection into a sigma of per-segment budgets, build a
    per-segment assignment and fiber injections.
    (Legacy helper removed; FrontierGate builds digest assignment directly.) -/

/- Existence of a segment with at least one unit of work when the
   total work is positive (uses the heavy‑segment lemma). -/
theorem exists_segment_with_op_ge_one
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (h_total_pos : (∑ j, (segments j).digestOperations) ≥ 1)
    (_h_single : run.strategy = .singleRun) :
    0 < run.segmentCount → ∃ i, (segments i).digestOperations ≥ 1 := by
  intro _hm
  classical
  by_contra hnone
  have hAllZero : ∀ i, (segments i).digestOperations = 0 := by
    intro i
    have hnot : ¬ (1 ≤ (segments i).digestOperations) := (not_exists).mp hnone i
    have hxlt : (segments i).digestOperations < 1 := Nat.lt_of_not_ge hnot
    exact Nat.lt_one_iff.mp hxlt
  have : (∑ j, (segments j).digestOperations) = 0 := by
    simp [hAllZero]
  have : 1 ≤ 0 := by simp [this] at h_total_pos
  exact (Nat.not_succ_le_self 0) this

/- Segment counting lower bound: if the total parity work across
   segments is positive, then at least one segment must exist. This
   lemma connects to FG+SeedChain by instantiating `segments` from the
   run’s decomposition and deriving the total from emergent slice
   obligations. -/
theorem segment_count_lower_bound
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (required : Nat)
    (h_required_pos : 0 < required)
    (h_total_ops : (∑ j, (segments j).digestOperations) ≥ required)
    (_h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 := by
  classical
  -- Case analysis on the number of segments.
  cases hcnt : run.segmentCount with
  | zero =>
    -- Restore the explicit ≤ chain using an explicit empty‑fiber argument
    have hsum_zero :
        (∑ j : Fin run.segmentCount, (segments j).digestOperations) = 0 := by
      classical
      -- With `segmentCount = 0`, every index `i : Fin 0` is impossible
      have hempty : ∀ i : Fin run.segmentCount, (segments i).digestOperations = 0 := by
        intro i
        -- contradiction from `i.1 < 0`
        have : i.1 < 0 := by simpa [hcnt] using i.2
        exact (Nat.not_lt_zero _ this).elim
      simp [hempty]
    -- required ≤ sum (from hypothesis), and sum = 0 ⇒ required ≤ 0
    have hreq_le_sum :
        required ≤ (∑ j : Fin run.segmentCount, (segments j).digestOperations) := by
      simpa using h_total_ops
    have hle : required ≤ 0 := by
      exact le_trans hreq_le_sum (by simp [hsum_zero])
    exact (lt_of_le_of_lt hle h_required_pos).false.elim
  | succ m =>
    exact Nat.succ_le_succ (Nat.zero_le m)

/- Corollary: if `b>0` work units are assigned to segments and each
   segment accounts for its assigned units in `digestOperations`, then a
   single-run must have at least one segment. -/
theorem segment_count_ge_one_of_assignment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (b : Nat) (hpos : 0 < b)
    (assign : Fin b → Fin run.segmentCount)
    (perSeg : ∀ i, assignedCount run b assign i ≤ (segments i).digestOperations)
    (h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 :=
  segment_count_lower_bound run segments b hpos
    (total_parity_ops_ge_of_assignment run segments b assign perSeg) h_single

/- Aggregate time lower bound from assigned work: if runtime is at least
   the sum of per-segment parity operations and `b>0` work units are
   assigned across segments with each segment shouldering at least its
   assignment, then total time is at least 1. -/
theorem time_ge_one_of_assignment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (b : Nat) (hpos : 0 < b)
    (assign : Fin b → Fin run.segmentCount)
    (perSeg : ∀ i, assignedCount run b assign i ≤ (segments i).digestOperations)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.time ≥ 1 := by
  have hsum_ge_b : b ≤ (∑ i, (segments i).digestOperations) :=
    total_parity_ops_ge_of_assignment run segments b assign perSeg
  have htime_ge_b : b ≤ run.time := le_trans hsum_ge_b time_ge_total_ops
  have hb_ge_one : 1 ≤ b := Nat.succ_le_of_lt hpos
  exact le_trans hb_ge_one htime_ge_b

-- Note: global-injection corollaries are provided in FrontierGate; here we
-- only keep the assignment-based primitives used there.

/-- Combinatorial segment lower bound from fiber capacity (power-of-two case).

    If `2^ρ` items are assigned to at most `run.segmentCount` buckets and each bucket
    holds at most `2^s` items, then `run.segmentCount ≥ 2^(ρ−s)`.

    Pure counting argument (no execution semantics):
    - Let `b = 2^ρ`, `cap = 2^s`, `k = run.segmentCount`.
    - By capacity: `b = Σ_i |fiber i| ≤ Σ_i cap = k·cap`.
    - Since `s ≤ ρ`, `b = 2^(ρ−s)·2^s`. If `k < 2^(ρ−s)`, then `k·2^s < 2^ρ`, contradiction.
-/
theorem segmentCount_ge_two_pow_diff_of_fiber_cap
    {A X : Type} (run : DeterministicRun A X)
    (rho s : Nat)
    (assign : Fin (2 ^ rho) → Fin run.segmentCount)
    (h_cap : ∀ i : Fin run.segmentCount,
      assignedCount run (2 ^ rho) assign i ≤ 2 ^ s)
    (h_le : s ≤ rho) :
    run.segmentCount ≥ 2 ^ (rho - s) := by
  classical
  -- Sum of fibers equals total
  have h_sum : (∑ i : Fin run.segmentCount, assignedCount run (2 ^ rho) assign i)
               = 2 ^ rho := by
    simpa using sum_assignedCount_eq run (2 ^ rho) assign

  -- Sum of fibers ≤ k * 2^s from capacity per bucket
  have h_sum_le : (∑ i : Fin run.segmentCount, assignedCount run (2 ^ rho) assign i)
                   ≤ run.segmentCount * 2 ^ s := by
    have : (∑ i : Fin run.segmentCount, assignedCount run (2 ^ rho) assign i)
            ≤ ∑ i : Fin run.segmentCount, (2 ^ s) := by
      exact Finset.sum_le_sum (by intro i _; exact h_cap i)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      using this

  -- Combine to get 2^rho ≤ k * 2^s
  have h_le_prod : 2 ^ rho ≤ run.segmentCount * 2 ^ s := by
    simpa [h_sum] using h_sum_le

  -- Contradiction if k < 2^(rho - s)
  by_contra h_not_ge
  have h_lt : run.segmentCount < 2 ^ (rho - s) := lt_of_not_ge h_not_ge
  have twoPowPos : 0 < 2 ^ s := Nat.two_pow_pos s
  have h_mul_lt : run.segmentCount * 2 ^ s < (2 ^ (rho - s)) * 2 ^ s := by
    exact Nat.mul_lt_mul_of_pos_right h_lt twoPowPos
  -- (rho - s) + s = rho (since s ≤ rho)
  have h_add : (rho - s) + s = rho := Nat.sub_add_cancel h_le
  have h_rhs_eq : (2 ^ (rho - s)) * 2 ^ s = 2 ^ rho := by
    calc (2 ^ (rho - s)) * 2 ^ s
        = 2 ^ ((rho - s) + s) := by simp [Nat.pow_add, Nat.mul_comm]
      _ = 2 ^ rho := by simp [h_add]
  have : run.segmentCount * 2 ^ s < 2 ^ rho := by simpa [h_rhs_eq] using h_mul_lt
  exact (not_lt_of_ge h_le_prod) this

/- Per-segment digest cost lower bound from an injection of `t` distinct
   unit tasks into the segment's parity operation budget. -/
theorem parity_cost_per_segment_from_inj
    (seg : Segment) (t : Nat)
    (inj : {_k : Fin t // True} ↪ Fin seg.digestOperations) :
    seg.digestOperations ≥ t := by
  classical
  -- Cardinality of fiber injects into `Fin seg.digestOperations` ⇒ t ≤ digestOperations
  have hcard :
      Fintype.card {k : Fin t // True} ≤
        Fintype.card (Fin seg.digestOperations) := by
    refine Fintype.card_le_of_injective (fun x => inj x) ?_
    intro a b h; exact inj.inj' h
  simpa [Fintype.card_fin] using hcard

/- Note: The aggregate per-instance deterministic lower bound is provided by
   fg_universal_work_bound (FrontierGate.lean), which gives segmentCount ≥ 1 ∧ time ≥ 1
   for FG-wired instances with explicit proofs.

   The bound run.time ≥ 1 for nontrivial computation is either:
   - Trivially true (any computation takes nonzero time by definition)
   - Or derivable from fg_universal_work_bound for FG-wired cases (the only cases used)
-/

end TimingModel


/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

end LStar.StructuralOWF.Foundations
