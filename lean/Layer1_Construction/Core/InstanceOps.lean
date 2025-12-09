import Layer0_Foundations.Base.CNF
import Layer0_Foundations.Base.DAG
import Layer0_Foundations.Base.FiniteEncoding
import Layer1_Construction.Core.LStarInstance
import Layer1_Construction.Core.EmergenceMatrix
import Layer1_Construction.Core.Pools
import Layer1_Construction.Core.SeedChain
import Mathlib.Data.Finset.Basic

/-! ## InstanceOps: Operations on L* Instances

**Main Operations**: Essential computations on LStarInstanceFull for seed propagation and cut analysis.

**computeSeed**: Forward seed propagation
```lean
computeSeed L v hist assignment : Seed (seedWidth_v)
Formula: Seed_v = encodeSeed(hist, E_v · assignment)  (emergence matrix application + encoding)
```

**Algorithm**:
1. **Emergence**: emergent_v = E_v · assignment  (matrix-vector mult over GF(2))
2. **Encode**: Seed_v = encodeSeed(hist, emergent_v)  (pack parents + emergent bits)

**Key Property**: `computeSeed_deterministic` - Same inputs always give same output (A4 Closure).
Determinism crucial for OWF: Plant function f(r) must be deterministic (inverting nondeterministic
functions is ill-defined).

**frontier**: Cut-frontier extraction
```lean
frontier L C = {v ∈ V | v ∉ C ∧ parents(v) ⊆ C ∧ parents(v) ≠ ∅}
```

**Interpretation**: Information flow boundary.
- **v ∉ C**: Vertex outside cut (not resolved yet)
- **parents(v) ⊆ C**: All parents inside cut (inputs resolved)
- **parents(v) ≠ ∅**: Has parents (not source node)

**Role in SCL**: Frontier F(C) marks WHERE information flows—vertices whose seeds depend on
unresolved λ(C) bits from C. Enables compositional reasoning about information bottlenecks.

**Theorem: frontier_disjoint_cut**: frontier L C ∩ C = ∅ (immediate from definition).
Ensures clean separation for information accounting.

**Trust Boundary**: Pure functions (no axioms). computeSeed uses emergence matrix + encodeSeed,
frontier uses Finset.filter with decidable predicates.

**Paper**: §3 "Seed Propagation", §2.4.3 "Cut-Level Analysis", §7.2.1 "SCL at Cuts".

See Layer1_Construction/Layer1_README.md for seed chain mechanism and A4 Closure details.
-/

namespace LStar

open Finset

/- Instance utilities built on the core definition. -/

namespace LStarInstanceFull

variable (L : LStarInstanceFull)

/-- Compute seed for vertex `v` from parent history and local assignment via emergence. -/
noncomputable def computeSeed (v : Fin L.dag.n)
  (hist : ParentHistory L v)
  (assignment : Seed (L.seedWidth v)) : Seed (L.seedWidth v) :=
  let eSeed := EmergenceMatrix.apply (L.emergence v) assignment
  -- Convert emergent seed to vector of bits for encodeSeed
  let emergent : Vector Bool (L.R v) :=
    Vector.ofFn (fun j : Fin (L.R v) => ((eSeed.val >>> j.val) % 2 = 1))
  encodeSeed L v hist emergent

/-- Determinism of `computeSeed` (definitional). -/
theorem computeSeed_deterministic (v : Fin L.dag.n)
  (hist : ParentHistory L v) (assignment : Seed (L.seedWidth v)) :
  computeSeed L v hist assignment = computeSeed L v hist assignment := rfl

/-- Frontier at a cut `C` (paper-aligned): vertices not in `C` whose
    parents are all in `C` and with at least one parent (edge crossing). -/
def frontier (C : Finset (Fin L.dag.n)) : Finset (Fin L.dag.n) :=
  Finset.univ.filter (fun v => v ∉ C ∧ (∀ u ∈ L.dag.parents v, u ∈ C) ∧ (L.dag.parents v).Nonempty)

theorem frontier_disjoint_cut (C : Finset (Fin L.dag.n)) :
    Disjoint (frontier L C) C := by
  classical
  refine Finset.disjoint_left.mpr ?h
  intro v hv_front hv_C
  -- From membership in frontier: v ∉ C
  have hv_notin : v ∉ C := by
    have := Finset.mem_filter.mp hv_front
    exact this.2.1
  exact hv_notin hv_C



/-- Compute the full chain of seeds for all vertices in the DAG.

    Uses well-founded recursion on the DAG's parent relation. Requires acyclicity
    to ensure the parent relation is well-founded. -/
noncomputable def computeSeedChain (L : LStarInstanceFull)
  (entropy : (v : Fin L.dag.n) → Seed (L.seedWidth v)) :
  (v : Fin L.dag.n) → Seed (L.seedWidth v) :=
  fun v =>
    -- Use well-founded recursion on the DAG (requires acyclicity for well-foundedness)
    @WellFounded.fix (Fin L.dag.n) (fun v => Seed (L.seedWidth v))
      (L.dag.lt) (L.dag.lt_wf L.dagAcyclic)
      (fun v recurse =>
        let hist : ParentHistory L v := fun u =>
          recurse u.1 u.2
        L.computeSeed v hist (entropy v))
      v

/-- Functoriality of computeSeedChain: equal entropy functions produce equal seeds.

    This is the key lemma showing that seed computation is deterministic - if two
    entropy functions agree pointwise, the resulting seed chains are identical.

    This enables proving OAP roundtrip properties by showing entropy equality. -/
theorem computeSeedChain_ext (L : LStarInstanceFull)
    (entropy1 entropy2 : (v : Fin L.dag.n) → Seed (L.seedWidth v))
    (h_ext : ∀ v, entropy1 v = entropy2 v) :
    ∀ v, computeSeedChain L entropy1 v = computeSeedChain L entropy2 v := by
  intro v
  -- Use well-founded induction on the DAG order
  have wf := L.dag.lt_wf L.dagAcyclic
  induction v using wf.induction with
  | h v ih =>
    -- Unfold computeSeedChain on both sides (just beta reduction)
    show wf.fix (fun v recurse =>
        let hist : ParentHistory L v := fun u => recurse u.1 u.2
        L.computeSeed v hist (entropy1 v)) v =
      wf.fix (fun v recurse =>
        let hist : ParentHistory L v := fun u => recurse u.1 u.2
        L.computeSeed v hist (entropy2 v)) v
    -- Apply the unfolding equation for both sides
    rw [WellFounded.fix_eq, WellFounded.fix_eq]
    -- Build the parent history from the recursion
    let hist1 := fun (u : { u // L.dag.lt u v }) =>
        wf.fix (fun v recurse => L.computeSeed v (fun u => recurse u.1 u.2) (entropy1 v)) u.1
    let hist2 := fun (u : { u // L.dag.lt u v }) =>
        wf.fix (fun v recurse => L.computeSeed v (fun u => recurse u.1 u.2) (entropy2 v)) u.1
    -- Show hist1 = hist2 using the induction hypothesis
    have h_hist : hist1 = hist2 := by
      funext u
      exact ih u.1 u.2
    -- Rewrite to use the same history and then apply entropy equality
    show L.computeSeed v hist1 (entropy1 v) = L.computeSeed v hist2 (entropy2 v)
    rw [h_hist, h_ext v]

/-- Localized version of computeSeedChain_ext: if entropies agree on all nodes with
    index at most that of target, AND parent indices are always less than child indices,
    then the seeds at target are equal.

    Key insight: Seed computation at a node only depends on the node's own entropy and
    the seeds of its parents. When parent indices < child indices, the seed at target only
    depends on entropies at nodes with index ≤ target.val.

    The hypothesis h_parent_lt is satisfied by build3SATReductionDAG (see parents_have_smaller_indices). -/
theorem computeSeedChain_ext_local (L : LStarInstanceFull)
    (entropy1 entropy2 : (v : Fin L.dag.n) → Seed (L.seedWidth v))
    (target : Fin L.dag.n)
    (h_parent_lt : ∀ v u, L.dag.lt u v → u.val < v.val)
    (h_ext : ∀ v, v.val ≤ target.val → entropy1 v = entropy2 v) :
    computeSeedChain L entropy1 target = computeSeedChain L entropy2 target := by
  -- Use well-founded induction on the DAG order
  have wf := L.dag.lt_wf L.dagAcyclic

  -- For the proof, use well-founded induction
  induction target using wf.induction with
  | h v ih =>
    -- Unfold computeSeedChain
    show wf.fix (fun v recurse =>
        let hist : ParentHistory L v := fun u => recurse u.1 u.2
        L.computeSeed v hist (entropy1 v)) v =
      wf.fix (fun v recurse =>
        let hist : ParentHistory L v := fun u => recurse u.1 u.2
        L.computeSeed v hist (entropy2 v)) v
    rw [WellFounded.fix_eq, WellFounded.fix_eq]
    let hist1 := fun (u : { u // L.dag.lt u v }) =>
        wf.fix (fun v recurse => L.computeSeed v (fun u => recurse u.1 u.2) (entropy1 v)) u.1
    let hist2 := fun (u : { u // L.dag.lt u v }) =>
        wf.fix (fun v recurse => L.computeSeed v (fun u => recurse u.1 u.2) (entropy2 v)) u.1
    -- Show hist1 = hist2
    have h_hist : hist1 = hist2 := by
      funext u
      apply ih u.1 u.2
      -- Need: ∀ w, w.val ≤ u.1.val → entropy1 w = entropy2 w
      intro w hw
      apply h_ext w
      -- Need: w.val ≤ v.val
      -- We have hw : w.val ≤ u.1.val and h_parent_lt gives u.1.val < v.val
      have h_u_val_lt_v : u.1.val < v.val := h_parent_lt v u.1 u.2
      omega
    show L.computeSeed v hist1 (entropy1 v) = L.computeSeed v hist2 (entropy2 v)
    rw [h_hist]
    have h_v : entropy1 v = entropy2 v := h_ext v (Nat.le_refl _)
    rw [h_v]

/-- Ancestor relation: u is an ancestor of v if there's a path from u to v via parent edges.
    This is the transitive closure of the lt (parent) relation. -/
inductive isAncestorOf (G : DAG) : Fin G.n → Fin G.n → Prop where
  | parent : ∀ u v, G.lt u v → isAncestorOf G u v
  | trans : ∀ u w v, isAncestorOf G u w → G.lt w v → isAncestorOf G u v

/-- Ancestor-based extensionality: if entropies agree on target AND on all ancestors,
    then the seeds at target are equal.

    This is stronger than computeSeedChain_ext_local because it only requires agreement
    on ancestors of target, not all nodes with smaller indices. This is useful when
    non-ancestor nodes (like gates in the FG construction) have different entropies.

    The key insight: computeSeedChain uses well-founded recursion on the DAG's parent
    relation. The seed at v depends on:
    1. entropy v (the entropy at v itself)
    2. Seeds at parents of v (which recursively depend on their ancestors' entropies)

    Therefore, nodes that are NOT ancestors of v don't affect the seed at v. -/
theorem computeSeedChain_ext_ancestors (L : LStarInstanceFull)
    (entropy1 entropy2 : (v : Fin L.dag.n) → Seed (L.seedWidth v))
    (target : Fin L.dag.n)
    (h_ext_target : entropy1 target = entropy2 target)
    (h_ext_ancestors : ∀ u, isAncestorOf L.dag u target → entropy1 u = entropy2 u) :
    computeSeedChain L entropy1 target = computeSeedChain L entropy2 target := by
  -- Use well-founded induction on the DAG order
  have wf := L.dag.lt_wf L.dagAcyclic
  induction target using wf.induction with
  | h v ih =>
    -- Unfold computeSeedChain
    show wf.fix (fun v recurse =>
        let hist : ParentHistory L v := fun u => recurse u.1 u.2
        L.computeSeed v hist (entropy1 v)) v =
      wf.fix (fun v recurse =>
        let hist : ParentHistory L v := fun u => recurse u.1 u.2
        L.computeSeed v hist (entropy2 v)) v
    rw [WellFounded.fix_eq, WellFounded.fix_eq]
    let hist1 := fun (u : { u // L.dag.lt u v }) =>
        wf.fix (fun v recurse => L.computeSeed v (fun u => recurse u.1 u.2) (entropy1 v)) u.1
    let hist2 := fun (u : { u // L.dag.lt u v }) =>
        wf.fix (fun v recurse => L.computeSeed v (fun u => recurse u.1 u.2) (entropy2 v)) u.1
    -- Show hist1 = hist2
    have h_hist : hist1 = hist2 := by
      funext u
      apply ih u.1 u.2
      · -- entropy1 u.1 = entropy2 u.1 (u is a direct parent of v, hence an ancestor)
        apply h_ext_ancestors u.1
        exact isAncestorOf.parent u.1 v u.2
      · -- For any ancestor w of u.1, entropy1 w = entropy2 w
        intro w hw
        apply h_ext_ancestors w
        -- w is an ancestor of u.1, and u.1 is a parent of v
        -- So w is an ancestor of v (by transitivity)
        exact isAncestorOf.trans w u.1 v hw u.2
    show L.computeSeed v hist1 (entropy1 v) = L.computeSeed v hist2 (entropy2 v)
    rw [h_hist, h_ext_target]

end LStarInstanceFull

/-- `computeSeedChain` is invariant under `pools` changes.

    When two LStarInstanceFull structures are identical except for `pools`,
    their `computeSeedChain` functions produce equal results for equal entropy.

    This is because `computeSeed` (and its components `emergence`, `encodeSeed`)
    do NOT depend on `pools`.

    This simpler version takes a single L and two pool configs. -/
theorem computeSeedChain_pools_irrelevant
    (n : Nat) (n_pos : n > 0) (dag : DAG) (dagAcyclic : DAG.isAcyclic dag)
    (seedWidth : Fin dag.n → Nat) (R : Fin dag.n → Nat)
    (emergence : (v : Fin dag.n) → EmergenceMatrix (R v) (seedWidth v))
    (seedWidth_ok : ∀ v : Fin dag.n, (∑ u ∈ dag.parents v, seedWidth u) + R v ≤ seedWidth v)
    (pools1 pools2 : PoolConfig dag.n)
    (entropy : (v : Fin dag.n) → Seed (seedWidth v)) :
    let L1 : LStarInstanceFull := ⟨n, n_pos, dag, dagAcyclic, seedWidth, R, emergence, pools1, seedWidth_ok⟩
    let L2 : LStarInstanceFull := ⟨n, n_pos, dag, dagAcyclic, seedWidth, R, emergence, pools2, seedWidth_ok⟩
    ∀ v, LStarInstanceFull.computeSeedChain L1 entropy v =
         LStarInstanceFull.computeSeedChain L2 entropy v := by
  intro L1 L2 v
  -- L1 and L2 are definitionally equal on all fields except pools
  -- computeSeedChain only uses: dag, dagAcyclic, seedWidth, R, emergence, seedWidth_ok
  -- It does NOT use pools, so the results are definitionally equal
  rfl

-- Axiom audit for key operations
#print axioms LStar.LStarInstanceFull.computeSeed_deterministic
#print axioms LStar.LStarInstanceFull.frontier_disjoint_cut
#print axioms LStar.LStarInstanceFull.computeSeedChain
#print axioms LStar.LStarInstanceFull.computeSeedChain_ext

end LStar
