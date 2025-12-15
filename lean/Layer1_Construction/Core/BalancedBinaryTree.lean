import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Range
import Mathlib.Tactic.Ring

/-! ## BalancedBinaryTree: Logarithmic-Depth Aggregation Structure

A balanced binary tree for aggregating `m` leaf items into a single root
with O(log m) depth. This is a generic combinatorial structure used whenever
we need to combine many items without blowing up the depth.

**Structure**: Given m leaves indexed `[base, base+1, ..., base+m-1]`, the tree
creates `m-1` internal nodes that pairwise combine items level by level.

**Indexing**: Internal nodes are numbered sequentially by level, bottom-up:
- Level 0: m leaves (input items)
- Level 1: ⌊m/2⌋ internal nodes pairing adjacent leaves
- Level 2: ⌊⌊m/2⌋/2⌋ internal nodes pairing level-1 outputs
- ...continuing until one root remains

**Odd arities**: When a level has an odd number of items, the unpaired last
item is carried upward unchanged (no duplication).

**Key properties**:
- Depth: O(log m)
- Internal nodes: exactly m - 1
- Acyclicity: children always have smaller indices than parents
- Disjointness: left and right subtrees have disjoint leaf sets

**Application**: Used in the DAG to combine m items into a single root.
The disjointness property is critical for proving that summation over the
tree doesn't cause double-counting.
-/

namespace LStar.Construction.BalancedBinaryTree

/-!
## Tree Size Computation
-/

/-- Number of items at each tree level.

Level 0 has `m` items (the leaves).
Level `k+1` has `⌈(items at level k)/2⌉` items. -/
def nodesAtLevel (m : Nat) : Nat → Nat
  | 0 => m
  | k + 1 => (nodesAtLevel m k + 1) / 2

/-- Depth of the tree for `m` leaves (a conservative `⌈log₂ m⌉` bound). -/
def depth (m : Nat) : Nat :=
  if m ≤ 1 then 0 else Nat.log 2 m + 1

/-- Total number of internal nodes: exactly `m - 1` for `m > 1`. -/
def size (m : Nat) : Nat :=
  if m ≤ 1 then 0 else m - 1

/-!
## Node Indexing and Child Pointers

We start with the ordered list of leaf indices:
`[base, base+1, ..., base+m-1]`.
At each level we:
- combine adjacent pairs `(a,b)` into a new internal node, and
- carry an unpaired last item unchanged.

Internal nodes are assigned indices `base+m, base+m+1, ..., base+m+(size m)-1`.
-/

private def nthPairChildren : Nat → List Nat → Nat × Nat
  | 0, a :: b :: _ => (a, b)
  | n + 1, _ :: _ :: rest => nthPairChildren n rest
  | _, _ => (0, 0)

private def pairCount {α : Type} : List α → Nat
  | _ :: _ :: rest => pairCount rest + 1
  | _ => 0

private def nextItems (nextNodeIdx : Nat) (items : List Nat) : List Nat :=
  let pairs := pairCount items
  let newNodes := (List.range pairs).map (fun i => nextNodeIdx + i)
  newNodes ++ items.drop (2 * pairs)

private def childIndicesAux (clauseBase m redIdx nextNodeIdx : Nat) (items : List Nat) : Nat × Nat :=
  let pairs := pairCount items
  if pairs = 0 then
    (0, 0)
  else if redIdx < pairs then
    nthPairChildren redIdx items
  else
    childIndicesAux clauseBase m (redIdx - pairs) (nextNodeIdx + pairs) (nextItems nextNodeIdx items)
termination_by redIdx
decreasing_by
  all_goals
    simp_wf
    omega

/-- Child indices for internal node `redIdx`, given `m` leaves starting at `clauseBase`.

Index ranges:
- Leaves: `clauseBase .. clauseBase + m - 1`
- Internal nodes: `clauseBase + m .. clauseBase + m + size m - 1` -/
def simpleChildIndices (clauseBase m redIdx : Nat) : Nat × Nat :=
  let initItems := (List.range m).map (fun i => clauseBase + i)
  childIndicesAux clauseBase m redIdx (clauseBase + m) initItems

private lemma nthPairChildren_lt {n nextNodeIdx : Nat} {items : List Nat}
    (h_pairs : pairCount items ≠ 0) (h : n < pairCount items)
    (h_items : ∀ x ∈ items, x < nextNodeIdx) :
    (nthPairChildren n items).1 < nextNodeIdx ∧ (nthPairChildren n items).2 < nextNodeIdx := by
  induction n generalizing items with
  | zero =>
      cases items with
      | nil =>
          cases h_pairs rfl
      | cons a t =>
          cases t with
          | nil =>
              cases h_pairs rfl
          | cons b _ =>
              simp [nthPairChildren]
              constructor
              · exact h_items a (by simp)
              · exact h_items b (by simp)
  | succ n ih =>
      cases items with
      | nil =>
          cases h_pairs rfl
      | cons _ t =>
          cases t with
          | nil =>
              cases h_pairs rfl
          | cons _ t' =>
              have h_items' : ∀ x ∈ t', x < nextNodeIdx := by
                intro x hx
                exact h_items x (by simp [hx])
              have h' : n < pairCount t' := by
                -- `pairCount (_::_::t') = pairCount t' + 1`
                simpa [pairCount, Nat.succ_eq_add_one, Nat.add_assoc] using (Nat.lt_of_succ_lt_succ h)
              have h_pairs' : pairCount t' ≠ 0 := by
                -- `pairCount t' = 0` would imply `pairCount (_::_::t') = 1`, contradicting `h_pairs = 0`.
                omega
              simpa [nthPairChildren] using ih (items := t') h_pairs' h' h_items'

private lemma nextItems_lt (nextNodeIdx : Nat) (items : List Nat)
    (h_items : ∀ x ∈ items, x < nextNodeIdx) :
    ∀ x ∈ nextItems nextNodeIdx items, x < nextNodeIdx + pairCount items := by
  intro x hx
  have hx' : x ∈ ((List.range (pairCount items)).map (fun i => nextNodeIdx + i) ++
      items.drop (2 * (pairCount items))) := by
    simpa [nextItems] using hx
  rcases List.mem_append.1 hx' with hx_new | hx_tail
  · rcases List.mem_map.1 hx_new with ⟨i, hi, rfl⟩
    have hi' : i < pairCount items := by simpa [List.mem_range] using hi
    omega
  · have hx_items : x ∈ items := List.mem_of_mem_drop hx_tail
    have : x < nextNodeIdx := h_items x hx_items
    omega

private lemma childIndicesAux_children_lt_sum
    (clauseBase m : Nat) :
    ∀ (redIdx nextNodeIdx : Nat) (items : List Nat),
      nextNodeIdx > 0 →
      (∀ x ∈ items, x < nextNodeIdx) →
      let (l, r) := childIndicesAux clauseBase m redIdx nextNodeIdx items
      l < nextNodeIdx + redIdx ∧ r < nextNodeIdx + redIdx := by
  intro redIdx nextNodeIdx items h_next_pos h_items
  -- strong induction on `redIdx` matches the recursion measure
  induction redIdx using Nat.strong_induction_on generalizing nextNodeIdx items with
  | _ redIdx ih =>
      -- unfold one step of the worker
      unfold childIndicesAux
      dsimp
      set pairs := pairCount items with h_pairs_def
      by_cases hpairs0 : pairs = 0
      · -- In this branch the worker returns `(0,0)`. We still have `nextNodeIdx > 0`,
        -- hence `0 < nextNodeIdx + redIdx`.
        have : 0 < nextNodeIdx + redIdx := by omega
        simp [hpairs0, this]
      · by_cases h : redIdx < pairs
        · have h_children := nthPairChildren_lt (items := items) (n := redIdx) (nextNodeIdx := nextNodeIdx)
            (by omega) h h_items
          have h_next_le : nextNodeIdx ≤ nextNodeIdx + redIdx := Nat.le_add_right _ _
          -- simplify the worker to the selection branch
          simpa [hpairs0, h, h_pairs_def, pairs] using
            (And.intro (lt_of_lt_of_le h_children.1 h_next_le) (lt_of_lt_of_le h_children.2 h_next_le))
        · have h_ge : pairs ≤ redIdx := by omega
          let items' := nextItems nextNodeIdx items
          let next' := nextNodeIdx + pairs
          have h_items' : ∀ x ∈ items', x < next' := by
            intro x hx
            have := nextItems_lt (nextNodeIdx := nextNodeIdx) (items := items) h_items x hx
            simpa [items', next', h_pairs_def, pairs] using this
          have h_redIdx_lt : redIdx - pairs < redIdx := by
            have : pairs > 0 := by omega
            omega
          have h_rec := ih (redIdx - pairs) h_redIdx_lt next' items' (by omega) h_items'
          -- align the target bound: `next' + (redIdx - pairs) = nextNodeIdx + redIdx`
          -- Rewrite the right-hand side bound to `redIdx + nextNodeIdx`.
          have h_bound :
              nextNodeIdx + (pairs + (redIdx - pairs)) = redIdx + nextNodeIdx := by
            -- Use `pairs ≤ redIdx` to cancel the subtraction.
            -- `pairs + (redIdx - pairs) = (redIdx - pairs) + pairs = redIdx`
            calc
              nextNodeIdx + (pairs + (redIdx - pairs))
                  = nextNodeIdx + ((redIdx - pairs) + pairs) := by
                      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              _ = nextNodeIdx + redIdx := by
                      simp [Nat.sub_add_cancel h_ge, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              _ = redIdx + nextNodeIdx := by
                      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          -- Finish by aligning both sides.
          simpa [hpairs0, h, items', next', h_pairs_def, pairs, h_bound,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_rec

/-- Children always have smaller indices than their parent (ensures acyclicity).

For internal node at index `clauseBase + m + redIdx`, both children
have indices strictly less than the parent. -/
theorem simpleChildIndices_children_less_than_parent
    (clauseBase m redIdx : Nat) (_h_m : m > 0) (_h_redIdx : redIdx < size m) :
    let (left, right) := simpleChildIndices clauseBase m redIdx
    left < clauseBase + m + redIdx ∧ right < clauseBase + m + redIdx := by
  -- Apply the general auxiliary lemma to the initial state.
  unfold simpleChildIndices
  dsimp
  set initItems := (List.range m).map (fun i => clauseBase + i) with h_initItems
  set initNext := clauseBase + m with h_initNext
  have h_items : ∀ x ∈ initItems, x < initNext := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨i, hi, rfl⟩
    have hi' : i < m := by simpa [List.mem_range] using hi
    omega
  have h :=
    childIndicesAux_children_lt_sum clauseBase m redIdx initNext initItems (by omega) h_items
  -- `initNext + redIdx = clauseBase + m + redIdx`
  simpa [initNext, h_initNext, initItems, h_initItems, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-!
## Leaf Descendant Sets

For any internal node, we compute the set of leaves in its subtree.
This is essential for proving that aggregation over the tree doesn't
double-count: each leaf contributes to exactly one path to the root.

We define the leaf set of a node index (`0..m-1` for leaves,
`m..m+size m-1` for internal nodes) by recursion using `simpleChildIndices 0 m`.
-/

private def clauseSetNodeWithProof (m idx : Nat) : { s : Finset Nat // s ⊆ Finset.range m } :=
  Nat.strongRecOn' idx (fun idx rec =>
    if h : idx < m then
      ⟨{idx}, by
        intro x hx
        have : x = idx := by simpa using hx
        subst this
        simpa [Finset.mem_range] using h⟩
    else
      let redIdx := idx - m
      if h_red : redIdx < size m then
        let l := (simpleChildIndices 0 m redIdx).1
        let r := (simpleChildIndices 0 m redIdx).2
        have hm : m > 0 := by
          unfold size at h_red
          by_cases hle : m ≤ 1 <;> simp [hle] at h_red <;> omega
        have h_children :=
          simpleChildIndices_children_less_than_parent (clauseBase := 0) (m := m) (redIdx := redIdx) hm h_red
        have hmle : m ≤ idx := Nat.le_of_not_gt h
        have h_parent : m + redIdx = idx := by
          calc
            m + redIdx = redIdx + m := by simp [Nat.add_comm]
            _ = idx := by simpa [redIdx] using (Nat.sub_add_cancel hmle)
        have h_l : l < idx := by
          simpa [l, h_parent, simpleChildIndices, Nat.add_assoc, Nat.zero_add] using h_children.1
        have h_r : r < idx := by
          simpa [r, h_parent, simpleChildIndices, Nat.add_assoc, Nat.zero_add] using h_children.2
        let sl := (rec l h_l).1
        let sr := (rec r h_r).1
        have pl : sl ⊆ Finset.range m := (rec l h_l).2
        have pr : sr ⊆ Finset.range m := (rec r h_r).2
        ⟨sl ∪ sr, by
          intro x hx
          have hx' : x ∈ sl ∨ x ∈ sr := by
            simpa [Finset.mem_union] using hx
          rcases hx' with hx' | hx'
          · exact pl hx'
          · exact pr hx'⟩
      else
        ⟨∅, by simp⟩)

def clauseSetNode (m idx : Nat) : Finset Nat :=
  (clauseSetNodeWithProof m idx).1

/-- Leaf set for internal node `redIdx` (0-based among internal nodes). -/
def clauseSet (m redIdx : Nat) : Finset Nat :=
  clauseSetNode m (m + redIdx)

/-- Leaf descendant count for internal node `redIdx` (cardinality of its leaf set). -/
def clauseDescendantCount (m redIdx : Nat) : Nat :=
  (clauseSet m redIdx).card

lemma clauseSetNode_subset_range (m idx : Nat) :
    clauseSetNode m idx ⊆ Finset.range m :=
  (clauseSetNodeWithProof m idx).2

/-- Leaf descendants never exceed total leaves. -/
theorem clauseDescendantCount_le (m redIdx : Nat)
    (_h_m : m > 1) (_h_redIdx : redIdx < size m) :
    clauseDescendantCount m redIdx ≤ m := by
  unfold clauseDescendantCount
  calc
    (clauseSet m redIdx).card ≤ (Finset.range m).card := by
      exact Finset.card_le_card (clauseSetNode_subset_range m (m + redIdx))
    _ = m := by simp

/-!
## Recursive Structure Lemmas

Key lemmas for unfolding the leaf set computation at leaves vs internal nodes.
-/

/-- At a leaf node, the leaf set is the singleton containing just that leaf. -/
lemma clauseSetNode_leaf (m idx : Nat) (h : idx < m) :
    clauseSetNode m idx = {idx} := by
  unfold clauseSetNode
  unfold clauseSetNodeWithProof
  rw [Nat.strongRecOn'_beta]
  simp [h]

/-- At an internal node, the leaf set is the union of its children's leaf sets. -/
lemma clauseSetNode_reduction_eq_union (m redIdx : Nat) (h_red : redIdx < size m) :
    let l := (simpleChildIndices 0 m redIdx).1
    let r := (simpleChildIndices 0 m redIdx).2
    clauseSetNode m (m + redIdx) = clauseSetNode m l ∪ clauseSetNode m r := by
  unfold clauseSetNode
  unfold clauseSetNodeWithProof
  rw [Nat.strongRecOn'_beta]
  have h_not : ¬ (m + redIdx < m) := by omega
  simp [h_not, h_red]

/-!
## Level-by-Level Indexing

These lemmas model the tree construction level by level and establish arithmetic
invariants about node allocation. They enable the disjointness proof by providing
a representation for each internal node index as `levelOffset m k + i`.
-/

private def levelState (m : Nat) : Nat → Nat × List Nat
  | 0 => (m, List.range m)
  | k + 1 =>
      let st := levelState m k
      let next := st.1
      let items := st.2
      (next + pairCount items, nextItems next items)

private def levelNext (m k : Nat) : Nat :=
  (levelState m k).1

private def levelItems (m k : Nat) : List Nat :=
  (levelState m k).2

private def levelPairs (m k : Nat) : Nat :=
  pairCount (levelItems m k)

private def levelOffset (m k : Nat) : Nat :=
  levelNext m k - m

private lemma levelNext_succ (m k : Nat) :
    levelNext m (k + 1) = levelNext m k + levelPairs m k := by
  simp [levelNext, levelPairs, levelState, levelItems]

private lemma levelItems_succ (m k : Nat) :
    levelItems m (k + 1) = nextItems (levelNext m k) (levelItems m k) := by
  simp [levelItems, levelState, levelNext]

private lemma levelOffset_zero (m : Nat) : levelOffset m 0 = 0 := by
  simp [levelOffset, levelNext, levelState]

private lemma levelOffset_succ (m k : Nat) :
    levelOffset m (k + 1) = levelOffset m k + levelPairs m k := by
  -- show `m ≤ levelNext m k` so we can rewrite subtraction
  have hm_le_next : m ≤ levelNext m k := by
    induction k with
    | zero =>
        simp [levelNext, levelState]
    | succ k ih =>
        have h := levelNext_succ (m := m) (k := k)
        -- `levelNext` is monotone and starts at `m`
        calc
          m ≤ levelNext m k := ih
          _ ≤ levelNext m k + levelPairs m k := Nat.le_add_right _ _
          _ = levelNext m (k + 1) := by simpa [h] using rfl
  unfold levelOffset
  calc
    levelNext m (k + 1) - m
        = (levelNext m k + levelPairs m k) - m := by
            simp [levelNext_succ]
    _ = (levelNext m k - m) + levelPairs m k := by
            -- commute then use `Nat.add_sub_assoc`
            calc
              (levelNext m k + levelPairs m k) - m
                  = (levelPairs m k + levelNext m k) - m := by
                      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              _ = levelPairs m k + (levelNext m k - m) := by
                      simpa using (Nat.add_sub_assoc hm_le_next (levelPairs m k))
              _ = (levelNext m k - m) + levelPairs m k := by
                      simp [Nat.add_comm]

private lemma two_mul_pairCount_le_length {α : Type} (items : List α) :
    2 * pairCount items ≤ items.length := by
  -- strong induction on list length (consuming 2 elements at a time)
  let P : Nat → Prop :=
    fun n => ∀ l : List α, l.length = n → 2 * pairCount l ≤ l.length
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strongRecOn n (fun n ih => ?_)
    intro l hl
    cases l with
    | nil =>
        simp [pairCount] at hl
        subst hl
        simp [pairCount]
    | cons a t =>
        cases t with
        | nil =>
            simp at hl
            subst hl
            simp [pairCount]
        | cons b rest =>
            have hrest_len : rest.length < n := by
              have : rest.length + 2 = n := by simpa using hl
              omega
            have hrest : 2 * pairCount rest ≤ rest.length := by
              have := ih rest.length hrest_len
              exact this rest rfl
            simpa [pairCount, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              Nat.add_le_add_right hrest 2
  exact hP items.length items rfl

private lemma pairCount_le_length {α : Type} (items : List α) :
    pairCount items ≤ items.length := by
  have h2 : 2 * pairCount items ≤ items.length := two_mul_pairCount_le_length (items := items)
  have : pairCount items ≤ 2 * pairCount items := by omega
  exact le_trans this h2

private lemma nextItems_length (nextNodeIdx : Nat) (items : List Nat) :
    (nextItems nextNodeIdx items).length = items.length - pairCount items := by
  unfold nextItems
  set pairs := pairCount items
  set len := items.length
  simp [pairs, len, List.length_append, List.length_map, List.length_range, List.length_drop]
  have hp : pairs ≤ len := by
    simpa [pairs, len] using (pairCount_le_length (items := items))
  apply Nat.add_right_cancel
  have h2 : 2 * pairs ≤ len := by
    simpa [pairs, len] using (two_mul_pairCount_le_length (items := items))
  calc
    pairs + (len - 2 * pairs) + pairs
        = (len - 2 * pairs) + (2 * pairs) := by omega
    _ = len := Nat.sub_add_cancel h2
    _ = (len - pairs) + pairs := (Nat.sub_add_cancel hp).symm

private lemma levelOffset_add_length_levelItems (m : Nat) :
    ∀ k, levelOffset m k + (levelItems m k).length = m := by
  intro k
  induction k with
  | zero =>
      simp [levelOffset, levelNext, levelItems, levelState]
  | succ k ih =>
      have h_items : levelItems m (k + 1) = nextItems (levelNext m k) (levelItems m k) :=
        levelItems_succ (m := m) (k := k)
      have h_off : levelOffset m (k + 1) = levelOffset m k + levelPairs m k :=
        levelOffset_succ (m := m) (k := k)
      have h_len' :
          (levelItems m (k + 1)).length =
            (levelItems m k).length - levelPairs m k := by
        simpa [h_items, levelPairs] using
          (nextItems_length (nextNodeIdx := levelNext m k) (items := levelItems m k))
      have hb : levelPairs m k ≤ (levelItems m k).length := by
        unfold levelPairs
        simpa using (pairCount_le_length (items := levelItems m k))
      calc
        levelOffset m (k + 1) + (levelItems m (k + 1)).length
            = (levelOffset m k + levelPairs m k) + ((levelItems m k).length - levelPairs m k) := by
                simp [h_off, h_len', Nat.add_assoc]
        _ = levelOffset m k + (levelItems m k).length := by
                calc
                  (levelOffset m k + levelPairs m k) + ((levelItems m k).length - levelPairs m k)
                      = levelOffset m k + (levelPairs m k + ((levelItems m k).length - levelPairs m k)) := by
                          simp [Nat.add_assoc]
                  _ = levelOffset m k + (levelItems m k).length := by
                          have : levelPairs m k + ((levelItems m k).length - levelPairs m k) = (levelItems m k).length := by
                            simpa [Nat.add_comm] using (Nat.sub_add_cancel hb)
                          simp [this]
        _ = m := ih

private lemma levelOffset_add_lt_size (m k i : Nat) (h_m : m > 1) (h_i : i < levelPairs m k) :
    levelOffset m k + i < size m := by
  set len := (levelItems m k).length
  have h_inv : levelOffset m k + len = m := by
    simpa [len] using (levelOffset_add_length_levelItems (m := m) k)
  have h_len_le_m : len ≤ m := by omega
  have hpairs_pos : 0 < levelPairs m k := by omega
  have hpairs2 : 2 * levelPairs m k ≤ len := by
    unfold levelPairs
    simpa [len] using (two_mul_pairCount_le_length (items := levelItems m k))
  have h1le_len : 1 ≤ len := by omega
  have hpairs_le_len1 : levelPairs m k ≤ len - 1 := by
    -- follows from `0 < pairs` and `2*pairs ≤ len`
    omega
  have hi_lt_len1 : i < len - 1 := lt_of_lt_of_le h_i hpairs_le_len1
  have h_off : levelOffset m k = m - len := by
    have := congrArg (fun t => t - len) h_inv
    simpa [Nat.add_sub_cancel] using this
  have h_lt : levelOffset m k + i < levelOffset m k + (len - 1) :=
    Nat.add_lt_add_left hi_lt_len1 _
  have h_eq : levelOffset m k + (len - 1) = m - 1 := by
    calc
      levelOffset m k + (len - 1)
          = (m - len) + (len - 1) := by simp [h_off]
      _ = ((m - len) + len) - 1 := by
            simpa using (Nat.add_sub_assoc (m := len) (k := 1) h1le_len (m - len)).symm
      _ = m - 1 := by simp [Nat.sub_add_cancel h_len_le_m]
  have h_lt_m1 : levelOffset m k + i < m - 1 := lt_of_lt_of_eq h_lt h_eq
  have h_size : size m = m - 1 := by
    have : ¬ m ≤ 1 := by omega
    simp [size, this]
  simpa [h_size] using h_lt_m1

private lemma childIndicesAux_offset_eq_level (m : Nat) :
    ∀ k i,
      childIndicesAux 0 m (levelOffset m k + i) m (List.range m) =
        childIndicesAux 0 m i (levelNext m k) (levelItems m k) := by
  intro k
  induction k with
  | zero =>
      intro i
      simp [levelOffset, levelNext, levelItems, levelState]
  | succ k ih =>
      intro i
      -- abbreviate the level-`k` state
      set next := levelNext m k
      set items := levelItems m k
      set pairs := levelPairs m k
      have h_off : levelOffset m (k + 1) = levelOffset m k + pairs := by
        simpa [pairs, levelPairs] using (levelOffset_succ (m := m) (k := k))
      have h_idx :
          levelOffset m (k + 1) + i = levelOffset m k + (pairs + i) := by
        simp [h_off, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have ih' :
          childIndicesAux 0 m (levelOffset m k + (pairs + i)) m (List.range m) =
            childIndicesAux 0 m (pairs + i) next items := by
        -- apply the IH at local index `pairs + i`
        simpa [next, items, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (i := pairs + i)
      -- unfold one step of the worker at level `k`
      by_cases hp0 : pairs = 0
      · -- stable level: no pairs, so state doesn't change
        have h_next : levelNext m (k + 1) = next := by
          simp [next, pairs, hp0, levelNext_succ]
        have h_items : levelItems m (k + 1) = items := by
          -- `nextItems` is identity when `pairCount = 0`
          have : pairCount items = 0 := by simpa [pairs, levelPairs, items] using hp0
          simp [items, next, levelItems_succ, nextItems, this]
        have h_off' : levelOffset m (k + 1) = levelOffset m k := by
          simp [h_off, hp0]
        simpa [h_idx, hp0, h_next, h_items, h_off', next, items] using ih'
      · -- real reduction step: `pairs > 0`, so `pairs + i` takes the recursion branch
        have hpc : pairCount items = pairs := by simp [pairs, levelPairs, items]
        have h_not_lt : ¬ (pairs + i < pairCount items) := by
          -- `¬ (pairs + i < pairs)` since `pairs ≤ pairs + i`
          have : ¬ (pairs + i < pairs) := Nat.not_lt.mpr (Nat.le_add_right pairs i)
          simpa [hpc] using this
        have hpairs_ne : pairCount items ≠ 0 := by
          simpa [hpc] using hp0
        have h_step :
            childIndicesAux 0 m (pairs + i) next items =
              childIndicesAux 0 m i (next + pairs) (nextItems next items) := by
          have h1 :
              childIndicesAux 0 m (pairs + i) next items =
                childIndicesAux 0 m ((pairs + i) - pairCount items) (next + pairCount items)
                  (nextItems next items) := by
            -- one unfolding step of the *LHS* only; the recursion call is exactly the `else` branch
            conv_lhs => unfold childIndicesAux
            simp [hpairs_ne, h_not_lt]
          -- simplify the arithmetic in the recursive call
          simpa [hpc, Nat.add_sub_cancel_left] using h1
        have h_next : levelNext m (k + 1) = next + pairs := by
          simpa [next, pairs, levelPairs] using (levelNext_succ (m := m) (k := k))
        have h_items : levelItems m (k + 1) = nextItems next items := by
          simpa [next, items] using (levelItems_succ (m := m) (k := k))
        calc
          childIndicesAux 0 m (levelOffset m (k + 1) + i) m (List.range m)
              = childIndicesAux 0 m (levelOffset m k + (pairs + i)) m (List.range m) := by
                  simpa [h_idx]
          _ = childIndicesAux 0 m (pairs + i) next items := ih'
          _ = childIndicesAux 0 m i (next + pairs) (nextItems next items) := h_step
          _ = childIndicesAux 0 m i (levelNext m (k + 1)) (levelItems m (k + 1)) := by
                  simp [h_next, h_items]

private lemma simpleChildIndices_at_level (m k i : Nat) (h_i : i < levelPairs m k) :
    simpleChildIndices 0 m (levelOffset m k + i) = nthPairChildren i (levelItems m k) := by
  unfold simpleChildIndices
  dsimp
  simp
  have h0 := childIndicesAux_offset_eq_level (m := m) (k := k) (i := i)
  -- reduce the global worker call to the level-`k` worker call, then pick the `nthPairChildren` branch
  have hlt : i < pairCount (levelItems m k) := by simpa [levelPairs] using h_i
  have hpairs_ne : pairCount (levelItems m k) ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i) hlt)
  calc
    childIndicesAux 0 m (levelOffset m k + i) m (List.range m)
        = childIndicesAux 0 m i (levelNext m k) (levelItems m k) := h0
    _ = nthPairChildren i (levelItems m k) := by
        simp [childIndicesAux, hpairs_ne, hlt]

private lemma pairCount_map {α β : Type} (f : α → β) :
    ∀ l : List α, pairCount (l.map f) = pairCount l := by
  intro l
  -- strong induction on list length (since `pairCount` consumes 2 items per step)
  let P : Nat → Prop :=
    fun n => ∀ l : List α, l.length = n → pairCount (l.map f) = pairCount l
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strongRecOn n (fun n ih => ?_)
    intro l hl
    cases l with
    | nil =>
        simp [pairCount] at hl
        subst hl
        simp [pairCount]
    | cons a t =>
        cases t with
        | nil =>
            simp at hl
            subst hl
            simp [pairCount]
        | cons b rest =>
            have hrest_len : rest.length < n := by
              have : rest.length + 2 = n := by simpa using hl
              omega
            have hrest : pairCount (rest.map f) = pairCount rest := by
              have := ih rest.length hrest_len
              exact this rest rfl
            simp [pairCount, hrest]
  exact hP l.length l rfl

private lemma nextItems_map_add (base nextNodeIdx : Nat) (items : List Nat) :
    nextItems (base + nextNodeIdx) (items.map (fun x => base + x)) =
      (nextItems nextNodeIdx items).map (fun x => base + x) := by
  unfold nextItems
  set pairs := pairCount items
  have hpairs : pairCount (items.map (fun x => base + x)) = pairs := by
    simpa [pairs] using (pairCount_map (f := fun x : Nat => base + x) items)
  -- rewrite `pairs` on the LHS to match the RHS
  simp [pairs, hpairs, List.map_append, List.map_map, List.map_drop, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma nthPairChildren_map_add (base n : Nat) (items : List Nat) (h : n < pairCount items) :
    nthPairChildren n (items.map (fun x => base + x)) =
      (base + (nthPairChildren n items).1, base + (nthPairChildren n items).2) := by
  induction n generalizing items with
  | zero =>
      cases items with
      | nil => simpa [pairCount] using h
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using h
          | cons b rest =>
              simp [nthPairChildren]
  | succ n ih =>
      cases items with
      | nil => simpa [pairCount] using h
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using h
          | cons b rest =>
              have h' : n < pairCount rest := by
                -- `pairCount (_::_::rest) = pairCount rest + 1`
                simpa [pairCount, Nat.succ_eq_add_one, Nat.add_assoc] using (Nat.lt_of_succ_lt_succ h)
              simpa [nthPairChildren] using ih (items := rest) h'

private lemma childIndicesAux_offset_eq_level_add (clauseBase m : Nat) :
    ∀ k i,
      childIndicesAux clauseBase m (levelOffset m k + i) (clauseBase + m)
        ((List.range m).map (fun j => clauseBase + j)) =
        childIndicesAux clauseBase m i (clauseBase + levelNext m k)
          ((levelItems m k).map (fun j => clauseBase + j)) := by
  intro k
  induction k with
  | zero =>
      intro i
      simp [levelOffset, levelNext, levelItems, levelState]
  | succ k ih =>
      intro i
      set next0 := levelNext m k
      set items0 := levelItems m k
      set pairs := levelPairs m k
      have h_off : levelOffset m (k + 1) = levelOffset m k + pairs := by
        simpa [pairs, levelPairs] using (levelOffset_succ (m := m) (k := k))
      have h_idx :
          levelOffset m (k + 1) + i = levelOffset m k + (pairs + i) := by
        simp [h_off, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have ih' :
          childIndicesAux clauseBase m (levelOffset m k + (pairs + i)) (clauseBase + m)
              ((List.range m).map (fun j => clauseBase + j)) =
            childIndicesAux clauseBase m (pairs + i) (clauseBase + next0)
              (items0.map (fun j => clauseBase + j)) := by
        simpa [next0, items0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (i := pairs + i)
      by_cases hp0 : pairs = 0
      · -- stable level
        have h_next : levelNext m (k + 1) = next0 := by
          simp [next0, pairs, hp0, levelNext_succ]
        have h_items0 : nextItems next0 items0 = items0 := by
          have : pairCount items0 = 0 := by simpa [pairs, levelPairs, items0] using hp0
          simp [nextItems, this]
        have h_items : levelItems m (k + 1) = items0 := by
          simpa [items0, next0, h_items0] using (levelItems_succ (m := m) (k := k))
        have h_off' : levelOffset m (k + 1) = levelOffset m k := by simp [h_off, hp0]
        simpa [h_idx, hp0, h_next, h_items, h_off', next0, items0] using ih'
      · -- real reduction step
        have hpc : pairCount (items0.map (fun j => clauseBase + j)) = pairs := by
          simpa [pairs, levelPairs, items0] using
            (pairCount_map (f := fun x : Nat => clauseBase + x) items0)
        have h_not_lt : ¬ (pairs + i < pairCount (items0.map (fun j => clauseBase + j))) := by
          have : ¬ (pairs + i < pairs) := Nat.not_lt.mpr (Nat.le_add_right pairs i)
          simpa [hpc] using this
        have hpairs_ne : pairCount (items0.map (fun j => clauseBase + j)) ≠ 0 := by
          simpa [hpc] using hp0
        have h_step :
            childIndicesAux clauseBase m (pairs + i) (clauseBase + next0) (items0.map (fun j => clauseBase + j)) =
              childIndicesAux clauseBase m i ((clauseBase + next0) + pairs)
                (nextItems (clauseBase + next0) (items0.map (fun j => clauseBase + j))) := by
          have h1 :
              childIndicesAux clauseBase m (pairs + i) (clauseBase + next0) (items0.map (fun j => clauseBase + j)) =
                childIndicesAux clauseBase m ((pairs + i) - pairCount (items0.map (fun j => clauseBase + j)))
                  ((clauseBase + next0) + pairCount (items0.map (fun j => clauseBase + j)))
                  (nextItems (clauseBase + next0) (items0.map (fun j => clauseBase + j))) := by
            conv_lhs => unfold childIndicesAux
            simp [hpairs_ne, h_not_lt]
          simpa [hpc, Nat.add_sub_cancel_left, Nat.add_assoc] using h1
        have h_next : levelNext m (k + 1) = next0 + pairs := by
          simpa [next0, pairs, levelPairs] using (levelNext_succ (m := m) (k := k))
        have h_items : levelItems m (k + 1) = nextItems next0 items0 := by
          simpa [next0, items0] using (levelItems_succ (m := m) (k := k))
        have h_items_map :
            nextItems (clauseBase + next0) (items0.map (fun j => clauseBase + j)) =
              (nextItems next0 items0).map (fun j => clauseBase + j) := by
          simpa using (nextItems_map_add (base := clauseBase) (nextNodeIdx := next0) (items := items0))
        calc
          childIndicesAux clauseBase m (levelOffset m (k + 1) + i) (clauseBase + m)
              ((List.range m).map (fun j => clauseBase + j))
              = childIndicesAux clauseBase m (levelOffset m k + (pairs + i)) (clauseBase + m)
                  ((List.range m).map (fun j => clauseBase + j)) := by
                    simpa [h_idx]
          _ = childIndicesAux clauseBase m (pairs + i) (clauseBase + next0)
                (items0.map (fun j => clauseBase + j)) := ih'
          _ = childIndicesAux clauseBase m i ((clauseBase + next0) + pairs)
                (nextItems (clauseBase + next0) (items0.map (fun j => clauseBase + j))) := h_step
          _ = childIndicesAux clauseBase m i (clauseBase + levelNext m (k + 1))
                ((levelItems m (k + 1)).map (fun j => clauseBase + j)) := by
                simp [h_next, h_items, h_items_map, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma simpleChildIndices_at_level_add (clauseBase m k i : Nat) (h_i : i < levelPairs m k) :
    simpleChildIndices clauseBase m (levelOffset m k + i) =
      (clauseBase + (nthPairChildren i (levelItems m k)).1, clauseBase + (nthPairChildren i (levelItems m k)).2) := by
  unfold simpleChildIndices
  dsimp
  have h0 := childIndicesAux_offset_eq_level_add (clauseBase := clauseBase) (m := m) (k := k) (i := i)
  have hlt : i < pairCount (levelItems m k) := by simpa [levelPairs] using h_i
  have hpairs_ne : pairCount ((levelItems m k).map (fun j => clauseBase + j)) ≠ 0 := by
    have : pairCount (levelItems m k) ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i) hlt)
    have hpc : pairCount ((levelItems m k).map (fun j => clauseBase + j)) = pairCount (levelItems m k) := by
      simpa using (pairCount_map (f := fun j : Nat => clauseBase + j) (levelItems m k))
    simpa [hpc] using this
  have hlt' : i < pairCount ((levelItems m k).map (fun j => clauseBase + j)) := by
    have hpc : pairCount ((levelItems m k).map (fun j => clauseBase + j)) = pairCount (levelItems m k) := by
      simpa using (pairCount_map (f := fun j : Nat => clauseBase + j) (levelItems m k))
    simpa [hpc] using hlt
  calc
    childIndicesAux clauseBase m (levelOffset m k + i) (clauseBase + m)
        ((List.range m).map (fun j => clauseBase + j))
        = childIndicesAux clauseBase m i (clauseBase + levelNext m k)
            ((levelItems m k).map (fun j => clauseBase + j)) := h0
    _ = nthPairChildren i ((levelItems m k).map (fun j => clauseBase + j)) := by
          simp [childIndicesAux, hpairs_ne, hlt']
    _ = (clauseBase + (nthPairChildren i (levelItems m k)).1, clauseBase + (nthPairChildren i (levelItems m k)).2) := by
          simpa using (nthPairChildren_map_add (base := clauseBase) (n := i) (items := levelItems m k) hlt)

/-!
## Subtree Disjointness

The critical property: left and right subtrees of any internal node have
disjoint leaf sets. This ensures that summing over the tree doesn't
double-count any leaf.
-/

private def ItemsDisjoint (m : Nat) (items : List Nat) : Prop :=
  items.Pairwise (fun a b => Disjoint (clauseSetNode m a) (clauseSetNode m b))

private lemma range_get (m : Nat) (i : Fin (List.range m).length) :
    (List.range m).get i = (i : Nat) := by
  -- bridge `List.get` and `getElem`, then use the `range'` indexing lemma
  rw [List.get_eq_getElem]
  have hi : (i : Nat) < (List.range' 0 m).length := by
    simpa [List.range_eq_range'] using i.isLt
  calc
    (List.range m)[(i : Nat)] = (List.range' 0 m)[(i : Nat)] := by
      simp [List.range_eq_range']
    _ = (0 : Nat) + (i : Nat) := List.getElem_range'_1 (n := 0) (m := m) (i := (i : Nat)) hi
    _ = (i : Nat) := by simp

private lemma ItemsDisjoint_range (m : Nat) :
    ItemsDisjoint m (List.range m) := by
  unfold ItemsDisjoint
  -- use the indexing characterization of `Pairwise`
  rw [List.pairwise_iff_get]
  intro i j hij
  have hi_lt : (i : Nat) < m := by simpa using (show (i : Nat) < (List.range m).length from i.isLt)
  have hj_lt : (j : Nat) < m := by simpa using (show (j : Nat) < (List.range m).length from j.isLt)
  have hij' : (i : Nat) < (j : Nat) := hij
  have hne : (i : Nat) ≠ (j : Nat) := ne_of_lt hij'
  have hne' : (j : Nat) ≠ (i : Nat) := Ne.symm hne
  -- all elements of `List.range m` are leaves, so clause sets are singletons
  simp [range_get, clauseSetNode_leaf, hi_lt, hj_lt, Finset.disjoint_singleton, hne']

private lemma nthPairChildren_mem {n : Nat} {items : List Nat} (h : n < pairCount items) :
    (nthPairChildren n items).1 ∈ items ∧ (nthPairChildren n items).2 ∈ items := by
  induction n generalizing items with
  | zero =>
      cases items with
      | nil => simpa [pairCount] using h
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using h
          | cons b rest =>
              simp [nthPairChildren]
  | succ n ih =>
      cases items with
      | nil => simpa [pairCount] using h
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using h
          | cons b rest =>
              have h' : n < pairCount rest := by
                simpa [pairCount, Nat.succ_eq_add_one, Nat.add_assoc] using (Nat.lt_of_succ_lt_succ h)
              have ih' := ih (items := rest) h'
              constructor
              ·
                  have : (nthPairChildren n rest).1 ∈ b :: rest := List.mem_cons_of_mem b ih'.1
                  exact List.mem_cons_of_mem a this
              ·
                  have : (nthPairChildren n rest).2 ∈ b :: rest := List.mem_cons_of_mem b ih'.2
                  exact List.mem_cons_of_mem a this

private lemma nthPairChildren_children_disjoint (m n : Nat) (items : List Nat)
    (h_items : ItemsDisjoint m items) (h : n < pairCount items) :
    Disjoint (clauseSetNode m (nthPairChildren n items).1) (clauseSetNode m (nthPairChildren n items).2) := by
  induction n generalizing items with
  | zero =>
      cases items with
      | nil => simpa [pairCount] using h
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using h
          | cons b rest =>
              -- `a` is disjoint from everything in `b :: rest`, in particular `b`
              have hcons : (∀ a' : Nat, a' ∈ (b :: rest) → Disjoint (clauseSetNode m a) (clauseSetNode m a')) ∧
                  ItemsDisjoint m (b :: rest) := by
                simpa [ItemsDisjoint] using (List.pairwise_cons.1 h_items)
              have hab : Disjoint (clauseSetNode m a) (clauseSetNode m b) := hcons.1 b (by simp)
              simpa [nthPairChildren] using hab
  | succ n ih =>
      cases items with
      | nil => simpa [pairCount] using h
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using h
          | cons b rest =>
              have h_tail : ItemsDisjoint m rest := by
                have hbr : ItemsDisjoint m (b :: rest) := (List.pairwise_cons.1 h_items).2
                simpa [ItemsDisjoint] using (List.pairwise_cons.1 hbr).2
              have h' : n < pairCount rest := by
                simpa [pairCount, Nat.succ_eq_add_one, Nat.add_assoc] using (Nat.lt_of_succ_lt_succ h)
              simpa [nthPairChildren] using ih (items := rest) h_tail h'

private lemma nthPairChildren_mem_take_paired {n : Nat} {items : List Nat} (h : n < pairCount items) :
    (nthPairChildren n items).1 ∈ items.take (2 * pairCount items) ∧
      (nthPairChildren n items).2 ∈ items.take (2 * pairCount items) := by
  induction n generalizing items with
  | zero =>
      cases items with
      | nil => simpa [pairCount] using h
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using h
          | cons b rest =>
              -- `take (2 * (pairCount rest + 1)) (a::b::rest)` contains `a` and `b`
              have hmul : 2 * pairCount (a :: b :: rest) = 2 + 2 * pairCount rest := by
                simp [pairCount, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              constructor
              · -- `a` is the head of the taken list
                -- rewrite `2 + t` as `t + 2` so the addition reduces
                rw [hmul]
                rw [Nat.add_comm 2 (2 * pairCount rest)]
                simp [nthPairChildren, pairCount]
              · -- `b` is the second element of the taken list
                rw [hmul]
                rw [Nat.add_comm 2 (2 * pairCount rest)]
                simp [nthPairChildren, pairCount]
  | succ n ih =>
      cases items with
      | nil => simpa [pairCount] using h
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using h
          | cons b rest =>
              have h' : n < pairCount rest := by
                simpa [pairCount, Nat.succ_eq_add_one, Nat.add_assoc] using (Nat.lt_of_succ_lt_succ h)
              have ih' := ih (items := rest) h'
              constructor
              ·
                  -- lift membership from `rest` into the larger `take`
                  have hmem : (nthPairChildren n rest).1 ∈ rest.take (2 * pairCount rest) := ih'.1
                  have htake :
                      (a :: b :: rest).take (2 * pairCount (a :: b :: rest)) =
                        a :: b :: (rest.take (2 * pairCount rest)) := by
                    -- `pairCount (a::b::rest) = pairCount rest + 1`, and `take` of a `2+...` prefix peels two conses
                    have hmul : 2 * pairCount (a :: b :: rest) = 2 + 2 * pairCount rest := by
                      simp [pairCount, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                    rw [hmul]
                    rw [Nat.add_comm 2 (2 * pairCount rest)]
                    simp
                  -- rewrite the target `take`, then lift membership through the two conses
                  rw [htake]
                  exact List.mem_cons_of_mem a (List.mem_cons_of_mem b hmem)
              ·
                  have hmem : (nthPairChildren n rest).2 ∈ rest.take (2 * pairCount rest) := ih'.2
                  have htake :
                      (a :: b :: rest).take (2 * pairCount (a :: b :: rest)) =
                        a :: b :: (rest.take (2 * pairCount rest)) := by
                    have hmul : 2 * pairCount (a :: b :: rest) = 2 + 2 * pairCount rest := by
                      simp [pairCount, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                    rw [hmul]
                    rw [Nat.add_comm 2 (2 * pairCount rest)]
                    simp
                  rw [htake]
                  exact List.mem_cons_of_mem a (List.mem_cons_of_mem b hmem)

private lemma disjoint_union_union {α : Type} [DecidableEq α] (A B C D : Finset α)
    (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C) (hBD : Disjoint B D) :
    Disjoint (A ∪ B) (C ∪ D) := by
  have h1 : Disjoint (A ∪ B) C := (Finset.disjoint_union_left).2 ⟨hAC, hBC⟩
  have h2 : Disjoint (A ∪ B) D := (Finset.disjoint_union_left).2 ⟨hAD, hBD⟩
  exact (Finset.disjoint_union_right).2 ⟨h1, h2⟩

private lemma nthPairChildren_cross_disjoint (m : Nat) :
    ∀ {i j : Nat} {items : List Nat},
      ItemsDisjoint m items →
      i < j →
      j < pairCount items →
      let pi := nthPairChildren i items
      let pj := nthPairChildren j items
      (Disjoint (clauseSetNode m pi.1) (clauseSetNode m pj.1)) ∧
        (Disjoint (clauseSetNode m pi.1) (clauseSetNode m pj.2)) ∧
        (Disjoint (clauseSetNode m pi.2) (clauseSetNode m pj.1)) ∧
        (Disjoint (clauseSetNode m pi.2) (clauseSetNode m pj.2)) := by
  intro i
  induction i with
  | zero =>
      intro j items h_items hij hj
      cases items with
      | nil => simpa [pairCount] using hj
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using hj
          | cons b rest =>
              -- `j` must be `j'+1` since `0 < j`
              cases j with
              | zero => omega
              | succ j' =>
                  have hj' : j' < pairCount rest := by
                    -- `pairCount (a::b::rest) = pairCount rest + 1`
                    simpa [pairCount, Nat.succ_eq_add_one, Nat.add_assoc] using (Nat.lt_of_succ_lt_succ hj)
                  have hjmem := nthPairChildren_mem (items := rest) hj'
                  -- unpack Pairwise facts for `a :: b :: rest`
                  have h1 : (∀ x : Nat, x ∈ (b :: rest) → Disjoint (clauseSetNode m a) (clauseSetNode m x)) ∧
                      ItemsDisjoint m (b :: rest) := by
                    simpa [ItemsDisjoint] using (List.pairwise_cons.1 h_items)
                  have h2 : (∀ x : Nat, x ∈ rest → Disjoint (clauseSetNode m b) (clauseSetNode m x)) ∧
                      ItemsDisjoint m rest := by
                    simpa [ItemsDisjoint] using (List.pairwise_cons.1 h1.2)
                  -- finish by membership-based disjointness (both pairs reduce to `rest`)
                  -- `pi = (a,b)` and `pj = nthPairChildren j' rest`
                  simpa [nthPairChildren] using
                    (And.intro
                      (h1.1 _ (by simp [hjmem.1]))
                      (And.intro
                        (h1.1 _ (by simp [hjmem.2]))
                        (And.intro (h2.1 _ hjmem.1) (h2.1 _ hjmem.2))))
  | succ i ih =>
      intro j items h_items hij hj
      cases items with
      | nil => simpa [pairCount] using hj
      | cons a t =>
          cases t with
          | nil => simpa [pairCount] using hj
          | cons b rest =>
              -- peel two items; both `i` and `j` decrement
              have h_rest : ItemsDisjoint m rest := by
                have hbr : ItemsDisjoint m (b :: rest) := (List.pairwise_cons.1 h_items).2
                simpa [ItemsDisjoint] using (List.pairwise_cons.1 hbr).2
              -- `j` must be `j'+1` since `i+1 < j`
              cases j with
              | zero => omega
              | succ j' =>
                  have hij' : i < j' := Nat.lt_of_succ_lt_succ hij
                  have hj' : j' < pairCount rest := by
                    simpa [pairCount, Nat.succ_eq_add_one, Nat.add_assoc] using (Nat.lt_of_succ_lt_succ hj)
                  -- rewrite both pairs into `rest` and apply IH
                  simpa [nthPairChildren] using ih (j := j') (items := rest) h_rest hij' hj'

private lemma m_le_levelNext (m : Nat) : ∀ k, m ≤ levelNext m k := by
  intro k
  induction k with
  | zero =>
      simp [levelNext, levelState]
  | succ k ih =>
      have : levelNext m k ≤ levelNext m (k + 1) := by
        simp [levelNext_succ, Nat.le_add_right]
      exact le_trans ih this

private lemma clauseSetNode_levelNext_add_eq_union (m k i : Nat) (h_m : m > 1) (h_i : i < levelPairs m k) :
    clauseSetNode m (levelNext m k + i) =
      clauseSetNode m (nthPairChildren i (levelItems m k)).1 ∪
        clauseSetNode m (nthPairChildren i (levelItems m k)).2 := by
  -- rewrite node index as `m + redIdx`
  have h_red : levelOffset m k + i < size m := levelOffset_add_lt_size (m := m) (k := k) (i := i) h_m h_i
  have hmle : m ≤ levelNext m k := m_le_levelNext (m := m) k
  have h_idx : levelNext m k + i = m + (levelOffset m k + i) := by
    have hnext : levelNext m k = m + levelOffset m k := by
      unfold levelOffset
      -- `Nat.sub_add_cancel hmle : levelNext - m + m = levelNext`
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.sub_add_cancel hmle).symm
    calc
      levelNext m k + i = (m + levelOffset m k) + i := by simpa [hnext]
      _ = m + (levelOffset m k + i) := by simp [Nat.add_assoc]
  -- unfold at the corresponding reduction node
  have hunion := clauseSetNode_reduction_eq_union (m := m) (redIdx := levelOffset m k + i) h_red
  -- identify children as the `nthPairChildren` of this level
  have hchild :
      simpleChildIndices 0 m (levelOffset m k + i) = nthPairChildren i (levelItems m k) := by
    simpa using (simpleChildIndices_at_level (m := m) (k := k) (i := i) h_i)
  -- finish
  simpa [h_idx, hchild] using hunion

private lemma ItemsDisjoint_levelItems (m : Nat) (h_m : m > 1) :
    ∀ k, ItemsDisjoint m (levelItems m k) := by
  intro k
  induction k with
  | zero =>
      simp [levelItems, levelState, ItemsDisjoint_range]
  | succ k ih =>
      -- abbreviations
      set items := levelItems m k
      set next := levelNext m k
      set pairs := levelPairs m k
      have h_items : ItemsDisjoint m items := by simpa [items] using ih
      -- split `items` into paired prefix and carry tail
      let n := 2 * pairCount items
      have hpairwise_split :
          (items.take n).Pairwise (fun a b => Disjoint (clauseSetNode m a) (clauseSetNode m b)) ∧
            (items.drop n).Pairwise (fun a b => Disjoint (clauseSetNode m a) (clauseSetNode m b)) ∧
              ∀ a, a ∈ items.take n → ∀ b, b ∈ items.drop n →
                Disjoint (clauseSetNode m a) (clauseSetNode m b) := by
        have hpa :
            (items.take n ++ items.drop n).Pairwise (fun a b => Disjoint (clauseSetNode m a) (clauseSetNode m b)) := by
          simpa [n, items, List.take_append_drop, ItemsDisjoint] using h_items
        simpa using (List.pairwise_append.1 hpa)
      have h_take := hpairwise_split.1
      have h_drop := hpairwise_split.2.1
      have h_cross := hpairwise_split.2.2
      -- show the new nodes (the `range pairs` mapped) are pairwise disjoint
      have h_new :
          ((List.range pairs).map (fun i => next + i)).Pairwise
            (fun a b => Disjoint (clauseSetNode m a) (clauseSetNode m b)) := by
        -- use `pairwise_map` to reduce to a Pairwise statement on `List.range pairs`
        apply (List.pairwise_map).2
        -- now prove Pairwise on indices `i<j<pairs`
        rw [List.pairwise_iff_get]
        intro i j hij
        have hi_lt : (i : Nat) < pairs := by
          simpa [pairs] using (show (i : Nat) < (List.range pairs).length from i.isLt)
        have hj_lt : (j : Nat) < pairs := by
          simpa [pairs] using (show (j : Nat) < (List.range pairs).length from j.isLt)
        have hij' : (i : Nat) < (j : Nat) := hij
        have hgi : (List.range pairs).get i = (i : Nat) := range_get pairs i
        have hgj : (List.range pairs).get j = (j : Nat) := range_get pairs j
        -- expand each new node as a union of its two children (at level `k`)
        have hi_pairs : (i : Nat) < levelPairs m k := by simpa [pairs, levelPairs, items] using hi_lt
        have hj_pairs : (j : Nat) < levelPairs m k := by simpa [pairs, levelPairs, items] using hj_lt
        have hUi := clauseSetNode_levelNext_add_eq_union (m := m) (k := k) (i := (i : Nat)) h_m hi_pairs
        have hUj := clauseSetNode_levelNext_add_eq_union (m := m) (k := k) (i := (j : Nat)) h_m hj_pairs
        -- disjointness between the four child combinations
        have hcross' :=
          nthPairChildren_cross_disjoint (m := m) (i := (i : Nat)) (j := (j : Nat)) (items := items)
            h_items hij' (by simpa [pairs, levelPairs, items] using hj_lt)
        -- package into disjointness of unions
        have hdisj :=
          disjoint_union_union
            (clauseSetNode m (nthPairChildren (i : Nat) items).1)
            (clauseSetNode m (nthPairChildren (i : Nat) items).2)
            (clauseSetNode m (nthPairChildren (j : Nat) items).1)
            (clauseSetNode m (nthPairChildren (j : Nat) items).2)
            hcross'.1 hcross'.2.1 hcross'.2.2.1 hcross'.2.2.2
        -- rewrite the goal into the union form, then close with `hdisj` (avoid simp expanding `Disjoint _ (∪_)`)
        have hUi' :
            clauseSetNode m (next + (i : Nat)) =
              clauseSetNode m (nthPairChildren (i : Nat) items).1 ∪
                clauseSetNode m (nthPairChildren (i : Nat) items).2 := by
          simpa [next, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hUi
        have hUj' :
            clauseSetNode m (next + (j : Nat)) =
              clauseSetNode m (nthPairChildren (j : Nat) items).1 ∪
                clauseSetNode m (nthPairChildren (j : Nat) items).2 := by
          simpa [next, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hUj
        -- `Pairwise` goal uses `get` from `List.range`
        -- so first rewrite those gets, then rewrite by `hUi'`/`hUj'`.
        -- (the goal is `Disjoint (clauseSetNode m (next + (range.get i))) (clauseSetNode m (next + (range.get j)))`)
        -- (after rewriting: `Disjoint (clauseSetNode m (next + i)) (clauseSetNode m (next + j))`)
        simpa [hgi, hgj] using (by
          -- now in the simplified goal
          -- rewrite both sides to unions and finish
          simpa [hUi', hUj'] using hdisj)
      -- now assemble `nextItems`: newNodes ++ carryTail
      have h_items_succ : levelItems m (k + 1) = nextItems next items := by
        simpa [next, items] using (levelItems_succ (m := m) (k := k))
      -- `nextItems next items = newNodes ++ items.drop (2*pairs)`
      unfold nextItems at h_items_succ
      -- restate with `items`/`pairs`/`next`
      have h_items_succ' :
          levelItems m (k + 1) = ((List.range pairs).map (fun i => next + i)) ++ (items.drop (2 * pairs)) := by
        simpa [h_items_succ, pairs, levelPairs, items, next, List.map_append, List.map_map, Nat.add_assoc]
      -- prove Pairwise on the append via `pairwise_append`
      unfold ItemsDisjoint
      -- show: Pairwise R (newNodes ++ tail)
      rw [h_items_succ']
      -- use `pairwise_append` characterization
      rw [List.pairwise_append]
      refine ⟨h_new, ?_, ?_⟩
      · -- tail is a drop of `items`, so inherits Pairwise from the split lemma
        simpa [pairs, levelPairs, items, n] using h_drop
      · intro a ha b hb
        -- `a` is a fresh node `next + i` for some `i < pairs`
        rcases List.mem_map.1 ha with ⟨i, hi, rfl⟩
        have hi_lt : i < pairs := by simpa [List.mem_range] using hi
        have hi_pairs : i < levelPairs m k := by simpa [pairs, levelPairs, items] using hi_lt
        have hU := clauseSetNode_levelNext_add_eq_union (m := m) (k := k) (i := i) h_m hi_pairs
        -- `b` is in the carry tail `items.drop (2*pairs)`, so also in `items.drop n`
        have hb' : b ∈ items.drop n := by
          simpa [n, pairs, levelPairs, items] using hb
        -- children are in the paired prefix `items.take n`
        have hmem := nthPairChildren_mem_take_paired (items := items) (n := i) (by simpa [pairs, levelPairs, items] using hi_lt)
        have h1 : Disjoint (clauseSetNode m (nthPairChildren i items).1) (clauseSetNode m b) :=
          h_cross _ hmem.1 _ hb'
        have h2 : Disjoint (clauseSetNode m (nthPairChildren i items).2) (clauseSetNode m b) :=
          h_cross _ hmem.2 _ hb'
        -- conclude union disjointness
        have : Disjoint (clauseSetNode m (nthPairChildren i items).1 ∪ clauseSetNode m (nthPairChildren i items).2)
            (clauseSetNode m b) :=
          (Finset.disjoint_union_left).2 ⟨h1, h2⟩
        -- avoid `simp` rewriting `Disjoint (A ∪ B) _` into a conjunction
        have hU' :
            clauseSetNode m (next + i) =
              clauseSetNode m (nthPairChildren i items).1 ∪ clauseSetNode m (nthPairChildren i items).2 := by
          simpa [next] using hU
        rw [hU']
        exact this

private lemma levelItems_length_pos (m k : Nat) (h_m0 : 0 < m) : 0 < (levelItems m k).length := by
  induction k with
  | zero =>
      simp [levelItems, levelState, h_m0]
  | succ k ih =>
      have h_items :
          levelItems m (k + 1) = nextItems (levelNext m k) (levelItems m k) :=
        levelItems_succ (m := m) (k := k)
      -- rewrite the goal to the `nextItems` view, then case-split on the current frontier list
      rw [h_items]
      cases hL : levelItems m k with
      | nil =>
          -- impossible: the frontier is never empty when `m > 0`
          have : False := by simpa [hL] using ih
          cases this
      | cons a t =>
          cases t with
          | nil =>
              -- singleton: `pairCount = 0`, so the item is carried upward
              simp [nextItems, pairCount, hL]
          | cons b rest =>
              -- at least 2 items: show `0 < len - pairCount` then use `nextItems_length`
              have h2 :
                  2 * pairCount (a :: b :: rest) ≤ (a :: b :: rest).length :=
                two_mul_pairCount_le_length (items := a :: b :: rest)
              have hpc_pos : 0 < pairCount (a :: b :: rest) := by simp [pairCount]
              have hpc1_le_2pc :
                  pairCount (a :: b :: rest) + 1 ≤ 2 * pairCount (a :: b :: rest) := by
                have : 1 ≤ pairCount (a :: b :: rest) := Nat.succ_le_iff.2 hpc_pos
                have : pairCount (a :: b :: rest) + 1 ≤
                    pairCount (a :: b :: rest) + pairCount (a :: b :: rest) := by omega
                simpa [two_mul] using this
              have hpc1_le_len :
                  pairCount (a :: b :: rest) + 1 ≤ (a :: b :: rest).length :=
                le_trans hpc1_le_2pc h2
              have hpc_lt_len :
                  pairCount (a :: b :: rest) < (a :: b :: rest).length :=
                lt_of_lt_of_le (Nat.lt_succ_self _) hpc1_le_len
              have hpos :
                  0 < (a :: b :: rest).length - pairCount (a :: b :: rest) :=
                Nat.sub_pos_of_lt hpc_lt_len
              have hlen :
                  (nextItems (levelNext m k) (a :: b :: rest)).length =
                    (a :: b :: rest).length - pairCount (a :: b :: rest) := by
                simpa using
                  (nextItems_length (nextNodeIdx := levelNext m k) (items := a :: b :: rest))
              -- close via the length formula
              simpa [hlen] using hpos

private lemma levelOffset_le_size (m k : Nat) (h_m : m > 1) : levelOffset m k ≤ size m := by
  have h_m0 : 0 < m := by omega
  have hlen_pos : 0 < (levelItems m k).length := levelItems_length_pos (m := m) (k := k) h_m0
  have hlen_ge1 : 1 ≤ (levelItems m k).length := Nat.succ_le_iff.2 hlen_pos
  have hinv := levelOffset_add_length_levelItems (m := m) k
  have hoff : levelOffset m k = m - (levelItems m k).length := by
    have := congrArg (fun t => t - (levelItems m k).length) hinv
    simpa [Nat.add_sub_cancel] using this
  have h_off_le_m1 : levelOffset m k ≤ m - 1 := by
    rw [hoff]
    exact Nat.sub_le_sub_left hlen_ge1 m
  have hsize : size m = m - 1 := by
    have : ¬ m ≤ 1 := by omega
    simp [size, this]
  simpa [hsize] using h_off_le_m1

private lemma pairCount_pos_of_length_ge_two {α : Type} (items : List α) (h : 2 ≤ items.length) :
    0 < pairCount items := by
  cases items with
  | nil => simpa using h
  | cons a t =>
      cases t with
      | nil => simpa using h
      | cons b rest =>
          simp [pairCount]

private lemma levelPairs_pos_of_offset_lt (m k : Nat) (h_m : m > 1) (h_off : levelOffset m k < size m) :
    0 < levelPairs m k := by
  have hsize : size m = m - 1 := by
    have : ¬ m ≤ 1 := by omega
    simp [size, this]
  have hinv := levelOffset_add_length_levelItems (m := m) k
  have hlen : (levelItems m k).length = m - levelOffset m k := by
    have := congrArg (fun t => t - levelOffset m k) hinv
    simpa [Nat.add_sub_cancel_left] using this
  have hlen_ge : 2 ≤ (levelItems m k).length := by
    -- `offset < m-1` implies `m - offset ≥ 2`
    have : levelOffset m k ≤ m - 2 := by omega
    omega
  unfold levelPairs
  exact pairCount_pos_of_length_ge_two (items := levelItems m k) hlen_ge

private lemma levelOffset_ge_id (m : Nat) (h_m : m > 1) :
    ∀ k, k ≤ size m → k ≤ levelOffset m k := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k ≤ size m := by omega
      have ih' : k ≤ levelOffset m k := ih hk'
      -- either we are already at the final offset, or we advance by at least 1
      by_cases h_eq : levelOffset m k = size m
      · -- stable: `offset(k+1) = offset(k) + pairs = size + 0 = size`
        have : k + 1 ≤ size m := by omega
        have : k + 1 ≤ levelOffset m k := by simpa [h_eq] using this
        have hmono : levelOffset m k ≤ levelOffset m (k + 1) := by
          simp [levelOffset_succ, Nat.le_add_right]
        exact le_trans this hmono
      · -- strict: `offset k < size`, so `pairs > 0` and offset increases
        have h_lt : levelOffset m k < size m := lt_of_le_of_ne (levelOffset_le_size (m := m) (k := k) h_m) h_eq
        have hpairs : 0 < levelPairs m k := levelPairs_pos_of_offset_lt (m := m) (k := k) h_m h_lt
        have hoff : levelOffset m (k + 1) = levelOffset m k + levelPairs m k := levelOffset_succ (m := m) (k := k)
        have : k + 1 ≤ levelOffset m k + levelPairs m k := by omega
        simpa [hoff] using this

private lemma levelOffset_at_size (m : Nat) (h_m : m > 1) : levelOffset m (size m) = size m := by
  have hle : size m ≤ levelOffset m (size m) :=
    levelOffset_ge_id (m := m) h_m (size m) (by rfl)
  have hge : levelOffset m (size m) ≤ size m := levelOffset_le_size (m := m) (k := size m) h_m
  exact le_antisymm hge hle

private lemma exists_level_rep (m redIdx : Nat) (h_m : m > 1) (h_red : redIdx < size m) :
    ∃ k i, i < levelPairs m k ∧ redIdx = levelOffset m k + i := by
  -- choose the first `k` such that `redIdx < levelOffset (k+1)`
  have hex : ∃ k, redIdx < levelOffset m (k + 1) := by
    refine ⟨size m - 1, ?_⟩
    have hpos : 0 < size m := by omega
    have : size m - 1 + 1 = size m := Nat.sub_add_cancel (Nat.succ_le_iff.2 hpos)
    -- `levelOffset (size) = size`, so `redIdx < size = levelOffset (size)`
    simpa [this, levelOffset_at_size (m := m) h_m] using h_red
  let k0 := Nat.find hex
  have hk0 : redIdx < levelOffset m (k0 + 1) := Nat.find_spec hex
  have hk0_min : ∀ k < k0, ¬ redIdx < levelOffset m (k + 1) := by
    intro k hk hk'
    have : k0 ≤ k := Nat.find_min' hex (m := k) hk'
    exact Nat.not_le_of_gt hk this
  have hle : levelOffset m k0 ≤ redIdx := by
    by_cases hk0z : k0 = 0
    · simpa [hk0z, levelOffset_zero]
    · have hk0pos : 0 < k0 := Nat.pos_of_ne_zero hk0z
      have hk1_lt : k0 - 1 < k0 := Nat.sub_lt hk0pos (by omega)
      have hnot : ¬ redIdx < levelOffset m ((k0 - 1) + 1) := hk0_min (k0 - 1) hk1_lt
      have hnot' : ¬ redIdx < levelOffset m k0 := by
        simpa [Nat.sub_add_cancel (Nat.succ_le_iff.2 hk0pos)] using hnot
      exact le_of_not_gt hnot'
  let i := redIdx - levelOffset m k0
  have hi : i < levelPairs m k0 := by
    have hk0' : redIdx < levelOffset m (1 + k0) := by
      simpa [Nat.add_comm] using hk0
    have hoff : levelOffset m (1 + k0) = levelOffset m k0 + levelPairs m k0 := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (levelOffset_succ (m := m) (k := k0))
    have hlt : redIdx < levelOffset m k0 + levelPairs m k0 := by
      simpa [hoff, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk0'
    have : redIdx - levelOffset m k0 < levelPairs m k0 :=
      Nat.sub_lt_left_of_lt_add hle hlt
    simpa [i] using this
  refine ⟨k0, i, hi, ?_⟩
  have : redIdx = (redIdx - levelOffset m k0) + levelOffset m k0 :=
    (Nat.sub_add_cancel hle).symm
  simpa [i, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

theorem simpleChildIndices_add (clauseBase m redIdx : Nat) (h_m : m > 1) (h_red : redIdx < size m) :
    simpleChildIndices clauseBase m redIdx =
      (clauseBase + (simpleChildIndices 0 m redIdx).1, clauseBase + (simpleChildIndices 0 m redIdx).2) := by
  rcases exists_level_rep (m := m) (redIdx := redIdx) h_m h_red with ⟨k, i, hi, hrepr⟩
  subst hrepr
  have h0 : simpleChildIndices 0 m (levelOffset m k + i) = nthPairChildren i (levelItems m k) := by
    simpa using (simpleChildIndices_at_level (m := m) (k := k) (i := i) hi)
  have hb :
      simpleChildIndices clauseBase m (levelOffset m k + i) =
        (clauseBase + (nthPairChildren i (levelItems m k)).1, clauseBase + (nthPairChildren i (levelItems m k)).2) := by
    simpa using
      (simpleChildIndices_at_level_add (clauseBase := clauseBase) (m := m) (k := k) (i := i) hi)
  simpa [h0] using hb

theorem clauseSetNode_children_disjoint (m redIdx : Nat) (h_m : m > 1) (h_red : redIdx < size m) :
    let l := (simpleChildIndices 0 m redIdx).1
    let r := (simpleChildIndices 0 m redIdx).2
    Disjoint (clauseSetNode m l) (clauseSetNode m r) := by
  rcases exists_level_rep (m := m) (redIdx := redIdx) h_m h_red with ⟨k, i, hi, hrepr⟩
  -- rewrite the child computation to the `nthPairChildren` view at level `k`
  have hsc : simpleChildIndices 0 m redIdx = nthPairChildren i (levelItems m k) := by
    subst hrepr
    simpa using (simpleChildIndices_at_level (m := m) (k := k) (i := i) hi)
  have h_items : ItemsDisjoint m (levelItems m k) := ItemsDisjoint_levelItems (m := m) h_m k
  have hi' : i < pairCount (levelItems m k) := by simpa [levelPairs] using hi
  have hdisj := nthPairChildren_children_disjoint (m := m) (n := i) (items := levelItems m k) h_items hi'
  -- unpack `l`/`r`
  simpa [hsc] using hdisj

/- Axiom audit: core functions and key theorems. -/
#print axioms depth
#print axioms size
#print axioms simpleChildIndices
#print axioms simpleChildIndices_children_less_than_parent
#print axioms clauseSetNode
#print axioms clauseDescendantCount
#print axioms clauseDescendantCount_le

end LStar.Construction.BalancedBinaryTree
