import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Range
import Mathlib.Tactic.Ring

/-! ## ReductionTree: Logarithmic-Depth Clause Combination

Balanced reduction tree used to combine `m` clause outputs into a single result
with logarithmic depth.

Reduction nodes are indexed sequentially, level by level from bottom to top.
For **odd** arities we **carry** the unpaired last item upward (we do not duplicate it).

This yields:
- depth `O(log m)`
- exactly `m - 1` reduction nodes for `m > 0`
- structural acyclicity by construction: every node’s children have smaller indices.
-/

namespace LStar.Construction.ReductionTree

/-!
## Tree Size Computation
-/

/-- Number of items at each reduction level.

Level 0 has `m` items.
Level `k+1` has `⌈(items at level k)/2⌉` items. -/
def nodesAtLevel (m : Nat) : Nat → Nat
  | 0 => m
  | k + 1 => (nodesAtLevel m k + 1) / 2

/-- Depth of reduction tree for `m` leaves (a conservative `⌈log₂ m⌉` bound). -/
def depth (m : Nat) : Nat :=
  if m ≤ 1 then 0 else Nat.log 2 m + 1

/-- Total number of internal reduction nodes. -/
def size (m : Nat) : Nat :=
  if m ≤ 1 then 0 else m - 1

/-!
## Node Indexing and Child Pointers

We start with the ordered list of clause indices:
`[clauseBase, clauseBase+1, ..., clauseBase+m-1]`.
At each reduction level we:
- combine adjacent pairs `(a,b)` into a new node with the next unused index, and
- carry an unpaired last item unchanged.

This assigns reduction nodes indices:
`clauseBase+m, clauseBase+m+1, ..., clauseBase+m+(size m)-1`.
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

/-- Child indices for reduction node `redIdx`, assuming `m` clause nodes start at `clauseBase`.

Global indices:
- clauses: `clauseBase .. clauseBase + m - 1`
- reductions: `clauseBase + m .. clauseBase + m + size m - 1` -/
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

/-- Children are always before their parents in the indexing scheme.

For reduction node at global index `(clauseBase + m + redIdx)`, both children
have indices `< (clauseBase + m + redIdx)`. -/
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
## Clause Descendant Counting

For seed-width bounds we need: for every reduction node, the number of distinct
clause leaves in its subtree is ≤ `m`.

We define the clause-leaf set of a **global** node index (`0..m-1` for leaves,
`m..m+size m-1` for reduction nodes) by recursion on the parent index using
`simpleChildIndices 0 m`.
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

/-- Clause-leaf set for reduction node `redIdx` (0-based among reduction nodes). -/
def clauseSet (m redIdx : Nat) : Finset Nat :=
  clauseSetNode m (m + redIdx)

/-- Clause descendant count for reduction node `redIdx` (cardinality of its leaf-set). -/
def clauseDescendantCount (m redIdx : Nat) : Nat :=
  (clauseSet m redIdx).card

lemma clauseSetNode_subset_range (m idx : Nat) :
    clauseSetNode m idx ⊆ Finset.range m :=
  (clauseSetNodeWithProof m idx).2

/-- Clause descendants never exceed total clauses. -/
theorem clauseDescendantCount_le (m redIdx : Nat)
    (_h_m : m > 1) (_h_redIdx : redIdx < size m) :
    clauseDescendantCount m redIdx ≤ m := by
  unfold clauseDescendantCount
  calc
    (clauseSet m redIdx).card ≤ (Finset.range m).card := by
      exact Finset.card_le_card (clauseSetNode_subset_range m (m + redIdx))
    _ = m := by simp

/-!
## Tight-path unfold lemmas

These are used downstream when turning “seedWidth sums along the reduction tree” into a statement
about “how many clause leaves are under a node”.
-/

lemma clauseSetNode_leaf (m idx : Nat) (h : idx < m) :
    clauseSetNode m idx = {idx} := by
  unfold clauseSetNode
  unfold clauseSetNodeWithProof
  rw [Nat.strongRecOn'_beta]
  simp [h]

/-- Unfold `clauseSetNode` at a valid reduction node: it is the union of its children’s clause sets. -/
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
## Level-by-level indexing facts (tight-path infrastructure)

These lemmas model the reduction process “level by level” and give arithmetic invariants about
how many internal nodes have been allocated after `k` levels. They are used by the airtight
disjointness/additivity proof (next step).
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

/-!
## Disjointness (airtight path)

To turn “seedWidth = parent sum” into an `nclauses × nvars` bound, we need additivity:
the left and right subtrees under any reduction node must have disjoint clause-leaf sets.
-/

private def ItemsDisjoint (m : Nat) (items : List Nat) : Prop :=
  items.Pairwise (fun a b => Disjoint (clauseSetNode m a) (clauseSetNode m b))

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

/- Axiom audit: core functions and key theorems. -/
#print axioms depth
#print axioms size
#print axioms simpleChildIndices
#print axioms simpleChildIndices_children_less_than_parent
#print axioms clauseSetNode
#print axioms clauseDescendantCount
#print axioms clauseDescendantCount_le

end LStar.Construction.ReductionTree
