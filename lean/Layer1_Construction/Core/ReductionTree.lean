import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
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

/- Axiom audit: core functions and key theorems. -/
#print axioms depth
#print axioms size
#print axioms simpleChildIndices
#print axioms simpleChildIndices_children_less_than_parent
#print axioms clauseSetNode
#print axioms clauseDescendantCount
#print axioms clauseDescendantCount_le

end LStar.Construction.ReductionTree
