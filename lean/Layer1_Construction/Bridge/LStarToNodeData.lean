import Layer0_Foundations.SCL.NodeData
import Layer0_Foundations.SCL.SCLNode
import Layer1_Construction.Core.InstanceOps
import Layer1_Construction.Core.SeedChain
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

/-! ## LStarToNodeData: L* Instance → SCL NodeData Bridge

**Main Definitions**: `NodeDataFull` - Transform L* instance at cut C into SCL NodeData structure.

**Mathematical Content**:
For L* instance L and cut C ⊆ V, construct NodeData N where:
```
Unknown = Σ_{v∈C} Fin (R_v)  (all unresolved bits across cut)
Known = Π_{v∈C} ParentHistory_v  (all parent seed assignments)
State = Π_{v∈C} Seed_v  (all vertex seeds)
state(k, a) = (λ v. encodeSeed_v(k(v), emergent_v(a)))  (seed encoding per vertex)
```

**Key Theorems**:
1. **NodeDataFull_keyed**: A2 (encodeSeed injective) → keyedness (distinct assignments → distinct states)
2. **NodeDataFull_satisfies_SCL**: Keyedness → SCL_node bound (|State| ≥ 2^λ)
3. **lambda_sum_R**: λ(C) = Σ_{v∈C} R_v (emergent bits sum)

**Why This Matters - A2 Injectivity Bridges to SCL Keyedness**:

This file solves the bridge problem:
```
L* Property A2 (encodeSeed injective)
  ↓  NodeDataFull construction  ↓
NodeData property (keyed: distinct assignments → distinct states)
  ↓  SCL_node theorem (Layer 0)  ↓
Information bound: |State| ≥ 2^λ
```

**How the Bridge Works**:
- Define state function using encodeSeed: state(k, a) = (λ v. encodeSeed_v(k(v), emergent_v(a)))
- Prove: Different assignments → different emergents (by emergence matrix)
- Apply: encodeSeed injective → different seeds (A2)
- Result: Different assignments → different states (keyedness) ✓

**Significance**: Axiom-free connection! A2 is PROVEN (SeedChain.lean), keyedness is PROVEN
(this file), therefore SCL bounds apply with zero additional axioms.

**Trust Boundary**: Proven theorems (no custom axioms). Uses encodeSeed_injective from SeedChain.

**Paper**: §7 "SCL Application to L*", §6 "A2 Injectivity", §7.2.1 "Keyedness from A2".

See Layer1_Construction/Layer1_README.md for A2 property details.
-/

namespace LStar

noncomputable section

open scoped Classical

variable (L : LStarInstanceFull)

/-- Subtype of vertices in a cut. -/
abbrev InCut (C : Finset (Fin L.dag.n)) := { v : Fin L.dag.n // v ∈ C }

/-- Unknown indices at cut `C`: local emergent coordinates per vertex. -/
def UnknownIdxFull (C : Finset (Fin L.dag.n)) : Type :=
  Sigma (fun v : InCut L C => Fin (L.R v))

namespace UnknownIdxFull

noncomputable instance instDecidableEq (C : Finset (Fin L.dag.n)) : DecidableEq (UnknownIdxFull L C) := by
  infer_instance

end UnknownIdxFull

/-- Known information at `C`: provide parent histories for each `v ∈ C`. -/
def KnownFull (C : Finset (Fin L.dag.n)) : Type :=
  (v : InCut L C) → ParentHistory L v

namespace KnownFull

noncomputable instance instDecidableEq (C : Finset (Fin L.dag.n)) : DecidableEq (KnownFull L C) := by
  classical
  infer_instance

noncomputable instance instInhabited (C : Finset (Fin L.dag.n)) : Inhabited (KnownFull L C) := by
  classical
  -- Constant-zero parent histories supply an inhabitant for any `v`.
  refine ⟨fun _v (_u : {u // u ∈ L.dag.parents _}) => LStar.zero _⟩

-- Finiteness is provided locally in NodeDataFull via `Fintype.ofFinite`.

end KnownFull

/-- Observable state at `C`: the per-vertex seeds after encoding. -/
def StateFull (C : Finset (Fin L.dag.n)) : Type :=
  (v : InCut L C) → Seed (L.seedWidth v)

namespace StateFull

noncomputable instance instDecidableEq (C : Finset (Fin L.dag.n)) : DecidableEq (StateFull L C) := by
  classical
  infer_instance

-- Finiteness is provided locally in NodeDataFull via `Fintype.ofFinite`.

end StateFull

/-- Finite instance for InCut (subtype of Finset). -/
noncomputable instance instFinite_InCut (C : Finset (Fin L.dag.n)) :
  Finite (InCut L C) :=
  Finset.finite_toSet C

/-- Finite instance for UnknownIdxFull (Sigma of Finite types). -/
noncomputable instance instFinite_UnknownIdxFull (C : Finset (Fin L.dag.n)) :
  Finite (UnknownIdxFull L C) := by
  classical
  -- UnknownIdxFull is definitionally Sigma (v : InCut) => Fin (L.R v)
  -- Unfold the definition and use that Sigma of Finite types is Finite
  show Finite (Sigma (fun v : InCut L C => Fin (L.R v)))
  have _ : Finite (InCut L C) := instFinite_InCut L C
  have _ : ∀ v : InCut L C, Finite (Fin (L.R v)) := fun _ => inferInstance
  infer_instance

/-- Finite instance for KnownFull (Pi type from Finite to Finite). -/
noncomputable instance instFinite_KnownFull (C : Finset (Fin L.dag.n)) :
  Finite (KnownFull L C) := by
  classical
  -- KnownFull is definitionally Pi over InCut to ParentHistory
  show Finite ((v : InCut L C) → ParentHistory L v)
  have _ : Finite (InCut L C) := instFinite_InCut L C
  have _ : ∀ (v : InCut L C), Finite (ParentHistory L v) := by
    intro v
    show Finite ((u : parentSubtype L v) → Seed (L.seedWidth u.1))
    have _ : Finite (parentSubtype L v) := inferInstance
    have _ : ∀ u : parentSubtype L v, Finite (Seed (L.seedWidth u.1)) :=
      fun u => @Fintype.finite _ (Seed.instFintype (L.seedWidth u.1))
    infer_instance
  infer_instance

/-- Finite instance for StateFull. -/
noncomputable instance instFinite_StateFull (C : Finset (Fin L.dag.n)) :
  Finite (StateFull L C) := by
  classical
  -- StateFull is definitionally Pi from InCut to Seed
  show Finite ((v : InCut L C) → Seed (L.seedWidth v))
  have _ : Finite (InCut L C) := instFinite_InCut L C
  have _ : ∀ v : InCut L C, Finite (Seed (L.seedWidth v)) :=
    fun v => @Fintype.finite _ (Seed.instFintype (L.seedWidth v))
  infer_instance

/-- Fintype instance for UnknownIdxFull (needed for cardinality calculations). -/
noncomputable instance instFintype_UnknownIdxFull (C : Finset (Fin L.dag.n)) :
  Fintype (UnknownIdxFull L C) :=
  Fintype.ofFinite _

/-- NodeData for the full instance at cut `C`. -/
def NodeDataFull (C : Finset (Fin L.dag.n)) : NodeData where
  Known := KnownFull L C
  UnknownIdx := UnknownIdxFull L C
  State := StateFull L C
  dec_K := by classical exact inferInstance
  inh_K := by classical exact inferInstance
  dec_I := by classical exact inferInstance
  dec_S := by classical exact inferInstance
  fin_K := by
    classical
    exact Fintype.ofFinite (KnownFull L C)
  fin_I := by
    classical
    -- Build Finiteness for the sigma type and convert to Fintype
    have _ : Finite (InCut L C) := inferInstance
    have _ : ∀ v : InCut L C, Finite (Fin (L.R v)) := fun v => inferInstance
    exact Fintype.ofFinite (UnknownIdxFull L C)
  fin_S := by
    classical
    exact Fintype.ofFinite (StateFull L C)
  state := by
    intro ⟨kHist, assign⟩
    classical
    -- Build emergent vector by slicing assignment on sigma index
    let emergentOf : (v : InCut L C) → Vector Bool (L.R v) :=
      fun v => Vector.ofFn (fun i : Fin (L.R v) => assign ⟨v, i⟩)
    -- Encode seeds from parent history and emergent bits
    exact fun v => encodeSeed L v (kHist v) (emergentOf v)

/-- Direct keyedness: different assignments change at least one emergent coordinate,
    which changes the corresponding encoded seed by A2 injectivity. -/
theorem NodeDataFull_keyed (C : Finset (Fin L.dag.n)) :
  NodeData.keyed (NodeDataFull L C) := by
  classical
  intro kHist a1 a2 hneq hstate
  -- Find a coordinate where assignments differ
  have hx : ∃ x, a1 x ≠ a2 x := by
    -- If equal everywhere, then functions are equal
    by_contra hforall
    apply hneq
    funext x
    by_contra hx'
    exact hforall ⟨x, hx'⟩
  rcases hx with ⟨⟨v,i⟩, hbit⟩
  -- Consider the output at vertex `v`
  have hget := congrArg (fun (st : StateFull L C) => (st v)) hstate
  -- Define emergent vectors under a1 and a2
  let e1 : Vector Bool (L.R v) := Vector.ofFn (fun j : Fin (L.R v) => a1 ⟨v, j⟩)
  let e2 : Vector Bool (L.R v) := Vector.ofFn (fun j : Fin (L.R v) => a2 ⟨v, j⟩)
  have he_diff : e1 ≠ e2 := by
    intro heq
    have := congrArg (fun (w : Vector Bool (L.R v)) => w.get i) heq
    -- Bits differ at i by assumption; use Vector/Array indexing
    simp only [e1, e2, Vector.get, Vector.ofFn, Array.getElem_ofFn] at this
    exact hbit this
  -- Capacity lemma for vertex `v`
  have hcap := parentBits_le_from_seedWidth_ok L v
  -- Apply A2 injectivity at vertex `v`
  have hinj := encodeSeed_injective L v hcap (kHist v) (kHist v) e1 e2 (Or.inr he_diff)
  -- But `hget` states encoded seeds are equal, contradiction
  exact hinj hget

/-- Direct SCL bound at cut `C` using the full NodeData. -/
theorem NodeDataFull_satisfies_SCL (C : Finset (Fin L.dag.n)) :
  let N := NodeDataFull L C
  Fintype.card N.State ≥ 2 ^ NodeData.lambda N := by
  classical
  have hkey := NodeDataFull_keyed (L := L) C
  simpa using NodeData.SCL_node (NodeDataFull L C) hkey

/-- Λ(C) equals the sum of `R v` over the cut, by cardinality of the sigma index. -/
theorem lambda_sum_R (C : Finset (Fin L.dag.n)) :
  NodeData.lambda (NodeDataFull L C) = Fintype.card (UnknownIdxFull L C) := rfl

/- Axiom audit: Bridge from L* to NodeData, establishing keyedness and SCL bound.
   Core definitions and theorems connecting Layer 1 construction to Layer 0 framework.
   Relies on encodeSeed_injective (A2) and SCL_node theorem. -/
#print axioms UnknownIdxFull
#print axioms KnownFull
#print axioms StateFull
#print axioms NodeDataFull
#print axioms NodeDataFull_keyed
#print axioms NodeDataFull_satisfies_SCL
#print axioms lambda_sum_R

end

end LStar
