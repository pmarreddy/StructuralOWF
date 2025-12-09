import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mathlib.Order.PiLex
import Mathlib.Order.Synonym
import Layer0_Foundations.Base.CNF
import Layer2_StructuralOWF.Extractor.Extractor

/-! ## RandomnessSpace: Finite Randomness Domain for Probability Analysis

**Main Structure**: `RandomnessN numGates numVars` - Finite randomness space for OWF input domain.

**Structure**:
```lean
structure RandomnessN (dgLen : Nat) (numGates : Nat) (numVars : Nat) where
  assignment : Fin numVars → Bool  (variable assignments)
  gateDigests : Vector (Vector Bool dgLen) numGates  (FG digests)
  structuralBits : Vector Bool numGates  (auxiliary bits)
```

**Why finite**: Enables probability calculations over uniform inputs. Avoids infinite
function space `Assignment = Nat → Bool` by restricting to `Fin numVars → Bool`.

**Type design**: Separate `numGates` and `numVars` parameters ensure correct dimensions
(assignment has φ.nvars bits for CNF formulas).

**Key instances**:
- `Fintype RandomnessN`: Enables cardinality reasoning
- `LinearOrder RandomnessN`: Enables lex-min witness selection (via transport)

**Trust Boundary**: Axiom-free (standard Lean foundations only).

**Paper**: §8 "Randomness Domain for Probability Analysis", §2.1 "Finite Input Spaces"

See Layer3_InformationBounds/Layer3_README.md for randomness structure and probability context.
-/

namespace LStar.StructuralOWF.Foundations

open LStar
open LStar.StructuralOWF
open Classical

/-- **Fintype instance for Vector via equivalence with (Fin n → α).**

Vector α n is mathematically equivalent to (Fin n → α):
- Forward: Vector.ofFn constructs a vector from a function
- Backward: Vector.get accesses elements by index
- These form an equivalence, allowing Fintype transport
-/
noncomputable instance vectorFintype {α : Type*} [Fintype α] {n : Nat} :
    Fintype (Vector α n) :=
  Fintype.ofEquiv (Fin n → α) ⟨
    Vector.ofFn,
    Vector.get,
    fun f => funext fun i => Vector.getElem_ofFn i.2,
    fun v => by ext i h; exact Vector.getElem_ofFn h⟩

/-- Finite randomness space with parametric digest length.

  - `dgLen`: digest length (e.g., (log n)² for QP-sharp, n for exponential)
  - `numGates`: number of FG gates (typically 1 for single-gate construction)
  - `numVars`: number of CNF variables (typically φ.nvars)
  - `assignment`: truth values for `numVars` variables
  - `gateDigests`: `numGates` digests, each `dgLen` bits
  - `structuralBits`: `numGates` auxiliary bits

**Type design**: Parametric dgLen supports QP-sharp ((log n)²) and exponential (n) profiles.
-/
structure RandomnessN (dgLen : Nat) (numGates : Nat) (numVars : Nat) where
  assignment : Fin numVars → Bool
  gateDigests : Vector (Vector Bool dgLen) numGates
  structuralBits : Vector Bool numGates
  deriving DecidableEq, Repr

/-- Product type isomorphic to RandomnessN -/
abbrev RandomnessNProduct (dgLen : Nat) (numGates : Nat) (numVars : Nat) :=
  (Fin numVars → Bool) × Vector (Vector Bool dgLen) numGates × Vector Bool numGates

/-- **Equivalence between RandomnessN and its product representation.**

This allows transporting the Fintype instance from the product type
(which has automatic instances) to the structure type.
-/
def randomnessNEquiv (dgLen numGates numVars : Nat) :
    RandomnessN dgLen numGates numVars ≃ RandomnessNProduct dgLen numGates numVars where
  toFun r := (r.assignment, r.gateDigests, r.structuralBits)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv r := by cases r; rfl
  right_inv p := by obtain ⟨a, g, s⟩ := p; rfl

/-- Fintype instance for RandomnessN via equivalence with product type.

RandomnessN dgLen numGates numVars is finite because each field is finite:
- assignment: |Fin numVars → Bool| = 2^numVars
- gateDigests: |Vector (Vector Bool dgLen) numGates| = (2^dgLen)^numGates
- structuralBits: |Vector Bool numGates| = 2^numGates

Proof: Transport Fintype from product type via randomnessNEquiv. -/
noncomputable instance (dgLen numGates numVars : Nat) : Fintype (RandomnessN dgLen numGates numVars) :=
  Fintype.ofEquiv (RandomnessNProduct dgLen numGates numVars) (randomnessNEquiv dgLen numGates numVars).symm

namespace RandomnessN

/-- Extend a bounded assignment `Fin numVars → Bool` to a total `Nat → Bool` by
    defaulting out-of-range indices to `false`.

Uses numVars parameter to correctly extend assignment to the number of CNF variables. -/
def extendAssign (numVars : Nat) (σ : Fin numVars → Bool) : Assignment :=
  fun i => if h : i < numVars then σ ⟨i, h⟩ else false

/-- Convert `RandomnessN dgLen 1 numVars` to the full `Randomness`.
    With the single-gate constraint, numGates = 1.

    Uses numVars for assignment extension to correctly represent CNFs with many variables.
    The dgLen parameter specifies digest length (e.g., (log n)² for QP-sharp).

    **Note**: Pads structuralBits with zeros to meet the 64-bit salt requirement. -/
def toRandomness (dgLen numVars : Nat) (h_dgLen_pos : dgLen > 0) (r : RandomnessN dgLen 1 numVars) : Randomness :=
  { dgLen := dgLen
    h_dgLen_pos := h_dgLen_pos
    assignment := extendAssign numVars r.assignment  -- Extends assignment to numVars variables
    gateDigests := r.gateDigests.toList
    -- Pad structuralBits to length 64 (required for h_sufficient_salts)
    structuralBits := r.structuralBits.toList ++ List.replicate 63 false
    h_single_gate := by
      -- gateDigests is a Vector of length 1, so toList has length 1
      have : r.gateDigests.toList.length = 1 := by
        obtain ⟨arr, h_size⟩ := r.gateDigests
        simp [Vector.toList]
        exact h_size
      exact this
    h_sufficient_salts := by
      -- structuralBits.toList has length 1, plus 63 padding = 64 total
      have h_orig : r.structuralBits.toList.length = 1 := by
        obtain ⟨arr, h_size⟩ := r.structuralBits
        simp [Vector.toList]
        exact h_size
      simp [List.length_append] }

/-- The finite randomness space is nonempty for all dgLen, gate and variable counts. -/
theorem nonempty (dgLen numGates numVars : Nat) : Nonempty (RandomnessN dgLen numGates numVars) := by
  classical
  refine ⟨{ assignment := (fun _ => false)
           , gateDigests := Vector.replicate numGates (Vector.replicate dgLen false)
           , structuralBits := Vector.replicate numGates false }⟩

/-- Inhabited instance for RandomnessN (all-false default). -/
instance (dgLen numGates numVars : Nat) : Inhabited (RandomnessN dgLen numGates numVars) :=
  ⟨{ assignment := (fun _ => false)
     , gateDigests := Vector.replicate numGates (Vector.replicate dgLen false)
     , structuralBits := Vector.replicate numGates false }⟩

/-- For single-gate randomness (numGates=1), gate count equals 1 exactly.

    This theorem justifies `owf_gate_count_bound` in Plant.lean: in the OWF
    security proof, all Randomness values are constructed via `toRandomness`
    from `RandomnessN dgLen 1 numVars`, so they inherit the bound gateDigests.length = 1. -/
theorem gate_count_eq (dgLen numVars : Nat) (h_dgLen_pos : dgLen > 0) (r : RandomnessN dgLen 1 numVars) :
    (toRandomness dgLen numVars h_dgLen_pos r).gateDigests.length = 1 := by
  simp [toRandomness, Vector.toList]

/-- toRandomness preserves dgLen: the resulting Randomness has the same dgLen parameter. -/
theorem toRandomness_dgLen (dgLen numVars : Nat) (h_dgLen_pos : dgLen > 0) (r : RandomnessN dgLen 1 numVars) :
    (toRandomness dgLen numVars h_dgLen_pos r).dgLen = dgLen := rfl

/-- Corollary: gate count is bounded by 1. -/
theorem gate_count_bound (dgLen numVars : Nat) (h_dgLen_pos : dgLen > 0) (r : RandomnessN dgLen 1 numVars) :
    (toRandomness dgLen numVars h_dgLen_pos r).gateDigests.length ≤ 1 := by
  rw [gate_count_eq dgLen numVars h_dgLen_pos r]

/-- **LinearOrder instance for Vector via lexicographic order on lists.**

Vector α n gets a lexicographic LinearOrder when α has LinearOrder.
This compares vectors element-by-element from left to right by lifting
through Vector.toList, which has LinearOrder from List.instLinearOrder.

**Construction**: Uses LinearOrder.lift' with Vector.toList (injective function).
The injectivity proof is automatic via simp - Vector.toList is definitionally injective.
-/
noncomputable instance vectorLinearOrder {α : Type*} [LinearOrder α] [DecidableEq α]
    [DecidableRel (α := α) (· ≤ ·)] {n : Nat} :
    LinearOrder (Vector α n) :=
  LinearOrder.lift' (f := Vector.toList) (inj := by
    intro v w h
    -- simp automatically proves v.toList = w.toList → v = w
    simp [Vector.toList] at h
    ext i hi
    simp [h])

/-- **Injective function to nested Lex type for RandomnessNProduct.**

This function converts the product type to a nested Lex-wrapped type that has
automatic LinearOrder instances from Mathlib. The nesting is:
- Outer Lex: wraps the main product
- First component: Lex-wrapped function type (for Pi.Lex.linearOrder)
- Second component: Lex-wrapped pair of vectors (for Prod.Lex.linearOrder)

This allows us to use the automatic LinearOrder instances from:
- Pi.Lex.linearOrder for `Lex (Fin numVars → Bool)`
- Prod.Lex.linearOrder for products
- Our vectorLinearOrder for Vector types
-/
noncomputable def randomnessNProductToNestedLex (dgLen numGates numVars : Nat) :
    RandomnessNProduct dgLen numGates numVars →
    Lex (Lex (Fin numVars → Bool) × Lex (Vector (Vector Bool dgLen) numGates × Vector Bool numGates)) :=
  fun ⟨f, v1, v2⟩ => toLex (toLex f, toLex (v1, v2))

/-- **Proof that randomnessNProductToNestedLex is injective.**

The function is injective because it's a composition of injective functions:
- toLex is injective (it's just a type wrapper)
- Pair construction is injective
- Product projection is injective
-/
theorem randomnessNProductToNestedLex_injective (dgLen numGates numVars : Nat) :
    Function.Injective (randomnessNProductToNestedLex dgLen numGates numVars) := by
  intro ⟨f1, v1, v2⟩ ⟨f1', v1', v2'⟩ h
  -- Unfold and apply injectivity
  unfold randomnessNProductToNestedLex at h
  -- Extract equalities from the pair using Prod.Lex.mk.injEq
  simp only at h
  -- h gives us two equalities wrapped in toLex
  -- toLex is just an identity wrapper, so we can extract directly
  cases h
  -- Extract from inner pair equality
  simp only

/-- **LinearOrder instance for RandomnessNProduct via nested Lex lifting.**

The product type `(Fin numVars → Bool) × Vector (Vector Bool dgLen) numGates × Vector Bool numGates`
has a lexicographic LinearOrder constructed by:
1. Converting to nested Lex-wrapped type using randomnessNProductToNestedLex
2. Using automatic LinearOrder instances from Mathlib:
   - Pi.Lex.linearOrder for function types
   - Prod.Lex.linearOrder for products
   - vectorLinearOrder (proven above) for Vector types
3. Lifting back via LinearOrder.lift' using injectivity proof

**No axioms needed!** This is a complete proof using standard Mathlib infrastructure.
-/
noncomputable instance randomnessNProductLinearOrder (dgLen numGates numVars : Nat) :
    LinearOrder (RandomnessNProduct dgLen numGates numVars) :=
  LinearOrder.lift'
    (randomnessNProductToNestedLex dgLen numGates numVars)
    (randomnessNProductToNestedLex_injective dgLen numGates numVars)

/-- **LinearOrder instance for RandomnessN via product equivalence.**

This is needed for the OWF → FP≠FNP bridge (owf_exists_implies_fpnefnp_at_types),
which uses lexicographic minimum witness selection (LexMinWitness.lean).

**Construction**: Transport LinearOrder from RandomnessNProduct via randomnessNEquiv.

**Instance chain**:
- Bool has LinearOrder (✓ via Bool.linearOrder)
- Vector Bool n has LinearOrder (✓ via vectorLinearOrder above)
- Vector (Vector Bool dgLen) m has LinearOrder (✓ via nested vectorLinearOrder)
- RandomnessNProduct has LinearOrder (✓ via randomnessNProductLinearOrder above)
- RandomnessN has LinearOrder (✓ transport via randomnessNEquiv)
-/
noncomputable instance (dgLen numGates numVars : Nat) : LinearOrder (RandomnessN dgLen numGates numVars) :=
  @LinearOrder.lift' (RandomnessN dgLen numGates numVars) (RandomnessNProduct dgLen numGates numVars)
    (randomnessNProductLinearOrder dgLen numGates numVars)
    (randomnessNEquiv dgLen numGates numVars).toFun
    (randomnessNEquiv dgLen numGates numVars).injective

end RandomnessN

/-! ## Axiom Verification

These definitions and theorems use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms LStar.StructuralOWF.Foundations.RandomnessN.toRandomness
#print axioms LStar.StructuralOWF.Foundations.RandomnessN.nonempty
#print axioms LStar.StructuralOWF.Foundations.RandomnessN.gate_count_eq

end LStar.StructuralOWF.Foundations
