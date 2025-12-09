/-! ## Sized: Explicit Size Function Typeclass (0 axioms)

**Purpose**: Make input size explicit for complexity-theoretic definitions.

**Design**: Typeclass capturing "types with a natural notion of size".

**Standard Instances**: Bitstrings, natural numbers, finite types, lists.

**Why Needed**: Complexity theory measures time as function of input size.
For abstract types α, we need explicit size : α → Nat to define polynomial time.

**Usage**: RandAdv, complexity class definitions require [Sized α].

See Layer5_Applications/Layer5_README.md §ComplexityClasses.
-/

namespace LStar.Complexity

/-- Types with a natural notion of "size" for complexity analysis.

**Examples**:
- Bitstrings: size = length
- Natural numbers: size = n+1 (unary, conservative)
- Finite types: size = constant (single element)
- Lists: size = list length
- Products: size (a,b) = size a + size b

**Purpose**: Makes polynomial time well-defined for abstract types.
Standard complexity theory assumes inputs are encoded as bitstrings
with well-defined length. This typeclass makes that assumption explicit.
-/
class Sized (α : Type) where
  /-- Size function: maps values to their "complexity size" (typically encoding length). -/
  size : α → Nat
  /-- Size is always positive (ensures non-degeneracy). -/
  size_pos : ∀ x, 0 < size x

/-- Instance: Bitstrings (Vector Bool n) have size = n+1 (avoid zero size) -/
instance sizedBitstring {n : Nat} : Sized (Vector Bool n) where
  size := fun _ => n + 1
  size_pos := fun _ => Nat.zero_lt_succ n

/-- Instance: Natural numbers have size = n+1 (unary, conservative bound). -/
instance sizedNat : Sized Nat where
  size := fun n => n + 1
  size_pos := fun _ => Nat.zero_lt_succ _

/-- Instance: Lists have size = length + 1 (avoid zero size) -/
instance sizedList {α : Type} : Sized (List α) where
  size := fun l => l.length + 1
  size_pos := fun _ => Nat.zero_lt_succ _

/-- Instance: Products have size = sum of component sizes -/
instance sizedProd {α β : Type} [Sized α] [Sized β] : Sized (α × β) where
  size := fun (a, b) => Sized.size a + Sized.size b
  size_pos := fun (a, b) => Nat.add_pos_left (Sized.size_pos a) (Sized.size b)

/-- Instance: Finite types have constant size (single element encoding) -/
instance sizedFin {n : Nat} : Sized (Fin n) where
  size := fun _ => Nat.log2 n + 1  -- Bits needed to encode index
  size_pos := fun _ => Nat.zero_lt_succ _

/-- Instance: Booleans have constant size 1 (single bit) -/
instance sizedBool : Sized Bool where
  size := fun _ => 1
  size_pos := fun _ => Nat.zero_lt_one

/-- Instance: Sigma types (dependent pairs) have size = sum of component sizes -/
instance sizedSigma {α : Type} {β : α → Type} [Sized α] [∀ a, Sized (β a)] : Sized (Sigma β) where
  size := fun ⟨a, b⟩ => Sized.size a + Sized.size b
  size_pos := fun ⟨a, b⟩ => Nat.add_pos_left (Sized.size_pos a) (Sized.size b)

-- Axiom Audits: Trust Boundary Transparency
#print axioms Sized
#print axioms sizedBitstring
#print axioms sizedNat
#print axioms sizedList
#print axioms sizedProd
#print axioms sizedFin
#print axioms sizedBool
#print axioms sizedSigma

end LStar.Complexity
