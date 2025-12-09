import Layer1_Construction.Core.InstanceOps
import Layer1_Construction.Core.Pools

/-! ## A1_Hermeticity: Typed Address Isolation

**Theorem**: `L_satisfies_A1` - L* instance satisfies A1 (Hermeticity).

**Statement**:
```lean
∀ v₁ v₂, v₁ ≠ v₂ → computeAddress(v₁, ...) ≠ computeAddress(v₂, ...)
```

**Proof**: Immediate from `address_hermetic` theorem (Pools.lean).
Typed addresses ⟨v, offset⟩ ensure different vertices → different addresses (structural).

**Why This Matters**: Enables unambiguous designated read accounting (q_v per vertex).
Without hermeticity, address collisions would make information accounting ambiguous.

**Trust Boundary**: Proven theorem (no axioms). Uses address_hermetic from Pools.lean.

**Paper**: §6 "A1 Hermeticity", §2.1 "Designated Reads".

See Layer1_Construction/Layer1_README.md for A1 property details.
-/

namespace LStar
namespace Properties

open scoped Classical

/-- A1: No address collisions across distinct vertices. -/
def satisfies_A1 (L : LStarInstanceFull) : Prop :=
  ∀ v₁ v₂ : Fin L.dag.n, v₁ ≠ v₂ →
  ∀ (s₁ : Seed (L.seedWidth v₁)) (s₂ : Seed (L.seedWidth v₂)) (i₁ i₂ p₁ p₂ : Nat),
    computeAddress L.pools v₁ s₁ i₁ p₁ ≠ computeAddress L.pools v₂ s₂ i₂ p₂

theorem L_satisfies_A1 (L : LStarInstanceFull) : satisfies_A1 L := by
  intro v₁ v₂ hne s₁ s₂ i₁ i₂ p₁ p₂
  exact address_hermetic L.pools hne s₁ s₂ i₁ i₂ p₁ p₂

/- Axiom audit: Hermeticity property proof using typed addresses.
   Relies on address_hermetic from InstanceOps. -/
#print axioms satisfies_A1
#print axioms L_satisfies_A1

end Properties
end LStar
