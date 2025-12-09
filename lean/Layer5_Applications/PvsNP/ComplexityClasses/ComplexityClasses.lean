import Layer5_Applications.PvsNP.ComplexityClasses.NPDefs
import Layer5_Applications.PvsNP.ComplexityClasses.UniformPPT
import Layer5_Applications.PvsNP.ComplexityClasses.RandAdv
import Layer5_Applications.PvsNP.ComplexityClasses.Sized
import Layer5_Applications.PvsNP.ComplexityClasses.BitEncoding
import Layer5_Applications.PvsNP.ComplexityClasses.StructuralOWFSizedInstances

/-! ## ComplexityClasses: P, NP, FP, FNP

**Purpose**: Standard complexity class definitions for OWF → P≠NP bridge.

**Definitions**: InP, InFP, InFNP, InNP_Alg (RandAdv-based).

**Theorems**: p_subset_np (P ⊆ NP).

**Size Function**: All definitions use the Sized typeclass to make input size
explicit and unambiguous. This eliminates the abstraction gap between "input x"
and "size of x" by requiring a constructive size function via [Sized α].

**Rigorous Polynomial Time**: Time bounds are explicit functions of actual
input sizes via poly_explicit field: ∀ x : α, time_bound (size x) ≤ C * (size x + 1)^k.

**Trust Boundary**: 0 axioms (fully constructive definitions).

**References**: Sipser §7.3-7.4, Arora-Barak §1.4-2.1.
-/

namespace LStar.Complexity

open Classical Sized
open LStar.StructuralOWF.Foundations

/-- **P (Polynomial Time)**: Languages decidable by deterministic poly-time algorithms.

A language L is in P if there exists a RandAdv A such that:
- A is deterministic (same output for all coin sequences)
- A correctly decides L (L x ↔ A.run outputs true)
- A runs in polynomial time (via RandAdv's time_bound fields)
-/
def InP {α : Type} [Sized α] (L : Lang α) : Prop :=
  ∃ (T : Nat) (A : RandAdv α Bool T),
    (∀ c₁ c₂ x, A.run c₁ x = A.run c₂ x) ∧
    (∀ x, L x ↔ A.run ⟨0, A.coins_pos⟩ x = true)

/-- **FP (Polynomial-Time Functions)**: Functions computable in polynomial time.

A function f : α → β is in FP if there exists a deterministic RandAdv A
that computes f correctly on all inputs within polynomial time.
-/
def InFP {α β : Type} [Sized α] [Sized β] (f : α → β) : Prop :=
  ∃ (T : Nat) (A : RandAdv α β T),
    (∀ c₁ c₂ x, A.run c₁ x = A.run c₂ x) ∧
    (∀ x, A.run ⟨0, A.coins_pos⟩ x = f x)

/-- **FNP (Function NP)**: Relations with polynomial-time verifiable witnesses.

A relation R : α → β → Prop is in FNP if:
- Witnesses are polynomially bounded in input size
- Membership is polynomial-time verifiable
-/
def InFNP {α β : Type} [Sized α] [Sized β] (R : α → β → Prop) : Prop :=
  ∃ (T : Nat) (V : RandAdv (α × β) Bool T) (C_wit k_wit : Nat),
    (∀ c₁ c₂ p, V.run c₁ p = V.run c₂ p) ∧
    (∀ x y, R x y → size y ≤ C_wit * (size x + 1) ^ k_wit) ∧
    (∀ x y, R x y ↔ V.run ⟨0, V.coins_pos⟩ (x, y) = true)

/-- **NP (Algorithmic Definition)**: Languages with polynomial-time verifiable witnesses.

This is NP defined algorithmically using RandAdv verifiers, matching the
abstraction level of InP, InFP, InFNP.

**Textbook Alignment**: Includes explicit polynomial witness-size bounds,
matching standard NP definitions (Sipser §7.3, Arora-Barak §2.1).
-/
def InNP_Alg {α : Type} [Sized α] (L : Lang α) : Prop :=
  ∃ (β : Type) (_inst : Sized β) (T : Nat) (V : RandAdv (α × β) Bool T) (C_wit k_wit : Nat),
    (∀ c₁ c₂ p, V.run c₁ p = V.run c₂ p) ∧
    (∀ x y, V.run ⟨0, V.coins_pos⟩ (x, y) = true → size y ≤ C_wit * (size x + 1) ^ k_wit) ∧
    (∀ x, L x ↔ ∃ y : β, V.run ⟨0, V.coins_pos⟩ (x, y) = true)

/-- **P ⊆ NP**: Every polynomial-time decidable language is in NP.

**Proof**: Use trivial witness (Unit). The P decider becomes the verifier
that ignores the witness.
-/
theorem p_subset_np {α : Type} [Sized α] (L : Lang α) (h : InP L) : InNP L := by
  obtain ⟨T, A, h_det, h_correct⟩ := h
  refine ⟨⟨Unit, fun x _ => A.run ⟨0, A.coins_pos⟩ x = true, ?_⟩⟩
  intro x
  simp only
  constructor
  · intro hL
    exists ()
    exact h_correct x |>.mp hL
  · intro ⟨_, hw⟩
    exact h_correct x |>.mpr hw

/-- **P = NP (Classical Formulation)**: Standard textbook statement.

Every language with polynomial-time verifiable witnesses (NP) has a
polynomial-time decider (P).

**References**: Sipser §7.4, Arora-Barak §2.3.

**Note**: The proof uses the parametric formulation internally
(see ParametricBitstringBridge.lean) which is mathematically equivalent.
-/
def PeqNP_classical : Prop :=
  ∀ (α : Type) [Sized α] (L : Lang α), InNP_Alg L → InP L

#print axioms InP
#print axioms InFP
#print axioms InFNP
#print axioms InNP_Alg
#print axioms p_subset_np
#print axioms PeqNP_classical

end LStar.Complexity
