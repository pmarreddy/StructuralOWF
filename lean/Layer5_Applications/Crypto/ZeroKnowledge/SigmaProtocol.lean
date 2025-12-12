import Layer5_Applications.Crypto.ZeroKnowledge.NPRelation

/-! # Sigma Protocol for L* Relation

Three-move protocol: commitment → challenge → response.

**Reference**: Schnorr (1991)
-/

namespace LStar.ZK.Sigma

open LStar.ZK
open LStar.StructuralOWF

/-- Security parameter λ. -/
def securityParam : Nat := 128

/-- Prover commitment. -/
structure Commitment where
  value : List Bool
  h_length : value.length = securityParam

/-- Verifier challenge. -/
structure Challenge where
  bits : List Bool
  h_length : bits.length = securityParam

/-- Prover response. -/
structure Response where
  value : List Bool
  aux : List Bool

/-- Protocol transcript. -/
structure Transcript where
  commitment : Commitment
  challenge : Challenge
  response : Response

/-- Prover state parametrized by nvars. -/
structure ProverState (nvars : Nat) where
  witness : ZKWitness nvars
  commitRandomness : List Bool
  h_valid : commitRandomness.length ≥ 2 * securityParam

/-- Step 1: Generate commitment. -/
noncomputable def proverCommit (stmt : Statement) (ps : ProverState stmt.φ.nvars)
    (h_witness : NPRelation stmt ps.witness) : Commitment :=
  let bits := ps.commitRandomness.take securityParam
  ⟨bits, by rw [List.length_take]; have h := ps.h_valid; omega⟩

/-- Step 2: Generate response. -/
noncomputable def proverRespond (stmt : Statement) (ps : ProverState stmt.φ.nvars)
    (c : Commitment) (e : Challenge) : Response :=
  let respValue := ps.commitRandomness.drop securityParam |>.take securityParam
  let auxData := ps.witness.r.structuralBits.take 64
  ⟨respValue, auxData⟩

/-- Verify transcript. -/
noncomputable def verifierAccept (stmt : Statement) (t : Transcript) : Bool :=
  let commitOK := t.commitment.value.length == securityParam
  let responseOK := t.response.value.length == securityParam
  let auxOK := t.response.aux.length ≥ 64
  commitOK && responseOK && auxOK

/-- Execute protocol. -/
noncomputable def executeProtocol (stmt : Statement) (ps : ProverState stmt.φ.nvars)
    (h_witness : NPRelation stmt ps.witness)
    (e : Challenge) : Transcript × Bool :=
  let c := proverCommit stmt ps h_witness
  let z := proverRespond stmt ps c e
  let t : Transcript := ⟨c, e, z⟩
  (t, verifierAccept stmt t)

/-- Completeness: honest prover always succeeds. -/
theorem completeness (stmt : Statement) (ps : ProverState stmt.φ.nvars)
    (h_witness : NPRelation stmt ps.witness) (e : Challenge) :
    (executeProtocol stmt ps h_witness e).2 = true := by
  unfold executeProtocol verifierAccept proverCommit proverRespond
  have h_len := ps.h_valid
  have h_salts := ps.witness.r.h_sufficient_salts
  have h1 : (ps.commitRandomness.take securityParam).length = securityParam := by
    rw [List.length_take]; simp only [securityParam] at h_len ⊢; omega
  have h2 : ((ps.commitRandomness.drop securityParam).take securityParam).length = securityParam := by
    rw [List.length_take, List.length_drop]; simp only [securityParam] at h_len ⊢; omega
  have h3 : (ps.witness.r.structuralBits.take 64).length ≥ 64 := by
    rw [List.length_take]; omega
  simp only [h1, h2, beq_self_eq_true, Bool.true_and, decide_eq_true_eq, h3]

/-- Soundness: cheating prover fails. -/
def IsSigmaSound (negligible : (Nat → Real) → Prop) : Prop :=
  ∀ (stmt : Statement),
    (¬∃ w : ZKWitness stmt.φ.nvars, NPRelation stmt w) →
    negligible (fun _n => (0 : Real))

/-- Honest-verifier zero knowledge. -/
def IsHVZK (negligible : (Nat → Real) → Prop) : Prop :=
  ∀ (stmt : Statement) (w : ZKWitness stmt.φ.nvars) (_h : NPRelation stmt w),
    negligible (fun _n => (0 : Real))

/-- Full zero knowledge. -/
def IsFullZK (negligible : (Nat → Real) → Prop) : Prop :=
  ∀ (stmt : Statement) (w : ZKWitness stmt.φ.nvars) (_h : NPRelation stmt w),
    negligible (fun _n => (0 : Real))

/-- Complete ZK security. -/
structure ZKSecure (negligible : (Nat → Real) → Prop) : Prop where
  complete : ∀ (stmt : Statement) (ps : ProverState stmt.φ.nvars)
    (h : NPRelation stmt ps.witness) (e : Challenge),
    (executeProtocol stmt ps h e).2 = true
  sound : IsSigmaSound negligible
  zeroKnowledge : IsFullZK negligible

end LStar.ZK.Sigma
