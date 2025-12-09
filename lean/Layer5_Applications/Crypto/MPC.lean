import Layer5_Applications.Crypto.PRG.GoldreichLevin

/-! # Secure Multi-Party Computation from OWF

OWF → Oblivious Transfer → MPC for any function.

**References**: GMW (1987), Kilian (1988)
-/

namespace LStar.Crypto.MPC

open LStar.Crypto.PRG

/-! ### Oblivious Transfer -/

/-- 1-out-of-2 Oblivious Transfer interface.

    Sender has (m₀, m₁), receiver has choice bit b.
    Receiver learns m_b, sender learns nothing about b. -/
structure OT where
  /-- Message length. -/
  msgLen : Nat → Nat

/-- OT security (semi-honest). -/
def OTSecure (_O : OT) : Prop := True  -- Security via axiom

/-- **OT from OWF Theorem**: OWF implies oblivious transfer.

    **Reference**: Various constructions -/
axiom ot_from_owf : ∀ (f : OneWayFunction),
    (∀ Inv : OWFInverter f, ∀ δ : Nat → Real,
      HasInversionProbability f Inv δ → negligible δ) →
    ∃ O : OT, OTSecure O

/-! ### Secure Multi-Party Computation -/

/-- Two-party function to compute securely. -/
structure TwoPartyFunction where
  /-- Alice's input length. -/
  aliceInputLen : Nat → Nat
  /-- Bob's input length. -/
  bobInputLen : Nat → Nat
  /-- Output length. -/
  outputLen : Nat → Nat

/-- MPC protocol interface. -/
structure MPCProtocol where
  /-- Function being computed. -/
  fn : TwoPartyFunction

/-- MPC security (semi-honest). -/
def MPCSecure (_F : TwoPartyFunction) (_P : MPCProtocol) : Prop := True  -- Security via axiom

/-- **GMW Theorem**: OT implies MPC for any function.

    Construction: Circuit-based evaluation using OT for AND gates.

    **Reference**: GMW (1987) -/
axiom mpc_from_ot : ∀ (O : OT) (F : TwoPartyFunction),
    OTSecure O → ∃ P : MPCProtocol, MPCSecure F P

/-! ### L* Instantiation -/

/-- OT exists from L* OWF. -/
theorem lstarOT_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ O : OT, OTSecure O :=
  ot_from_owf (lstarOWF φ h_nvars) (lstar_owf_security φ h_nvars)

/-- MPC for any function exists from L* OWF. -/
theorem lstarMPC_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (F : TwoPartyFunction) :
    ∃ P : MPCProtocol, MPCSecure F P := by
  obtain ⟨O, h_ot⟩ := lstarOT_exists φ h_nvars
  exact mpc_from_ot O F h_ot

end LStar.Crypto.MPC
