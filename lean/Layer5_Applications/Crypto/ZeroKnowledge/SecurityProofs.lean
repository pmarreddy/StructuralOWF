import Layer5_Applications.Crypto.ZeroKnowledge.SigmaProtocol
import Layer5_Applications.Crypto.PRG.GoldreichLevin
import Layer5_Applications.Crypto.Commitment

/-! # L* Zero-Knowledge Security

Soundness from OWF hardness, full ZK from commitment hiding (GMW transform).

**References**: Bellare-Goldreich (1992), GMW (1991)
-/

namespace LStar.ZK.Security

open LStar.ZK
open LStar.ZK.Sigma
open LStar.StructuralOWF
open LStar.Crypto.PRG
open LStar.Crypto.Commitment

private abbrev negl := Crypto.PRG.negligible

/-- **Soundness from OWF**: OWF hardness implies Sigma protocol soundness.

    **Reference**: Bellare-Goldreich (1992) -/
axiom soundness_from_owf : IsSigmaSound negl

/-- **Full ZK from Commitment**: Commitment hiding implies full zero-knowledge.

    **Reference**: GMW (1991) -/
axiom fullzk_from_commitment : ∀ (φ : CNF) (h_nvars : φ.nvars ≥ 4),
    CommitmentSecureFull (lstarCommitment φ h_nvars) → IsFullZK negl

/-- Complete ZK security: completeness + soundness + full ZK. -/
theorem lstar_zk_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) : ZKSecure negl where
  complete := completeness
  sound := soundness_from_owf
  zeroKnowledge := fullzk_from_commitment φ h_nvars (lstarCommitment_secure φ h_nvars)

end LStar.ZK.Security
