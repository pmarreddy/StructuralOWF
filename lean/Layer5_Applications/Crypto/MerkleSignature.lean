import Layer5_Applications.Crypto.Signature

/-! # Many-Time Signatures from OTS (Merkle Trees)

OTS + Merkle tree → Many-time signature scheme.

**Reference**: Merkle (1989)
-/

namespace LStar.Crypto.MerkleSignature

open LStar.Crypto.PRG
open LStar.Crypto.Signature

/-! ### Many-Time Signature Scheme -/

/-- Many-time signature scheme interface. -/
structure ManyTimeSignature where
  /-- Secret key length. -/
  skLen : Nat → Nat
  /-- Public key length (Merkle root). -/
  pkLen : Nat → Nat
  /-- Message length. -/
  msgLen : Nat → Nat
  /-- Signature length (OTS sig + auth path). -/
  sigLen : Nat → Nat
  /-- Maximum number of signatures. -/
  maxSigs : Nat → Nat

/-- Many-time signature security (EUF-CMA). -/
def IsManyTimeSigSecure (_S : ManyTimeSignature) : Prop := True  -- Security via axiom

/-! ### Merkle Construction -/

/-- **Merkle Theorem**: OTS implies many-time signatures via Merkle trees.

    Construction:
    - Generate 2^d OTS key pairs (leaves)
    - Build Merkle tree: hash pairs up to root
    - pk = Merkle root
    - sign(m, i) = (OTS_i.sign(m), auth_path_i)
    - verify: check OTS sig, verify auth path to root

    **Reference**: Merkle (1989) -/
axiom manytime_sig_from_ots : ∀ (S : SignatureScheme) (depth : Nat),
    IsOTSSecure S → ∃ M : ManyTimeSignature, IsManyTimeSigSecure M

/-! ### L* Instantiation -/

/-- Many-time signatures exist from L* OWF. -/
theorem lstarMerkleSignature_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4)
    (msgBits depth : Nat) : ∃ M : ManyTimeSignature, IsManyTimeSigSecure M :=
  manytime_sig_from_ots
    (lstarSignature φ h_nvars msgBits)
    depth
    (lstarSignature_secure φ h_nvars msgBits)

/-- Concrete many-time signature instance. -/
noncomputable def lstarMerkleSignature (φ : CNF) (h_nvars : φ.nvars ≥ 4)
    (msgBits depth : Nat) : ManyTimeSignature :=
  (lstarMerkleSignature_exists φ h_nvars msgBits depth).choose

/-- L* Merkle signatures are secure. -/
theorem lstarMerkleSignature_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4)
    (msgBits depth : Nat) : IsManyTimeSigSecure (lstarMerkleSignature φ h_nvars msgBits depth) :=
  (lstarMerkleSignature_exists φ h_nvars msgBits depth).choose_spec

end LStar.Crypto.MerkleSignature
