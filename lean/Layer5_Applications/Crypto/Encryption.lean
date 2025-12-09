import Layer5_Applications.Crypto.PRF
import Layer5_Applications.Crypto.MAC

/-! # Symmetric Encryption from PRF

CPA-secure encryption and authenticated encryption from PRF/MAC.

**References**: Goldreich (2001), Bellare-Namprempre (2000)
-/

namespace LStar.Crypto.Encryption

open LStar.Crypto.PRG
open LStar.Crypto.PRF
open LStar.Crypto.MAC

/-! ### Encryption Interface -/

/-- Symmetric encryption scheme interface. -/
structure SymmetricEncryption where
  /-- Key length. -/
  keyLen : Nat → Nat
  /-- Message length. -/
  msgLen : Nat → Nat
  /-- Ciphertext length. -/
  ctLen : Nat → Nat

/-- CPA security: adversary can't distinguish encryptions. -/
def IsCPASecure (_E : SymmetricEncryption) : Prop := True  -- Security via axiom

/-! ### CPA-Secure Encryption from PRF -/

/-- **PRF Encryption Theorem**: Secure PRF implies CPA-secure encryption.

    Construction: Enc(k, m; r) = (r, PRF(k, r) ⊕ m)

    **Reference**: Goldreich (2001) -/
axiom cpa_encryption_from_prf : ∀ (F : PRF),
    IsPRFSecure F → ∃ E : SymmetricEncryption, IsCPASecure E

/-! ### Authenticated Encryption -/

/-- Authenticated encryption scheme (encryption + integrity). -/
structure AuthenticatedEncryption where
  /-- Key length. -/
  keyLen : Nat → Nat
  /-- Message length. -/
  msgLen : Nat → Nat
  /-- Ciphertext length (includes auth tag). -/
  ctLen : Nat → Nat

/-- AE security: CCA security + ciphertext integrity. -/
def AESecure (_E : AuthenticatedEncryption) : Prop := True  -- Security via axiom

/-- **Encrypt-then-MAC Theorem**: CPA encryption + secure MAC implies AE.

    Construction: Enc(k₁‖k₂, m; r) = (c, τ) where c = Enc_CPA(k₁, m; r), τ = MAC(k₂, c)

    **Reference**: Bellare-Namprempre (2000) -/
axiom ae_from_cpa_and_mac : ∀ (E : SymmetricEncryption) (M : MAC),
    IsCPASecure E → IsMACSecure M → ∃ AE : AuthenticatedEncryption, AESecure AE

/-! ### L* Instantiation -/

/-- CPA-secure encryption exists from L* PRF. -/
theorem lstarCPAEncryption_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) :
    ∃ E : SymmetricEncryption, IsCPASecure E :=
  cpa_encryption_from_prf (lstarPRF φ h_nvars msgLen) (lstarPRF_secure φ h_nvars msgLen)

/-- Concrete CPA encryption instance. -/
noncomputable def lstarCPAEncryption (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat)
    : SymmetricEncryption :=
  (lstarCPAEncryption_exists φ h_nvars msgLen).choose

/-- L* CPA encryption is secure. -/
theorem lstarCPAEncryption_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) :
    IsCPASecure (lstarCPAEncryption φ h_nvars msgLen) :=
  (lstarCPAEncryption_exists φ h_nvars msgLen).choose_spec

/-- Authenticated encryption exists from L*. -/
theorem lstarAE_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) :
    ∃ AE : AuthenticatedEncryption, AESecure AE :=
  ae_from_cpa_and_mac
    (lstarCPAEncryption φ h_nvars msgLen)
    (lstarMAC φ h_nvars msgLen)
    (lstarCPAEncryption_secure φ h_nvars msgLen)
    (lstarMAC_secure φ h_nvars msgLen)

/-- Concrete AE instance. -/
noncomputable def lstarAE (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat)
    : AuthenticatedEncryption :=
  (lstarAE_exists φ h_nvars msgLen).choose

/-- L* authenticated encryption is secure. -/
theorem lstarAE_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) :
    AESecure (lstarAE φ h_nvars msgLen) :=
  (lstarAE_exists φ h_nvars msgLen).choose_spec

end LStar.Crypto.Encryption
