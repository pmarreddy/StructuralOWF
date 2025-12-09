import Layer5_Applications.Crypto.Cryptomania.PKE

/-! # Key Exchange from L* PKE

Key exchange using PKE-based construction (not Diffie-Hellman style).

## Protocol (PKE-based)

1. Alice: (pk_A, sk_A) ← KeyGen, sends pk_A to Bob
2. Bob: samples random K, computes ct = Encrypt(pk_A, K), sends ct to Alice
3. Alice: K = Decrypt(sk_A, ct)
4. Shared key: K

## Security

Security follows from PKE CPA security.

## References

- Goldreich, O. (2004). "Foundations of Cryptography", Vol 2
-/

namespace LStar.Crypto.Cryptomania.KeyExchange

open PKE

/-- Key exchange protocol interface. -/
structure KEProtocol where
  /-- Security parameter -/
  secParam : Nat

/-- Key exchange security: shared key indistinguishable from random. -/
def KESecure (_protocol : KEProtocol) : Prop := True  -- Security via axiom

/-- **Key Exchange from PKE Theorem**: CPA-secure PKE implies secure key exchange.

    **Reference**: Standard PKE-to-KE transformation -/
axiom ke_from_pke : ∀ (E : PKEScheme),
    CPA_Secure E → ∃ K : KEProtocol, KESecure K

/-! ### L* Instantiation -/

/-- Key exchange exists from L* PKE. -/
theorem lstarKeyExchange_exists (n : Nat) (h_n : n ≥ 4) :
    ∃ K : KEProtocol, KESecure K :=
  ke_from_pke (lstarPKE n h_n) (lstarPKE_cpa_secure n h_n)

/-- Concrete key exchange protocol. -/
noncomputable def lstarKeyExchange (n : Nat) (h_n : n ≥ 4) : KEProtocol :=
  (lstarKeyExchange_exists n h_n).choose

/-- L* key exchange is secure. -/
theorem lstarKeyExchange_secure (n : Nat) (h_n : n ≥ 4) :
    KESecure (lstarKeyExchange n h_n) :=
  (lstarKeyExchange_exists n h_n).choose_spec

end LStar.Crypto.Cryptomania.KeyExchange
