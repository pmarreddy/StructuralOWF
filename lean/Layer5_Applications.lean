/-! # Layer 5: Applications

- **PvsNP**: Structural OWF → FP≠FNP → P≠NP
- **Crypto**: Structural OWF → PRG/PRF/PRP/MAC/Commitment/Signatures/ZK/MPC (Minicrypt)
-/

-- P vs NP
import Layer5_Applications.PvsNP.ComplexityClasses.ComplexityClasses
import Layer5_Applications.PvsNP.ComplexityClasses.NPDefs
import Layer5_Applications.PvsNP.ComplexityClasses.UniformPPT
import Layer5_Applications.PvsNP.ComplexityClasses.RandAdv
import Layer5_Applications.PvsNP.PrimaryPath.ParametricBitstringBridge
import Layer5_Applications.PvsNP.PrimaryPath.ParametricComplexity

-- Crypto (Minicrypt)
import Layer5_Applications.Crypto.PRG.HardcoreBit
import Layer5_Applications.Crypto.PRG.GoldreichLevin
import Layer5_Applications.Crypto.PRG.PRG1Bit
import Layer5_Applications.Crypto.PRG.PRGAmplify
import Layer5_Applications.Crypto.Commitment
import Layer5_Applications.Crypto.PRF
import Layer5_Applications.Crypto.PRP
import Layer5_Applications.Crypto.MAC
import Layer5_Applications.Crypto.Signature
import Layer5_Applications.Crypto.MerkleSignature
import Layer5_Applications.Crypto.CoinFlip
import Layer5_Applications.Crypto.MPC
import Layer5_Applications.Crypto.Encryption
import Layer5_Applications.Crypto.UOWHF
import Layer5_Applications.Crypto.ZeroKnowledge.NPRelation
import Layer5_Applications.Crypto.ZeroKnowledge.SigmaProtocol
import Layer5_Applications.Crypto.ZeroKnowledge.SecurityProofs
import Layer5_Applications.Crypto.Minicrypt
