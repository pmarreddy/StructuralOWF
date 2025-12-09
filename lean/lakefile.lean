import Lake
open Lake DSL

package «P_neq_NP_Layered» where
  moreLeanArgs := #[]
  moreServerArgs := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "stable"

-- Layer 0: Mathematical Foundations
@[default_target]
lean_lib «Layer0_Foundations» where
  globs := #[.submodules `Layer0_Foundations]

-- Layer 1: L* Construction
lean_lib «Layer1_Construction» where
  globs := #[.submodules `Layer1_Construction]

-- Layer 2: Structural OWF Construction
lean_lib «Layer2_StructuralOWF» where
  globs := #[.submodules `Layer2_StructuralOWF]

-- Layer 3: Information Bounds
lean_lib «Layer3_InformationBounds» where
  globs := #[.submodules `Layer3_InformationBounds]

-- Layer 4: Operational Semantics
lean_lib «Layer4_Operational» where
  globs := #[.submodules `Layer4_Operational]

-- Infrastructure: Cross-cutting concerns
lean_lib «Infrastructure» where
  globs := #[.submodules `Infrastructure]

-- Layer 5: Applications (P≠NP, ZK, etc.) - derived from Structural OWF
lean_lib «Layer5_Applications» where
  globs := #[.submodules `Layer5_Applications]

-- Testing: Definition validation and bridge testing
lean_lib «testing» where
  globs := #[.submodules `testing]
