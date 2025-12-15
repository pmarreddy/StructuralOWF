-- Core construction components (8 files)
import Layer1_Construction.Core.Pools
import Layer1_Construction.Core.EmergenceMatrix
import Layer1_Construction.Core.LStarInstance
import Layer1_Construction.Core.SeedChain
import Layer1_Construction.Core.BalancedBinaryTree
import Layer1_Construction.Core.MultiLevelDAG
import Layer1_Construction.Core.InstanceOps

-- Properties (A1-A5)
import Layer1_Construction.Properties.A1_Hermeticity
import Layer1_Construction.Properties.A2_Injectivity
import Layer1_Construction.Properties.A3_Emergence

-- Bridge (SCL ↔ L* integration)
import Layer1_Construction.Bridge.LStarToNodeData

/-! # Layer 1: L* Construction

Exports all Layer 1 modules: Core components and A1-A5 properties.

**Core Components**:
- Pools, EmergenceMatrix, Core structure
- SeedChain, BalancedBinaryTree, MultiLevelDAG
- LStarFull (complete instance with operations)

**Properties**:
- A1 (Hermeticity), A2 (Injectivity), A3 (Emergence)
-/
