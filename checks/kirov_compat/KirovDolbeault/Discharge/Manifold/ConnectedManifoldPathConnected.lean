import Mathlib.Topology.Connected.LocPathConnected

/-!
# Connected + locally path-connected ⇒ path-connected

This file packages the standard mathlib fact
`PathConnectedSpace.of_locPathConnectedSpace` under a name local to this
project, for downstream use in the manifold path-connectedness chain.
-/

namespace Jacobians.Discharge.Manifold

/-- Any topological space that is connected and locally path-connected is
path-connected. This is exactly `PathConnectedSpace.of_locPathConnectedSpace`
from mathlib, re-exported under a project-local name. -/
theorem pathConnectedSpace_of_connectedSpace_locPathConnected
    {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y] [LocPathConnectedSpace Y] :
    PathConnectedSpace Y :=
  PathConnectedSpace.of_locPathConnectedSpace

end Jacobians.Discharge.Manifold
