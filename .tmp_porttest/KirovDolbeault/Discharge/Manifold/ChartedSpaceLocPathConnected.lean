/-
Copyright (c) 2026 Jacobian Lean Challenge contributors. All rights reserved.

Foundation chip ZZ162: register `LocPathConnectedSpace` for `ℂ` and for any
topological space charted on `ℂ`. Mathlib provides
`LocallyConvexSpace.toLocPathConnectedSpace` for ℝ-LCSes and
`ChartedSpace.locPathConnectedSpace` to lift across charts; this file just
wires them together for `ℂ` so downstream chips can use `inferInstance`.
-/
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic

namespace Jacobians.Discharge.Manifold

/-- `ℂ`, viewed as an ℝ-normed space, is locally path-connected. -/
instance instLocPathConnectedSpace_complex : LocPathConnectedSpace ℂ :=
  inferInstance

/-- Any topological space charted on `ℂ` is locally path-connected. -/
theorem locPathConnectedSpace_of_chartedSpace_complex
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    LocPathConnectedSpace Y :=
  ChartedSpace.locPathConnectedSpace ℂ Y

end Jacobians.Discharge.Manifold
