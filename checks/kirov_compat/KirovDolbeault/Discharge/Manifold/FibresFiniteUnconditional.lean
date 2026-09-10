/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.ChartOverlapPropagationDischarge
import KirovDolbeault.Discharge.Manifold.ClopennessOfLocallyConstDischarge

set_option autoImplicit true


/-! # Unconditional `fibres_finite_statement`

ZZ47 closed `ClopennessOfLocallyConstHypothesis` unconditionally. ZZ46
reduced `fibres_finite_statement` to that hypothesis. Composing the two
gives an unconditional discharge of the first `Degree` statement. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-- **Unconditional `fibres_finite_statement`.** Direct composition of
`fibres_finite_statement_holds_of_clopennessOfLocallyConst` (ZZ46) with
`clopennessOfLocallyConst_holds` (ZZ47). -/
theorem fibres_finite_statement_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_statement_holds_of_clopennessOfLocallyConst
    clopennessOfLocallyConst_holds

end Degree
end ContMDiff
end Jacobians.Discharge
