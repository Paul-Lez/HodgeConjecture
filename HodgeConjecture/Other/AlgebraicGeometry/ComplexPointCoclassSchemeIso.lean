/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicTopology.ChartLocalClassHomeomorph
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexAnalyticMaps
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexPointCoclassOrientationComparison

/-! # Exact point-coclass naturality for actual complex scheme isomorphisms

The actual maps of complex points are holomorphic in both directions. Analytic
chart-transition invariance therefore proves that their literal point-pair maps
carry the exactly normalized local class to the exactly normalized local class.
Dual normalization proves the point-coclass pullback identity with coefficient one.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Topology
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Scheme} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
  (e : Y ≅ X) (he : e.hom ≫ sX = sY) (d : ℕ)
  [SmoothOfRelativeDimension d sX] [SmoothOfRelativeDimension d sY]
  [IsProjective sX] [IsProjective sY] (z : ComplexPoint Y sY)

/-- The actual point-complement map associated with the actual analytic homeomorphism. -/
def complexSchemeIsoPointPairMap :
    pointComplementPair z ⟶ pointComplementPair (Point.map e.hom he z) :=
  pointComplementHomeomorphPairMap (Point.isoMapHomeomorph e he) z

omit [IsProjective sX] [IsProjective sY] in
/-- Scheme-isomorphism naturality preserves the exact complex local orientation,
proved from analyticity of both actual coordinate transitions. -/
theorem complexSchemeIsoPointPairMap_localClass :
    relativeHomologyMap ℚ (2 * d) (complexSchemeIsoPointPairMap sX sY e he z)
      (analyticPointLocalHomologyClass sY d z) =
      analyticPointLocalHomologyClass sX d (Point.map e.hom he z) := by
  let H := Point.isoMapHomeomorph e he
  let a := localChart sY d z
  let b := localChart sX d (H z)
  let hz := mem_localChart_source sY d z
  let hb := mem_localChart_source sX d (H z)
  change relativeHomologyMap ℚ (2 * d) (pointComplementHomeomorphPairMap H z)
    (localClassOfChart d a z hz) = localClassOfChart d b (H z) hb
  rw [localClassOfChart_homeomorphTransport]
  apply localClassOfChart_eq_of_analyticAt_transition
  · change AnalyticAt ℂ (fun v => b (H (a.symm v))) (a (H.symm (H z)))
    rw [H.symm_apply_apply]
    apply analyticAt_localChart_symm_map sY sX e.hom he d d z (a.map_source hz)
    change H (a.symm (a z)) ∈ b.source
    rw [a.left_inv hz]
    exact hb
  · change AnalyticAt ℂ (fun v => a (H.symm (b.symm v))) (b (H z))
    have hi : e.inv ≫ sY = sX := by rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    have hback : Point.map e.inv hi (H z) = z := H.left_inv z
    have hmem : Point.map e.inv hi (b.symm (b (H z))) ∈
        (localChart sY d (Point.map e.inv hi (H z))).source := by
      rw [b.left_inv hb, hback]
      exact hz
    have ha := analyticAt_localChart_symm_map sX sY e.inv hi d d (H z) (b.map_source hb) hmem
    have hsymm (q : ComplexPoint X sX) : H.symm q = Point.map e.inv hi q := rfl
    simpa only [hback, hsymm] using ha

/-- The old normalized point coclass pulls back exactly under the actual scheme iso. -/
theorem analyticPointLocalCoclass_schemeIso_pullback :
    relativeCohomologyMap ℚ (2 * d) (complexSchemeIsoPointPairMap sX sY e he z)
      (analyticPointLocalCoclass sX d (Point.map e.hom he z)) =
      analyticPointLocalCoclass sY d z := by
  apply (eq_analyticPointLocalCoclass_iff sY d z _).mpr
  rw [relativeCohomologyMap_apply]
  change analyticPointLocalCoclass sX d (Point.map e.hom he z)
    (relativeHomologyMap ℚ (2 * d) (complexSchemeIsoPointPairMap sX sY e he z)
      (analyticPointLocalHomologyClass sY d z)) = 1
  rw [complexSchemeIsoPointPairMap_localClass, analyticPointLocalCoclass_apply_localClass]

end AlgebraicGeometry.ComplexPoint
