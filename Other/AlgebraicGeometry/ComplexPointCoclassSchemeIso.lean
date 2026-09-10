/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.ChartLocalClassHomeomorph
public import Other.AlgebraicGeometry.ComplexAnalyticMaps
public import Other.AlgebraicGeometry.ComplexPointCoclassOrientationComparison

/-! # Exact point-coclass naturality for actual complex scheme isomorphisms

The actual maps of complex points are holomorphic in both directions. Analytic
chart-transition invariance therefore proves that their literal point-pair maps
carry the exactly normalized local class to the exactly normalized local class.
Dual normalization proves the point-coclass pullback identity with coefficient one.
-/

@[expose] public noncomputable section

open CategoryTheory Topology
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (e : Y ≅ X) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
  [IsProjective X.hom] [IsProjective Y.hom] (z : ComplexPoint Y)

/-- The actual point-complement map associated with the actual analytic homeomorphism. -/
def complexSchemeIsoPointPairMap :
    pointComplementPair z ⟶ pointComplementPair (Point.map e.hom z) :=
  pointComplementHomeomorphPairMap (Point.isoMapHomeomorph e) z

omit [IsProjective X.hom] [IsProjective Y.hom] in
/-- Scheme-isomorphism naturality preserves the exact complex local orientation,
proved from analyticity of both actual coordinate transitions. -/
theorem complexSchemeIsoPointPairMap_localClass :
    relativeHomologyMap ℚ (2 * d) (complexSchemeIsoPointPairMap X Y e z)
      (analyticPointLocalHomologyClass Y d z) =
      analyticPointLocalHomologyClass X d (Point.map e.hom z) := by
  let H := Point.isoMapHomeomorph e
  let a := localChart Y d z
  let b := localChart X d (H z)
  let hz := mem_localChart_source Y d z
  let hb := mem_localChart_source X d (H z)
  change relativeHomologyMap ℚ (2 * d) (pointComplementHomeomorphPairMap H z)
    (localClassOfChart d a z hz) = localClassOfChart d b (H z) hb
  rw [localClassOfChart_homeomorphTransport]
  apply localClassOfChart_eq_of_analyticAt_transition
  · change AnalyticAt ℂ (fun v => b (H (a.symm v))) (a (H.symm (H z)))
    rw [H.symm_apply_apply]
    apply analyticAt_localChart_symm_map Y X e.hom d d z (a.map_source hz)
    change H (a.symm (a z)) ∈ b.source
    rw [a.left_inv hz]
    exact hb
  · change AnalyticAt ℂ (fun v => a (H.symm (b.symm v))) (b (H z))
    have hback : Point.map e.inv (H z) = z := H.left_inv z
    have hmem : Point.map e.inv (b.symm (b (H z))) ∈
        (localChart Y d (Point.map e.inv (H z))).source := by
      rw [b.left_inv hb, hback]
      exact hz
    have ha := analyticAt_localChart_symm_map X Y e.inv d d (H z) (b.map_source hb) hmem
    have hsymm (q : ComplexPoint X) : H.symm q = Point.map e.inv q := rfl
    simpa only [hback, hsymm] using ha

/-- The old normalized point coclass pulls back exactly under the actual scheme iso. -/
theorem analyticPointLocalCoclass_schemeIso_pullback :
    relativeCohomologyMap ℚ (2 * d) (complexSchemeIsoPointPairMap X Y e z)
      (analyticPointLocalCoclass X d (Point.map e.hom z)) =
      analyticPointLocalCoclass Y d z := by
  apply (eq_analyticPointLocalCoclass_iff Y d z _).mpr
  rw [relativeCohomologyMap_apply]
  change analyticPointLocalCoclass X d (Point.map e.hom z)
    (relativeHomologyMap ℚ (2 * d) (complexSchemeIsoPointPairMap X Y e z)
      (analyticPointLocalHomologyClass Y d z)) = 1
  rw [complexSchemeIsoPointPairMap_localClass, analyticPointLocalCoclass_apply_localClass]

end AlgebraicGeometry.ComplexPoint
