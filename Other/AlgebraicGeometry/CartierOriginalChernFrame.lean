/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.CartierWindingChartCoefficient
public import Other.AlgebraicGeometry.ChernRelativeCanonicalLift

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order

namespace AlgebraicGeometry.ComplexPoint

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance originalChernFrameTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {L : X.left.Modules} {c : Scheme.CartierData X.left}
  (g : ∀ i : c.ι, Γ(L, c.opens i))
  (E : HolomorphicUnitExtension X (dim X.left))
  (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)
  (hg : ∀ i, Scheme.Modules.Generates (g i))
  {x : X.left} {q : ComplexPoint X}
  (ch : ChernWindingChart X c x (dim X.left) 1 q)

set_option maxHeartbeats 1000000 in
lemma ChernWindingChart.compatible_frame_restriction
    (ℓ : E.middle.obj.obj
      (op ((analyticClosedSupport X (badLocus c)).compl)))
    (hcompat : IsCartierComplementLift g E e hg
      ((analyticClosedSupport X (badLocus c)).compl) ℓ)
    (z : ComplexPoint X) (hcz : ch.carrier ≤ E.localLifts.opens z)
    (hx : c.divisor x ≠ 0) :
    let Ω : Opens (TopCat.of (ComplexPoint X)) :=
      (analyticClosedSupport X (badLocus c)).compl
    let hEq : ch.carrier ⊓ Ω = ch.punctured :=
      ch.inf_goodComplement_eq_punctured hx
    let ℓU := E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
      (ch.holomorphicGenerates_regularFrame g E e hg)
    let w : (holomorphicUnitSheaf X (dim X.left)).obj.obj
        (op (ch.carrier ⊓ Ω)) :=
      (holomorphicUnitSheaf X (dim X.left)).obj.map (homOfLE hEq.le).op
        ch.cartierUnit
    E.projection.hom.app (op ch.carrier) ℓU = integerOneRestrict X ch.carrier ∧
      E.inclusion.hom.app (op (ch.carrier ⊓ Ω)) w =
        E.middle.obj.map (homOfLE inf_le_right).op ℓ -
          E.middle.obj.map (homOfLE inf_le_left).op ℓU := by
  let Ω : Opens (TopCat.of (ComplexPoint X)) :=
    (analyticClosedSupport X (badLocus c)).compl
  let hΩc : Ω ≤ divisorComplementOpen c := by
    intro y hy hydiv
    exact hy (cycleAnalyticClosedSupport_le_badLocus (X := X) c hydiv)
  let hpunctΩ : ch.punctured ≤ Ω := ch.punctured_le_goodComplement
  let hEq : ch.carrier ⊓ Ω = ch.punctured := ch.inf_goodComplement_eq_punctured hx
  let ℓU := E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
    (ch.holomorphicGenerates_regularFrame g E e hg)
  let w : (holomorphicUnitSheaf X (dim X.left)).obj.obj
      (op (ch.carrier ⊓ Ω)) :=
    (holomorphicUnitSheaf X (dim X.left)).obj.map (homOfLE hEq.le).op ch.cartierUnit
  dsimp only
  constructor
  · exact E.projection_frameLift z ch.carrier hcz (ch.regularFrame g E e)
      (ch.holomorphicGenerates_regularFrame g E e hg)
  · have hframe := hcompat.restrict_chart_eq_restrict_regularLift_add g E e hg ch hΩc
      hpunctΩ z hcz
    have hframe' : E.inclusion.hom.app (op ch.punctured) ch.cartierUnit =
        sres E.middle hpunctΩ ℓ - sres E.middle ch.punctured_le ℓU := by
      rw [hframe]
      dsimp only [ℓU]
      rw [← E.frameLift_restrict z hcz ch.punctured_le
        (ch.regularFrame g E e) (ch.holomorphicGenerates_regularFrame g E e hg)]
      abel
    have hres := congrArg (sres E.middle hEq.le) hframe'
    rw [sres_hom] at hres
    have hmapΩ (s : E.middle.obj.obj (op Ω)) :
        sres E.middle hEq.le (sres E.middle hpunctΩ s) =
          sres E.middle inf_le_right s := by
      rw [sres_sres]
    have hmapU (s : E.middle.obj.obj (op ch.carrier)) :
        sres E.middle hEq.le (sres E.middle ch.punctured_le s) =
          sres E.middle inf_le_left s := by
      rw [sres_sres]
    have hres' : E.inclusion.hom.app (op (ch.carrier ⊓ Ω)) w =
        sres E.middle inf_le_right ℓ - sres E.middle inf_le_left ℓU := by
      calc
        E.inclusion.hom.app (op (ch.carrier ⊓ Ω)) w =
            sres E.middle hEq.le
              (sres E.middle hpunctΩ ℓ - sres E.middle ch.punctured_le ℓU) := by
          simpa only [w, sres] using hres
        _ = sres E.middle inf_le_right ℓ - sres E.middle inf_le_left ℓU := by
          change E.middle.obj.map (homOfLE hEq.le).op
              (sres E.middle hpunctΩ ℓ - sres E.middle ch.punctured_le ℓU) = _
          rw [map_sub]
          exact congrArg₂ (· - ·) (hmapΩ ℓ) (hmapU ℓU)
    simpa only [sres, ℓU] using hres'

end AlgebraicGeometry.ComplexPoint
