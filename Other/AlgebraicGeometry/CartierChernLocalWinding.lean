/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierWindingChartFrame
public import Other.AlgebraicGeometry.RelativeChernFrameWinding
public import Other.AlgebraicGeometry.RelativeChernFrameRestriction

/-!
# The actual Cartier frame difference is positive winding

On a winding chart, the compatible complement lift is the regular-frame lift plus the actual
Cartier unit.  The relative Chern frame-variation theorem therefore identifies the difference of
the two constructed relative classes with the positive winding class of that unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance cartierChernLocalWindingTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {L : X.left.Modules} {c : Scheme.CartierData X.left}
  (g : ∀ i : c.ι, Γ(L, c.opens i))
  (E : HolomorphicUnitExtension X (dim X.left))
  (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)
  (hg : ∀ i, Scheme.Modules.Generates (g i))
  {x : X.left} {q : ComplexPoint X}
  (ch : ChernWindingChart X c x (dim X.left) 1 q)

set_option maxHeartbeats 1000000 in
/-- The compatible Cartier lift has positive winding relative to the regular algebraic frame on a
chart.  All classes in this identity are the actual relative Chern classes and the actual chart
unit; no local-model or cycle-class equality is assumed. -/
theorem IsCartierComplementLift.relativeChernClass_sub_eq_windingSheaf_cartier
    {Ω : Opens (TopCat.of (ComplexPoint X))} {ℓ : E.middle.obj.obj (op Ω)}
    (hℓ : IsCartierComplementLift g E e hg Ω ℓ)
    (hℓ₀ : E.projection.hom.app (op Ω) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (hΩc : Ω ≤ divisorComplementOpen c) (hchΩ : ch.punctured ≤ Ω)
    (z : ComplexPoint X) (hcz : ch.carrier ≤ E.localLifts.opens z)
    (cmp : RelativeChernComparison X (dim X.left) ch.punctured) :
    let ℓ₁ := E.middle.obj.map (homOfLE ch.punctured_le).op
      (E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
        (ch.holomorphicGenerates_regularFrame g E e hg))
    let hℓ₁ := E.projection_restrict_lift X ch.punctured_le _
      (E.projection_frameLift z ch.carrier hcz (ch.regularFrame g E e)
        (ch.holomorphicGenerates_regularFrame g E e hg))
    let ℓ₂ := E.middle.obj.map (homOfLE hchΩ).op ℓ
    let hℓ₂ := E.projection_restrict_lift X hchΩ ℓ hℓ₀
    let Y := TopCat.of (ComplexPoint X)
    let S : Closeds Y := ⟨(ch.punctured : Set Y)ᶜ, ch.punctured.isOpen.isClosed_compl⟩
    let j : ⊤ ⊓ S.compl ⟶ ch.punctured :=
      homOfLE (fun _y hy => not_not.mp hy.2)
    let zc := coneSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2
      (E.relativeChernClass ch.punctured ℓ₂ hℓ₂ cmp -
        E.relativeChernClass ch.punctured ℓ₁ hℓ₁ cmp)
    (complexSupportInjectiveCohomologySheafIsoRelative X S 2).hom.hom.app (op ⊤)
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y (complexSupportInjectiveComplex X S) 2 ⊤ zc) =
      windingSheafHom (hasWindingPeriods X (dim X.left) ⊤ S)
        ((holomorphicUnitSheaf X (dim X.left)).obj.map j.op ch.cartierUnit) := by
  dsimp only
  let ℓ₁ := E.middle.obj.map (homOfLE ch.punctured_le).op
    (E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
      (ch.holomorphicGenerates_regularFrame g E e hg))
  let hℓ₁ := E.projection_restrict_lift X ch.punctured_le _
    (E.projection_frameLift z ch.carrier hcz (ch.regularFrame g E e)
      (ch.holomorphicGenerates_regularFrame g E e hg))
  let ℓ₂ := E.middle.obj.map (homOfLE hchΩ).op ℓ
  let hℓ₂ := E.projection_restrict_lift X hchΩ ℓ hℓ₀
  have hframe := hℓ.restrict_chart_eq_restrict_regularLift_add g E e hg ch hΩc hchΩ z hcz
  have hw0 : E.inclusion.hom.app (op ch.punctured) ch.cartierUnit =
      sres E.middle hchΩ ℓ - sres E.middle ch.punctured_le
        (E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
          (ch.holomorphicGenerates_regularFrame g E e hg)) := by
    rw [hframe]
    abel
  have hw : E.inclusion.hom.app (op ch.punctured) ch.cartierUnit = ℓ₂ - ℓ₁ := by
    exact hw0
  exact E.relativeChernClass_sub_eq_windingSheaf X ch.punctured (dim X.left) ℓ₁ ℓ₂ hℓ₁ hℓ₂ cmp
    ch.cartierUnit hw

end AlgebraicGeometry.ComplexPoint
