/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierWindingChartFrame
public import Other.AlgebraicGeometry.RelativeChernFrameLocalVanishing
/-!
# The regular Cartier chart frame has zero local relative Chern class

The regular algebraic generator defines a holomorphic frame over the whole chart.
Its lift therefore satisfies the general extending-frame vanishing theorem on
the punctured chart, for the existing relative Chern construction.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
set_option autoImplicit false
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
namespace AlgebraicGeometry.ComplexPoint
variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance cartierVanishingAmbientDerived : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _
local instance cartierVanishingOpenDerived (V : Opens (TopCat.of (ComplexPoint X))) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of V)) := HasDerivedCategory.standard _
attribute [local instance] isNoetherian_of_isProjective
variable {L : X.left.Modules} {c : Scheme.CartierData X.left}
  (g : ∀ i : c.ι, Γ(L, c.opens i))
  (E : HolomorphicUnitExtension X (dim X.left))
  (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)
  (hg : ∀ i, Scheme.Modules.Generates (g i))
  {x : X.left} {q : ComplexPoint X}
  (ch : ChernWindingChart X c x (dim X.left) 1 q)

/-- The actual regular-frame reference vanishes after derived restriction to the chart. -/
lemma ChernWindingChart.regularFrame_relativeChernClass_restrict_eq_zero
    (z : ComplexPoint X) (hcz : ch.carrier ≤ E.localLifts.opens z)
    (cmp : RelativeChernComparison X (dim X.left) ch.punctured) :
    let ℓ := E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
      (ch.holomorphicGenerates_regularFrame g E e hg)
    let hℓ := E.projection_frameLift z ch.carrier hcz (ch.regularFrame g E e)
      (ch.holomorphicGenerates_regularFrame g E e hg)
    (restrictToOpen X ch.carrier).mapDerivedCategory.map
      (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (E.relativeChernClass ch.punctured (E.middle.obj.map (homOfLE ch.punctured_le).op ℓ)
          (E.projection_restrict_lift X ch.punctured_le ℓ hℓ) cmp)) = 0 := by
  exact E.relativeChernClass_restrict_eq_zero X (dim X.left) ch.punctured_le
    (E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
      (ch.holomorphicGenerates_regularFrame g E e hg))
    (E.projection_frameLift z ch.carrier hcz (ch.regularFrame g E e)
      (ch.holomorphicGenerates_regularFrame g E e hg)) cmp
end AlgebraicGeometry.ComplexPoint
