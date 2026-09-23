/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierWindingChartUnit
public import Other.AlgebraicGeometry.ChernRelativeChartFormulaSplitting

/-!
# The Cartier frame formula on a winding chart

A complement lift retaining its Cartier restriction formulas restricts on a punctured
winding chart to the lift of a regular frame plus the image of the chart's full Cartier
unit. The regular-frame lift extends over the entire chart. Consequently the quotient
morphism in the cone difference evaluates to the negative Cartier unit, with the sign
required by the existing splitting retraction.

This is a statement about the actual extension and its representing Cartier data. It
does not assume the local Chern chart formula or an equality of cycle and Chern classes.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open CategoryTheory TopologicalSpace Opposite Order
open scoped Manifold ContDiff
namespace AlgebraicGeometry.ComplexPoint
variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance cartierWindingChartFrameTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective
variable {L : X.left.Modules} {c : Scheme.CartierData X.left}
  (g : ∀ i : c.ι, Γ(L, c.opens i))
  (E : HolomorphicUnitExtension X (dim X.left))
  (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)
  (hg : ∀ i, Scheme.Modules.Generates (g i))

lemma UnitDatum.regularFrame_eq_restrict {p : X.left} (D : c.UnitDatum p) :
    UnitDatum.regularFrame g E e D =
      holRes E.sectionSheafOfModules (analyticOpen_mono X D.le)
        (e.hom.val.app (op (analyticOpen X (c.opens D.i)))
          (analyticSection X (dim X.left) L (c.opens D.i) (g D.i))) := by
  unfold UnitDatum.regularFrame
  rw [analyticSection_res]
  exact PresheafOfModules.naturality_apply e.hom.val _ _

lemma analyticUnit_toUnitDatum {i : c.ι} {x : X.left} (F : c.LocalForm i x)
    (p : X.left) (hp : p ∈ X.left.basicOpen F.equation) :
    Additive.ofMul (UnitDatum.analyticUnit (F.toUnitDatum p hp)) =
      analyticUnitHom (X := X) (d := dim X.left) _ (Additive.ofMul F.cartierUnit) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact UnitDatum.unitSection_analyticUnit (F.toUnitDatum p hp)

variable {x : X.left} {q : ComplexPoint X}
  (ch : ChernWindingChart X c x (dim X.left) 1 q)

/-- The regular algebraic generator on the whole winding chart. -/
def ChernWindingChart.regularFrame : E.sectionSheafOfModules.val.obj (op ch.carrier) :=
  holRes E.sectionSheafOfModules
    (ch.le_analytic.trans (analyticOpen_mono X ch.localForm.le))
    (e.hom.val.app (op (analyticOpen X (c.opens ch.index)))
      (analyticSection X (dim X.left) L (c.opens ch.index) (g ch.index)))

include hg in
lemma ChernWindingChart.holomorphicGenerates_regularFrame :
    HolomorphicGenerates (ch.regularFrame g E e) :=
  ((analytificationGenerates X (dim X.left) L (c.opens ch.index) _ (hg ch.index)).map_iso e).restrict _

lemma ChernWindingChart.regularFrame_restrict_unitDatum
    (y : ch.punctured) {V : Opens (TopCat.of (ComplexPoint X))}
    (hVp : V ≤ ch.punctured) :
    holRes E.sectionSheafOfModules (hVp.trans ch.punctured_le_basicOpen)
        (UnitDatum.regularFrame g E e
          (ch.localForm.toUnitDatum (Point.underlying (y : ComplexPoint X))
            (ch.punctured_le_basicOpen y.property))) =
      holRes E.sectionSheafOfModules (hVp.trans ch.punctured_le) (ch.regularFrame g E e) := by
  rw [UnitDatum.regularFrame_eq_restrict, holRes_holRes]
  unfold ChernWindingChart.regularFrame
  rw [holRes_holRes]
  rfl

/-- The rational Cartier lift restricted to a winding chart is the regular-frame lift plus
its full Cartier unit. -/
theorem IsCartierComplementLift.restrict_chart
    {Ω : Opens (TopCat.of (ComplexPoint X))} {ℓ : E.middle.obj.obj (op Ω)}
    (hℓ : IsCartierComplementLift g E e hg Ω ℓ)
    (hΩc : Ω ≤ divisorComplementOpen c) (hchΩ : ch.punctured ≤ Ω)
    (z : ComplexPoint X) (hcz : ch.carrier ≤ E.localLifts.opens z) :
    sres E.middle hchΩ ℓ =
      E.frameLift z ch.punctured (ch.punctured_le.trans hcz)
        (holRes E.sectionSheafOfModules ch.punctured_le (ch.regularFrame g E e))
        ((ch.holomorphicGenerates_regularFrame g E e hg).restrict _) +
      E.inclusion.hom.app (op ch.punctured) ch.cartierUnit := by
  let W : ch.punctured → Opens (TopCat.of (ComplexPoint X)) :=
    fun y => ch.punctured ⊓ E.localLifts.opens y
  have hcover : ch.punctured ≤ iSup W := fun y hy =>
    Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hy, E.localLifts.mem_opens y⟩
  apply E.middle.eq_of_locally_eq' W ch.punctured (fun _ => homOfLE inf_le_left) hcover
  intro y
  let D := ch.localForm.toUnitDatum (Point.underlying (y : ComplexPoint X))
    (ch.punctured_le_basicOpen y.property)
  have hWp : W y ≤ ch.punctured := inf_le_left
  have hWl : W y ≤ liftOpen E y D :=
    le_inf (hWp.trans (hchΩ.trans hΩc))
      (le_inf (hWp.trans ch.punctured_le_basicOpen) inf_le_right)
  change sres E.middle hWp (sres E.middle hchΩ ℓ) = sres E.middle hWp _
  rw [sres_sres, hℓ y D (W y) (hWp.trans hchΩ) hWl,
    localLift_eq_regularFrameLift_add_unit]
  erw [sres_add, sres_add, sres_hom, sres_hom,
    ← E.frameLift_restrict, ← E.frameLift_restrict, sres_sres]
  have hframe := ch.regularFrame_restrict_unitDatum g E e y hWp
  have heq := E.frameLift_eq y z (W y) inf_le_right
    (hWp.trans (ch.punctured_le.trans hcz))
    (holRes E.sectionSheafOfModules (hWp.trans ch.punctured_le) (ch.regularFrame g E e))
    ((ch.holomorphicGenerates_regularFrame g E e hg).restrict _)
  apply congrArg₂ (fun a b : E.middle.obj.obj (op (W y)) => a + b)
  · convert heq using 1
    · congr 1
    · congr 1
  · congr 1
    erw [analyticUnit_toUnitDatum]
    unfold ChernWindingChart.cartierUnit
    rw [sres_sres]
    rfl

/-- The regular-frame part of the chart formula extends across the component. -/
theorem IsCartierComplementLift.restrict_chart_eq_restrict_regularLift_add
    {Ω : Opens (TopCat.of (ComplexPoint X))} {ℓ : E.middle.obj.obj (op Ω)}
    (hℓ : IsCartierComplementLift g E e hg Ω ℓ)
    (hΩc : Ω ≤ divisorComplementOpen c) (hchΩ : ch.punctured ≤ Ω)
    (z : ComplexPoint X) (hcz : ch.carrier ≤ E.localLifts.opens z) :
    sres E.middle hchΩ ℓ =
      sres E.middle ch.punctured_le
        (E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
          (ch.holomorphicGenerates_regularFrame g E e hg)) +
      E.inclusion.hom.app (op ch.punctured) ch.cartierUnit := by
  rw [hℓ.restrict_chart g E e hg ch hΩc hchΩ z hcz, E.frameLift_restrict]

/-- The quotient morphism in the cone difference evaluates to the negative Cartier unit. -/
theorem IsCartierComplementLift.chart_liftHom_difference_section
    {Ω : Opens (TopCat.of (ComplexPoint X))} {ℓ : E.middle.obj.obj (op Ω)}
    (hℓ : IsCartierComplementLift g E e hg Ω ℓ)
    (hΩc : Ω ≤ divisorComplementOpen c) (hchΩ : ch.punctured ≤ Ω)
    (z : ComplexPoint X) (hcz : ch.carrier ≤ E.localLifts.opens z)
    (s : constantIntegerSheaf X ⟶
      (openRestrictionFunctor ch.punctured).obj (holomorphicUnitSheaf X (dim X.left)))
    (hs : s ≫ (openRestrictionFunctor ch.punctured).map E.inclusion =
      E.liftHom ch.punctured (sres E.middle ch.punctured_le
        (E.frameLift z ch.carrier hcz (ch.regularFrame g E e)
          (ch.holomorphicGenerates_regularFrame g E e hg))) -
      E.liftHom ch.punctured (sres E.middle hchΩ ℓ)) :
    (openRestrictionTopEval ch.punctured).hom.app (holomorphicUnitSheaf X (dim X.left))
      (s.hom.app (op ⊤) HolomorphicUnitExtension.integerOneSection) = -ch.cartierUnit := by
  apply E.liftHom_difference_section_eq_neg_unit ch.punctured _ _ s hs ch.cartierUnit
  rw [hℓ.restrict_chart_eq_restrict_regularLift_add g E e hg ch hΩc hchΩ z hcz,
    add_sub_cancel_left]

end AlgebraicGeometry.ComplexPoint
