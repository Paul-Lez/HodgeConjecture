/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialSupportWinding
public import Other.AlgebraicGeometry.RelativeChernFrameVariation
public import Other.AlgebraicGeometry.ChernWindingChartPeriods
/-!
# The actual relative Chern frame variation is positive winding

The fixed support comparison sends the actual exponential boundary to negative
winding. The frame-difference cone calculation supplies the negative quotient
unit, so the two signs give positive winding of the frame-change unit. Both
relative-cohomology and cohomology-sheaf versions retain the original comparison.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open CochainComplex.HomComplex ChernWinding
set_option autoImplicit false
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (Ω : Opens (TopCat.of (ComplexPoint X)))
local instance frameWindingOpenParacompact : ∀ V : Opens (ComplexPoint X), ParacompactSpace V :=
  openParacompactSpace X
variable (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (u : (holomorphicUnitSheaf X d).obj.obj (op Ω))
/-- The actual support boundary is negative winding, expressed using the existing
additive winding homomorphism on the literal punctured open. -/
lemma rationalSupportBoundary_restrictedSingularOneCocycle_eq_windingHom :
    let Y := TopCat.of (ComplexPoint X)
    let S : Closeds Y := ⟨(Ω : Set Y)ᶜ, Ω.isOpen.isClosed_compl⟩
    let j : ⊤ ⊓ S.compl ⟶ Ω := homOfLE (fun _q hq => not_not.mp hq.2)
    let z := (restrictedSingularOneCocycle X d Ω).precomp
      ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
        ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u)))
    complexSupportInjectiveSectionCohomologyEquiv X S ⊤ 2
      (coneSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2
        (hypercohomologyMap X
          (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X S)) 1
          (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
            ((constantIntegerSheafComplexIntIsoSingle X).hom ≫ Cocycle.equivHomShift.symm z)))) =
    -windingRelativeHom (hasWindingPeriods X d ⊤ S)
      ((holomorphicUnitSheaf X d).obj.map j.op u) := by
  exact rationalSupportBoundary_restrictedSingularOneCocycle_eq_winding X Ω d u

variable (E : HolomorphicUnitExtension X d)
  (ℓ₁ ℓ₂ : E.middle.obj.obj (op Ω))
  (hℓ₁ : E.projection.hom.app (op Ω) ℓ₁ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
  (hℓ₂ : E.projection.hom.app (op Ω) ℓ₂ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

/-- Changing a frame by a unit changes the actual relative first Chern class
by positive winding under the original support and relative-cohomology comparisons. -/
lemma HolomorphicUnitExtension.relativeChernClass_sub_eq_winding
    (cmp : RelativeChernComparison X d Ω)
    (w : (holomorphicUnitSheaf X d).obj.obj (op Ω))
    (hw : E.inclusion.hom.app (op Ω) w = ℓ₂ - ℓ₁) :
    let Y := TopCat.of (ComplexPoint X)
    let S : Closeds Y := ⟨(Ω : Set Y)ᶜ, Ω.isOpen.isClosed_compl⟩
    let j : ⊤ ⊓ S.compl ⟶ Ω := homOfLE (fun _q hq => not_not.mp hq.2)
    let F := (coneSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2).trans
      (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ 2)
    F (E.relativeChernClass Ω ℓ₂ hℓ₂ cmp) - F (E.relativeChernClass Ω ℓ₁ hℓ₁ cmp) =
      windingRelativeHom (hasWindingPeriods X d ⊤ S)
        ((holomorphicUnitSheaf X d).obj.map j.op w) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let S : Closeds Y := ⟨(Ω : Set Y)ᶜ, Ω.isOpen.isClosed_compl⟩
  let j : ⊤ ⊓ S.compl ⟶ Ω := homOfLE (fun _q hq => not_not.mp hq.2)
  let F := (coneSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2).trans
    (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ 2)
  have hb := E.relativeChernClass_sub_eq_neg_unit_boundary X Ω ℓ₁ ℓ₂ hℓ₁ hℓ₂ cmp w hw
  have hc := rationalSupportBoundary_restrictedSingularOneCocycle_eq_windingHom X Ω d (-w)
  calc
    F (E.relativeChernClass Ω ℓ₂ hℓ₂ cmp) - F (E.relativeChernClass Ω ℓ₁ hℓ₁ cmp) =
        F (E.relativeChernClass Ω ℓ₂ hℓ₂ cmp - E.relativeChernClass Ω ℓ₁ hℓ₁ cmp) :=
      (F.map_sub _ _).symm
    _ = -windingRelativeHom (hasWindingPeriods X d ⊤ S)
        ((holomorphicUnitSheaf X d).obj.map j.op (-w)) := (congrArg F hb).trans hc
    _ = windingRelativeHom (hasWindingPeriods X d ⊤ S)
        ((holomorphicUnitSheaf X d).obj.map j.op w) := by rw [map_neg, map_neg, neg_neg]

/-- The same actual frame variation in the cohomology sheaf used to normalize
the constructed cycle class, through its prescribed section comparison. -/
lemma HolomorphicUnitExtension.relativeChernClass_sub_eq_windingSheaf
    (cmp : RelativeChernComparison X d Ω)
    (w : (holomorphicUnitSheaf X d).obj.obj (op Ω))
    (hw : E.inclusion.hom.app (op Ω) w = ℓ₂ - ℓ₁) :
    let Y := TopCat.of (ComplexPoint X)
    let S : Closeds Y := ⟨(Ω : Set Y)ᶜ, Ω.isOpen.isClosed_compl⟩
    let j : ⊤ ⊓ S.compl ⟶ Ω := homOfLE (fun _q hq => not_not.mp hq.2)
    let z := coneSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2
      (E.relativeChernClass Ω ℓ₂ hℓ₂ cmp - E.relativeChernClass Ω ℓ₁ hℓ₁ cmp)
    (complexSupportInjectiveCohomologySheafIsoRelative X S 2).hom.hom.app (op ⊤)
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y (complexSupportInjectiveComplex X S) 2 ⊤ z) =
      windingSheafHom (hasWindingPeriods X d ⊤ S)
        ((holomorphicUnitSheaf X d).obj.map j.op w) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let S : Closeds Y := ⟨(Ω : Set Y)ᶜ, Ω.isOpen.isClosed_compl⟩
  let F := (coneSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2).trans
    (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ 2)
  refine (complexSupportInjectiveCohomologySheafIsoRelative_section_apply X S 2 ⊤ _).trans ?_
  exact congrArg (fun b => (supportRelativeCohomologyToSheaf Y S 2).app (op ⊤) b)
    ((F.map_sub _ _).trans
      (E.relativeChernClass_sub_eq_winding X Ω d ℓ₁ ℓ₂ hℓ₁ hℓ₂ cmp w hw))

end AlgebraicGeometry.ComplexPoint
