/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialIntrinsicWindingClass
public import Other.AlgebraicGeometry.RationalSupportBoundaryRelative
public import Other.AlgebraicGeometry.ChernWindingRawBoundary
/-!
# The actual exponential boundary under the fixed support comparison

This composes the exact intrinsic-complement representative of the restricted
singular cocycle with the fixed support-boundary normalization. The result is
the negative of the existing winding class, with all pair transports retained.
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
local instance supportWindingOpenParacompact : ∀ V : Opens (ComplexPoint X), ParacompactSpace V :=
  openParacompactSpace X
variable (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (u : (holomorphicUnitSheaf X d).obj.obj (op Ω))

/-- The actual exponential boundary maps to negative winding under the fixed support
comparison and the existing section-to-relative comparison. -/
lemma rationalSupportBoundary_restrictedSingularOneCocycle_eq_winding :
    let Y := TopCat.of (ComplexPoint X)
    let S : Closeds Y := ⟨(Ω : Set Y)ᶜ, Ω.isOpen.isClosed_compl⟩
    let j : ⊤ ⊓ S.compl ⟶ Ω := homOfLE (fun _q hq => not_not.mp hq.2)
    let q := openIntersectionPairIsoSupportComplement Y S S.isClosed ⊤
    let g : C(ChernWinding.puncturedSpace (M := ComplexPoint X)
      (Set.univ : Set (ComplexPoint X)) (Ω : Set (ComplexPoint X))ᶜ, ℂ) :=
      ((holomorphicUnitFunction X d Ω u).comp (topMap ((Opens.toTopCat Y).map j))).comp
      (topMap q.inv.left)
    let hg : ∀ y, g y ≠ 0 := fun _y => holomorphicUnitFunction_ne_zero X d Ω u _
    let z := (restrictedSingularOneCocycle X d Ω).precomp
      ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
        ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u)))
    complexSupportInjectiveSectionCohomologyEquiv X S ⊤ 2
      (rationalSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2
        (hypercohomologyMap X
          (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X S)) 1
          (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
            ((constantIntegerSheafComplexIntIsoSingle X).hom ≫ Cocycle.equivHomShift.symm z)))) =
    -ChernWinding.windingClass (M := ComplexPoint X) Set.univ (Ω : Set (ComplexPoint X))ᶜ g hg := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let S : Closeds Y := ⟨(Ω : Set Y)ᶜ, Ω.isOpen.isClosed_compl⟩
  let j : ⊤ ⊓ S.compl ⟶ Ω := homOfLE (fun _q hq => not_not.mp hq.2)
  let q := openIntersectionPairIsoSupportComplement Y S S.isClosed ⊤
  let gΩ := holomorphicUnitFunction X d Ω u
  let hgΩ := holomorphicUnitFunction_ne_zero X d Ω u
  let g : C(ChernWinding.puncturedSpace (M := ComplexPoint X)
      (Set.univ : Set (ComplexPoint X)) (Ω : Set (ComplexPoint X))ᶜ, ℂ) := (gΩ.comp (topMap ((Opens.toTopCat Y).map j))).comp (topMap q.inv.left)
  let hg : ∀ y, g y ≠ 0 := fun _y => hgΩ _
  let h := ChernWinding.hasRationalWindingPeriod (M := ComplexPoint X) Set.univ (Ω : Set (ComplexPoint X))ᶜ g hg
  let w := ChernWinding.openRawRationalWindingClass Y Ω gΩ hgΩ
  let zΩ := HomologicalComplex.homologyMap (openRawToIntrinsicComplement X Ω) 1 w
  let e := complementRationalHypercohomologyAddEquivGlobalSections X S 1
  let z := (restrictedSingularOneCocycle X d Ω).precomp
    ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
      ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
      ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u)))
  let a := Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
    ((constantIntegerSheafComplexIntIsoSingle X).hom ≫ Cocycle.equivHomShift.symm z)
  have ha : a = e.symm (HomologicalComplex.homologyMap
      (globalRawComplementToDerivedPushforwardInt X S S.isClosed) 1 zΩ) := by
    apply e.injective
    exact (complementRationalHypercohomology_restrictedSingularOneCocycle_eq_intrinsicWinding
      X Ω d u).trans (e.apply_symm_apply _).symm
  have hb := rationalSupportAddEquivSupportedInjectiveHomology_raw_boundary_relative X S 2 zΩ
  have htop : HomologicalComplex.homologyMap
      (globalRawComplementToTopOpenCochains ℚ Y S.compl) 1 zΩ =
    ChernWinding.openRawRationalWindingClass Y (⊤ ⊓ S.compl)
      (g.comp (topMap q.hom.left)) (fun y => hg (q.hom.left y)) := by
    have hm := congrArg (fun f => HomologicalComplex.homologyMap f 1)
      (openRawToIntrinsicComplement_comp_topOpen X Ω)
    rw [HomologicalComplex.homologyMap_comp] at hm
    have hh := ConcreteCategory.congr_hom hm w
    have hr := ChernWinding.openRawRationalWindingClass_restriction Y j gΩ hgΩ
    exact hh.trans hr
  have hw := ChernWinding.openRawRelative_winding_boundary Y S S.isClosed ⊤ g hg h
  let F : Hypercohomology X
      (derivedPushforwardComplementConstantRationalComplexInt X (S : Set (ComplexPoint X))) 1 →
      RelativeCohomology ℚ (neighborhoodSupportComplementPair ((⊤ : Opens Y) : Set Y) (S : Set Y)) 2 := fun b =>
    complexSupportInjectiveSectionCohomologyEquiv X S ⊤ 2
      (rationalSupportAddEquivSupportedInjectiveHomology X S S.isClosed 2
        (hypercohomologyMap X (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X S)) 1 b))
  refine (congrArg F ha).trans (hb.trans ?_)
  exact (congrArg (fun b =>
    -(relativeCohomologyMap ℚ 2 q.inv
      (openRawSingularRestrictionConeCohomologyEquivRelative ℚ Y
        (Opens.infLELeft ⊤ S.compl) 2
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (HomologicalComplex.extendMap
              (openRawSingularRestriction ℚ Y (Opens.infLELeft ⊤ S.compl))
              ComplexShape.embeddingUpNat)) 1 b)))) htop).trans
    (congrArg Neg.neg hw)
end AlgebraicGeometry.ComplexPoint
