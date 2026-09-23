/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialSingularRestriction
public import Other.AlgebraicTopology.SupportedSectionRestrictionCone
public import Other.AlgebraicTopology.SingularCochainOpenSections
public import Other.AlgebraicGeometry.ComplementResolutionBoundaryComparison

/-!
# Actual restricted exponential winding on local sections

The degree-one coefficient of the previously constructed restricted singular cocycle
factors through restriction of the literal unit-to-winding map. The factor is forced
by the universal property of the actual open restriction and extends the fixed natural
singular resolution comparison. Evaluation on every open gives the explicit raw winding
cochain of the unit on its complement intersection, with positive sign.

These are identities of actual sheaf maps and cochains. Transport to the prescribed
hypercohomology class and the supported divisor formula is a subsequent step.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular CochainComplex.HomComplex
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
local instance exponentialSingularSectionsTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω : Opens (TopCat.of (ComplexPoint X)))

/-- The degree-one coefficient of the actual restricted singular cocycle. -/
def restrictedSingularOneCoefficient :
    (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d) ⟶
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)).X 1 :=
  Cochain.fromSingleEquiv (zero_add (1 : ℤ)) (restrictedSingularOneCocycle X d Ω).1

lemma restrictionUnit_comp_restrictedSingularOneCoefficient :
    restrictionUnit Ω (holomorphicUnitSheaf X d) ≫ restrictedSingularOneCoefficient X d Ω =
    (holomorphicUnitToSingularOneSheaf X d ≫ (singularCochainSheafTermIso X 1).inv) ≫
      (naturalSingularResolutionRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl).f 1 := by
  have h := restrictedSingularOneCocycle_precomp X d Ω
  obtain ⟨a, ha, he⟩ := Cocycle.fromSingleMk_surjective
    (restrictedSingularOneCocycle X d Ω) 1 (zero_add (1 : ℤ)) 2 rfl
  rw [← he, ← Cocycle.fromSingleMk_precomp,
    holomorphicSingularOneCocycle, ← Cocycle.fromSingleMk_postcomp] at h
  have hc := congrArg (fun z => Cochain.fromSingleEquiv (zero_add (1 : ℤ)) z.1) h
  simp only [Cocycle.fromSingleMk_coe, Cochain.fromSingleEquiv_fromSingleMk] at hc
  unfold restrictedSingularOneCoefficient
  rw [← he]
  simp only [Cocycle.fromSingleMk_coe, Cochain.fromSingleEquiv_fromSingleMk]
  exact hc

/-- The fixed natural resolution comparison descended through restriction to the
specified open. The complement is written as `Ωᶜ` to match the actual cocycle. -/
def naturalSingularOutsideResolutionComparisonOnOpen :
    ((openRestrictionFunctor Ω).mapHomologicalComplex (.up ℤ)).obj
        (singularCochainSheafComplexInt X ℚ) ⟶
      derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ) :=
  HomologicalComplex.descOfPrecompBijective
    ((TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X)) Ω
      (singularCochainSheafComplexInt X ℚ)).g)
    (fun p q => isOpenRestrictionLocal_derivedPushforward X Ω ((Ω : Set (ComplexPoint X))ᶜ)
      (compl_compl _).symm q ((singularCochainSheafComplexInt X ℚ).X p))
    (naturalSingularResolutionRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
      Ω.isOpen.isClosed_compl)

lemma actualSingularRestriction_comp_naturalOutsideResolutionComparisonOnOpen :
    (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X)) Ω
      (singularCochainSheafComplexInt X ℚ)).g ≫
      naturalSingularOutsideResolutionComparisonOnOpen X Ω =
    naturalSingularResolutionRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
      Ω.isOpen.isClosed_compl :=
  HomologicalComplex.comp_descOfPrecompBijective _ _ _

/-- The actual restricted exponential winding coefficient is restriction of the
literal unit-to-singular-cochain map followed by the fixed natural comparison. -/
lemma restrictedSingularOneCoefficient_eq_restricted_winding :
    restrictedSingularOneCoefficient X d Ω =
    (openRestrictionFunctor Ω).map
      (holomorphicUnitToSingularOneSheaf X d ≫ (singularCochainSheafTermIso X 1).inv) ≫
        (naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1 := by
  apply (isOpenRestrictionLocal_derivedPushforward X Ω ((Ω : Set (ComplexPoint X))ᶜ)
    (compl_compl _).symm 1 (holomorphicUnitSheaf X d)).injective
  refine (restrictionUnit_comp_restrictedSingularOneCoefficient X d Ω).trans ?_
  let a := holomorphicUnitToSingularOneSheaf X d ≫ (singularCochainSheafTermIso X 1).inv
  have hn := (TopCat.Sheaf.toOpenRestrictionPushforward
    (TopCat.of (ComplexPoint X)) Ω).naturality a
  have hf := HomologicalComplex.congr_hom
    (actualSingularRestriction_comp_naturalOutsideResolutionComparisonOnOpen X Ω) 1
  change restrictionUnit Ω ((singularCochainSheafComplexInt X ℚ).X 1) ≫
    (naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1 = _ at hf
  symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1)
      hn.symm).trans ((Category.assoc _ _ _).trans (congrArg (fun k => a ≫ k) hf)))

/-- On global sections, the actual restricted coefficient is the image of the
winding cochain of the given holomorphic unit on the complement. -/
lemma restrictedSingularOneCoefficient_apply
    (u : (holomorphicUnitSheaf X d).obj.obj (op Ω)) :
    (restrictedSingularOneCoefficient X d Ω).hom.app (op ⊤)
      ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u) =
    ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op ⊤)
      ((openRestrictionTopEval Ω).inv.app ((singularCochainSheafComplexInt X ℚ).X 1)
        (((holomorphicUnitToSingularOneSheaf X d ≫ (singularCochainSheafTermIso X 1).inv).hom.app
          (op Ω)) u)) := by
  erw [restrictedSingularOneCoefficient_eq_restricted_winding X d Ω]
  let a := holomorphicUnitToSingularOneSheaf X d ≫ (singularCochainSheafTermIso X 1).inv
  have hn := (openRestrictionTopEval Ω).inv.naturality a
  have h := ConcreteCategory.congr_hom hn u
  exact congrArg
    (((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op ⊤)) h.symm

/-- The coefficient is closed in the actual complement resolution. -/
lemma restrictedSingularOneCoefficient_comp_d :
    restrictedSingularOneCoefficient X d Ω ≫
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)).d 1 2 = 0 := by
  obtain ⟨a, ha, he⟩ := Cocycle.fromSingleMk_surjective
    (restrictedSingularOneCocycle X d Ω) 1 (zero_add (1 : ℤ)) 2 rfl
  unfold restrictedSingularOneCoefficient
  rw [← he]
  simp only [Cocycle.fromSingleMk_coe, Cochain.fromSingleEquiv_fromSingleMk]
  exact ha

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The sheafified coefficient uses the literal raw winding cochain, with no
choice of a cohomology class or sign change. -/
lemma holomorphicSingularOneCoefficient_apply_raw
    (u : (holomorphicUnitSheaf X d).obj.obj (op Ω)) :
    ((holomorphicUnitToSingularOneSheaf X d ≫ (singularCochainSheafTermIso X 1).inv).hom.app
      (op Ω)) u =
    ((singularCochainSheafTermIso X 1).inv.hom.app (op Ω))
      ((openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) Ω).f 1
        (ChernWinding.rationalWindingCochain (holomorphicUnitFunction X d Ω u)
          (holomorphicUnitFunction_ne_zero X d Ω u)).hom) := rfl

/-- A global section of restricted units is sent by the actual restricted
singular cocycle to the fixed complement comparison of its raw winding cochain. -/
lemma restrictedSingularOneCoefficient_apply_raw
    (u : (holomorphicUnitSheaf X d).obj.obj (op Ω)) :
    (restrictedSingularOneCoefficient X d Ω).hom.app (op ⊤)
      ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u) =
    ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op ⊤)
      ((openRestrictionTopEval Ω).inv.app ((singularCochainSheafComplexInt X ℚ).X 1)
        (((singularCochainSheafTermIso X 1).inv.hom.app (op Ω))
          ((openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) Ω).f 1
            (ChernWinding.rationalWindingCochain (holomorphicUnitFunction X d Ω u)
              (holomorphicUnitFunction_ne_zero X d Ω u)).hom))) :=
  restrictedSingularOneCoefficient_apply X d Ω u

/-- The same literal winding representative on every local open intersection.
This is the form needed for a chart inside the ambient analytic space. -/
lemma restrictedSingularOneCoefficient_apply_on_open
    (V : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitSheaf X d).obj.obj (op (V ⊓ Ω))) :
    (restrictedSingularOneCoefficient X d Ω).hom.app (op V)
      ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω V
        (holomorphicUnitSheaf X d)).inv u) =
    ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op V)
      ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω V
        ((singularCochainSheafComplexInt X ℚ).X 1)).inv
          (((holomorphicUnitToSingularOneSheaf X d ≫ (singularCochainSheafTermIso X 1).inv).hom.app
            (op (V ⊓ Ω))) u)) := by
  erw [restrictedSingularOneCoefficient_eq_restricted_winding X d Ω]
  let a := holomorphicUnitToSingularOneSheaf X d ≫ (singularCochainSheafTermIso X 1).inv
  have hn := a.hom.naturality
    (eqToHom (congrArg op (Opens.functor_map_eq_inf Ω V).symm))
  have h := ConcreteCategory.congr_hom hn u
  exact congrArg
    (((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op V)) h

/-- Local sections of the actual restricted cocycle have the literal raw winding
representative on the punctured open intersection. -/
lemma restrictedSingularOneCoefficient_apply_on_open_raw
    (V : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitSheaf X d).obj.obj (op (V ⊓ Ω))) :
    (restrictedSingularOneCoefficient X d Ω).hom.app (op V)
      ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω V
        (holomorphicUnitSheaf X d)).inv u) =
    ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op V)
      ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω V
        ((singularCochainSheafComplexInt X ℚ).X 1)).inv
          (((singularCochainSheafTermIso X 1).inv.hom.app (op (V ⊓ Ω)))
            ((openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) (V ⊓ Ω)).f 1
              (ChernWinding.rationalWindingCochain (holomorphicUnitFunction X d (V ⊓ Ω) u)
                (holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) u)).hom))) :=
  restrictedSingularOneCoefficient_apply_on_open X d Ω V u

omit [SmoothOfRelativeDimension d X.hom] in
/-- The open-indexed factor is the fixed canonical complement comparison after
literal further restriction along the double-complement equality. -/
lemma naturalSingularOutsideResolutionComparisonOnOpen_eq_canonical :
    let U : Opens (TopCat.of (ComplexPoint X)) :=
      ⟨((Ω : Set (ComplexPoint X))ᶜ)ᶜ, Ω.isOpen.isClosed_compl.isOpen_compl⟩
    let h : U ≤ Ω := by intro x hx; exact not_not.mp hx
    ((TopCat.Sheaf.openRestrictionPushforwardMap (TopCat.of (ComplexPoint X)) h).mapHomologicalComplex
      (.up ℤ)).app (singularCochainSheafComplexInt X ℚ) ≫
        naturalSingularOutsideResolutionComparison X ((Ω : Set (ComplexPoint X))ᶜ)
          Ω.isOpen.isClosed_compl =
      naturalSingularOutsideResolutionComparisonOnOpen X Ω := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let K := singularCochainSheafComplexInt X ℚ
  let U : Opens Y :=
    ⟨((Ω : Set (ComplexPoint X))ᶜ)ᶜ, Ω.isOpen.isClosed_compl.isOpen_compl⟩
  let h : U ≤ Ω := by intro x hx; exact not_not.mp hx
  let η := (TopCat.Sheaf.supportRestrictionComplexShortComplex Y Ω K).g
  let t := ((TopCat.Sheaf.openRestrictionPushforwardMap Y h).mapHomologicalComplex (.up ℤ)).app K
  have he : η ≫ t = (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U K).g := by
    ext n
    exact NatTrans.congr_app (TopCat.Sheaf.toOpenRestrictionPushforward_comp Y h) (K.X n)
  apply HomologicalComplex.precomp_injective_of_degreewise η
    (fun p q => isOpenRestrictionLocal_derivedPushforward X Ω ((Ω : Set (ComplexPoint X))ᶜ)
      (compl_compl _).symm q (K.X p))
  change η ≫ (t ≫ _) = η ≫ _
  rw [← Category.assoc, he]
  exact (actualSingularRestriction_comp_naturalOutsideResolutionComparison X
    ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl).trans
    (actualSingularRestriction_comp_naturalOutsideResolutionComparisonOnOpen X Ω).symm

end AlgebraicGeometry.ComplexPoint
