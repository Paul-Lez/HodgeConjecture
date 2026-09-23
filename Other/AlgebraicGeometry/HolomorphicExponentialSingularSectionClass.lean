/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CocycleGlobalSections
public import Other.AlgebraicGeometry.HolomorphicExponentialSingularSections
public import Other.AlgebraicGeometry.RationalSupportConeBoundaryComparison

/-!
# The cohomology class of the actual restricted winding coefficient

Evaluating the existing restricted singular cocycle on a unit gives a closed global
section whose coefficient is the literal winding cochain under the fixed complement
resolution comparison. Both the direct derived comparison and the particular flasque
hypercohomology comparison used by the support boundary compute its actual class.

The remaining comparison with the raw winding class must still carry the coefficient
through the grading and sheafification maps. The final chart/divisor formula is not
assumed here.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular CochainComplex.HomComplex
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
local instance exponentialSingularSectionClassTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance exponentialSingularSectionClassDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω : Opens (TopCat.of (ComplexPoint X)))
  (u : (holomorphicUnitSheaf X d).obj.obj (op Ω))

/-- The actual restricted singular cocycle evaluated on the section defined by a unit. -/
def restrictedSingularOneGlobalCocycle :
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))).cycles 1 :=
  TopCat.Sheaf.integerCocycleGlobalSection (TopCat.of (ComplexPoint X)) _ 1
    ((restrictedSingularOneCocycle X d Ω).precomp
      ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
        ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u))))

/-- Its actual global-section cochain is the literal winding cochain under the
fixed complement-resolution comparison. -/
lemma iCycles_restrictedSingularOneGlobalCocycle :
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))).iCycles 1
      (restrictedSingularOneGlobalCocycle X d Ω u) =
    ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op ⊤)
      ((openRestrictionTopEval Ω).inv.app ((singularCochainSheafComplexInt X ℚ).X 1)
        (((singularCochainSheafTermIso X 1).inv.hom.app (op Ω))
          ((openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) Ω).f 1
            (ChernWinding.rationalWindingCochain (holomorphicUnitFunction X d Ω u)
              (holomorphicUnitFunction_ne_zero X d Ω u)).hom))) :=
  (TopCat.Sheaf.iCycles_integerCocycleGlobalSection_precomp_constHom
    (TopCat.of (ComplexPoint X)) _ 1
    ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
    (restrictedSingularOneCocycle X d Ω)
    ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u)).trans
      (restrictedSingularOneCoefficient_apply_raw X d Ω u)

/-- The existing derived/global-sections comparison sends the actual restricted
singular class on a unit to the class of the preceding explicit winding cocycle. -/
lemma derivedHomAddEquivGlobalSections_restrictedSingularOneCocycle :
    let := derivedPushforwardComplementConstantRationalComplexInt_isKInjective X
      ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl
    TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective (TopCat.of (ComplexPoint X))
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)) 1
      (ShiftedHom.map
        (((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
          ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
          ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u))) ≫
          Cocycle.equivHomShift.symm (restrictedSingularOneCocycle X d Ω)) DerivedCategory.Q) =
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))).homologyπ 1
      (restrictedSingularOneGlobalCocycle X d Ω u) := by
  dsimp only
  let := derivedPushforwardComplementConstantRationalComplexInt_isKInjective X
      ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl
  have h := derivedHomAddEquivGlobalSectionsKInjective_cocycle X
    (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)) 1
    ((restrictedSingularOneCocycle X d Ω).precomp
      ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
        ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u))))
  rw [Cocycle.equivHomShift_symm_precomp] at h
  exact h

/-- The particular complement hypercohomology comparison used by the fixed support
boundary computes the same actual section cocycle. -/
lemma complementRationalHypercohomology_restrictedSingularOneCocycle :
    let z := (restrictedSingularOneCocycle X d Ω).precomp
      ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
        ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u)))
    complementRationalHypercohomologyAddEquivGlobalSections X ((Ω : Set (ComplexPoint X))ᶜ) 1
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        ((constantIntegerSheafComplexIntIsoSingle X).hom ≫ Cocycle.equivHomShift.symm z)) =
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))).homologyπ 1
      (restrictedSingularOneGlobalCocycle X d Ω u) := by
  dsimp only
  let B := derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)
  let : B.IsStrictlyGE 0 := by
    dsimp only [B, derivedPushforwardComplementConstantRationalComplexInt]
    infer_instance
  let : B.IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_of_ge B (-1) 0 (by omega)
  let := derivedPushforwardComplementConstantRationalComplexInt_isKInjective X
    ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl
  let z := (restrictedSingularOneCocycle X d Ω).precomp
      ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
        ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u)))
  exact (hypercohomologyAddEquivGlobalSections_eq_kInjective X B (-1)
    (derivedPushforwardComplementConstantRationalComplexInt_term_isFlasque X
      ((Ω : Set (ComplexPoint X))ᶜ)) 1 _).trans
        (hypercohomologyAddEquivGlobalSectionsKInjective_mk_cocycle X B 1 z)
end AlgebraicGeometry.ComplexPoint
