/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingRawRepresentative
public import Other.AlgebraicGeometry.HolomorphicExponentialSingularSectionClass

/-!
# The actual restricted exponential singular class is the raw winding class

The literal raw winding cycle maps to the actual restricted singular cycle through
sheafification, the prescribed grading comparison, top-open evaluation and the
fixed complement resolution. Consequently the existing complement hypercohomology
comparison sends the actual class to the image of the existing raw winding class.
The support/chart comparison is still separate; no divisor identity is assumed.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
  (Ω : Opens (TopCat.of (ComplexPoint X)))
/-- Literal raw cochains on the specified open mapped to the fixed complement
resolution, retaining the actual sheafification, grading and top-open maps. -/
def openRawToComplementResolutionOnOpen :
    (openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X)) Ω).extend
        ComplexShape.embeddingUpNat ⟶
    TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)) :=
  HomologicalComplex.extendMap
      (openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) Ω)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) Ω)
      (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat).inv ≫
    ((NatIso.mapHomologicalComplex (openRestrictionTopEval Ω) (.up ℤ)).app
      (singularCochainSheafComplexInt X ℚ)).inv ≫
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex (.up ℤ)).map
      (naturalSingularOutsideResolutionComparisonOnOpen X Ω))

lemma openRawToComplementResolutionOnOpen_f (n : ℕ) :
    ((openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X)) Ω).extendXIso
      ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl).inv ≫
      (openRawToComplementResolutionOnOpen X Ω).f (n : ℤ) =
    (openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) Ω).f n ≫
      (singularCochainSheafTermIso X n).inv.hom.app (op Ω) ≫
      (openRestrictionTopEval Ω).inv.app ((singularCochainSheafComplexInt X ℚ).X (n : ℤ)) ≫
      ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f (n : ℤ)).hom.app (op ⊤) := by
  dsimp only [openRawToComplementResolutionOnOpen]
  simp only [HomologicalComplex.comp_f]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl]
  rw [HomologicalComplex.mapExtendCanonicalIso_inv_f _ _ _ (i := n) (j := (n : ℤ)) rfl]
  dsimp only [openSingularCochainSheafComplex]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl
variable (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (u : (holomorphicUnitSheaf X d).obj.obj (op Ω))

/-- The normalized raw winding cycle maps to the actual restricted exponential
singular cycle, through the specified sheafification and resolution maps. -/
lemma cyclesMap_openRawToComplementResolutionOnOpen_winding :
    HomologicalComplex.cyclesMap (openRawToComplementResolutionOnOpen X Ω) 1
      (ChernWinding.openRawRationalWindingCocycle (TopCat.of (ComplexPoint X)) Ω
        (holomorphicUnitFunction X d Ω u) (holomorphicUnitFunction_ne_zero X d Ω u)) =
    restrictedSingularOneGlobalCocycle X d Ω u := by
  let K := TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
    (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))
  let z := ChernWinding.openRawRationalWindingCocycle (TopCat.of (ComplexPoint X)) Ω
    (holomorphicUnitFunction X d Ω u) (holomorphicUnitFunction_ne_zero X d Ω u)
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).mp inferInstance
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (openRawToComplementResolutionOnOpen X Ω) 1) z
  have hz := ChernWinding.iCycles_openRawRationalWindingCocycle
    (TopCat.of (ComplexPoint X)) Ω (holomorphicUnitFunction X d Ω u)
    (holomorphicUnitFunction_ne_zero X d Ω u)
  have hf := ConcreteCategory.congr_hom
    (openRawToComplementResolutionOnOpen_f X Ω 1)
    (ChernWinding.rationalWindingCochain (holomorphicUnitFunction X d Ω u)
      (holomorphicUnitFunction_ne_zero X d Ω u)).hom
  exact (hn.trans ((congrArg ((openRawToComplementResolutionOnOpen X Ω).f 1) hz).trans hf)).trans
    (iCycles_restrictedSingularOneGlobalCocycle X d Ω u).symm

/-- The existing raw winding cohomology class maps to the class of the actual
restricted exponential singular cocycle. -/
lemma homologyMap_openRawToComplementResolutionOnOpen_winding :
    HomologicalComplex.homologyMap (openRawToComplementResolutionOnOpen X Ω) 1
      (ChernWinding.openRawRationalWindingClass (TopCat.of (ComplexPoint X)) Ω
        (holomorphicUnitFunction X d Ω u) (holomorphicUnitFunction_ne_zero X d Ω u)) =
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))).homologyπ 1
        (restrictedSingularOneGlobalCocycle X d Ω u) := by
  rw [← ChernWinding.homologyπ_openRawRationalWindingCocycle]
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (openRawToComplementResolutionOnOpen X Ω) 1)
    (ChernWinding.openRawRationalWindingCocycle (TopCat.of (ComplexPoint X)) Ω
      (holomorphicUnitFunction X d Ω u) (holomorphicUnitFunction_ne_zero X d Ω u))).trans
    (congrArg ((TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))).homologyπ 1)
      (cyclesMap_openRawToComplementResolutionOnOpen_winding X Ω d u))

/-- The prescribed complement hypercohomology comparison identifies the actual
restricted exponential singular class with the image of the existing normalized
raw winding class. -/
lemma complementRationalHypercohomology_restrictedSingularOneCocycle_eq_rawWinding :
    let z := (restrictedSingularOneCocycle X d Ω).precomp
      ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
        ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u)))
    complementRationalHypercohomologyAddEquivGlobalSections X ((Ω : Set (ComplexPoint X))ᶜ) 1
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
          CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)) =
    HomologicalComplex.homologyMap (openRawToComplementResolutionOnOpen X Ω) 1
      (ChernWinding.openRawRationalWindingClass (TopCat.of (ComplexPoint X)) Ω
        (holomorphicUnitFunction X d Ω u) (holomorphicUnitFunction_ne_zero X d Ω u)) :=
  (complementRationalHypercohomology_restrictedSingularOneCocycle X d Ω u).trans
    (homologyMap_openRawToComplementResolutionOnOpen_winding X Ω d u).symm
end AlgebraicGeometry.ComplexPoint
