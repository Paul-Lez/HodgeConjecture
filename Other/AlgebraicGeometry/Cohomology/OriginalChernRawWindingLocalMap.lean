/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWinding
public import Other.AlgebraicTopology.SupportedSingularBoundaryRelative

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint
local instance localMapTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance localMapDerivedCategory (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω U : Opens (TopCat.of (ComplexPoint X)))

/-- Raw overlap cochains mapped to the fixed complement resolution. -/
def originalLocalRawToComplementResolution :
    (openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω)).extend
        ComplexShape.embeddingUpNat ⟶
      ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (.up ℤ)).obj
        (((TopCat.Sheaf.openRestrictionPushforward
          (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
          (derivedPushforwardComplementConstantRationalComplexInt X
            ((Ω : Set (ComplexPoint X))ᶜ))) := by
  let Y := TopCat.of (ComplexPoint X)
  let P := derivedPushforwardComplementConstantRationalComplexInt X
    ((Ω : Set (ComplexPoint X))ᶜ)
  exact
    openRawToSupportedSingularOutside Y Ω U ≫
      ((TopCat.Sheaf.supportEvaluation Y U).mapHomologicalComplex (.up ℤ)).map
        (naturalSingularOutsideResolutionComparisonOnOpen X Ω) ≫
      ((NatIso.mapHomologicalComplex
        (TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso Y U) (.up ℤ)).app P).inv

lemma originalLocalRawToComplementResolution_f_one
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let P := derivedPushforwardComplementConstantRationalComplexInt X
      ((Ω : Set (ComplexPoint X))ᶜ)
    let r := originalLocalRawToComplementResolution X Ω U
    let raw :=
      ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op U)
        ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω U
          ((singularCochainSheafComplexInt X ℚ).X 1)).inv
            (((singularCochainSheafTermIso X 1).inv.hom.app (op (U ⊓ Ω)))
              ((openRawToSingularCochainSheafComplex ℚ Y (U ⊓ Ω)).f 1
                (ChernWinding.rationalWindingCochain
                  (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
                  (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))).hom)))
    let rawU : ((TopCat.Sheaf.supportEvaluation Y U).obj (P.X 1)) := raw
    ((r.f 1).hom)
      (((openRawSingularCochainComplex ℚ Y (U ⊓ Ω)).extendXIso
        ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl).inv
        (ChernWinding.rationalWindingCochain
          (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
          (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))).hom) =
      (ConcreteCategory.hom
        (((NatIso.mapHomologicalComplex
          (TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso Y U) (.up ℤ)).app P).inv.f
          1)) rawU := by
  dsimp only
  change
    (((openRawToSupportedSingularOutside (TopCat.of (ComplexPoint X)) Ω U ≫
      ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex
        (.up ℤ)).map (naturalSingularOutsideResolutionComparisonOnOpen X Ω) ≫
      ((NatIso.mapHomologicalComplex
        (TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso
          (TopCat.of (ComplexPoint X)) U) (.up ℤ)).app
        (derivedPushforwardComplementConstantRationalComplexInt X
          ((Ω : Set (ComplexPoint X))ᶜ))).inv).f 1).hom) _ = _
  dsimp only [openRawToSupportedSingularOutside]
  simp only [HomologicalComplex.comp_f]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
    (i := 1) (i' := (1 : ℤ)) rfl]
  rw [HomologicalComplex.mapExtendCanonicalIso_inv_f _ _ _
    (i := 1) (j := (1 : ℤ)) rfl]
  simp only [Category.assoc]
  dsimp [TopCat.Sheaf.supportRestrictionSectionsIntersectionIso]
  congr 1
  congr 1
  congr 1
  congr 1
  rw [← AddCommGrpCat.comp_apply]
  have hobj :
      (openSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω)).X 1 =
        ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) (U ⊓ Ω)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
            (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))).X 1) := by
    rfl
  have hIso :
      (HomologicalComplex.extendXIso
        (openSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω))
        ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl) =
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) (U ⊓ Ω)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))).extendXIso
          ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl := by
    rfl
  have hcomp :
      (HomologicalComplex.extendXIso
        (openSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω))
        ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl).inv ≫
        ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) (U ⊓ Ω)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))).extendXIso
            ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl).hom =
        eqToHom hobj := by
    rw [← hIso]
    rw [Iso.inv_hom_id]
    rfl
  rw [hcomp]
  have hraw (x : (openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))
      (U ⊓ Ω)).X 1) :
      (ConcreteCategory.hom
        ((HomologicalComplex.extendXIso
          (openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω))
          ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl).hom))
        ((ConcreteCategory.hom
          ((HomologicalComplex.extendXIso
            (openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω))
            ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl).inv)) x) = x := by
    rw [← AddCommGrpCat.comp_apply]
    rw [Iso.inv_hom_id]
    rfl
  rw [hraw]
  rfl

end AlgebraicGeometry.ComplexPoint
