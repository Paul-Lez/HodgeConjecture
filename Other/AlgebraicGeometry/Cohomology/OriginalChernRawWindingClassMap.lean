/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingLocalMap
public import Other.AlgebraicGeometry.ChernWindingRawRepresentative
public import Other.AlgebraicGeometry.CocycleGlobalSections
public import Other.AlgebraicGeometry.Cohomology.HypercohomologyShift

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint
local instance classMapTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance classMapDerivedCategory (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω U : Opens (TopCat.of (ComplexPoint X)))

/-- Raw overlap cochains mapped to the original ambient cone. -/
def originalLocalRawToAmbientCone :
    (openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω)).extend
        ComplexShape.embeddingUpNat ⟶
      TopCat.Sheaf.globalSectionsComplexInt (TopCat.of U)
        (((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mappingCone (ambientRationalInjectiveRestriction X
            ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl))) := by
  let H := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let c := CochainComplex.mappingCone.inr
    (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))
  let m := rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
    Ω.isOpen.isClosed_compl
  exact originalLocalRawToComplementResolution X Ω U ≫
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of U)).mapHomologicalComplex (.up ℤ)).map ((H.mapHomologicalComplex (.up ℤ)).map (c ≫ m))

lemma originalLocalRawToAmbientCone_cyclesMap_raw_winding
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let YU := TopCat.of U
    let H := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let B := TopCat.Sheaf.globalSectionsComplexInt YU
      ((H.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone
        (ambientRationalInjectiveRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
          Ω.isOpen.isClosed_compl)))
    let r := originalLocalRawToAmbientCone X Ω U
    let z := ChernWinding.openRawRationalWindingCocycle Y (U ⊓ Ω)
      (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
    B.iCycles 1 (HomologicalComplex.cyclesMap r 1 z) =
      (r.f 1).hom
        (((openRawSingularCochainComplex ℚ Y (U ⊓ Ω)).extendXIso
          ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl).inv
          (ChernWinding.rationalWindingCochain
            (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
            (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))).hom) := by
  dsimp only
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (originalLocalRawToAmbientCone X Ω U) 1)
    (ChernWinding.openRawRationalWindingCocycle (TopCat.of (ComplexPoint X)) (U ⊓ Ω)
      (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w)))
  have hz := ChernWinding.iCycles_openRawRationalWindingCocycle
    (TopCat.of (ComplexPoint X)) (U ⊓ Ω)
      (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
  exact hn.trans (congrArg ((originalLocalRawToAmbientCone X Ω U).f 1).hom hz)

lemma originalLocalRawToAmbientCone_cyclesMap_raw_winding_explicit
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let YU := TopCat.of U
    let H := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let P := derivedPushforwardComplementConstantRationalComplexInt X
      ((Ω : Set (ComplexPoint X))ᶜ)
    let c := CochainComplex.mappingCone.inr
      (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))
    let m := rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
      Ω.isOpen.isClosed_compl
    let Γ := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor YU)
      |>.mapHomologicalComplex (.up ℤ)
    let B := TopCat.Sheaf.globalSectionsComplexInt YU
      ((H.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone
        (ambientRationalInjectiveRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
          Ω.isOpen.isClosed_compl)))
    let e := (NatIso.mapHomologicalComplex
      (TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso Y U) (.up ℤ)).app P
    let r := originalLocalRawToAmbientCone X Ω U
    let z := ChernWinding.openRawRationalWindingCocycle Y (U ⊓ Ω)
      (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
    let raw :=
      ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op U)
        ((TopCat.Sheaf.supportedOutsideIntersectionIso Y Ω U
          ((singularCochainSheafComplexInt X ℚ).X 1)).inv
            (((singularCochainSheafTermIso X 1).inv.hom.app (op (U ⊓ Ω)))
              ((openRawToSingularCochainSheafComplex ℚ Y (U ⊓ Ω)).f 1
                (ChernWinding.rationalWindingCochain
                  (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
                  (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))).hom)))
    B.iCycles 1 (HomologicalComplex.cyclesMap r 1 z) =
      ((Γ.map ((H.mapHomologicalComplex (.up ℤ)).map (c ≫ m))).f 1).hom
        ((e.inv.f 1).hom
          raw) := by
  dsimp only
  have hcycles := originalLocalRawToAmbientCone_cyclesMap_raw_winding X d Ω U w
  have hf := originalLocalRawToComplementResolution_f_one X d Ω U w
  dsimp only at hcycles hf
  dsimp only [originalLocalRawToAmbientCone] at hcycles
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hcycles
  let Y := TopCat.of (ComplexPoint X)
  let P := derivedPushforwardComplementConstantRationalComplexInt X
    ((Ω : Set (ComplexPoint X))ᶜ)
  let K := ((TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex (.up ℤ)).obj
    (((TopCat.Sheaf.openRestrictionPushforward Y U).mapHomologicalComplex (.up ℤ)).obj P)
  let T := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of U)).mapHomologicalComplex (.up ℤ)
  let S := ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
    (.up ℤ)).map ((CochainComplex.mappingCone.inr
      (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))) ≫
      rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl)
  have hh := congrArg (fun a : K.X 1 => (T.map S).f 1 |>.hom a) hf
  exact hcycles.trans hh

/-- The shifted Chern boundary is the raw winding cycle of the negative frame difference. -/
lemma originalLocalBoundaryMap_shift_cyclesMap_raw_winding
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let YU := TopCat.of U
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X
      ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl)
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    let B := H.obj C
    let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
    let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat YU) 0
    let q := J.map (TopCat.Sheaf.constantToOpenSheafRestriction Y U
      (AddCommGrpCat.of ℤ)) ≫
      I.inv.app ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℤ))
    let c := q ≫ originalLocalBoundaryMap X d Ω U w ≫
      ((H.commShiftIso (1 : ℤ)).hom.app C)
    let zChern := TopCat.Sheaf.integerCocycleGlobalSection YU (B⟦(1 : ℤ)⟧) 0
      (CochainComplex.HomComplex.Cocycle.ofHom c)
    let s := TopCat.Sheaf.globalSectionsShiftShortComplex YU B 1 0 1 (by omega)
    let zraw := ChernWinding.openRawRationalWindingCocycle Y (U ⊓ Ω)
      (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
    let r := originalLocalRawToAmbientCone X Ω U
    ShortComplex.cyclesMap s zChern =
      HomologicalComplex.cyclesMap r 1 zraw := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let YU := TopCat.of U
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X
    ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl)
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let H := F.mapHomologicalComplex (.up ℤ)
  let B := H.obj C
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat YU) 0
  let q := J.map (TopCat.Sheaf.constantToOpenSheafRestriction Y U
    (AddCommGrpCat.of ℤ)) ≫
    I.inv.app ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℤ))
  let c := q ≫ originalLocalBoundaryMap X d Ω U w ≫
    ((H.commShiftIso (1 : ℤ)).hom.app C)
  let zChern := TopCat.Sheaf.integerCocycleGlobalSection YU (B⟦(1 : ℤ)⟧) 0
    (CochainComplex.HomComplex.Cocycle.ofHom c)
  let s := TopCat.Sheaf.globalSectionsShiftShortComplex YU B 1 0 1 (by omega)
  let zraw := ChernWinding.openRawRationalWindingCocycle Y (U ⊓ Ω)
    (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
    (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
  let r := originalLocalRawToAmbientCone X Ω U
  apply (AddCommGrpCat.mono_iff_injective
    ((TopCat.Sheaf.globalSectionsComplexInt YU B).iCycles 1)).mp inferInstance
  have hleft := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i s) zChern
  have hz := TopCat.Sheaf.iCycles_integerCocycleGlobalSection YU (B⟦(1 : ℤ)⟧) 0
    (CochainComplex.HomComplex.Cocycle.ofHom c)
  have hl : (TopCat.Sheaf.globalSectionsComplexInt YU B).iCycles 1
      (ShortComplex.cyclesMap s zChern) =
      (((q ≫ originalLocalBoundaryMap X d Ω U w).f 0).hom.app (op ⊤))
        (TopCat.Sheaf.integerOne (Y := YU)) := by
    refine hleft.trans ((congrArg (fun a => s.τ₂ a) hz).trans ?_)
    rfl
  have hc := originalLocalBoundaryMap_integerOne_raw_winding X d Ω U w
  have hr := originalLocalRawToAmbientCone_cyclesMap_raw_winding_explicit X d Ω U w
  dsimp only at hc hr
  exact hl.trans (hc.trans hr.symm)

end AlgebraicGeometry.ComplexPoint
