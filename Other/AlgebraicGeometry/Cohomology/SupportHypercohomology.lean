/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportHypercohomology
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportHypercohomology
public import Other.AlgebraicGeometry.Cohomology.GlobalSections
public import Other.AlgebraicGeometry.Cohomology.SupportSingularGlobal

/-!
# SupportHypercohomology, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportHypercohomology`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra
namespace AlgebraicGeometry.ComplexPoint
open Point
universe u v
variable (X : Over (Spec ↧ℂ))
attribute [local instance] bettiSupportHypercohomologyComparisonHasDerivedCategory
attribute [local instance] bettiSupportHypercohomologyAddCommGrpHasDerivedCategory
section
open AlgebraicTopology.Singular

/-- The natural singular support cone is concentrated in degrees at least `-1`. -/
lemma naturalSingularSupportCone_isStrictlyGE
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    (CochainComplex.mappingCone
      (naturalSingularResolutionRestriction X Z hZ)).IsStrictlyGE (-1) := by
  exact CochainComplex.isStrictlyGE_mappingCone
    (naturalSingularResolutionRestriction X Z hZ) 0 0 (-1)
      (by lia) (by lia)

/-- Every term of the derived complement resolution is flasque. In nonnegative degrees it is
the pushforward of an injective sheaf; in negative degrees it is zero. -/
theorem derivedPushforwardComplementConstantRationalComplexInt_term_isFlasque
    (Z : Set (ComplexPoint X)) (q : ℤ) :
    (derivedPushforwardComplementConstantRationalComplexInt X Z).X q |>.IsFlasque := by
  by_cases hq : ∃ m : ℕ, (m : ℤ) = q
  · obtain ⟨m, rfl⟩ := hq
    let K := derivedPushforwardComplementConstantRationalComplexNat X Z
    let e := K.extendXIso ComplexShape.embeddingUpNat (i := m) rfl
    let hP : TopCat.Presheaf.IsFlasque (K.X m).obj := by
      let F :=
        (complementConstantRationalInjectiveResolution X Z).cocomplex.X m
      let : Injective F := by
        dsimp [F]
        infer_instance
      let : TopCat.Sheaf.IsFlasque F :=
        TopCat.Sheaf.injective_isFlasque _ F
      exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque F
        (analyticComplementInclusion X Z)
    change TopCat.Presheaf.IsFlasque ((K.extend
      ComplexShape.embeddingUpNat).X (m : ℤ)).obj
    exact @TopCat.Presheaf.IsFlasque.of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapIso e) hP
  · apply TopCat.Sheaf.IsFlasque.of_isZero
    exact (derivedPushforwardComplementConstantRationalComplexNat X Z).isZero_extend_X
      ComplexShape.embeddingUpNat q (fun i hi ↦ hq ⟨i, hi⟩)

/-- Every term of the natural singular support cone is flasque on a hereditarily paracompact
Hausdorff analytic space. -/
theorem naturalSingularSupportCone_term_isFlasque
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (q : ℤ) :
    ((CochainComplex.mappingCone
      (naturalSingularResolutionRestriction X Z hZ)).X q).IsFlasque := by
  apply TopCat.Sheaf.IsFlasque.BoundedBelowComplex.mappingCone_term_isFlasque
    (naturalSingularResolutionRestriction X Z hZ)
  · exact singularCochainSheafComplexInt_isFlasque X
  · exact derivedPushforwardComplementConstantRationalComplexInt_term_isFlasque X Z

end
end AlgebraicGeometry.ComplexPoint
end

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra
namespace AlgebraicGeometry.ComplexPoint
open Point
universe u v
variable (X : Over (Spec ↧ℂ))
attribute [local instance] bettiSupportHypercohomologyComparisonHasDerivedCategory
attribute [local instance] bettiSupportHypercohomologyAddCommGrpHasDerivedCategory
open AlgebraicTopology.Singular

/-- Hypercohomology/global-sections comparison through a fixed termwise-injective resolution. -/
def hypercohomologyAddEquivGlobalSectionsOfResolution
    (K I : CochainComplex.Plus (AnalyticAdditiveSheaf X))
    [∀ q, Injective (I.obj.X q)]
    (i : K ⟶ I) [QuasiIso i.hom]
    [QuasiIso (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i.hom)]
    (n : ℤ) :
    ↥((analyticHypercohomologyFunctor X n).obj K) ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X)) K.obj).homology n :=
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let F := analyticHypercohomologyFunctor X n
  letI : IsIso (DerivedCategory.Plus.Q.map i) := inferInstance
  letI : IsIso (F.map i) := by
    dsimp only [F, analyticHypercohomologyFunctor, Functor.comp_map]
    infer_instance
  let e₀ := (asIso (F.map i)).addCommGroupIsoToAddEquiv
  let e₁ := (TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat Y I n
    ).addCommGroupIsoToAddEquiv
  let e₂ := (asIso (HomologicalComplex.homologyMap
    ((Γ.mapHomologicalComplex (.up ℤ)).map i.hom) n)).symm.addCommGroupIsoToAddEquiv
  e₀.trans <| e₁.trans e₂

/-- Additive hypercohomology/global-sections comparison for a bounded-below termwise-flasque
complex. -/
def hypercohomologyAddEquivGlobalSections
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (N : ℤ) [K.IsStrictlyGE N]
    (hKflasque : ∀ q, (K.X q).IsFlasque) (n : ℤ) :
    ↥((analyticHypercohomologyFunctor X n).obj
      (⟨K, ⟨N, inferInstance⟩⟩ : CochainComplex.Plus (AnalyticAdditiveSheaf X))) ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X)) K).homology n :=
  let Y := TopCat.of (ComplexPoint X)
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N
  let I := hres.choose
  let i := hres.choose_spec.choose
  haveI : QuasiIso i := hres.choose_spec.choose_spec.choose
  haveI : ∀ q, Injective (I.X q) := hres.choose_spec.choose_spec.choose_spec.choose
  haveI : I.IsStrictlyGE N := hres.choose_spec.choose_spec.choose_spec.choose_spec
  haveI : I.IsKInjective := CochainComplex.isKInjective_of_injective I N
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  haveI : QuasiIso
      (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i N N hKflasque hIflasque
  let K' : CochainComplex.Plus (AnalyticAdditiveSheaf X) := ⟨K, ⟨N, inferInstance⟩⟩
  let I' : CochainComplex.Plus (AnalyticAdditiveSheaf X) := ⟨I, ⟨N, inferInstance⟩⟩
  let i' : K' ⟶ I' := ⟨i⟩
  hypercohomologyAddEquivGlobalSectionsOfResolution X K' I' i' n

/-- Global sections of a mapping cone are canonically isomorphic to the mapping cone of the
global-sections map. -/
def globalSectionsNaturalSingularConeIsoMappingCone
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X))
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction X Z hZ)) ≅
      CochainComplex.mappingCone
        (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (naturalSingularResolutionRestriction X Z hZ)) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso
    (naturalSingularResolutionRestriction X Z hZ)
    (TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X)))

/-- Replacing rational constants by the natural singular resolution identifies the two support
hypercohomology groups, additively. -/
def rationalSupportHypercohomologyAddEquivNaturalSingularCone
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃+
      ↥((analyticHypercohomologyFunctor X n).obj
        (⟨(shiftFunctor _ (-1 : ℤ)).obj (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction X Z hZ)),
          ⟨0, by
            let _ := naturalSingularSupportCone_isStrictlyGE X Z hZ
            exact CochainComplex.isStrictlyGE_shift _ (-1) (-1) 0 (by norm_num)⟩⟩ :
            CochainComplex.Plus (AnalyticAdditiveSheaf X))) :=
  let L : CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
    ⟨(shiftFunctor _ (-1 : ℤ)).obj (CochainComplex.mappingCone
      (naturalSingularResolutionRestriction X Z hZ)),
      ⟨0, by
        let _ := naturalSingularSupportCone_isStrictlyGE X Z hZ
        exact CochainComplex.isStrictlyGE_shift _ (-1) (-1) 0 (by norm_num)⟩⟩
  let f : rationalCohomologyWithSupportComplexPlus X Z ⟶ L :=
    ⟨(shiftFunctor _ (-1 : ℤ)).map
      (rationalSupportConeToNaturalSingularCone X Z hZ)⟩
  letI : QuasiIso f.hom := (CochainComplex.quasiIso_shift_iff
    (rationalSupportConeToNaturalSingularCone X Z hZ) (-1)).2 inferInstance
  letI : IsIso (DerivedCategory.Plus.Q.map f) := inferInstance
  let F := analyticHypercohomologyFunctor X n
  letI : IsIso (F.map f) := by
    dsimp only [F, analyticHypercohomologyFunctor, Functor.comp_map]
    infer_instance
  (asIso (F.map f)).addCommGroupIsoToAddEquiv

/-- Additive form of the computation of rational constant-sheaf cohomology with support by
global sections of the natural singular support cone. -/
def rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X))
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction X Z hZ))).homology (n - 1) :=
  let K := CochainComplex.mappingCone
    (naturalSingularResolutionRestriction X Z hZ)
  letI : K.IsStrictlyGE (-1) :=
    naturalSingularSupportCone_isStrictlyGE X Z hZ
  let L := (shiftFunctor _ (-1 : ℤ)).obj K
  letI : L.IsStrictlyGE 0 :=
    CochainComplex.isStrictlyGE_shift _ (-1) (-1) 0 (by norm_num)
  have hLflasque : ∀ q, (L.X q).IsFlasque := by
    intro q
    let e := K.shiftFunctorObjXIso (-1) q (q - 1) (by omega)
    exact @TopCat.Presheaf.IsFlasque.of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoint X))).mapIso e.symm)
      (naturalSingularSupportCone_term_isFlasque X Z hZ (q - 1))
  let e₀ := rationalSupportHypercohomologyAddEquivNaturalSingularCone X Z hZ n
  let e₁ := hypercohomologyAddEquivGlobalSections X L 0 hLflasque n
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat (TopCat.of (ComplexPoint X))
  let G := (Γ.mapHomologicalComplex (.up ℤ)).obj K
  let e₂ : ((Γ.mapHomologicalComplex (.up ℤ)).obj L).homology n ≅
      ((shiftFunctor _ (-1 : ℤ)).obj G).homology n :=
    HomologicalComplex.homologyMapIso
      (((Γ.mapHomologicalComplex (.up ℤ)).commShiftIso (-1)).app K) n
  let e₃ : ((shiftFunctor _ (-1 : ℤ)).obj G).homology n ≅ G.homology (n - 1) :=
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
      (-1) n (n - 1) (by omega)).app G
  e₀.trans <| e₁.trans <| (e₂ ≪≫ e₃).addCommGroupIsoToAddEquiv

/-- Additive singular comparison for rational cohomology with closed support. -/
def rationalCohomologyWithSupportAddEquivSingular
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℕ) :
    RationalCohomologyWithSupport X Z (n : ℤ) ≃+
      CohomologyWithSupport ℚ
        (TopCat.of (ComplexPoint X)) Z n :=
  (rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections
      X Z hZ (n : ℤ)).trans <|
    ((HomologicalComplex.homologyMapIso
      (globalSectionsNaturalSingularConeIsoMappingCone
        X Z hZ) ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv).trans <|
    ((asIso (HomologicalComplex.homologyMap
      (globalRawSupportConeToGlobalNaturalSingularCone
        X Z hZ) ((n : ℤ) - 1))).symm.addCommGroupIsoToAddEquiv).trans <|
    globalRawSingularRestrictionConeCohomologyEquivSupport ℚ
      (TopCat.of (ComplexPoint X)) Z n

end AlgebraicGeometry.ComplexPoint
end
