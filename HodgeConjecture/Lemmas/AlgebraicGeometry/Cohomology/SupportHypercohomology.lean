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

/-!
# Constructions used only in proofs

These were built to prove the results about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportHypercohomology`.
The statement of the conjecture never inspects them: every path from the statement to one
of them runs through a proof, so proof irrelevance makes their bodies immaterial.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra

namespace AlgebraicGeometry.ComplexPoint

open Point

universe u v

variable (X : Over (Spec ↧ℂ))

attribute [local instance] bettiSupportHypercohomologyComparisonHasDerivedCategory

attribute [local instance] bettiSupportHypercohomologyAddCommGrpHasDerivedCategory

/-- Additive form of the hypercohomology/global-sections comparison for a fixed K-injective
resolution. -/
def hypercohomologyAddEquivGlobalSectionsOfResolution
    (K I : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective]
    (i : K ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    Hypercohomology X K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) K).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let A := constantIntegerSheafComplexInt X
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e : A ≅ A' := constantIntegerSheafComplexIntIsoSingle X
  let e₀ := hypercohomologyAddEquivDerived X K n
  let eI : (DerivedCategory.Q.obj K)⟦n⟧ ≅
      (DerivedCategory.Q.obj I)⟦n⟧ :=
    (shiftFunctor (DerivedCategory (AnalyticAdditiveSheaf X)) n).mapIso
      (asIso (DerivedCategory.Q.map i))
  let e₁ : ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj K) n ≃+
      ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) n :=
    isoHomCongrAddEquiv (Iso.refl _) eI
  let e₂ : ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) n ≃+
      ShiftedHom (DerivedCategory.Q.obj A') (DerivedCategory.Q.obj I) n :=
    isoHomCongrAddEquiv (DerivedCategory.Q.mapIso e) (Iso.refl _)
  let e₃ := kInjectiveDerivedHomAddEquivCohomologyClass A' I n
  let e₄ := (CochainComplex.HomComplex.homologyAddEquiv A' I n).symm
  let e₅ := (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y I) n)
      |>.addCommGroupIsoToAddEquiv
  let : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) := inferInstance
  let e₆ := (asIso (HomologicalComplex.homologyMap
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) n)).symm
      |>.addCommGroupIsoToAddEquiv
  exact e₀.trans <| e₁.trans <| e₂.trans <| e₃.trans <| e₄.trans <| e₅.trans e₆

/-- Additive hypercohomology/global-sections comparison for a bounded-below termwise-flasque
complex. -/
def hypercohomologyAddEquivGlobalSections
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (N : ℤ) [K.IsStrictlyGE N]
    (hKflasque : ∀ q, (K.X q).IsFlasque) (n : ℤ) :
    Hypercohomology X K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) K).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  choose I i _ _ _ using
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N
  letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I N
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i N N hKflasque hIflasque
  exact hypercohomologyAddEquivGlobalSectionsOfResolution
    X K I i n

open AlgebraicTopology.Singular

/-- Global sections of the pushed-forward comparison from singular cochains on the complement
to its chosen injective resolution. -/
def globalComplementSingularToInjectiveResolutionNat
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    globalPushforwardSingularCochainSheafComplex ℚ
        (analyticComplementInclusion X Z) ⟶
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (derivedPushforwardComplementConstantRationalComplexNat X Z) :=
  ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticComplementInclusion X Z)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
      (complementSingularToInjectiveResolution X Z hZ))

/-- Raw singular cochains on the complement map to global sections of the chosen derived
pushforward through sheafification and the injective-resolution comparison. -/
def globalRawComplementToDerivedPushforwardNat
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    globalRawPushforwardSingularCochainComplex ℚ
        (analyticComplementInclusion X Z) ⟶
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (derivedPushforwardComplementConstantRationalComplexNat X Z) :=
  globalRawPushforwardToSingularSheaf ℚ
      (analyticComplementInclusion X Z) ≫
    globalComplementSingularToInjectiveResolutionNat X Z hZ

/-- On a hereditarily paracompact Hausdorff ambient space, global sections of the complement
singular-to-injective comparison are a quasi-isomorphism. -/
theorem globalComplementSingularToInjectiveResolutionNat_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [hpara : ∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (globalComplementSingularToInjectiveResolutionNat
      X Z hZ) := by
  let U := TopCat.of ↥Zᶜ
  let j := analyticComplementInclusion X Z
  let : T2Space U := inferInstance
  let : ∀ W : Opens U, ParacompactSpace W := fun W ↦
    opens_paracompactSpace_of_isOpenEmbedding j
      (analyticComplementInclusion_isOpenEmbedding X Z hZ) hpara W
  change QuasiIso
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor U
      ).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (complementSingularToInjectiveResolution X Z hZ))
  let : QuasiIso
      (complementSingularToInjectiveResolution X Z hZ) :=
    complementSingularToInjectiveResolution_quasiIso X Z hZ
  apply globalSectionsNat_map_quasiIso
  · intro m
    change TopCat.Sheaf.IsFlasque
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ U m)
    infer_instance
  · exact fun _ ↦ inferInstance

/-- Raw complement cochains map quasi-isomorphically to global sections of the chosen derived
pushforward model. -/
theorem globalRawComplementToDerivedPushforwardNat_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (globalRawComplementToDerivedPushforwardNat
      X Z hZ) := by
  let : QuasiIso (globalRawPushforwardToSingularSheaf ℚ
      (analyticComplementInclusion X Z)) :=
    globalRawComplementToSingularSheaf_quasiIso X Z hZ
  let : QuasiIso (globalComplementSingularToInjectiveResolutionNat
      X Z hZ) :=
    globalComplementSingularToInjectiveResolutionNat_quasiIso
      X Z hZ
  unfold globalRawComplementToDerivedPushforwardNat
  infer_instance

/-- Restriction on global sections of the natural singular-resolution map. -/
def globalNaturalSingularResolutionRestrictionNat
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    globalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X)) ⟶
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (derivedPushforwardComplementConstantRationalComplexNat X Z) :=
  ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (naturalSingularResolutionRestrictionNat X Z hZ)

set_option backward.isDefEq.respectTransparency false in
/-- The natural singular-resolution restriction square commutes after taking global sections. -/
lemma globalNaturalSingularResolutionRestrictionNat_naturality
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    topOpenToGlobalSingularCochainSheafComplex ℚ
          (TopCat.of (ComplexPoint X)) ≫
        globalNaturalSingularResolutionRestrictionNat X Z hZ =
      globalRawSingularRestriction ℚ
          (analyticComplementInclusion X Z) ≫
        globalRawComplementToDerivedPushforwardNat X Z hZ := by
  unfold globalNaturalSingularResolutionRestrictionNat
    naturalSingularResolutionRestrictionNat
    globalRawComplementToDerivedPushforwardNat
    globalComplementSingularToInjectiveResolutionNat
  rw [Functor.map_comp]
  change topOpenToGlobalSingularCochainSheafComplex ℚ _ ≫
        globalSingularSheafRestriction ℚ
          (analyticComplementInclusion X Z) ≫ _ = _
  rw [← Category.assoc, globalSingularSheafRestriction_naturality]
  rw [Category.assoc]

/-- Raw ambient cochains map to global sections of the integer-indexed singular-cochain sheaf
complex. -/
def globalRawToSingularSheafInt :
    globalRawSingularCochainComplexInt ℚ
        (TopCat.of (ComplexPoint X)) ⟶
      TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ) :=
  HomologicalComplex.extendMap
      (topOpenToGlobalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X)))
      (singularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat).inv

/-- Raw complement cochains map to global sections of the integer-indexed derived-pushforward
model. -/
def globalRawComplementToDerivedPushforwardInt
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    globalRawPushforwardSingularCochainComplexInt ℚ
        (TopCat.of (ComplexPoint X))
        Zᶜ ⟶
      TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (derivedPushforwardComplementConstantRationalComplexInt X Z) :=
  HomologicalComplex.extendMap
      (globalRawComplementToDerivedPushforwardNat X Z hZ)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X)))
      (derivedPushforwardComplementConstantRationalComplexNat X Z)
      ComplexShape.embeddingUpNat).inv

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The integer-indexed raw ambient-to-sheaf comparison is a quasi-isomorphism. -/
theorem globalRawToSingularSheafInt_quasiIso
    [T2Space (ComplexPoint X)]
    [hpara : ∀ U : Opens (ComplexPoint X), ParacompactSpace U] :
    QuasiIso (globalRawToSingularSheafInt X) := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let f := topOpenToGlobalSingularCochainSheafComplex ℚ Y
  let fInt := HomologicalComplex.extendMap f ComplexShape.embeddingUpNat
  let e := HomologicalComplex.mapExtendCanonicalIso Γ
    (singularCochainSheafComplex ℚ Y) ComplexShape.embeddingUpNat
  let : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (hpara (⊤ : Opens (ComplexPoint X)))
  let : QuasiIso f :=
    topOpenToGlobalSingularCochainSheafComplex_quasiIso
  let hfInt : QuasiIso fInt :=
    (HomologicalComplex.quasiIso_extendMap_iff f ComplexShape.embeddingUpNat).mpr
      inferInstance
  let he : QuasiIso e.inv := inferInstance
  change QuasiIso (fInt ≫ e.inv)
  refine ⟨fun i ↦ ?_⟩
  letI : QuasiIsoAt fInt i := hfInt.quasiIsoAt i
  letI : QuasiIsoAt e.inv i := he.quasiIsoAt i
  exact quasiIsoAt_comp fInt e.inv i

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The integer-indexed raw complement-to-derived-pushforward comparison is a
quasi-isomorphism. -/
theorem globalRawComplementToDerivedPushforwardInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (globalRawComplementToDerivedPushforwardInt
      X Z hZ) := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let f := globalRawComplementToDerivedPushforwardNat X Z hZ
  let fInt := HomologicalComplex.extendMap f ComplexShape.embeddingUpNat
  let e := HomologicalComplex.mapExtendCanonicalIso Γ
    (derivedPushforwardComplementConstantRationalComplexNat X Z)
      ComplexShape.embeddingUpNat
  let : QuasiIso f :=
    globalRawComplementToDerivedPushforwardNat_quasiIso
      X Z hZ
  let hfInt : QuasiIso fInt :=
    (HomologicalComplex.quasiIso_extendMap_iff f ComplexShape.embeddingUpNat).mpr
      inferInstance
  let he : QuasiIso e.inv := inferInstance
  change QuasiIso (fInt ≫ e.inv)
  refine ⟨fun i ↦ ?_⟩
  letI : QuasiIsoAt fInt i := hfInt.quasiIsoAt i
  letI : QuasiIsoAt e.inv i := he.quasiIsoAt i
  exact quasiIsoAt_comp fInt e.inv i

set_option backward.isDefEq.respectTransparency false in
/-- The raw and sheaf-level restriction maps commute after extension to integer degrees. -/
lemma globalNaturalSingularResolutionRestrictionInt_naturality
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    globalRawToSingularSheafInt X ≫
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (naturalSingularResolutionRestriction X Z hZ) =
      globalRawSingularRestrictionInt ℚ
          (TopCat.of (ComplexPoint X))
          Zᶜ ≫
        globalRawComplementToDerivedPushforwardInt X Z hZ := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let S := singularCochainSheafComplex ℚ Y
  let D := derivedPushforwardComplementConstantRationalComplexNat X Z
  let g := naturalSingularResolutionRestrictionNat X Z hZ
  let a := topOpenToGlobalSingularCochainSheafComplex ℚ Y
  let f := globalRawSingularRestriction ℚ
    (analyticComplementInclusion X Z)
  let b := globalRawComplementToDerivedPushforwardNat X Z hZ
  let eS := HomologicalComplex.mapExtendCanonicalIso Γ S ComplexShape.embeddingUpNat
  let eD := HomologicalComplex.mapExtendCanonicalIso Γ D ComplexShape.embeddingUpNat
  have hg : HomologicalComplex.extendMap
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map g)
          ComplexShape.embeddingUpNat ≫ eD.inv =
      eS.inv ≫ (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) :=
    HomologicalComplex.mapExtendCanonicalIso_inv_naturality Γ g ComplexShape.embeddingUpNat
  have hab : a ≫
        (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map g = f ≫ b :=
    globalNaturalSingularResolutionRestrictionNat_naturality
      X Z hZ
  change (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat ≫ eS.inv) ≫
      (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) =
    HomologicalComplex.extendMap f ComplexShape.embeddingUpNat ≫
      (HomologicalComplex.extendMap b ComplexShape.embeddingUpNat ≫ eD.inv)
  rw [Category.assoc, ← hg, ← Category.assoc,
    ← HomologicalComplex.extendMap_comp, hab,
    HomologicalComplex.extendMap_comp, Category.assoc]

/-- The commuting integer-indexed restriction square induces a map from the raw support cone to
the cone of restriction on global sections. -/
def globalRawSupportConeToGlobalNaturalSingularCone
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    CochainComplex.mappingCone
        (globalRawSingularRestrictionInt ℚ
          (TopCat.of (ComplexPoint X))
          Zᶜ) ⟶
      CochainComplex.mappingCone
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (naturalSingularResolutionRestriction X Z hZ)) :=
  CochainComplex.mappingCone.map
    (globalRawSingularRestrictionInt ℚ
      (TopCat.of (ComplexPoint X))
      Zᶜ)
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
      (naturalSingularResolutionRestriction X Z hZ))
    (globalRawToSingularSheafInt X)
    (globalRawComplementToDerivedPushforwardInt X Z hZ)
    (globalNaturalSingularResolutionRestrictionInt_naturality
      X Z hZ).symm

set_option backward.isDefEq.respectTransparency false in
/-- The raw-to-global-sections map of support cones is a quasi-isomorphism. -/
noncomputable instance globalRawSupportConeToGlobalNaturalSingularCone_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (globalRawSupportConeToGlobalNaturalSingularCone
      X Z hZ) := by
  let : QuasiIso (globalRawToSingularSheafInt X) :=
    globalRawToSingularSheafInt_quasiIso X
  let : QuasiIso (globalRawComplementToDerivedPushforwardInt
      X Z hZ) :=
    globalRawComplementToDerivedPushforwardInt_quasiIso
      X Z hZ
  change QuasiIso (CochainComplex.mappingCone.map
    (globalRawSingularRestrictionInt ℚ
      (TopCat.of (ComplexPoint X))
      Zᶜ)
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
      (naturalSingularResolutionRestriction X Z hZ))
    (globalRawToSingularSheafInt X)
    (globalRawComplementToDerivedPushforwardInt X Z hZ) _)
  exact CochainComplex.mappingCone.map_quasiIso_of_vertical_quasiIso _ _ _ _ _

/-- Global sections of a mapping cone are canonically isomorphic to the mapping cone of the
global-sections map. -/
def globalSectionsNaturalSingularConeIsoMappingCone
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction X Z hZ)) ≅
      CochainComplex.mappingCone
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (naturalSingularResolutionRestriction X Z hZ)) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso
    (naturalSingularResolutionRestriction X Z hZ)
    (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X)))

/-- Replacing rational constants by the natural singular resolution identifies the two support
hypercohomology groups, additively. -/
def rationalSupportHypercohomologyAddEquivNaturalSingularCone
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃+
      Hypercohomology X
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction X Z hZ)) (n - 1) where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv
    (rationalSupportConeToNaturalSingularCone X Z hZ)
    (rationalSupportConeToNaturalSingularCone_quasiIso X Z hZ)
  map_add' α β := (hypercohomologyMap X
    (rationalSupportConeToNaturalSingularCone X Z hZ) (n - 1)).map_add α β

/-- Additive form of the computation of rational constant-sheaf cohomology with support by
global sections of the natural singular support cone. -/
def rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction X Z hZ))).homology (n - 1) := by
  let K := CochainComplex.mappingCone
    (naturalSingularResolutionRestriction X Z hZ)
  letI : K.IsStrictlyGE (-1) :=
    naturalSingularSupportCone_isStrictlyGE X Z hZ
  exact (rationalSupportHypercohomologyAddEquivNaturalSingularCone
      X Z hZ n).trans
    (hypercohomologyAddEquivGlobalSections X K (-1)
      (naturalSingularSupportCone_term_isFlasque X Z hZ) (n - 1))

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
