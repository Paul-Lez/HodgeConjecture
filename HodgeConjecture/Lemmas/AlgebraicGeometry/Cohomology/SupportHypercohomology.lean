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

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

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

/-- Extension by zero of a natural-number-indexed termwise-flasque complex remains
termwise flasque. -/
theorem extendNat_term_isFlasque
    {Y : TopCat.{0}} (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℕ)
    (hK : ∀ m, (K.X m).IsFlasque) (q : ℤ) :
    ((K.extend ComplexShape.embeddingUpNat).X q).IsFlasque := by
  by_cases hq : ∃ m : ℕ, (m : ℤ) = q
  · obtain ⟨m, rfl⟩ := hq
    let e := K.extendXIso ComplexShape.embeddingUpNat (i := m) rfl
    let hP : TopCat.Presheaf.IsFlasque (K.X m).obj := hK m
    change TopCat.Presheaf.IsFlasque
      ((K.extend ComplexShape.embeddingUpNat).X (m : ℤ)).obj
    exact @TopCat.Presheaf.IsFlasque.of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat Y).mapIso e) hP
  · apply TopCat.Sheaf.IsFlasque.of_isZero
    exact K.isZero_extend_X ComplexShape.embeddingUpNat q
      (fun i hi ↦ hq ⟨i, hi⟩)

/-- A quasi-isomorphism of nonnegative termwise-flasque sheaf complexes remains a
quasi-isomorphism after taking global sections. -/
theorem globalSectionsNat_map_quasiIso
    {Y : TopCat.{0}}
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℕ}
    (f : K ⟶ L) [QuasiIso f]
    (hK : ∀ m, (K.X m).IsFlasque) (hL : ∀ m, (L.X m).IsFlasque) :
    QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℕ)).map f) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let KInt : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ :=
    K.extend ComplexShape.embeddingUpNat
  let LInt : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ :=
    L.extend ComplexShape.embeddingUpNat
  let fInt : KInt ⟶ LInt :=
    HomologicalComplex.extendMap f ComplexShape.embeddingUpNat
  let eK := HomologicalComplex.mapExtendCanonicalIso Γ K ComplexShape.embeddingUpNat
  let eL := HomologicalComplex.mapExtendCanonicalIso Γ L ComplexShape.embeddingUpNat
  let : QuasiIso ((Γ.mapHomologicalComplex ℤᵘᵖ).map fInt) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      fInt 0 0 (extendNat_term_isFlasque K hK) (extendNat_term_isFlasque L hL)
  have h : HomologicalComplex.extendMap
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
          ComplexShape.embeddingUpNat ≫ eL.inv =
      eK.inv ≫ (Γ.mapHomologicalComplex ℤᵘᵖ).map fInt :=
    HomologicalComplex.mapExtendCanonicalIso_inv_naturality Γ f ComplexShape.embeddingUpNat
  have hcomp : QuasiIso
      (HomologicalComplex.extendMap
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
          ComplexShape.embeddingUpNat ≫ eL.inv) := by
    rw [h]
    infer_instance
  have hext : QuasiIso (HomologicalComplex.extendMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
        ComplexShape.embeddingUpNat) :=
    quasiIso_of_comp_right _ eL.inv
  exact (HomologicalComplex.quasiIso_extendMap_iff
    ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
      ComplexShape.embeddingUpNat).mp hext

/-- Hereditary paracompactness descends through an open embedding. -/
lemma opens_paracompactSpace_of_isOpenEmbedding
    {U Y : TopCat.{0}} (j : U ⟶ Y) (hj : Topology.IsOpenEmbedding j)
    (hY : ∀ V : Opens Y, ParacompactSpace V) (W : Opens U) :
    ParacompactSpace W := by
  let Wi : Opens Y := ⟨j '' (W : Set U), (hj.isOpen_iff_image_isOpen).mp W.2⟩
  have hWi : ParacompactSpace Wi := hY Wi
  exact (hj.toIsEmbedding.homeomorphImage (W : Set U)).paracompactSpace_iff.mpr hWi

section

open AlgebraicTopology.Singular

/-- For an inclusion into an ambient space, sheafification of raw cochains on the inverse image
of the top open is the ordinary top-open sheafification map on the source space. -/
lemma globalRawPushforwardToSingularSheaf_eq_topOpen
    {U Y : TopCat.{0}} (j : U ⟶ Y) :
    globalRawPushforwardToSingularSheaf ℚ j =
      topOpenToGlobalSingularCochainSheafComplex ℚ U := by
  apply HomologicalComplex.Hom.ext
  funext m
  rw [topOpenToGlobalSingularCochainSheafComplex_f]
  rfl

/-- The raw-to-sheaf comparison on the complement is a quasi-isomorphism. -/
theorem globalRawComplementToSingularSheaf_quasiIso
    [T2Space (ComplexPoint X)]
    [hpara : ∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (globalRawPushforwardToSingularSheaf ℚ
      (analyticComplementInclusion X Z)) := by
  let U := TopCat.of ↥Zᶜ
  let j := analyticComplementInclusion X Z
  let Uopen : Opens (TopCat.of (ComplexPoint X)) :=
    ⟨Zᶜ, hZ.isOpen_compl⟩
  let : ParacompactSpace U := hpara Uopen
  rw [globalRawPushforwardToSingularSheaf_eq_topOpen j]
  exact topOpenToGlobalSingularCochainSheafComplex_quasiIso

end

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
  refine ⟨fun i ↦ ?_⟩
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
  refine ⟨fun i ↦ ?_⟩
  exact quasiIsoAt_comp fInt e.inv i

set_option backward.isDefEq.respectTransparency false in
/-- The raw and sheaf-level restriction maps commute after extension to integer degrees. -/
lemma globalNaturalSingularResolutionRestrictionInt_naturality
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    globalRawToSingularSheafInt X ≫
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex
            ℤᵘᵖ).map
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
      eS.inv ≫ (Γ.mapHomologicalComplex ℤᵘᵖ).map
        (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) :=
    HomologicalComplex.mapExtendCanonicalIso_inv_naturality Γ g ComplexShape.embeddingUpNat
  have hab : a ≫
        (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map g = f ≫ b :=
    globalNaturalSingularResolutionRestrictionNat_naturality
      X Z hZ
  change (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat ≫ eS.inv) ≫
      (Γ.mapHomologicalComplex ℤᵘᵖ).map
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
            ℤᵘᵖ).map
          (naturalSingularResolutionRestriction X Z hZ)) :=
  CochainComplex.mappingCone.map
    (globalRawSingularRestrictionInt ℚ
      (TopCat.of (ComplexPoint X))
      Zᶜ)
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        ℤᵘᵖ).map
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
        ℤᵘᵖ).map
      (naturalSingularResolutionRestriction X Z hZ))
    (globalRawToSingularSheafInt X)
    (globalRawComplementToDerivedPushforwardInt X Z hZ) _)
  exact CochainComplex.mappingCone.map_quasiIso_of_vertical_quasiIso _ _ _ _ _

end AlgebraicGeometry.ComplexPoint
