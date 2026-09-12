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

public import HodgeConjecture.Lemmas.Algebra.Homology.MapExtendNaturality
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeComparison
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportSingularGlobal

import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Hypercohomology and singular cohomology with support

This file develops the bounded-below flasque comparison needed for cohomology with support.
It applies the same explicit injective-replacement argument used for ordinary singular cohomology
to the mapping cone of singular restriction. No hypercohomology spectral sequence is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra

namespace AlgebraicGeometry.ComplexPoint

open Point

universe u v

variable (X : Over (Spec ↧ℂ))

local instance bettiSupportHypercohomologyComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance bettiSupportHypercohomologyAddCommGrpHasDerivedCategory :
    HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard AddCommGrpCat

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
  let : KInt.IsStrictlyGE 0 := by
    dsimp [KInt]
    infer_instance
  let : LInt.IsStrictlyGE 0 := by
    dsimp [LInt]
    infer_instance
  let : QuasiIso fInt :=
    (HomologicalComplex.quasiIso_extendMap_iff f ComplexShape.embeddingUpNat).mpr
      inferInstance
  let : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map fInt) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      fInt 0 0 (extendNat_term_isFlasque K hK) (extendNat_term_isFlasque L hL)
  have h : HomologicalComplex.extendMap
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
          ComplexShape.embeddingUpNat ≫ eL.inv =
      eK.inv ≫ (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map fInt :=
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

/-- Conjugating a morphism by two isomorphisms is an additive equivalence of Hom groups. -/
def isoHomCongrAddEquiv
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B A' B' : C} (eA : A ≅ A') (eB : B ≅ B') :
    (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := Iso.homCongr eA eB
  map_add' f g := by simp [Iso.homCongr]

/-- The chosen additive structure on hypercohomology is transported from shifted morphisms in
the derived category. -/
def hypercohomologyAddEquivDerived
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    Hypercohomology X K n ≃+
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n where
  toEquiv := Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q
  map_add' := hypercohomologyEquiv_add X K n

/-- For a K-injective target, shifted derived morphisms are additively identified with
cohomology classes in the Hom complex. -/
def kInjectiveDerivedHomAddEquivCohomologyClass
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) n ≃+
      CochainComplex.HomComplex.CohomologyClass K L n := by
  let qSource : DerivedCategory.Q.obj K ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) :=
    (DerivedCategory.quotientCompQhIso C).symm.app K
  let qTarget : (DerivedCategory.Q.obj L)⟦n⟧ ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧)) :=
    (DerivedCategory.Q.commShiftIso n).symm.app L ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app (L⟦n⟧)
  let eDerived : ShiftedHom (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) n ≃+
      (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) :=
    isoHomCongrAddEquiv qSource qTarget
  let qhMap :
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) →+
        (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶
          DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) :=
    { toFun := DerivedCategory.Qh.map
      map_zero' := by simp
      map_add' f g := by rw [Functor.map_add] }
  let eQh :
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) ≃+
        (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶
          DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) :=
    AddEquiv.ofBijective qhMap
      (by
        let h := CochainComplex.IsKInjective.Qh_map_bijective
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) (L⟦n⟧)
        exact ⟨fun _ _ hfg ↦ h.injective hfg, h.surjective⟩)
  exact eDerived.trans <| eQh.symm.trans <|
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv.symm

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
  let : T2Space U := inferInstance
  let Uopen : Opens (TopCat.of (ComplexPoint X)) :=
    ⟨Zᶜ, hZ.isOpen_compl⟩
  let : ParacompactSpace U := hpara Uopen
  rw [globalRawPushforwardToSingularSheaf_eq_topOpen j]
  exact topOpenToGlobalSingularCochainSheafComplex_quasiIso

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

end AlgebraicGeometry.ComplexPoint
