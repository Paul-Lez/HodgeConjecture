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

public import Other.AlgebraicGeometry.BettiSupportConeComparison
public import Other.AlgebraicGeometry.BettiSupportSingularGlobalComparison

import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Hypercohomology and singular cohomology with support

This file develops the bounded-below flasque comparison needed for cohomology with support.
It applies the same explicit injective-replacement argument used for ordinary Betti cohomology
to the mapping cone of singular restriction. No hypercohomology spectral sequence is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra

namespace AlgebraicGeometry.ComplexPoint

open Point

universe u v

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

local instance bettiSupportHypercohomologyComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf structureMap) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf structureMap)

local instance bettiSupportHypercohomologyAddCommGrpHasDerivedCategory :
    HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard AddCommGrpCat

set_option backward.isDefEq.respectTransparency false in
private lemma mapExtendIso_inv_naturality
    {C D : Type u} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    {i i' : Type v} {c : ComplexShape i} {c' : ComplexShape i'}
    (F : Functor C D) [F.Additive] (K L : HomologicalComplex C c) (f : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    HomologicalComplex.extendMap
          ((F.mapHomologicalComplex c).map f) e ≫
        (HomologicalComplex.mapExtendIso F L e).inv =
      (HomologicalComplex.mapExtendIso F K e).inv ≫
        (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap f e) := by
  apply HomologicalComplex.Hom.ext
  funext q
  change HomologicalComplex.extend.mapX
        ((F.mapHomologicalComplex c).map f) (e.r q) ≫
      (HomologicalComplex.mapExtendXIsoAux F L (e.r q)).inv =
    (HomologicalComplex.mapExtendXIsoAux F K (e.r q)).inv ≫
      F.map (HomologicalComplex.extend.mapX f (e.r q))
  have aux (x : Option i) :
      HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map f) x ≫
          (HomologicalComplex.mapExtendXIsoAux F L x).inv =
        (HomologicalComplex.mapExtendXIsoAux F K x).inv ≫
          F.map (HomologicalComplex.extend.mapX f x) := by
    cases x with
    | none =>
        dsimp [HomologicalComplex.extend.mapX, HomologicalComplex.mapExtendXIsoAux]
        simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
    | some n =>
        dsimp [HomologicalComplex.extend.mapX, HomologicalComplex.mapExtendXIsoAux]
        change F.map (f.f n) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (f.f n)
        rw [Category.comp_id, Category.id_comp]
  exact aux (e.r q)

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
  let eK := HomologicalComplex.mapExtendIso Γ K ComplexShape.embeddingUpNat
  let eL := HomologicalComplex.mapExtendIso Γ L ComplexShape.embeddingUpNat
  let : KInt.IsStrictlyGE 0 := by
    dsimp [KInt]
    infer_instance
  let : LInt.IsStrictlyGE 0 := by
    dsimp [LInt]
    infer_instance
  let : QuasiIso fInt := by
    apply (HomologicalComplex.quasiIso_extendMap_iff
      f ComplexShape.embeddingUpNat).mpr
    infer_instance
  let : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map fInt) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      fInt 0 0 (extendNat_term_isFlasque K hK) (extendNat_term_isFlasque L hL)
  have h : HomologicalComplex.extendMap
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)
          ComplexShape.embeddingUpNat ≫ eL.inv =
      eK.inv ≫ (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map fInt :=
    mapExtendIso_inv_naturality Γ K L f ComplexShape.embeddingUpNat
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
  map_add' f g := by
    simp [Iso.homCongr]

/-- The chosen additive structure on hypercohomology is transported from shifted morphisms in
the derived category. -/
def hypercohomologyAddEquivDerived
    (K : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ) (n : ℤ) :
    Hypercohomology structureMap K n ≃+
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj K) n where
  toEquiv := Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  map_add' := hypercohomologyEquiv_add structureMap K n

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
      map_add' := by
        intro f g
        rw [Functor.map_add] }
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
        constructor
        · intro f g hfg
          change DerivedCategory.Qh.map f = DerivedCategory.Qh.map g at hfg
          exact h.injective hfg
        · intro f
          obtain ⟨g, hg⟩ := h.surjective f
          exact ⟨g, hg⟩)
  exact eDerived.trans <| eQh.symm.trans <|
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv.symm

/-- If a K-injective resolution of a sheaf complex remains a quasi-isomorphism after taking
global sections, then hypercohomology is computed by the original global-section complex. -/
def hypercohomologyEquivGlobalSectionsOfResolution
    (K I : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ)
    [I.IsKInjective]
    (i : K ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    Hypercohomology structureMap K n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap))) K).homology n := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let A := constantIntegerSheafComplexInt structureMap
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e : A ≅ A' := constantIntegerSheafComplexIntIsoSingle structureMap
  have hi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf structureMap)
      (ComplexShape.up ℤ) i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have he : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf structureMap)
      (ComplexShape.up ℤ) e.inv := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let e₁ := Localization.SmallShiftedHom.postcompEquiv
    (X := A) (Y := K) (Z := I) (a := n) i hi
  let e₂ := Localization.SmallShiftedHom.precompEquiv
    (X := A') (Y := A) (Z := I) (a := n) e.inv he
  let e₃ := (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
    (K := A') (L := I) (n := n)).symm
  let e₄ := (CochainComplex.HomComplex.homologyAddEquiv A' I n).symm.toEquiv
  let e₅ := (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y I) n)
      |>.addCommGroupIsoToAddEquiv.toEquiv
  let : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) := inferInstance
  let e₆ := (asIso (HomologicalComplex.homologyMap
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) n)).symm
      |>.addCommGroupIsoToAddEquiv.toEquiv
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))

/-- Additive form of the hypercohomology/global-sections comparison for a fixed K-injective
resolution. -/
def hypercohomologyAddEquivGlobalSectionsOfResolution
    (K I : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ)
    [I.IsKInjective]
    (i : K ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    Hypercohomology structureMap K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap))) K).homology n := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let A := constantIntegerSheafComplexInt structureMap
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e : A ≅ A' := constantIntegerSheafComplexIntIsoSingle structureMap
  let e₀ := hypercohomologyAddEquivDerived structureMap K n
  let eI : (DerivedCategory.Q.obj K)⟦n⟧ ≅
      (DerivedCategory.Q.obj I)⟦n⟧ :=
    (shiftFunctor (DerivedCategory (AnalyticAdditiveSheaf structureMap)) n).mapIso
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

/-- Hypercohomology of a bounded-below termwise-flasque sheaf complex is computed by its
global-section complex. The proof uses an explicit bounded-below injective replacement. -/
def hypercohomologyEquivGlobalSections
    (K : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ)
    (N : ℤ) [K.IsStrictlyGE N]
    (hKflasque : ∀ q, (K.X q).IsFlasque) (n : ℤ) :
    Hypercohomology structureMap K n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap))) K).homology n := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N
  let I := Classical.choose hres
  let hresI := Classical.choose_spec hres
  let i := Classical.choose hresI
  let hresi := Classical.choose_spec hresI
  let hi : QuasiIso i := Classical.choose hresi
  let hresiHi := Classical.choose_spec hresi
  let hI : ∀ q : ℤ, Injective (I.X q) := Classical.choose hresiHi
  let hIge : I.IsStrictlyGE N := Classical.choose_spec hresiHi
  letI : QuasiIso i := hi
  letI : ∀ q : ℤ, Injective (I.X q) := hI
  letI : I.IsStrictlyGE N := hIge
  letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I N
  have hIflasque : ∀ q, (I.X q).IsFlasque := by
    intro q
    infer_instance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i N N hKflasque hIflasque
  exact hypercohomologyEquivGlobalSectionsOfResolution structureMap K I i n

/-- Additive hypercohomology/global-sections comparison for a bounded-below termwise-flasque
complex. -/
def hypercohomologyAddEquivGlobalSections
    (K : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ)
    (N : ℤ) [K.IsStrictlyGE N]
    (hKflasque : ∀ q, (K.X q).IsFlasque) (n : ℤ) :
    Hypercohomology structureMap K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap))) K).homology n := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N
  let I := Classical.choose hres
  let hresI := Classical.choose_spec hres
  let i := Classical.choose hresI
  let hresi := Classical.choose_spec hresI
  let hi : QuasiIso i := Classical.choose hresi
  let hresiHi := Classical.choose_spec hresi
  let hI : ∀ q : ℤ, Injective (I.X q) := Classical.choose hresiHi
  let hIge : I.IsStrictlyGE N := Classical.choose_spec hresiHi
  letI : QuasiIso i := hi
  letI : ∀ q : ℤ, Injective (I.X q) := hI
  letI : I.IsStrictlyGE N := hIge
  letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I N
  have hIflasque : ∀ q, (I.X q).IsFlasque := by
    intro q
    infer_instance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i N N hKflasque hIflasque
  exact hypercohomologyAddEquivGlobalSectionsOfResolution
    structureMap K I i n

open AlgebraicTopology.Singular

/-- Global sections of the pushed-forward comparison from singular cochains on the complement
to its chosen injective resolution. -/
def globalComplementSingularToInjectiveResolutionNat
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    globalPushforwardSingularCochainSheafComplex ℚ
        (analyticComplementInclusion structureMap Z) ⟶
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (derivedPushforwardComplementConstantRationalComplexNat structureMap Z) :=
  ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticComplementInclusion structureMap Z)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
      (complementSingularToInjectiveResolution structureMap Z hZ))

/-- Raw singular cochains on the complement map to global sections of the chosen derived
pushforward through sheafification and the injective-resolution comparison. -/
def globalRawComplementToDerivedPushforwardNat
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    globalRawPushforwardSingularCochainComplex ℚ
        (analyticComplementInclusion structureMap Z) ⟶
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (derivedPushforwardComplementConstantRationalComplexNat structureMap Z) :=
  globalRawPushforwardToSingularSheaf ℚ
      (analyticComplementInclusion structureMap Z) ≫
    globalComplementSingularToInjectiveResolutionNat structureMap Z hZ

/-- On a hereditarily paracompact Hausdorff ambient space, global sections of the complement
singular-to-injective comparison are a quasi-isomorphism. -/
theorem globalComplementSingularToInjectiveResolutionNat_quasiIso
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [hpara : ∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    QuasiIso (globalComplementSingularToInjectiveResolutionNat
      structureMap Z hZ) := by
  let U := TopCat.of (AnalyticComplement structureMap Z)
  let j := analyticComplementInclusion structureMap Z
  let : T2Space U := by infer_instance
  let : ∀ W : Opens U, ParacompactSpace W := fun W ↦
    opens_paracompactSpace_of_isOpenEmbedding j
      (analyticComplementInclusion_isOpenEmbedding structureMap Z hZ) hpara W
  change QuasiIso
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor U
      ).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (complementSingularToInjectiveResolution structureMap Z hZ))
  let : QuasiIso
      (complementSingularToInjectiveResolution structureMap Z hZ) :=
    complementSingularToInjectiveResolution_quasiIso structureMap Z hZ
  apply globalSectionsNat_map_quasiIso
  · intro m
    change TopCat.Sheaf.IsFlasque
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ U m)
    infer_instance
  · intro m
    infer_instance

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
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [hpara : ∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    QuasiIso (globalRawPushforwardToSingularSheaf ℚ
      (analyticComplementInclusion structureMap Z)) := by
  let U := TopCat.of (AnalyticComplement structureMap Z)
  let j := analyticComplementInclusion structureMap Z
  let : T2Space U := by infer_instance
  let Uopen : Opens (TopCat.of (ComplexPoint (Over.mk structureMap))) :=
    ⟨Zᶜ, hZ.isOpen_compl⟩
  let : ParacompactSpace U := by
    change ParacompactSpace Uopen
    exact hpara Uopen
  rw [globalRawPushforwardToSingularSheaf_eq_topOpen j]
  exact topOpenToGlobalSingularCochainSheafComplex_quasiIso

/-- Raw complement cochains map quasi-isomorphically to global sections of the chosen derived
pushforward model. -/
theorem globalRawComplementToDerivedPushforwardNat_quasiIso
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    QuasiIso (globalRawComplementToDerivedPushforwardNat
      structureMap Z hZ) := by
  let : QuasiIso (globalRawPushforwardToSingularSheaf ℚ
      (analyticComplementInclusion structureMap Z)) :=
    globalRawComplementToSingularSheaf_quasiIso structureMap Z hZ
  let : QuasiIso (globalComplementSingularToInjectiveResolutionNat
      structureMap Z hZ) :=
    globalComplementSingularToInjectiveResolutionNat_quasiIso
      structureMap Z hZ
  unfold globalRawComplementToDerivedPushforwardNat
  infer_instance

/-- Restriction on global sections of the natural singular-resolution map. -/
def globalNaturalSingularResolutionRestrictionNat
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    globalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint (Over.mk structureMap))) ⟶
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (derivedPushforwardComplementConstantRationalComplexNat structureMap Z) :=
  ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (naturalSingularResolutionRestrictionNat structureMap Z hZ)

set_option backward.isDefEq.respectTransparency false in
/-- The natural singular-resolution restriction square commutes after taking global sections. -/
lemma globalNaturalSingularResolutionRestrictionNat_naturality
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    topOpenToGlobalSingularCochainSheafComplex ℚ
          (TopCat.of (ComplexPoint (Over.mk structureMap))) ≫
        globalNaturalSingularResolutionRestrictionNat structureMap Z hZ =
      globalRawSingularRestriction ℚ
          (analyticComplementInclusion structureMap Z) ≫
        globalRawComplementToDerivedPushforwardNat structureMap Z hZ := by
  unfold globalNaturalSingularResolutionRestrictionNat
    naturalSingularResolutionRestrictionNat
    globalRawComplementToDerivedPushforwardNat
    globalComplementSingularToInjectiveResolutionNat
  rw [Functor.map_comp]
  change topOpenToGlobalSingularCochainSheafComplex ℚ _ ≫
        globalSingularSheafRestriction ℚ
          (analyticComplementInclusion structureMap Z) ≫ _ = _
  rw [← Category.assoc, globalSingularSheafRestriction_naturality]
  rw [Category.assoc]

/-- Raw ambient cochains map to global sections of the integer-indexed singular-cochain sheaf
complex. -/
def globalRawToSingularSheafInt :
    globalRawSingularCochainComplexInt ℚ
        (TopCat.of (ComplexPoint (Over.mk structureMap))) ⟶
      TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap)))
        (singularCochainSheafComplexInt structureMap ℚ) :=
  HomologicalComplex.extendMap
      (topOpenToGlobalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint (Over.mk structureMap))))
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendIso
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint (Over.mk structureMap))))
      (singularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint (Over.mk structureMap))))
      ComplexShape.embeddingUpNat).inv

/-- Raw complement cochains map to global sections of the integer-indexed derived-pushforward
model. -/
def globalRawComplementToDerivedPushforwardInt
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    globalRawPushforwardSingularCochainComplexInt ℚ
        (TopCat.of (ComplexPoint (Over.mk structureMap)))
        (AnalyticComplement structureMap Z) ⟶
      TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap)))
        (derivedPushforwardComplementConstantRationalComplexInt structureMap Z) :=
  HomologicalComplex.extendMap
      (globalRawComplementToDerivedPushforwardNat structureMap Z hZ)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendIso
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint (Over.mk structureMap))))
      (derivedPushforwardComplementConstantRationalComplexNat structureMap Z)
      ComplexShape.embeddingUpNat).inv

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The integer-indexed raw ambient-to-sheaf comparison is a quasi-isomorphism. -/
theorem globalRawToSingularSheafInt_quasiIso
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [hpara : ∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U] :
    QuasiIso (globalRawToSingularSheafInt structureMap) := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let f := topOpenToGlobalSingularCochainSheafComplex ℚ Y
  let fInt := HomologicalComplex.extendMap f ComplexShape.embeddingUpNat
  let e := HomologicalComplex.mapExtendIso Γ
    (singularCochainSheafComplex ℚ Y) ComplexShape.embeddingUpNat
  let : ParacompactSpace (ComplexPoint (Over.mk structureMap)) :=
    (Homeomorph.Set.univ (ComplexPoint (Over.mk structureMap))).paracompactSpace_iff.mp
      (hpara (⊤ : Opens (ComplexPoint (Over.mk structureMap))))
  let : QuasiIso f :=
    topOpenToGlobalSingularCochainSheafComplex_quasiIso
  let hfInt : QuasiIso fInt := by
    apply (HomologicalComplex.quasiIso_extendMap_iff
      f ComplexShape.embeddingUpNat).mpr
    infer_instance
  let he : QuasiIso e.inv := by infer_instance
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
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    QuasiIso (globalRawComplementToDerivedPushforwardInt
      structureMap Z hZ) := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let f := globalRawComplementToDerivedPushforwardNat structureMap Z hZ
  let fInt := HomologicalComplex.extendMap f ComplexShape.embeddingUpNat
  let e := HomologicalComplex.mapExtendIso Γ
    (derivedPushforwardComplementConstantRationalComplexNat structureMap Z)
      ComplexShape.embeddingUpNat
  let : QuasiIso f :=
    globalRawComplementToDerivedPushforwardNat_quasiIso
      structureMap Z hZ
  let hfInt : QuasiIso fInt := by
    apply (HomologicalComplex.quasiIso_extendMap_iff
      f ComplexShape.embeddingUpNat).mpr
    infer_instance
  let he : QuasiIso e.inv := by infer_instance
  change QuasiIso (fInt ≫ e.inv)
  refine ⟨fun i ↦ ?_⟩
  letI : QuasiIsoAt fInt i := hfInt.quasiIsoAt i
  letI : QuasiIsoAt e.inv i := he.quasiIsoAt i
  exact quasiIsoAt_comp fInt e.inv i

set_option backward.isDefEq.respectTransparency false in
/-- The raw and sheaf-level restriction maps commute after extension to integer degrees. -/
lemma globalNaturalSingularResolutionRestrictionInt_naturality
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    globalRawToSingularSheafInt structureMap ≫
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (naturalSingularResolutionRestriction structureMap Z hZ) =
      globalRawSingularRestrictionInt ℚ
          (TopCat.of (ComplexPoint (Over.mk structureMap)))
          (AnalyticComplement structureMap Z) ≫
        globalRawComplementToDerivedPushforwardInt structureMap Z hZ := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let S := singularCochainSheafComplex ℚ Y
  let D := derivedPushforwardComplementConstantRationalComplexNat structureMap Z
  let g := naturalSingularResolutionRestrictionNat structureMap Z hZ
  let a := topOpenToGlobalSingularCochainSheafComplex ℚ Y
  let f := globalRawSingularRestriction ℚ
    (analyticComplementInclusion structureMap Z)
  let b := globalRawComplementToDerivedPushforwardNat structureMap Z hZ
  let eS := HomologicalComplex.mapExtendIso Γ S ComplexShape.embeddingUpNat
  let eD := HomologicalComplex.mapExtendIso Γ D ComplexShape.embeddingUpNat
  have hg : HomologicalComplex.extendMap
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map g)
          ComplexShape.embeddingUpNat ≫ eD.inv =
      eS.inv ≫ (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) :=
    mapExtendIso_inv_naturality Γ S D g ComplexShape.embeddingUpNat
  have hab : a ≫
        (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map g = f ≫ b :=
    globalNaturalSingularResolutionRestrictionNat_naturality
      structureMap Z hZ
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
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    CochainComplex.mappingCone
        (globalRawSingularRestrictionInt ℚ
          (TopCat.of (ComplexPoint (Over.mk structureMap)))
          (AnalyticComplement structureMap Z)) ⟶
      CochainComplex.mappingCone
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (naturalSingularResolutionRestriction structureMap Z hZ)) :=
  CochainComplex.mappingCone.map
    (globalRawSingularRestrictionInt ℚ
      (TopCat.of (ComplexPoint (Over.mk structureMap)))
      (AnalyticComplement structureMap Z))
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
      (naturalSingularResolutionRestriction structureMap Z hZ))
    (globalRawToSingularSheafInt structureMap)
    (globalRawComplementToDerivedPushforwardInt structureMap Z hZ)
    (globalNaturalSingularResolutionRestrictionInt_naturality
      structureMap Z hZ).symm

set_option backward.isDefEq.respectTransparency false in
/-- The raw-to-global-sections map of support cones is a quasi-isomorphism. -/
noncomputable instance globalRawSupportConeToGlobalNaturalSingularCone_quasiIso
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    QuasiIso (globalRawSupportConeToGlobalNaturalSingularCone
      structureMap Z hZ) := by
  let : QuasiIso (globalRawToSingularSheafInt structureMap) :=
    globalRawToSingularSheafInt_quasiIso structureMap
  let : QuasiIso (globalRawComplementToDerivedPushforwardInt
      structureMap Z hZ) :=
    globalRawComplementToDerivedPushforwardInt_quasiIso
      structureMap Z hZ
  change QuasiIso (CochainComplex.mappingCone.map
    (globalRawSingularRestrictionInt ℚ
      (TopCat.of (ComplexPoint (Over.mk structureMap)))
      (AnalyticComplement structureMap Z))
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
      (naturalSingularResolutionRestriction structureMap Z hZ))
    (globalRawToSingularSheafInt structureMap)
    (globalRawComplementToDerivedPushforwardInt structureMap Z hZ) _)
  exact CochainComplex.mappingCone.map_quasiIso_of_vertical_quasiIso _ _ _ _ _

/-- Global sections of a mapping cone are canonically isomorphic to the mapping cone of the
global-sections map. -/
def globalSectionsNaturalSingularConeIsoMappingCone
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap)))
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction structureMap Z hZ)) ≅
      CochainComplex.mappingCone
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (naturalSingularResolutionRestriction structureMap Z hZ)) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso
    (naturalSingularResolutionRestriction structureMap Z hZ)
    (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint (Over.mk structureMap))))

/-- Replacing rational constants by the natural singular resolution identifies the two support
hypercohomology groups. -/
def rationalSupportHypercohomologyEquivNaturalSingularCone
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport structureMap Z n ≃
      Hypercohomology structureMap
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction structureMap Z hZ)) (n - 1) :=
  Localization.SmallShiftedHom.postcompEquiv
    (rationalSupportConeToNaturalSingularCone structureMap Z hZ)
    (rationalSupportConeToNaturalSingularCone_quasiIso structureMap Z hZ)

/-- Additive form of the quasi-isomorphism invariance comparison between the rational support
cone and the natural singular support cone. -/
def rationalSupportHypercohomologyAddEquivNaturalSingularCone
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport structureMap Z n ≃+
      Hypercohomology structureMap
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction structureMap Z hZ)) (n - 1) where
  toEquiv := rationalSupportHypercohomologyEquivNaturalSingularCone
    structureMap Z hZ n
  map_add' α β := by
    exact (hypercohomologyMap structureMap
      (rationalSupportConeToNaturalSingularCone structureMap Z hZ) (n - 1)).map_add α β

/-- The natural singular support cone is concentrated in degrees at least `-1`. -/
lemma naturalSingularSupportCone_isStrictlyGE
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) :
    (CochainComplex.mappingCone
      (naturalSingularResolutionRestriction structureMap Z hZ)).IsStrictlyGE (-1) := by
  let : (singularCochainSheafComplexInt structureMap ℚ).IsStrictlyGE 0 := by
    dsimp [singularCochainSheafComplexInt]
    infer_instance
  let : (derivedPushforwardComplementConstantRationalComplexInt
      structureMap Z).IsStrictlyGE 0 := by
    dsimp [derivedPushforwardComplementConstantRationalComplexInt]
    infer_instance
  exact CochainComplex.isStrictlyGE_mappingCone
    (naturalSingularResolutionRestriction structureMap Z hZ) 0 0 (-1)
      (by lia) (by lia)

/-- Every term of the derived complement resolution is flasque. In nonnegative degrees it is
the pushforward of an injective sheaf; in negative degrees it is zero. -/
theorem derivedPushforwardComplementConstantRationalComplexInt_term_isFlasque
    (Z : Set (ComplexPoint (Over.mk structureMap))) (q : ℤ) :
    (derivedPushforwardComplementConstantRationalComplexInt structureMap Z).X q |>.IsFlasque := by
  by_cases hq : ∃ m : ℕ, (m : ℤ) = q
  · obtain ⟨m, rfl⟩ := hq
    let K := derivedPushforwardComplementConstantRationalComplexNat structureMap Z
    let e := K.extendXIso ComplexShape.embeddingUpNat (i := m) rfl
    let hP : TopCat.Presheaf.IsFlasque (K.X m).obj := by
      let F :=
        (complementConstantRationalInjectiveResolution structureMap Z).cocomplex.X m
      let : Injective F := by
        dsimp [F]
        infer_instance
      let : TopCat.Sheaf.IsFlasque F :=
        TopCat.Sheaf.injective_isFlasque _ F
      exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque F
        (analyticComplementInclusion structureMap Z)
    change TopCat.Presheaf.IsFlasque ((K.extend
      ComplexShape.embeddingUpNat).X (m : ℤ)).obj
    exact @TopCat.Presheaf.IsFlasque.of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapIso e) hP
  · apply TopCat.Sheaf.IsFlasque.of_isZero
    exact (derivedPushforwardComplementConstantRationalComplexNat structureMap Z).isZero_extend_X
      ComplexShape.embeddingUpNat q (fun i hi ↦ hq ⟨i, hi⟩)

/-- Every term of the natural singular support cone is flasque on a hereditarily paracompact
Hausdorff analytic space. -/
theorem naturalSingularSupportCone_term_isFlasque
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) (q : ℤ) :
    ((CochainComplex.mappingCone
      (naturalSingularResolutionRestriction structureMap Z hZ)).X q).IsFlasque := by
  apply TopCat.Sheaf.IsFlasque.BoundedBelowComplex.mappingCone_term_isFlasque
    (naturalSingularResolutionRestriction structureMap Z hZ)
  · intro i
    exact singularCochainSheafComplexInt_isFlasque structureMap i
  · intro i
    exact derivedPushforwardComplementConstantRationalComplexInt_term_isFlasque
      structureMap Z i

/-- Rational constant-sheaf cohomology with support is computed by global sections of the
natural singular support cone. -/
def rationalSupportHypercohomologyEquivNaturalSingularConeGlobalSections
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport structureMap Z n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap)))
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction structureMap Z hZ))).homology (n - 1) := by
  let K := CochainComplex.mappingCone
    (naturalSingularResolutionRestriction structureMap Z hZ)
  letI : K.IsStrictlyGE (-1) :=
    naturalSingularSupportCone_isStrictlyGE structureMap Z hZ
  exact (rationalSupportHypercohomologyEquivNaturalSingularCone
      structureMap Z hZ n).trans
    (hypercohomologyEquivGlobalSections structureMap K (-1)
      (naturalSingularSupportCone_term_isFlasque structureMap Z hZ) (n - 1))

/-- Additive form of the computation of rational constant-sheaf cohomology with support by
global sections of the natural singular support cone. -/
def rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport structureMap Z n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap)))
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction structureMap Z hZ))).homology (n - 1) := by
  let K := CochainComplex.mappingCone
    (naturalSingularResolutionRestriction structureMap Z hZ)
  letI : K.IsStrictlyGE (-1) :=
    naturalSingularSupportCone_isStrictlyGE structureMap Z hZ
  exact (rationalSupportHypercohomologyAddEquivNaturalSingularCone
      structureMap Z hZ n).trans
    (hypercohomologyAddEquivGlobalSections structureMap K (-1)
      (naturalSingularSupportCone_term_isFlasque structureMap Z hZ) (n - 1))

/-- Rational constant-sheaf cohomology with closed support agrees with rational singular
cohomology with the same support. -/
def rationalCohomologyWithSupportEquivSingular
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) (n : ℕ) :
    RationalCohomologyWithSupport structureMap Z (n : ℤ) ≃
      CohomologyWithSupport ℚ
        (TopCat.of (ComplexPoint (Over.mk structureMap))) Z n :=
  (rationalSupportHypercohomologyEquivNaturalSingularConeGlobalSections
      structureMap Z hZ (n : ℤ)).trans <|
    ((HomologicalComplex.homologyMapIso
      (globalSectionsNaturalSingularConeIsoMappingCone
        structureMap Z hZ) ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv.toEquiv).trans <|
    ((asIso (HomologicalComplex.homologyMap
      (globalRawSupportConeToGlobalNaturalSingularCone
        structureMap Z hZ) ((n : ℤ) - 1))).symm.addCommGroupIsoToAddEquiv.toEquiv).trans <|
    (globalRawSingularRestrictionConeCohomologyEquivSupport ℚ
      (TopCat.of (ComplexPoint (Over.mk structureMap))) Z n).toEquiv

/-- Additive Betti comparison for rational cohomology with closed support. -/
def rationalCohomologyWithSupportAddEquivSingular
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (Z : Set (ComplexPoint (Over.mk structureMap))) (hZ : IsClosed Z) (n : ℕ) :
    RationalCohomologyWithSupport structureMap Z (n : ℤ) ≃+
      CohomologyWithSupport ℚ
        (TopCat.of (ComplexPoint (Over.mk structureMap))) Z n :=
  (rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections
      structureMap Z hZ (n : ℤ)).trans <|
    ((HomologicalComplex.homologyMapIso
      (globalSectionsNaturalSingularConeIsoMappingCone
        structureMap Z hZ) ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv).trans <|
    ((asIso (HomologicalComplex.homologyMap
      (globalRawSupportConeToGlobalNaturalSingularCone
        structureMap Z hZ) ((n : ℤ) - 1))).symm.addCommGroupIsoToAddEquiv).trans <|
    globalRawSingularRestrictionConeCohomologyEquivSupport ℚ
      (TopCat.of (ComplexPoint (Over.mk structureMap))) Z n

end AlgebraicGeometry.ComplexPoint
