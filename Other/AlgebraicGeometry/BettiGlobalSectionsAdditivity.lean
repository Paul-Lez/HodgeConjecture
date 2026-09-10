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

public import HodgeConjecture.Definitions.AlgebraicGeometry.BettiGlobalSectionsComparison

/-!
# Additivity of the Betti global-sections comparison

This file upgrades the rational Betti comparison equivalences to additive equivalences.  The
group law on hypercohomology is transported from morphisms in the derived category, so
additivity of the localized-Hom steps is checked after applying the defining equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance bettiGlobalSectionsAdditivityHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

set_option maxHeartbeats 800000 in
/-- The comparison with global sections is additive when computed from a K-injective
resolution whose global-sections map is a quasi-isomorphism. -/
def rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    RationalSingularCochainHypercohomology X n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let A := constantIntegerSheafComplexInt X
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let S := singularCochainSheafComplexInt X ℚ
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e : A ≅ A' := constantIntegerSheafComplexIntIsoSingle X
  have hi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have he : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) e.inv := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let e₁ := Localization.SmallShiftedHom.postcompEquiv
    (X := A) (Y := S) (Z := I) (a := n) i hi
  let e₂ := Localization.SmallShiftedHom.precompEquiv
    (X := A') (Y := A) (Z := I) (a := n) e.inv he
  letI : AddCommGroup (Localization.SmallShiftedHom
      (analyticQuasiIsomorphisms X) A' I n) :=
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).addCommGroup
  have localizedEquiv_add (α β : Localization.SmallShiftedHom
      (analyticQuasiIsomorphisms X) A' I n) :
      (Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q) (α + β) =
        (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms X) DerivedCategory.Q) α +
        (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms X) DerivedCategory.Q) β := by
    simp [Equiv.add_def]
  let ae₁ : RationalSingularCochainHypercohomology X n ≃+
      Hypercohomology X I n :=
    { toEquiv := e₁
      map_add' α β := by
        apply (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
        rw [hypercohomologyEquiv_add X I n]
        dsimp only [e₁, Localization.SmallShiftedHom.postcompEquiv]
        simp only [Localization.SmallShiftedHom.equiv_comp]
        rw [hypercohomologyEquiv_add X S n]
        rw [CategoryTheory.ShiftedHom.add_comp] }
  let ae₂ : Hypercohomology X I n ≃+
      Localization.SmallShiftedHom
        (analyticQuasiIsomorphisms X) A' I n :=
    { toEquiv := e₂
      map_add' α β := by
        apply (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
        rw [localizedEquiv_add]
        dsimp only [e₂, Localization.SmallShiftedHom.precompEquiv]
        simp only [Localization.SmallShiftedHom.equiv_comp]
        rw [hypercohomologyEquiv_add X I n]
        rw [CategoryTheory.ShiftedHom.comp_add] }
  let ae₃' : CochainComplex.HomComplex.CohomologyClass A' I n ≃+
      Localization.SmallShiftedHom
        (analyticQuasiIsomorphisms X) A' I n :=
    { toEquiv := CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
      map_add' α β := by
        change
          CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom (α + β) =
            CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom α +
            CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom β
        apply (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
        rw [localizedEquiv_add]
        obtain ⟨α, rfl⟩ := α.mk_surjective
        obtain ⟨β, rfl⟩ := β.mk_surjective
        rw [← CochainComplex.HomComplex.CohomologyClass.mk_add]
        simp only [
          CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk,
          map_add, CategoryTheory.ShiftedHom.map_add] }
  let ae₃ := ae₃'.symm
  let ae₄ := (CochainComplex.HomComplex.homologyAddEquiv A' I n).symm
  let ae₅ := (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y I) n)
      |>.addCommGroupIsoToAddEquiv
  let : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) := inferInstance
  let ae₆ := (asIso (HomologicalComplex.homologyMap
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) n)).symm
      |>.addCommGroupIsoToAddEquiv
  exact ae₁.trans (ae₂.trans (ae₃.trans (ae₄.trans (ae₅.trans ae₆))))

/-- The canonical hypercohomology comparison with the global-section complex, bundled as an
additive equivalence. -/
def rationalSingularCochainHypercohomologyAddEquivGlobalSections
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    RationalSingularCochainHypercohomology X n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X ℚ
  let : S.IsStrictlyGE 0 := by
    dsimp [S, singularCochainSheafComplexInt]
    infer_instance
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S 0
  let I := Classical.choose hres
  let hresI := Classical.choose_spec hres
  let i := Classical.choose hresI
  let hresi := Classical.choose_spec hresI
  let hi : QuasiIso i := Classical.choose hresi
  let hresiHi := Classical.choose_spec hresi
  let hI : ∀ q : ℤ, Injective (I.X q) := Classical.choose hresiHi
  let hIge : I.IsStrictlyGE 0 := Classical.choose_spec hresiHi
  letI : QuasiIso i := hi
  letI : ∀ q : ℤ, Injective (I.X q) := hI
  letI : I.IsStrictlyGE 0 := hIge
  letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I 0
  have hSflasque : ∀ q, (S.X q).IsFlasque :=
    fun q ↦ singularCochainSheafComplexInt_isFlasque X q
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hSflasque hIflasque
  exact rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    X I i n

/-- The forward map of the original global-sections comparison preserves addition. -/
lemma rationalSingularCochainHypercohomologyEquivGlobalSections_add
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) (α β : RationalSingularCochainHypercohomology X n) :
    rationalSingularCochainHypercohomologyEquivGlobalSections X n (α + β) =
      rationalSingularCochainHypercohomologyEquivGlobalSections X n α +
      rationalSingularCochainHypercohomologyEquivGlobalSections X n β :=
  (rationalSingularCochainHypercohomologyAddEquivGlobalSections X n).map_add α β

/-- The forward map of the original global-sections comparison preserves zero. -/
lemma rationalSingularCochainHypercohomologyEquivGlobalSections_zero
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    rationalSingularCochainHypercohomologyEquivGlobalSections X n 0 = 0 :=
  (rationalSingularCochainHypercohomologyAddEquivGlobalSections X n).map_zero

/-- The comparison from rational singular-cochain hypercohomology to ordinary singular
cohomology, bundled as an additive equivalence. -/
def rationalSingularCochainHypercohomologyAddEquivCohomology
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    RationalSingularCochainHypercohomology X (n : ℤ) ≃+
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint X)) n := by
  let Y := TopCat.of (ComplexPoint X)
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  exact (rationalSingularCochainHypercohomologyAddEquivGlobalSections
      X (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsSingularCochainComplexIntIsoExtend X)
        (n : ℤ)).addCommGroupIsoToAddEquiv |>.trans <|
      (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).addCommGroupIsoToAddEquiv
        |>.trans <|
        (AlgebraicTopology.Singular.HereditarilyParacompact.rationalSingularCohomologyEquivGlobalSections
          Y n).symm

/-- The forward map of the original hypercohomology-to-singular-cohomology comparison
preserves addition. -/
lemma rationalSingularCochainHypercohomologyEquivCohomology_add
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) (α β : RationalSingularCochainHypercohomology X (n : ℤ)) :
    rationalSingularCochainHypercohomologyEquivCohomology X n (α + β) =
      rationalSingularCochainHypercohomologyEquivCohomology X n α +
      rationalSingularCochainHypercohomologyEquivCohomology X n β :=
  (rationalSingularCochainHypercohomologyAddEquivCohomology X n).map_add α β

/-- The forward map of the original hypercohomology-to-singular-cohomology comparison
preserves zero. -/
lemma rationalSingularCochainHypercohomologyEquivCohomology_zero
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    rationalSingularCochainHypercohomologyEquivCohomology X n 0 = 0 :=
  (rationalSingularCochainHypercohomologyAddEquivCohomology X n).map_zero

/-- Rational constant-sheaf cohomology and rational singular cohomology are additively
equivalent. -/
def rationalCohomologyAddEquivSingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    FieldCohomology ℚ X (n : ℤ) ≃+
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint X)) n :=
  (rationalCohomologySingularCochainAddEquiv X (n : ℤ)).trans
    (rationalSingularCochainHypercohomologyAddEquivCohomology X n)

/-- The forward map of the original rational Betti comparison preserves addition. -/
lemma rationalCohomologyEquivSingularCohomology_add
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) (α β : FieldCohomology ℚ X (n : ℤ)) :
    rationalCohomologyEquivSingularCohomology X n (α + β) =
      rationalCohomologyEquivSingularCohomology X n α +
      rationalCohomologyEquivSingularCohomology X n β :=
  (rationalCohomologyAddEquivSingularCohomology X n).map_add α β

/-- The forward map of the original rational Betti comparison preserves zero. -/
lemma rationalCohomologyEquivSingularCohomology_zero
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    rationalCohomologyEquivSingularCohomology X n 0 = 0 :=
  (rationalCohomologyAddEquivSingularCohomology X n).map_zero

end AlgebraicGeometry.ComplexPoint
