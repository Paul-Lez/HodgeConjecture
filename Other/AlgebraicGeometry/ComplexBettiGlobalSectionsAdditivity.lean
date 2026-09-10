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

public import Other.AlgebraicGeometry.ComplexBettiGlobalSectionsComparison

/-!
# Additivity of the complex Betti global-sections comparison

This file upgrades the complex Betti comparison equivalences to additive equivalences.  The
group law on hypercohomology is transported from morphisms in the derived category, so
additivity of the localized-Hom steps is checked after applying the defining equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The complex constant-to-singular-cochain comparison, bundled additively. -/
def complexCohomologySingularCochainAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ComplexConstantCohomology X n ≃+
      ComplexSingularCochainHypercohomology X n where
  toEquiv := complexCohomologySingularCochainEquiv X n
  map_add' α β :=
    (hypercohomologyMap X
      (complexToSingularCochainComplexInt X) n).map_add α β

local instance bettiGlobalSectionsAdditivityHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

set_option maxHeartbeats 800000 in
/-- The comparison with global sections is additive when computed from a K-injective
resolution whose global-sections map is a quasi-isomorphism. -/
def complexSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℂ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    ComplexSingularCochainHypercohomology X n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℂ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let A := constantIntegerSheafComplexInt X
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let S := singularCochainSheafComplexInt X ℂ
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
  let ae₁ : ComplexSingularCochainHypercohomology X n ≃+
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
def complexSingularCochainHypercohomologyAddEquivGlobalSections
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    ComplexSingularCochainHypercohomology X n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℂ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X ℂ
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
    fun q ↦ complexSingularCochainSheafComplexInt_isFlasque X q
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hSflasque hIflasque
  exact complexSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    X I i n

/-- The forward map of the original global-sections comparison preserves addition. -/
lemma complexSingularCochainHypercohomologyEquivGlobalSections_add
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) (α β : ComplexSingularCochainHypercohomology X n) :
    complexSingularCochainHypercohomologyEquivGlobalSections X n (α + β) =
      complexSingularCochainHypercohomologyEquivGlobalSections X n α +
      complexSingularCochainHypercohomologyEquivGlobalSections X n β :=
  (complexSingularCochainHypercohomologyAddEquivGlobalSections X n).map_add α β

/-- The forward map of the original global-sections comparison preserves zero. -/
lemma complexSingularCochainHypercohomologyEquivGlobalSections_zero
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    complexSingularCochainHypercohomologyEquivGlobalSections X n 0 = 0 :=
  (complexSingularCochainHypercohomologyAddEquivGlobalSections X n).map_zero

/-- The comparison from complex singular-cochain hypercohomology to ordinary singular
cohomology, bundled as an additive equivalence. -/
def complexSingularCochainHypercohomologyAddEquivCohomology
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    ComplexSingularCochainHypercohomology X (n : ℤ) ≃+
      AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint X)) n := by
  let Y := TopCat.of (ComplexPoint X)
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  exact (complexSingularCochainHypercohomologyAddEquivGlobalSections
      X (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsComplexSingularCochainComplexIntIsoExtend X)
        (n : ℤ)).addCommGroupIsoToAddEquiv |>.trans <|
      (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).addCommGroupIsoToAddEquiv
        |>.trans <|
        (AlgebraicTopology.Singular.HereditarilyParacompact.complexSingularCohomologyEquivGlobalSections
          Y n).symm

/-- The forward map of the original hypercohomology-to-singular-cohomology comparison
preserves addition. -/
lemma complexSingularCochainHypercohomologyEquivCohomology_add
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) (α β : ComplexSingularCochainHypercohomology X (n : ℤ)) :
    complexSingularCochainHypercohomologyEquivCohomology X n (α + β) =
      complexSingularCochainHypercohomologyEquivCohomology X n α +
      complexSingularCochainHypercohomologyEquivCohomology X n β :=
  (complexSingularCochainHypercohomologyAddEquivCohomology X n).map_add α β

/-- The forward map of the original hypercohomology-to-singular-cohomology comparison
preserves zero. -/
lemma complexSingularCochainHypercohomologyEquivCohomology_zero
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    complexSingularCochainHypercohomologyEquivCohomology X n 0 = 0 :=
  (complexSingularCochainHypercohomologyAddEquivCohomology X n).map_zero

/-- Complex constant-sheaf cohomology and complex singular cohomology are additively
equivalent. -/
def complexCohomologyAddEquivSingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    FieldCohomology ℂ X (n : ℤ) ≃+
      AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint X)) n :=
  (complexCohomologySingularCochainAddEquiv X (n : ℤ)).trans
    (complexSingularCochainHypercohomologyAddEquivCohomology X n)

/-- The forward map of the original complex Betti comparison preserves addition. -/
lemma complexCohomologyEquivSingularCohomology_add
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) (α β : FieldCohomology ℂ X (n : ℤ)) :
    complexCohomologyEquivSingularCohomology X n (α + β) =
      complexCohomologyEquivSingularCohomology X n α +
      complexCohomologyEquivSingularCohomology X n β :=
  (complexCohomologyAddEquivSingularCohomology X n).map_add α β

/-- The forward map of the original complex Betti comparison preserves zero. -/
lemma complexCohomologyEquivSingularCohomology_zero
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    complexCohomologyEquivSingularCohomology X n 0 = 0 :=
  (complexCohomologyAddEquivSingularCohomology X n).map_zero

end AlgebraicGeometry.ComplexPoint


