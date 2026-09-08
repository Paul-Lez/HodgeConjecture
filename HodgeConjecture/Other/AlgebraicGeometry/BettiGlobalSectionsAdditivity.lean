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

public import HodgeConjecture.Other.AlgebraicGeometry.BettiGlobalSectionsComparison

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

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

local instance bettiGlobalSectionsAdditivityHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf structureMap) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf structureMap)

set_option maxHeartbeats 800000 in
/-- The comparison with global sections is additive when computed from a K-injective
resolution whose global-sections map is a quasi-isomorphism. -/
def rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    (I : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ)
    [I.IsKInjective]
    (i : singularCochainSheafComplexInt structureMap ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint (Over.mk structureMap)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    RationalSingularCochainHypercohomology structureMap n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap)))
        (singularCochainSheafComplexInt structureMap ℚ)).homology n := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let A := constantIntegerSheafComplexInt structureMap
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let S := singularCochainSheafComplexInt structureMap ℚ
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
    (X := A) (Y := S) (Z := I) (a := n) i hi
  let e₂ := Localization.SmallShiftedHom.precompEquiv
    (X := A') (Y := A) (Z := I) (a := n) e.inv he
  letI : AddCommGroup (Localization.SmallShiftedHom
      (analyticQuasiIsomorphisms structureMap) A' I n) :=
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q).addCommGroup
  have localizedEquiv_add (α β : Localization.SmallShiftedHom
      (analyticQuasiIsomorphisms structureMap) A' I n) :
      (Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q) (α + β) =
        (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q) α +
        (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q) β := by
    simp [Equiv.add_def]
  let ae₁ : RationalSingularCochainHypercohomology structureMap n ≃+
      Hypercohomology structureMap I n :=
    { toEquiv := e₁
      map_add' := by
        intro α β
        apply (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q).injective
        rw [hypercohomologyEquiv_add structureMap I n]
        dsimp only [e₁, Localization.SmallShiftedHom.postcompEquiv]
        simp only [Localization.SmallShiftedHom.equiv_comp]
        rw [hypercohomologyEquiv_add structureMap S n]
        rw [CategoryTheory.ShiftedHom.add_comp] }
  let ae₂ : Hypercohomology structureMap I n ≃+
      Localization.SmallShiftedHom
        (analyticQuasiIsomorphisms structureMap) A' I n :=
    { toEquiv := e₂
      map_add' := by
        intro α β
        apply (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q).injective
        rw [localizedEquiv_add]
        dsimp only [e₂, Localization.SmallShiftedHom.precompEquiv]
        simp only [Localization.SmallShiftedHom.equiv_comp]
        rw [hypercohomologyEquiv_add structureMap I n]
        rw [CategoryTheory.ShiftedHom.comp_add] }
  let ae₃' : CochainComplex.HomComplex.CohomologyClass A' I n ≃+
      Localization.SmallShiftedHom
        (analyticQuasiIsomorphisms structureMap) A' I n :=
    { toEquiv := CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
      map_add' := by
        intro α β
        change
          CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom (α + β) =
            CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom α +
            CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom β
        apply (Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q).injective
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
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (n : ℤ) :
    RationalSingularCochainHypercohomology structureMap n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint (Over.mk structureMap)))
        (singularCochainSheafComplexInt structureMap ℚ)).homology n := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let S := singularCochainSheafComplexInt structureMap ℚ
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
  have hSflasque : ∀ q, (S.X q).IsFlasque := by
    intro q
    dsimp [S]
    exact singularCochainSheafComplexInt_isFlasque structureMap q
  have hIflasque : ∀ q, (I.X q).IsFlasque := by
    intro q
    infer_instance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hSflasque hIflasque
  exact rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    structureMap I i n

/-- The forward map of the original global-sections comparison preserves addition. -/
lemma rationalSingularCochainHypercohomologyEquivGlobalSections_add
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (n : ℤ) (α β : RationalSingularCochainHypercohomology structureMap n) :
    rationalSingularCochainHypercohomologyEquivGlobalSections structureMap n (α + β) =
      rationalSingularCochainHypercohomologyEquivGlobalSections structureMap n α +
      rationalSingularCochainHypercohomologyEquivGlobalSections structureMap n β := by
  exact (rationalSingularCochainHypercohomologyAddEquivGlobalSections
    structureMap n).map_add α β

/-- The forward map of the original global-sections comparison preserves zero. -/
lemma rationalSingularCochainHypercohomologyEquivGlobalSections_zero
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (n : ℤ) :
    rationalSingularCochainHypercohomologyEquivGlobalSections structureMap n 0 = 0 := by
  exact (rationalSingularCochainHypercohomologyAddEquivGlobalSections
    structureMap n).map_zero

/-- The comparison from rational singular-cochain hypercohomology to ordinary singular
cohomology, bundled as an additive equivalence. -/
def rationalSingularCochainHypercohomologyAddEquivCohomology
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (n : ℕ) :
    RationalSingularCochainHypercohomology structureMap (n : ℤ) ≃+
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint (Over.mk structureMap))) n := by
  let Y := TopCat.of (ComplexPoint (Over.mk structureMap))
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y
  letI : ParacompactSpace (ComplexPoint (Over.mk structureMap)) :=
    (Homeomorph.Set.univ (ComplexPoint (Over.mk structureMap))).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint (Over.mk structureMap))))
  exact (rationalSingularCochainHypercohomologyAddEquivGlobalSections
      structureMap (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsSingularCochainComplexIntIsoExtend structureMap)
        (n : ℤ)).addCommGroupIsoToAddEquiv |>.trans <|
      (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).addCommGroupIsoToAddEquiv
        |>.trans <|
        (AlgebraicTopology.Singular.HereditarilyParacompact.rationalSingularCohomologyEquivGlobalSections
          Y n).symm

/-- The forward map of the original hypercohomology-to-singular-cohomology comparison
preserves addition. -/
lemma rationalSingularCochainHypercohomologyEquivCohomology_add
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (n : ℕ) (α β : RationalSingularCochainHypercohomology structureMap (n : ℤ)) :
    rationalSingularCochainHypercohomologyEquivCohomology structureMap n (α + β) =
      rationalSingularCochainHypercohomologyEquivCohomology structureMap n α +
      rationalSingularCochainHypercohomologyEquivCohomology structureMap n β := by
  exact (rationalSingularCochainHypercohomologyAddEquivCohomology
    structureMap n).map_add α β

/-- The forward map of the original hypercohomology-to-singular-cohomology comparison
preserves zero. -/
lemma rationalSingularCochainHypercohomologyEquivCohomology_zero
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (n : ℕ) :
    rationalSingularCochainHypercohomologyEquivCohomology structureMap n 0 = 0 := by
  exact (rationalSingularCochainHypercohomologyAddEquivCohomology
    structureMap n).map_zero

/-- Rational constant-sheaf cohomology and rational singular cohomology are additively
equivalent. -/
def rationalCohomologyAddEquivSingularCohomology
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (n : ℕ) :
    FieldCohomology ℚ structureMap (n : ℤ) ≃+
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint (Over.mk structureMap))) n :=
  (rationalCohomologySingularCochainAddEquiv structureMap (n : ℤ)).trans
    (rationalSingularCochainHypercohomologyAddEquivCohomology structureMap n)

/-- The forward map of the original rational Betti comparison preserves addition. -/
lemma rationalCohomologyEquivSingularCohomology_add
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (n : ℕ) (α β : FieldCohomology ℚ structureMap (n : ℤ)) :
    rationalCohomologyEquivSingularCohomology structureMap n (α + β) =
      rationalCohomologyEquivSingularCohomology structureMap n α +
      rationalCohomologyEquivSingularCohomology structureMap n β := by
  exact (rationalCohomologyAddEquivSingularCohomology
    structureMap n).map_add α β

/-- The forward map of the original rational Betti comparison preserves zero. -/
lemma rationalCohomologyEquivSingularCohomology_zero
    [IsIntegral X] [Smooth structureMap]
    [T2Space (ComplexPoint (Over.mk structureMap))]
    [∀ U : Opens (ComplexPoint (Over.mk structureMap)), ParacompactSpace U]
    (n : ℕ) :
    rationalCohomologyEquivSingularCohomology structureMap n 0 = 0 := by
  exact (rationalCohomologyAddEquivSingularCohomology
    structureMap n).map_zero

end AlgebraicGeometry.ComplexPoint
