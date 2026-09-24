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

public import Other.AlgebraicGeometry.Cohomology.SupportHypercohomology

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra

namespace AlgebraicGeometry.ComplexPoint

open Point
open AlgebraicTopology.Singular

universe u v

variable (X : Over (Spec ↧ℂ))

attribute [local instance] bettiSupportHypercohomologyComparisonHasDerivedCategory
attribute [local instance] bettiSupportHypercohomologyAddCommGrpHasDerivedCategory

/-- If a K-injective resolution of a sheaf complex remains a quasi-isomorphism after taking
global sections, then hypercohomology is computed by the original global-section complex. -/
def hypercohomologyEquivGlobalSectionsOfResolution
    (K I : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective]
    (i : K ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    Hypercohomology X K n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) K).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let A := constantIntegerSheafComplexInt X
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
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

/-- Hypercohomology of a bounded-below termwise-flasque sheaf complex is computed by its
global-section complex. The proof uses an explicit bounded-below injective replacement. -/
def hypercohomologyEquivGlobalSections
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (N : ℤ) [K.IsStrictlyGE N]
    (hKflasque : ∀ q, (K.X q).IsFlasque) (n : ℤ) :
    Hypercohomology X K n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) K).homology n := by
  let Y := TopCat.of (ComplexPoint X)
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
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i N N hKflasque hIflasque
  exact hypercohomologyEquivGlobalSectionsOfResolution X K I i n

/-- Replacing rational constants by the natural singular resolution identifies the two support
hypercohomology groups. -/
def rationalSupportHypercohomologyEquivNaturalSingularCone
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃
      Hypercohomology X
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction X Z hZ)) (n - 1) :=
  Localization.SmallShiftedHom.postcompEquiv
    (rationalSupportConeToNaturalSingularCone X Z hZ)
    (rationalSupportConeToNaturalSingularCone_quasiIso X Z hZ)

/-- Rational constant-sheaf cohomology with support is computed by global sections of the
natural singular support cone. -/
def rationalSupportHypercohomologyEquivNaturalSingularConeGlobalSections
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (CochainComplex.mappingCone
          (naturalSingularResolutionRestriction X Z hZ))).homology (n - 1) := by
  let K := CochainComplex.mappingCone
    (naturalSingularResolutionRestriction X Z hZ)
  letI : K.IsStrictlyGE (-1) :=
    naturalSingularSupportCone_isStrictlyGE X Z hZ
  exact (rationalSupportHypercohomologyEquivNaturalSingularCone
      X Z hZ n).trans
    (hypercohomologyEquivGlobalSections X K (-1)
      (naturalSingularSupportCone_term_isFlasque X Z hZ) (n - 1))

/-- Rational constant-sheaf cohomology with closed support agrees with rational singular
cohomology with the same support. -/
def rationalCohomologyWithSupportEquivSingular
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℕ) :
    RationalCohomologyWithSupport X Z (n : ℤ) ≃
      CohomologyWithSupport ℚ
        (TopCat.of (ComplexPoint X)) Z n :=
  (rationalSupportHypercohomologyEquivNaturalSingularConeGlobalSections
      X Z hZ (n : ℤ)).trans <|
    ((HomologicalComplex.homologyMapIso
      (globalSectionsNaturalSingularConeIsoMappingCone
        X Z hZ) ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv.toEquiv).trans <|
    ((asIso (HomologicalComplex.homologyMap
      (globalRawSupportConeToGlobalNaturalSingularCone
        X Z hZ) ((n : ℤ) - 1))).symm.addCommGroupIsoToAddEquiv.toEquiv).trans <|
    (globalRawSingularRestrictionConeCohomologyEquivSupport ℚ
      (TopCat.of (ComplexPoint X)) Z n).toEquiv

end AlgebraicGeometry.ComplexPoint
