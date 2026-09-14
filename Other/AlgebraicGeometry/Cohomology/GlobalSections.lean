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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections

/-!
# Constructions used only in proofs

These were built to prove the results about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections`.
The statement of the conjecture never inspects them: every path from the statement to one
of them runs through a proof, so proof irrelevance makes their bodies immaterial.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace



namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

attribute [local instance] bettiGlobalSectionsHasDerivedCategory

local instance bettiGlobalSectionsAddCommGrpHasDerivedCategory :
    HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard AddCommGrpCat

/-- Every integer-indexed term of the singular-cochain resolution is flasque on a hereditarily
paracompact Hausdorff complex-point space. Negative terms are zero, and nonnegative terms are
the corresponding natural-number-indexed singular-cochain sheaves. -/
theorem singularCochainSheafComplexInt_isFlasque
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((singularCochainSheafComplexInt X ℚ).X n) := by
  by_cases hn : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hn
    let e := (AlgebraicTopology.Singular.singularCochainSheafComplex ℚ
      (TopCat.of (ComplexPoint X))).extendXIso
        ComplexShape.embeddingUpNat (i := m) rfl
    let hP : TopCat.Presheaf.IsFlasque
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℚ
          (TopCat.of (ComplexPoint X))).X m).obj := by
      change TopCat.Sheaf.IsFlasque
        (AlgebraicTopology.Singular.singularCochainSheaf ℚ
          (TopCat.of (ComplexPoint X)) m)
      infer_instance
    change TopCat.Presheaf.IsFlasque
      ((singularCochainSheafComplexInt X ℚ).X (m : ℤ)).obj
    exact @AlgebraicTopology.Singular.presheaf_isFlasque_of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapIso e.symm) hP
  · apply TopCat.Sheaf.IsFlasque.of_isZero
    exact (AlgebraicTopology.Singular.singularCochainSheafComplex ℚ
      (TopCat.of (ComplexPoint X))).isZero_extend_X
        ComplexShape.embeddingUpNat n (fun i hi ↦ hn ⟨i, hi⟩)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Taking global sections commutes with extending the natural-number-indexed singular-cochain
sheaf complex by zero to integer degrees. -/
def globalSectionsSingularCochainComplexIntIsoExtend :
    TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ) ≅
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X))).extend
          ComplexShape.embeddingUpNat :=
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let G := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let K := AlgebraicTopology.Singular.singularCochainSheafComplex ℚ Y
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : E.Additive := by dsimp [E]; infer_instance
  let eComp : F ⋙ E ≅ G := Iso.refl _
  HomologicalComplex.mapExtendCanonicalIso G K ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
      ((Functor.mapHomologicalComplexCompIso eComp (ComplexShape.up ℕ)).app K).symm

/-- The comparison with global sections is additive when computed from a K-injective
resolution whose global-sections map is a quasi-isomorphism. -/
def rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsStrictlyGE 0] [∀ q, Injective (I.X q)]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    RationalSingularCochainHypercohomology X n ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ)).homology n :=
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X ℚ
  let Splus : CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
    ⟨S, ⟨0, inferInstance⟩⟩
  let Iplus : CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
    ⟨I, ⟨0, inferInstance⟩⟩
  let f : Splus ⟶ Iplus := ⟨i⟩
  let F := analyticHypercohomologyFunctor X n
  let _ : IsIso (DerivedCategory.Plus.Q.map f) := inferInstance
  let _ : IsIso (F.map f) := by
    dsimp only [F, Functor.comp_map]
    infer_instance
  let e₁ := (asIso (F.map f)).addCommGroupIsoToAddEquiv
  let e₂ := (TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat Y Iplus n)
    |>.addCommGroupIsoToAddEquiv
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let _ : QuasiIso ((Γ.mapHomologicalComplex (.up ℤ)).map i) := inferInstance
  let e₃ := (asIso (HomologicalComplex.homologyMap
    ((Γ.mapHomologicalComplex (.up ℤ)).map i) n)).symm.addCommGroupIsoToAddEquiv
  e₁.trans (e₂.trans e₃)

/-- The canonical hypercohomology comparison with the global-section complex, bundled as an
additive equivalence. -/
def rationalSingularCochainHypercohomologyAddEquivGlobalSections
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    RationalSingularCochainHypercohomology X n ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ)).homology n :=
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X ℚ
  letI : S.IsStrictlyGE 0 := by
    dsimp [S, singularCochainSheafComplexInt]
    infer_instance
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S 0
  let I := hres.choose
  let i := hres.choose_spec.choose
  haveI : QuasiIso i := hres.choose_spec.choose_spec.choose
  haveI : ∀ q, Injective (I.X q) := hres.choose_spec.choose_spec.choose_spec.choose
  haveI : I.IsStrictlyGE 0 := hres.choose_spec.choose_spec.choose_spec.choose_spec
  haveI : I.IsKInjective := CochainComplex.isKInjective_of_injective I 0
  have hSflasque : ∀ q, (S.X q).IsFlasque :=
    fun q ↦ singularCochainSheafComplexInt_isFlasque X q
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  haveI : QuasiIso
      (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hSflasque hIflasque
  rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    X I i n

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular

universe u

variable (R : Type u) [CommRing R] (Y : TopCat.{u})

/-- Forgetting scalar multiplication commutes with taking the homology of the top-open singular
cochain complex. -/
def topOpenForgottenSingularCochainHomologyIso (n : ℕ) :
    (topOpenForgottenSingularCochainComplex R Y).homology n ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat).obj
        ((TopOpenSingularChainComplex R Y).linearDualCochainComplex.homology n) :=
  ShortComplex.mapHomologyIso
    ((TopOpenSingularChainComplex R Y).linearDualCochainComplex.sc n)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat)

/-- Ordinary singular cohomology agrees with the homology of the raw singular-cochain
presheaf evaluated on the top open subset. -/
def ordinarySingularCohomologyEquivGlobalRaw (n : ℕ) :
    Cohomology R Y n ≃+
      (globalRawSingularCochainComplex R Y).homology n :=
  ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapIso
      (HomologicalComplex.homologyMapIso
        (singularCochainComplexIsoTopOpen R Y) n)).addCommGroupIsoToAddEquiv |>.trans <|
    (topOpenForgottenSingularCochainHomologyIso R Y n).symm.addCommGroupIsoToAddEquiv |>.trans <|
      (HomologicalComplex.homologyMapIso
        (globalRawSingularCochainComplexIso R Y) n).symm.addCommGroupIsoToAddEquiv

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular.HereditarilyParacompact

/-- On a paracompact Hausdorff space, rational singular cohomology is the cohomology of the
global-section complex of the chosen singular-cochain sheaf resolution. -/
def ordinaryRationalSingularCohomologyEquivGlobalSections
    (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y] (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology ℚ Y n ≃+
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y).homology n :=
  letI := AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_quasiIso
    (Y := Y)
  AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℚ Y n |>.trans <|
    (asIso (HomologicalComplex.homologyMap
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℚ Y) n))
        |>.addCommGroupIsoToAddEquiv

end AlgebraicTopology.Singular.HereditarilyParacompact

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The comparison from rational singular-cochain hypercohomology to ordinary singular
cohomology, bundled as an additive equivalence. -/
def rationalSingularCochainHypercohomologyAddEquivCohomology
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    RationalSingularCochainHypercohomology X (n : ℤ) ≃+
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint X)) n :=
  let Y := TopCat.of (ComplexPoint X)
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  (rationalSingularCochainHypercohomologyAddEquivGlobalSections
      X (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsSingularCochainComplexIntIsoExtend X)
        (n : ℤ)).addCommGroupIsoToAddEquiv |>.trans <|
      (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).addCommGroupIsoToAddEquiv
        |>.trans <|
        (AlgebraicTopology.Singular.HereditarilyParacompact.ordinaryRationalSingularCohomologyEquivGlobalSections
          Y n).symm

/-- Rational constant-sheaf cohomology and rational singular cohomology are additively
equivalent. -/
def rationalCohomologyAddEquivSingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    H^(n : ℤ)(X; ℚ) ≃+
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint X)) n :=
  (rationalCohomologySingularCochainAddEquiv X (n : ℤ)).trans
    (rationalSingularCochainHypercohomologyAddEquivCohomology X n)

end AlgebraicGeometry.ComplexPoint
