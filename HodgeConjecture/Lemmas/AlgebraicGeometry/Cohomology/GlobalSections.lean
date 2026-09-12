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

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Taking global sections commutes with extending the natural-number-indexed singular-cochain
sheaf complex by zero to integer degrees. -/
def globalSectionsSingularCochainComplexIntIsoExtend :
    TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ) ≅
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X))).extend
          ComplexShape.embeddingUpNat := by
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let G := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let K := AlgebraicTopology.Singular.singularCochainSheafComplex ℚ Y
  let : F.Additive := by dsimp [F]; infer_instance
  let : E.Additive := by dsimp [E]; infer_instance
  let eComp : F ⋙ E ≅ G := Iso.refl _
  exact HomologicalComplex.mapExtendCanonicalIso G K ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
      ((Functor.mapHomologicalComplexCompIso eComp (ComplexShape.up ℕ)).app K).symm

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
  choose I i _ _ _ using
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S 0
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

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular

universe u

variable (R : Type u) [Field R] (Y : TopCat.{u})

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
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y).homology n := by
  let := AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_quasiIso
    (Y := Y)
  exact
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
