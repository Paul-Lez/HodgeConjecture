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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportComparison
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainRestriction
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Naturality of the supported singular comparison

This file constructs restriction of singular cochains through direct image and proves its
naturality with sheafification. For a closed subset of a smooth complex-point space, it also
constructs a compatible quasi-isomorphism from singular cochains on the open complement to the
chosen injective resolution. The resulting morphism to the derived direct-image model is induced
by the restriction of singular cochains. This file does not yet identify its global-section
mapping cone with relative singular cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Filter TopologicalSpace

universe u


namespace AlgebraicGeometry.ComplexPoint

open Point

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))

lemma analyticComplement_contractibleOpenBasis
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    ∀ (x : TopCat.of ↥Zᶜ)
      (V : Opens (TopCat.of ↥Zᶜ)), x ∈ V →
      ∃ (W : Opens (TopCat.of ↥Zᶜ)),
        x ∈ W ∧ ContractibleSpace W ∧ W ≤ V :=
  contractibleOpenBasis_of_isOpenEmbedding
    (analyticComplementInclusion X Z)
    (analyticComplementInclusion_isOpenEmbedding X Z hZ)
    (exists_contractibleOpen_le X)

lemma complementConstantsToSingularCochain_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (constantsToSingularCochainSheafComplex ℚ
      (TopCat.of ↥Zᶜ)) :=
  constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ
    (analyticComplement_contractibleOpenBasis X Z hZ)

def complementConstantRationalSingleComplex
    (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticComplementAdditiveSheaf X Z) ℕ :=
  (CochainComplex.single₀ (AnalyticComplementAdditiveSheaf X Z)).obj
    𝓒(↧↥Zᶜ; ℚ)

def complementSingularCochainSheafComplex
    (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticComplementAdditiveSheaf X Z) ℕ :=
  singularCochainSheafComplex ℚ (TopCat.of ↥Zᶜ)

def complementConstantsToSingularCochain
    (Z : Set (ComplexPoint X)) :
    complementConstantRationalSingleComplex X Z ⟶
      complementSingularCochainSheafComplex X Z :=
  constantsToSingularCochainSheafComplex ℚ
    (TopCat.of ↥Zᶜ)

def complementConstantsToSingularCochainInt
    (Z : Set (ComplexPoint X)) :
    (complementConstantRationalSingleComplex X Z).extend
        ComplexShape.embeddingUpNat ⟶
      (complementSingularCochainSheafComplex X Z).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap
    (complementConstantsToSingularCochain X Z)
      ComplexShape.embeddingUpNat

lemma complementConstantsToSingularCochainInt_mono
    (Z : Set (ComplexPoint X)) :
    Mono (complementConstantsToSingularCochainInt X Z) :=
  constantsToSingularCochainComplexInt_mono ℚ
    (TopCat.of ↥Zᶜ)

lemma complementConstantsToSingularCochainInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (complementConstantsToSingularCochainInt X Z) :=
  (HomologicalComplex.quasiIso_extendMap_iff (complementConstantsToSingularCochain X Z)
    ComplexShape.embeddingUpNat).mpr (complementConstantsToSingularCochain_quasiIso X Z hZ)

def complementResolutionMapInt (Z : Set (ComplexPoint X)) :
    (complementConstantRationalSingleComplex X Z).extend
        ComplexShape.embeddingUpNat ⟶
      (complementConstantRationalInjectiveResolution X Z).cocomplex.extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap
    (complementConstantRationalInjectiveResolution X Z).ι
      ComplexShape.embeddingUpNat

set_option linter.style.haveILetI false in
def complementSingularToInjectiveResolutionInt
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    (complementSingularCochainSheafComplex X Z).extend
        ComplexShape.embeddingUpNat ⟶
      (complementConstantRationalInjectiveResolution X Z).cocomplex.extend
        ComplexShape.embeddingUpNat :=
  let a := complementConstantsToSingularCochainInt X Z
  let r := complementResolutionMapInt X Z
  let I := (complementConstantRationalInjectiveResolution X Z).cocomplex.extend
    ComplexShape.embeddingUpNat
  letI : Mono a := complementConstantsToSingularCochainInt_mono X Z
  letI : QuasiIso a :=
    complementConstantsToSingularCochainInt_quasiIso X Z hZ
  have hI : ∀ n : ℤ, Injective (I.X n) := fun n ↦ by
    dsimp [I]
    infer_instance
  CochainComplex.liftToInjective a r hI

set_option linter.style.haveILetI false in
lemma complementConstants_comp_singularToInjectiveResolutionInt
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    complementConstantsToSingularCochainInt X Z ≫
        complementSingularToInjectiveResolutionInt X Z hZ =
      complementResolutionMapInt X Z := by
  let a := complementConstantsToSingularCochainInt X Z
  let r := complementResolutionMapInt X Z
  let I := (complementConstantRationalInjectiveResolution X Z).cocomplex.extend
    ComplexShape.embeddingUpNat
  let : Mono a := complementConstantsToSingularCochainInt_mono X Z
  let : QuasiIso a :=
    complementConstantsToSingularCochainInt_quasiIso X Z hZ
  have hI : ∀ n : ℤ, Injective (I.X n) := fun n ↦ by
    dsimp [I]
    infer_instance
  exact CochainComplex.comp_liftToInjective a r hI

def complementSingularToInjectiveResolution
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    complementSingularCochainSheafComplex X Z ⟶
      (complementConstantRationalInjectiveResolution X Z).cocomplex :=
  (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor
    (AnalyticComplementAdditiveSheaf X Z)).preimage
      (complementSingularToInjectiveResolutionInt X Z hZ)

lemma complementConstants_comp_singularToInjectiveResolution
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    complementConstantsToSingularCochain X Z ≫
        complementSingularToInjectiveResolution X Z hZ =
      (complementConstantRationalInjectiveResolution X Z).ι := by
  let E := ComplexShape.embeddingUpNat.extendFunctor
    (AnalyticComplementAdditiveSheaf X Z)
  apply E.map_injective
  change HomologicalComplex.extendMap
      (complementConstantsToSingularCochain X Z ≫
        complementSingularToInjectiveResolution X Z hZ)
        ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      (complementConstantRationalInjectiveResolution X Z).ι
        ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp, show HomologicalComplex.extendMap
      (complementSingularToInjectiveResolution X Z hZ)
        ComplexShape.embeddingUpNat =
      complementSingularToInjectiveResolutionInt X Z hZ from
    (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor
      (AnalyticComplementAdditiveSheaf X Z)).map_preimage _]
  exact complementConstants_comp_singularToInjectiveResolutionInt
    X Z hZ

set_option linter.style.haveILetI false in
lemma complementSingularToInjectiveResolutionInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (complementSingularToInjectiveResolutionInt X Z hZ) := by
  let a := complementConstantsToSingularCochainInt X Z
  let b := complementSingularToInjectiveResolutionInt X Z hZ
  let r := complementResolutionMapInt X Z
  let : QuasiIso a :=
    complementConstantsToSingularCochainInt_quasiIso X Z hZ
  have hr : QuasiIso r := by
    apply (HomologicalComplex.quasiIso_extendMap_iff
      (complementConstantRationalInjectiveResolution X Z).ι
        ComplexShape.embeddingUpNat).mpr
    infer_instance
  have hab : a ≫ b = r :=
    complementConstants_comp_singularToInjectiveResolutionInt X Z hZ
  let : QuasiIso (a ≫ b) := hab ▸ hr
  exact quasiIso_of_comp_left a b

lemma complementSingularToInjectiveResolution_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (complementSingularToInjectiveResolution X Z hZ) := by
  apply (HomologicalComplex.quasiIso_extendMap_iff
    (complementSingularToInjectiveResolution X Z hZ)
      ComplexShape.embeddingUpNat).mp
  rw [show HomologicalComplex.extendMap
      (complementSingularToInjectiveResolution X Z hZ)
        ComplexShape.embeddingUpNat =
      complementSingularToInjectiveResolutionInt X Z hZ from
    (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor
      (AnalyticComplementAdditiveSheaf X Z)).map_preimage _]
  exact complementSingularToInjectiveResolutionInt_quasiIso X Z hZ

def naturalSingularResolutionRestrictionNat
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) ⟶
      derivedPushforwardComplementConstantRationalComplexNat X Z :=
  singularRestrictionSheafComplex ℚ
      (analyticComplementInclusion X Z) ≫
    ((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticComplementInclusion X Z)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
      (complementSingularToInjectiveResolution X Z hZ)

def naturalSingularResolutionRestriction
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    singularCochainSheafComplexInt X ℚ ⟶
      derivedPushforwardComplementConstantRationalComplexInt X Z :=
  HomologicalComplex.extendMap
    (naturalSingularResolutionRestrictionNat X Z hZ)
      ComplexShape.embeddingUpNat

end AlgebraicGeometry.ComplexPoint
