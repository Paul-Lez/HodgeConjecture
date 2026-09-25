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

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyInjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FlasqueComparison
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
public import HodgeConjecture.Mathlib.Algebra.Homology.LiftToInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Cohomology with support computed by a flasque resolution

For a bounded-below resolution `F → K` by flasque sheaves, `H^n(V, V ⊓ U; F)` is the cohomology
of the supported sections `Γ_{X ∖ U}(V, K)`. The proof compares `K` with a chosen injective
resolution of `F`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian Opposite TopologicalSpace

namespace TopCat.Sheaf

variable (X : TopCat.{0}) (F : Sheaf AddCommGrpCat X)

set_option backward.isDefEq.respectTransparency false in
/-- A chosen injective resolution `I` of `F`, indexed by integers. -/
def injectiveResolutionComplex : CochainComplex (Sheaf AddCommGrpCat X) ℤ :=
  (injectiveResolution (C := Sheaf AddCommGrpCat.{0} X) F).cocomplex.extend
    ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation `F[0] → I`. -/
def injectiveResolutionAugmentation :
    (CochainComplex.singleFunctor _ 0).obj F ⟶ injectiveResolutionComplex X F :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
    HomologicalComplex.extendMap (injectiveResolution (C := Sheaf AddCommGrpCat.{0} X) F).ι
      ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
instance injectiveResolutionComplex_injective (q : ℤ) :
    Injective ((injectiveResolutionComplex X F).X q) :=
  CochainComplex.injective_extend_nat _
    (injectiveResolution (C := Sheaf AddCommGrpCat.{0} X) F).injective q

instance injectiveResolutionComplex_isStrictlyGE :
    (injectiveResolutionComplex X F).IsStrictlyGE 0 := by
  dsimp only [injectiveResolutionComplex]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance injectiveResolutionAugmentation_quasiIso :
    QuasiIso (injectiveResolutionAugmentation X F) := by
  dsimp only [injectiveResolutionAugmentation]
  have : QuasiIso (HomologicalComplex.extendMap
      (injectiveResolution (C := Sheaf AddCommGrpCat.{0} X) F).ι ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr inferInstance
  infer_instance

local instance : HasDerivedCategory (Sheaf AddCommGrpCat X) :=
  HasDerivedCategory.standard _

instance injectiveResolutionComplex_isKInjective :
    (injectiveResolutionComplex X F).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

variable (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ) [K.IsStrictlyGE 0]
  (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ K) [Mono ι] [QuasiIso ι]

/-- A chosen map `K → I` under `F[0]`. -/
def resolutionToInjective : K ⟶ injectiveResolutionComplex X F :=
  CochainComplex.liftToInjective ι (injectiveResolutionAugmentation X F) (fun _ => inferInstance)

lemma comp_resolutionToInjective :
    ι ≫ resolutionToInjective X F K ι = injectiveResolutionAugmentation X F :=
  CochainComplex.comp_liftToInjective ι _ _

instance resolutionToInjective_quasiIso : QuasiIso (resolutionToInjective X F K ι) := by
  have : QuasiIso (ι ≫ resolutionToInjective X F K ι) := by
    rw [comp_resolutionToInjective]
    infer_instance
  exact quasiIso_of_comp_left ι _

variable (U V W : Opens X) (hW : V ⊓ U = W) (hK : ∀ n, IsFlasque (K.X n))

include hK in
lemma supportedSections_map_resolutionToInjective_quasiIso :
    QuasiIso (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
      (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
        (resolutionToInjective X F K ι))) :=
  supportedSections_map_quasiIso_of_flasque X U V (resolutionToInjective X F K ι) 0 0 hK
    (fun _ => injective_isFlasque X _)

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

/-- `H^n(V, W; F) ≃ H^n(Γ_{X ∖ U}(V, K))` for a bounded-below flasque resolution `F[0] → K`. -/
def relHAddEquivSupportedSectionsHomologyOfFlasque (n : ℕ) :
    CategoryTheory.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V)) ≃+
      (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj K)).homology n :=
  haveI := supportedSections_map_resolutionToInjective_quasiIso X F K ι U V hK
  (@relHAddEquivSupportedSectionsHomology X U V W hW _ F (injectiveResolutionComplex X F)
    (injectiveResolutionComplex_isKInjective X F) (injectiveResolutionAugmentation X F)
    (injectiveResolutionAugmentation_quasiIso X F) n).trans
    (asIso (HomologicalComplex.homologyMap (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
      (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
        (resolutionToInjective X F K ι))) n)).symm.addCommGroupIsoToAddEquiv

end TopCat.Sheaf

end
