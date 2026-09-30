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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.Cohomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.CohomologyFlasqueModel

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-! # The supported injective model -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

variable (Z : Closeds (ComplexPoint X))

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
/-- Supported Ext is computed by sections of the supported injective model. -/
def rationalSupportAddEquivSupportedInjectiveHomology (n : ℕ) :
    TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) Z
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n ≃+
      (((TopCat.Sheaf.supportEvaluation ↧(ComplexPoint X) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
        (complexSupportInjectiveComplex X Z)).homology n :=
  @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology (TopCat.of (ComplexPoint X)) Z.compl ⊤
    Z.compl (top_inf_eq _) (analyticHasExt X) _ (ambientRationalInjectiveComplex X)
    (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n

section Rational

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The augmentation from rational constants to sheafified singular cochains. -/
def rationalSingularAugmentation :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(ComplexPoint X); ℚ) ⟶
      rationalSingularCochainComplex (TopCat.of (ComplexPoint X)) :=
  (constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫
    HomologicalComplex.extendMap
      (constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat

instance rationalSingularAugmentation_mono : Mono (rationalSingularAugmentation X) := by
  dsimp only [rationalSingularAugmentation]
  exact @mono_comp _ _ _ _ _ _ inferInstance _
    (constantsToSingularCochainComplexInt_mono ℚ (TopCat.of (ComplexPoint X)))

instance rationalSingularAugmentation_quasiIso : QuasiIso (rationalSingularAugmentation X) := by
  dsimp only [rationalSingularAugmentation]
  have h := HomologicalComplex.quasiIso_extendMap_iff
    (constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
    ComplexShape.embeddingUpNat
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _)
    (h.mpr (constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ
      (exists_contractibleOpen_le X)))

set_option maxHeartbeats 800000 in
/-- Supported Ext is naturally the local relative singular cohomology presheaf. -/
def rationalSupportCohomologyPresheafIsoRelative
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    TopCat.Sheaf.supportHOnOpenPresheaf
        (Z := S) ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ)) n ≅
      AlgebraicTopology.Singular.supportRelativeCohomologyPresheaf
        (TopCat.of (ComplexPoint X)) S n :=
  (TopCat.Sheaf.supportHOnOpenPresheafIsoOfFlasque
    (TopCat.of (ComplexPoint X)) S
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))
    (rationalSingularAugmentation X)
    (fun j => rationalSingularCochainComplex_isFlasque (TopCat.of (ComplexPoint X)) j) n).trans
    (AlgebraicTopology.Singular.supportedSingularCohomologyPresheafIsoRelative
      (TopCat.of (ComplexPoint X)) S S.isClosed n)

/-- Supported Ext is naturally the singular relative cohomology sheaf. -/
def rationalSupportCohomologySheafIsoRelative
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    TopCat.Sheaf.supportHCohomologySheaf
        (Z := S)
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ)) n ≅
      AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S n :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).mapIso
    (rationalSupportCohomologyPresheafIsoRelative X S n)

set_option maxHeartbeats 800000 in
/-- Supported Ext is the global section group of its cohomology sheaf in the lowest degree. -/
def rationalSupportAddEquivSupportedCohomologySheafSection
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero
      (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S j)) :
    TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ)) n ≃+
      (TopCat.Sheaf.supportHCohomologySheaf
        (Z := S)
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ)) n).presheaf.obj (op ⊤) :=
  TopCat.Sheaf.supportHCohomologySheafSectionAddEquivOfFlasque
    (TopCat.of (ComplexPoint X)) S
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))
    (rationalSingularAugmentation X)
    (fun j => rationalSingularCochainComplex_isFlasque (TopCat.of (ComplexPoint X)) j)
    (fun j => AlgebraicTopology.Singular.supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint X)) S j)
    (fun j => AlgebraicTopology.Singular.supportedSingularCohomologySheafIsoRelative
      (TopCat.of (ComplexPoint X)) S S.isClosed j)
    n hH

set_option maxHeartbeats 800000 in
/-- Supported Ext is the global section group of the singular cohomology sheaf. -/
def rationalSupportAddEquivSupportedRelativeCohomologySheafSection
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero
      (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S j)) :
    TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ)) n ≃+
      (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S n).presheaf.obj (op ⊤) :=
  (rationalSupportAddEquivSupportedCohomologySheafSection X S n hH).trans
    ((rationalSupportCohomologySheafIsoRelative X S n).hom.hom.app (op ⊤)).toAddCommGrpIso
      .addCommGroupIsoToAddEquiv

set_option maxHeartbeats 800000 in
/-- Supported Ext on an open is the corresponding singular cohomology-sheaf section group. -/
def rationalSupportAddEquivSupportedRelativeCohomologySheafSectionOnOpen
    (S : Closeds (ComplexPoint X)) (V W : Opens (ComplexPoint X))
    (hW : V ⊓ S.compl = W) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero
      ((V.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
          (TopCat.of (ComplexPoint X)) S j))) :
    CategoryTheory.Sheaf.relH
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
        n (homOfLE (hW ▸ inf_le_left : W ≤ V)) ≃+
      (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S n).presheaf.obj (op V) :=
  (TopCat.Sheaf.supportHCohomologySheafSectionAddEquivOfFlasqueOnOpen
    (TopCat.of (ComplexPoint X)) S
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))
    (rationalSingularAugmentation X)
    (fun j => rationalSingularCochainComplex_isFlasque (TopCat.of (ComplexPoint X)) j)
    (fun j => AlgebraicTopology.Singular.supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint X)) S j)
    (fun j => AlgebraicTopology.Singular.supportedSingularCohomologySheafIsoRelative
      (TopCat.of (ComplexPoint X)) S S.isClosed j)
    V W hW n hH).trans
    ((rationalSupportCohomologySheafIsoRelative X S n).hom.hom.app (op V)).toAddCommGrpIso
      .addCommGroupIsoToAddEquiv

@[simp]
theorem rationalSupportAddEquivSupportedRelativeCohomologySheafSection_apply
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero
      (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S j))
    (z : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    rationalSupportAddEquivSupportedRelativeCohomologySheafSection X S n hH z =
      (rationalSupportCohomologySheafIsoRelative X S n).hom.hom.app (op ⊤)
        (TopCat.Sheaf.supportHToSupportHCohomologySheafSection
          (Z := S)
          ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
            (AddCommGrpCat.of ℚ)) n z) := by
  rfl

/-- The injective-model cohomology sheaf is the supported singular cohomology sheaf. -/
def complexSupportInjectiveCohomologySheafIsoRelative
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    (complexSupportInjectiveComplex X S).homology (n : ℤ) ≅
      AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S n :=
  letI : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  (asIso (HomologicalComplex.homologyMap
    (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).symm ≪≫
      supportedSingularCohomologySheafIsoRelative
        (TopCat.of (ComplexPoint X)) S S.isClosed n

/-- Restriction carries the injective-model cohomology sheaf to the supported cohomology sheaf. -/
def complexSupportInjectiveCohomologySheafIsoRelative_restrict
    (S : Closeds (ComplexPoint X)) (V : Opens (ComplexPoint X)) (n : ℕ) :
    (((V.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).obj
      (complexSupportInjectiveComplex X S)).homology (n : ℤ) ≅
      (V.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
          (TopCat.of (ComplexPoint X)) S n) :=
  by
    let K := complexSupportInjectiveComplex X S
    let F := (TopologicalSpace.Opens.isOpenEmbedding
      (X := TopCat.of (ComplexPoint X)) V).sheafPullback AddCommGrpCat
    let L := (F.mapHomologicalComplex ℤᵘᵖ).obj K
    change L.homology (n : ℤ) ≅ F.obj
      (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S n)
    exact (K.sc (n : ℤ)).mapHomologyIso F ≪≫
      (V.isOpenEmbedding.sheafPullback AddCommGrpCat).mapIso
        (complexSupportInjectiveCohomologySheafIsoRelative X S n)

end Rational

end AlgebraicGeometry.ComplexPoint

end
