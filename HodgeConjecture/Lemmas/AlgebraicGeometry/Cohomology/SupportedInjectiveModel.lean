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

/-- For a closed support `S`, this is the complex `Γ_S(I^•)` of subsheaves of the ambient rational
injective resolution `I^•` whose sections vanish outside `S`. -/
def complexSupportInjectiveComplex (S : Closeds (ComplexPoint X)) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  ((TopCat.Sheaf.sheafSectionsSupportedOutside
    (TopCat.of (ComplexPoint X)) S.compl).mapHomologicalComplex ℤᵘᵖ).obj
      (ambientRationalInjectiveComplex X)

instance complexSupportInjectiveComplex_isStrictlyGE (S : Closeds (ComplexPoint X)) :
    (complexSupportInjectiveComplex X S).IsStrictlyGE 0 := by
  dsimp [complexSupportInjectiveComplex]
  infer_instance

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
/-- For a closed `S`, this identifies `H_[S]^n(X(ℂ);ℚ)` with degree-`n` cohomology of global
sections of the supported injective resolution of the constant sheaf `ℚ`. -/
def rationalSupportAddEquivSupportedInjectiveHomology (n : ℕ) :
    TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) Z
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n ≃+
      (((TopCat.Sheaf.supportEvaluation ↧(ComplexPoint X) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
        (complexSupportInjectiveComplex X Z)).homology n :=
  @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology (TopCat.of (ComplexPoint X)) Z.compl ⊤
    Z.compl (top_inf_eq _) inferInstance _ (ambientRationalInjectiveComplex X)
    (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n

section Rational

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance (V : Opens (ComplexPoint X)) : ParacompactSpace V := openParacompactSpace X V

/-- The quasi-isomorphic augmentation `ℚ[0] → C^•` from the constant rational sheaf to
sheafified singular cochains on `X(ℂ)`. -/
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
  let : QuasiIso (HomologicalComplex.extendMap
      (constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat) :=
    h.mpr (constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ
      (exists_contractibleOpen_le X))
  let : QuasiIso ((constantFieldSheafComplexIntIsoSingle ℚ X).inv) := quasiIso_of_isIso _
  exact quasiIso_comp ((constantFieldSheafComplexIntIsoSingle ℚ X).inv)
    (HomologicalComplex.extendMap
      (constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat)

/-- For the supported injective resolution, the degree-`n` cohomology sheaf is canonically the
local relative singular cohomology sheaf `𝓗_[S]^n(X(ℂ);ℚ)`. -/
def complexSupportInjectiveCohomologySheafIsoRelative
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    (complexSupportInjectiveComplex X S).homology (n : ℤ) ≅
      AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S n :=
  (asIso (HomologicalComplex.homologyMap
    (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).symm ≪≫
      supportedSingularCohomologySheafIsoRelative
        (TopCat.of (ComplexPoint X)) S S.isClosed n

set_option maxHeartbeats 800000 in
/-- For each open `V`, this identifies supported Ext `H^n(V,V \setminus S;ℚ)` with relative
singular cohomology `H^n(V,V \setminus S;ℚ)`, naturally in `V`. -/
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

/-- The presheaf comparison sheafifies to an isomorphism between the supported cohomology sheaf
`𝓗_[S]^n(X(ℂ);ℚ)` and the sheaf of local relative singular cohomology. -/
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
/-- If `𝓗_[S]^j(X(ℂ);ℚ) = 0` for `j < n`, this identifies `H_[S]^n(X(ℂ);ℚ)` with the global
sections of the supported cohomology sheaf in degree `n`. -/
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
/-- After the singular comparison, the same lower-degree vanishing identifies
`H_[S]^n(X(ℂ);ℚ)` with global sections of the local relative singular cohomology sheaf. -/
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
    (let e := rationalSupportCohomologySheafIsoRelative X S n
     letI : IsIso e.hom := e.isIso_hom
     letI : IsIso e.hom.hom := by
       change IsIso ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
         AddCommGrpCat).map e.hom)
       exact Functor.map_isIso _ e.hom
     (asIso (e.hom.hom.app (op ⊤))).addCommGroupIsoToAddEquiv)

set_option maxRecDepth 2000 in
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
  dsimp [rationalSupportAddEquivSupportedRelativeCohomologySheafSection]
  let e := rationalSupportCohomologySheafIsoRelative X S n
  let : IsIso e.hom := e.isIso_hom
  let : IsIso e.hom.hom := by
    change IsIso ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map e.hom)
    exact Functor.map_isIso _ e.hom
  change e.hom.hom.app (op ⊤)
      ((rationalSupportAddEquivSupportedCohomologySheafSection X S n hH) z) =
    e.hom.hom.app (op ⊤)
      (TopCat.Sheaf.supportHToSupportHCohomologySheafSection
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n z)
  congr 1
  exact TopCat.Sheaf.supportHCohomologySheafSectionAddEquivOfFlasque_apply
    (X := TopCat.of (ComplexPoint X))
    (Z := S)
    (F := (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ))
    (K := rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))
    (ι := rationalSingularAugmentation X)
    (hK := fun j => rationalSingularCochainComplex_isFlasque
      (TopCat.of (ComplexPoint X)) j)
    (H := fun j => AlgebraicTopology.Singular.supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint X)) S j)
    (e := fun j => AlgebraicTopology.Singular.supportedSingularCohomologySheafIsoRelative
      (TopCat.of (ComplexPoint X)) S S.isClosed j)
    n hH z

set_option maxHeartbeats 800000 in
/-- If the lower local relative cohomology sheaves vanish on `V`, this identifies
`H^n(V,V \setminus S;ℚ)` with sections on `V` of the local relative singular cohomology sheaf. -/
def rationalSupportAddEquivSupportedRelativeCohomologySheafSectionOnOpen
    (S : Closeds (ComplexPoint X)) (V W : Opens (ComplexPoint X))
    (hW : V ⊓ S.compl = W) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero
      ((V.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
          (TopCat.of (ComplexPoint X)) S j))) :
    CategoryTheory.Sheaf.relH
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
        n (homOfLE (hW ▸ (inf_le_left : V ⊓ S.compl ≤ V) : W ≤ V)) ≃+
      (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) S n).presheaf.obj (op V) :=
  let K := complexSupportInjectiveComplex X S
  let bridge := @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
    (TopCat.of (ComplexPoint X)) S.compl V W hW inferInstance
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (ambientRationalInjectiveComplex X)
    (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n
  let lowest := TopCat.Sheaf.openRestrictedLowestSectionCohomologyIsoOfNat
    (TopCat.of (ComplexPoint X)) V K
    (fun j => AlgebraicTopology.Singular.supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint X)) S j)
    (fun j => complexSupportInjectiveCohomologySheafIsoRelative X S j) n hH
    (fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) S.compl ((ambientRationalInjectiveComplex X).X j))
  bridge.trans lowest.addCommGroupIsoToAddEquiv

/-- After restriction to an open `V`, the degree-`n` cohomology sheaf of the supported injective
complex is the restriction of the local relative singular cohomology sheaf. -/
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
