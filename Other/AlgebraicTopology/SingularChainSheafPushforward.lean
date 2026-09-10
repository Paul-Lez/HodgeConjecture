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

public import Other.AlgebraicTopology.ClosedEmbeddingSheafification
public import HodgeConjecture.Lemmas.AlgebraicTopology.SingularChainSheafStalk

/-!
# Closed-embedding pushforward on the actual relative singular-chain sheaves

For every continuous map `i : Z → X`, the actual maps of pairs
`(Z, Z ∖ i⁻¹(U)) → (X, X ∖ U)` give a map from the direct image of the relative-chain
presheaf on `Z` to that on `X`. For a closed embedding, the proved normalized
sheafification/direct-image comparison turns this into a chain map
`i_* singularChainSheafComplex Z → singularChainSheafComplex X`.

This is ordinary direct image for a closed embedding, constructed from singular chains.
No claim of a direct-image/sheafification comparison for arbitrary nonproper maps, no
exceptional-pullback identification, and no support quasi-isomorphism is made.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] {Z X : TopCat.{u}} (i : Z ⟶ X)

instance singularChain_presheafPushforward_additive :
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).Additive where
  map_add := by intros; rfl

instance singularChain_sheafPushforward_additive :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).Additive where
  map_add := by intros; rfl

/-- The actual maps of relative pairs on ambient opens commute with restriction. -/
def openComplementPairPushforward :
    (Opens.map i).op ⋙ openComplementPairFunctor Z ⟶ openComplementPairFunctor X where
  app U := preimageSupportPairMap i (U.unop : Set X)
  naturality {U V} a := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- Covariance of relative singular chains gives the presheaf-level pushforward chain map. -/
def openRelativeSingularChainPushforward :
    (Opens.map i).op ⋙ openRelativeSingularChainComplexFunctor R Z ⟶
      openRelativeSingularChainComplexFunctor R X :=
  Functor.whiskerRight (openComplementPairPushforward i) (relativeChainFunctor R)

/-- Direct-image relative `n`-chains map to the ambient relative `n`-chains. -/
def singularChainPresheafPushforward (n : ℕ) :
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj (singularChainPresheaf R Z n) ⟶
      singularChainPresheaf R X n :=
  Functor.whiskerRight (openRelativeSingularChainPushforward R i) (chainDegreeAdditiveFunctor R n)

/-- On every open set the presheaf pushforward is the map of actual relative singular chains. -/
@[simp] lemma singularChainPresheafPushforward_app (U : Opens X) (n : ℕ) :
    (singularChainPresheafPushforward R i n).app (.op U) =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((relativeChainFunctor R).map (preimageSupportPairMap i (U : Set X))).f n) := rfl

/-- The pair-induced pushforward is compatible with the singular boundary. -/
@[reassoc] lemma singularChainPresheafPushforward_boundary (n : ℕ) :
    singularChainPresheafPushforward R i (n + 1) ≫ singularChainBoundary R X n =
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map (singularChainBoundary R Z n) ≫
        singularChainPresheafPushforward R i n := by
  apply NatTrans.ext
  funext U
  exact congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
    (((relativeChainFunctor R).map (preimageSupportPairMap i (U.unop : Set X))).comm (n + 1) n)

/-- The direct-image presheaf map assembled as a chain map. -/
def singularChainPresheafPushforwardComplex :
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainPresheafComplex R Z) ⟶
        singularChainPresheafComplex R X where
  f n := singularChainPresheafPushforward R i n
  comm' j k hjk := by
    obtain rfl := hjk
    simp only [Functor.mapHomologicalComplex_obj_d, singularChainPresheafComplex_d]
    exact singularChainPresheafPushforward_boundary R i k

/-- Chains relative to the whole space vanish: this is the actual cokernel of the chain
isomorphism induced by the homeomorphism from the full subtype to the space. -/
theorem relativeSingularChains_emptySupport_isZero (Z : TopCat.{u}) :
    IsZero ((relativeChainFunctor R).obj
      (TopPair.ofSubset (X := Z) ((⊥ : Opens Z) : Set Z)ᶜ)) := by
  rw [show ((⊥ : Opens Z) : Set Z)ᶜ = Set.univ by simp]
  let P := TopPair.ofSubset (X := Z) (Set.univ : Set Z)
  have hPi : IsIso P.map :=
    (TopCat.isIso_iff_isHomeomorph P.map).mpr (Homeomorph.Set.univ Z).isHomeomorph
  have hchain : IsIso ((chainPairFunctor R).obj P).hom := by
    change IsIso (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map P.map)
    infer_instance
  exact isZero_cokernel_of_epi ((chainPairFunctor R).obj P).hom

/-- The actual relative-chain presheaf has zero value on the empty open set. -/
theorem singularChainPresheaf_empty_isZero (Z : TopCat.{u}) (n : ℕ) :
    IsZero ((singularChainPresheaf R Z n).obj (.op ⊥)) :=
  (chainDegreeAdditiveFunctor R n).map_isZero (relativeSingularChains_emptySupport_isZero R Z)

/-- The sheafification/direct-image comparison assembled as an actual chain map. -/
def singularChainPushforwardSheafificationComparison :
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainPresheafComplex R Z)) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R Z) where
  f n := pushforwardSheafificationComparison i (singularChainPresheaf R Z n)
  comm' j k hjk := by
    obtain rfl := hjk
    simp only [Functor.mapHomologicalComplex_obj_d, singularChainPresheafComplex_d,
      singularChainSheafComplex_d]
    exact (pushforwardSheafificationComparison_naturality i (singularChainBoundary R Z k)).symm

/-- For a closed embedding, the comparison is a chain-complex isomorphism. -/
theorem singularChainPushforwardSheafificationComparison_isIso (hi : IsClosedEmbedding i) :
    IsIso (singularChainPushforwardSheafificationComparison R i) := by
  have hisos (n : ℕ) : IsIso ((singularChainPushforwardSheafificationComparison R i).f n) :=
    pushforwardSheafificationComparison_isIso i hi (singularChainPresheaf R Z n)
      (singularChainPresheaf_empty_isZero R Z n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The canonical, proved chain-level comparison for closed-embedding direct image. -/
def singularChainPushforwardSheafificationIso (hi : IsClosedEmbedding i) :
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainPresheafComplex R Z)) ≅
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R Z) := by
  have hiso := singularChainPushforwardSheafificationComparison_isIso R i hi
  exact asIso (singularChainPushforwardSheafificationComparison R i)

/-- Closed-embedding pushforward of the actual relative singular-chain sheaf complex. -/
def singularChainSheafPushforward (hi : IsClosedEmbedding i) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainSheafComplex R Z) ⟶
        singularChainSheafComplex R X :=
  (singularChainPushforwardSheafificationIso R i hi).inv ≫
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (singularChainPresheafPushforwardComplex R i)

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf chain map is obtained from the actual presheaf map through the canonical
comparison, not through an independently supplied equivalence. -/
@[reassoc] lemma singularChainSheafPushforward_comparison (hi : IsClosedEmbedding i) :
    singularChainPushforwardSheafificationComparison R i ≫
      singularChainSheafPushforward R i hi =
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (singularChainPresheafPushforwardComplex R i) := by
  change (singularChainPushforwardSheafificationIso R i hi).hom ≫
    ((singularChainPushforwardSheafificationIso R i hi).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- On original relative-chain sections, the sheaf pushforward is precisely the pair-induced
chain map followed by sheafification. This fixes the complete chain normalization. -/
@[reassoc] lemma singularChainSheafPushforward_unit (hi : IsClosedEmbedding i) (n : ℕ) :
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map
        (toSheafify (Opens.grothendieckTopology Z) (singularChainPresheaf R Z n)) ≫
      ((singularChainSheafPushforward R i hi).f n).hom =
      singularChainPresheafPushforward R i n ≫
        toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n) := by
  have hcomp := congrArg (fun f => (f.f n).hom)
    (singularChainSheafPushforward_comparison R i hi)
  change (pushforwardSheafificationComparison i (singularChainPresheaf R Z n)).hom ≫
      ((singularChainSheafPushforward R i hi).f n).hom =
      sheafifyMap (Opens.grothendieckTopology X) (singularChainPresheafPushforward R i n) at hcomp
  rw [← pushforwardSheafificationComparison_unit, Category.assoc, hcomp]
  exact (toSheafify_naturality (Opens.grothendieckTopology X)
    (singularChainPresheafPushforward R i n)).symm

/-- Degreewise sections of the constructed sheaf pushforward retain their actual
relative-singular-chain normalization on every ambient open set. -/
@[reassoc] lemma singularChainSheafPushforward_unit_app
    (hi : IsClosedEmbedding i) (n : ℕ) (U : Opens X) :
    (toSheafify (Opens.grothendieckTopology Z) (singularChainPresheaf R Z n)).app
        (.op ((Opens.map i).obj U)) ≫
      (((singularChainSheafPushforward R i hi).f n).hom).app (.op U) =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((relativeChainFunctor R).map (preimageSupportPairMap i (U : Set X))).f n) ≫
        (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n)).app (.op U) :=
  congr_app (singularChainSheafPushforward_unit R i hi n) (.op U)

/-- The same exact normalization on germs, before passing to homology. -/
@[reassoc] lemma singularChainSheafPushforward_unit_germ
    (hi : IsClosedEmbedding i) (n : ℕ) (U : Opens X) (x : X) (hx : x ∈ U) :
    (toSheafify (Opens.grothendieckTopology Z) (singularChainPresheaf R Z n)).app
        (.op ((Opens.map i).obj U)) ≫
      (((singularChainSheafPushforward R i hi).f n).hom).app (.op U) ≫
        TopCat.Presheaf.germ (singularChainSheaf R X n).obj U x hx =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((relativeChainFunctor R).map (preimageSupportPairMap i (U : Set X))).f n) ≫
        (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n)).app (.op U) ≫
          TopCat.Presheaf.germ (singularChainSheaf R X n).obj U x hx :=
  singularChainSheafPushforward_unit_app_assoc R i hi n U _

/-- The same constructed pushforward with homological degree `n` placed in cohomological
degree `-n`. The source is the regraded direct-image chain complex. -/
def singularChainSheafPushforwardRegraded (hi : IsClosedEmbedding i) :
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainSheafComplex R Z)).extend
        ComplexShape.embeddingDownNat ⟶ singularChainSheafCochainComplex R X :=
  HomologicalComplex.extendMap (singularChainSheafPushforward R i hi)
    ComplexShape.embeddingDownNat

end AlgebraicTopology.Singular
