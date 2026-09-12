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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.Chain
public import Mathlib.Topology.Sheaves.Functors

/-!
# Sheafification and closed-embedding direct image

The canonical comparison from the sheafification of a direct-image presheaf to the direct
image of its sheafification is an isomorphism for a closed embedding, provided the presheaf
has zero value on the empty open set. This normalization is essential: an arbitrary nonzero
empty-open value would create extra stalks off the closed image.

The comparison is constructed by the sheafification adjunction. Its invertibility is proved
using the existing inducing-map stalk comparison on the image and actual vanishing off the
closed image. No exceptional-pullback or proper-direct-image formalism is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

universe u

namespace AlgebraicTopology.Singular

variable {Z X : TopCat.{u}} (i : Z ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the canonical map from a direct-image stalk to its source stalk. -/
@[reassoc] lemma stalkPushforward_naturality_additive
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} Z} (a : P ⟶ Q) (z : Z) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map a) ≫
      Q.stalkPushforward AddCommGrpCat.{u} i z =
      P.stalkPushforward AddCommGrpCat.{u} i z ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map a := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hz
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    TopCat.Presheaf.stalkPushforward_germ, ← Category.assoc,
    TopCat.Presheaf.stalkPushforward_germ, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- A normalized direct-image presheaf has zero stalks off a closed image. -/
theorem pushforward_stalk_isZero_of_not_mem_range
    (hi : IsClosed (Set.range i)) (P : TopCat.Presheaf AddCommGrpCat.{u} Z)
    (hP : IsZero (P.obj (.op ⊥))) (x : X) (hx : x ∉ Set.range i) :
    IsZero (((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj P).stalk x) := by
  let U : Opens X := ⟨(Set.range i)ᶜ, hi.isOpen_compl⟩
  let F := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj P
  rw [IsZero.iff_id_eq_zero]
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hxV
  let W := V ⊓ U
  have hxW : x ∈ W := ⟨hxV, hx⟩
  have hpre : (Opens.map i).obj W = ⊥ := by
    ext z
    change (i z ∈ V ∧ i z ∉ Set.range i) ↔ False
    exact ⟨fun h => h.2 ⟨z, rfl⟩, False.elim⟩
  have hW : IsZero (F.obj (.op W)) := by
    change IsZero (P.obj (.op ((Opens.map i).obj W)))
    rw [hpre]
    exact hP
  have hg : F.germ W x hxW = 0 := hW.eq_zero_of_src _
  have hres := F.germ_res (Opens.infLELeft V U) x hxW
  rw [hg, comp_zero] at hres
  simpa only [Category.comp_id, comp_zero] using hres.symm

/-- The natural comparison from sheafifying a direct-image presheaf to directly imaging its
sheafification. It exists for any continuous map; invertibility requires more. -/
def pushforwardSheafificationComparison (P : TopCat.Presheaf AddCommGrpCat.{u} Z) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj P) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj P) :=
  ⟨sheafifyLift (Opens.grothendieckTopology X)
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map
      (toSheafify (Opens.grothendieckTopology Z) P))
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
      ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj P)).property⟩

/-- The comparison agrees with the actual direct image of the sheafification unit. -/
@[reassoc] lemma pushforwardSheafificationComparison_unit
    (P : TopCat.Presheaf AddCommGrpCat.{u} Z) :
    toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj P) ≫
      (pushforwardSheafificationComparison i P).hom =
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map
        (toSheafify (Opens.grothendieckTopology Z) P) :=
  toSheafify_sheafifyLift _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The constructed comparison is natural in morphisms of presheaves. -/
@[reassoc] lemma pushforwardSheafificationComparison_naturality
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} Z} (a : P ⟶ Q) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map a) ≫
      pushforwardSheafificationComparison i Q =
      pushforwardSheafificationComparison i P ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map
          ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).map a) := by
  apply CategoryTheory.Sheaf.hom_ext
  change sheafifyMap (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map a) ≫
      sheafifyLift (Opens.grothendieckTopology X) _ _ =
    sheafifyLift (Opens.grothendieckTopology X) _ _ ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map
        (sheafifyMap (Opens.grothendieckTopology Z) a)
  rw [sheafifyMap_sheafifyLift, ← sheafifyLift_comp,
    ← Functor.map_comp, ← Functor.map_comp, toSheafify_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- For an inducing map the direct image of the sheafification unit is an isomorphism on
stalks at every point of the image. -/
theorem pushforward_sheafificationUnit_stalk_isIso_on_range
    (hi : IsInducing i) (P : TopCat.Presheaf AddCommGrpCat.{u} Z) (z : Z) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)).map
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map
        (toSheafify (Opens.grothendieckTopology Z) P))) := by
  let a := toSheafify (Opens.grothendieckTopology Z) P
  let Q : TopCat.Presheaf AddCommGrpCat.{u} Z := sheafify (Opens.grothendieckTopology Z) P
  have hPiso : IsIso (P.stalkPushforward AddCommGrpCat.{u} i z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u} hi P z
  have hQiso : IsIso (Q.stalkPushforward AddCommGrpCat.{u} i z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u} hi Q z
  have ha : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map a) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z AddCommGrpCat.{u} P
  have hcomp : IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map a) ≫
          Q.stalkPushforward AddCommGrpCat.{u} i z) := by
    rw [stalkPushforward_naturality_additive]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Q.stalkPushforward AddCommGrpCat.{u} i z)

/-- For a closed embedding and a zero empty-open value, direct image preserves the
stalkwise sheafification equivalence at every ambient point. -/
theorem pushforward_sheafificationUnit_stalk_isIso
    (hi : IsClosedEmbedding i) (P : TopCat.Presheaf AddCommGrpCat.{u} Z)
    (hP : IsZero (P.obj (.op ⊥))) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map
        (toSheafify (Opens.grothendieckTopology Z) P))) := by
  by_cases hx : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hx
    exact pushforward_sheafificationUnit_stalk_isIso_on_range i hi.isEmbedding.isInducing P z
  · have hQ : IsZero ((sheafify (Opens.grothendieckTopology Z) P).obj (.op ⊥)) :=
      (TopCat.Sheaf.isTerminalOfEmpty
        ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj P)).isZero
    exact (pushforward_stalk_isZero_of_not_mem_range i hi.isClosed_range P hP x hx).isIso
      (pushforward_stalk_isZero_of_not_mem_range i hi.isClosed_range
        (sheafify (Opens.grothendieckTopology Z) P) hQ x hx) _

/-- The comparison is proved to be an isomorphism; it is not supplied as extra data. -/
theorem pushforwardSheafificationComparison_isIso
    (hi : IsClosedEmbedding i) (P : TopCat.Presheaf AddCommGrpCat.{u} Z)
    (hP : IsZero (P.obj (.op ⊥))) : IsIso (pushforwardSheafificationComparison i P) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro x
  let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hunit : IsIso (S.map (toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj P))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  have hpush : IsIso (S.map ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map
      (toSheafify (Opens.grothendieckTopology Z) P))) :=
    pushforward_sheafificationUnit_stalk_isIso i hi P hP x
  have hcomp : IsIso (S.map (toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj P)) ≫
        S.map (pushforwardSheafificationComparison i P).hom) := by
    rw [← S.map_comp, pushforwardSheafificationComparison_unit]
    exact hpush
  exact IsIso.of_isIso_comp_left
    (S.map (toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj P))) _

end AlgebraicTopology.Singular
