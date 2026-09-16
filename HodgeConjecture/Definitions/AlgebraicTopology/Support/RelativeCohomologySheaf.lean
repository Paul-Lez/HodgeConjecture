/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.MapOfLocalStalks
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NeighborhoodPair
/-!
# The local relative-cohomology presheaf and its sheafification

For a support `S ⊆ X`, the value on `V` is the rational relative cohomology of the pair
`(V, V \ S)` as an additive group, with restrictions the pullbacks along inclusions of
these pairs, and the sheaf is its sheafification. This module also proves local vanishing
away from a closed support.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex
open TopCat.Presheaf

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0}) (S : Set X) (n : ℕ)

/-- The literal presheaf of rational relative cohomology of neighborhood/support pairs.
We retain the rational group but forget its scalar structure for the additive sheaf API. -/
def supportRelativeCohomologyPresheaf : TopCat.Presheaf AddCommGrpCat X where
  obj V := AddCommGrpCat.of (RelativeCohomology ℚ
    (neighborhoodSupportComplementPair (V.unop : Set X) S) n)
  map {U V} f := AddCommGrpCat.ofHom
    (relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap
      (W := (V.unop : Set X)) (V := (U.unop : Set X)) (leOfHom f.unop) S)).toAddMonoidHom
  map_id V := by
    change AddCommGrpCat.ofHom
      (relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (show (V.unop : Set X) ⊆ V.unop from le_refl _) S)).toAddMonoidHom = _
    rw [neighborhoodSupportInclusionPairMap_id, relativeCohomologyMap_id]
    rfl
  map_comp {U V W} f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    change relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (W := (W.unop : Set X)) (V := (U.unop : Set X))
        (leOfHom (f ≫ g).unop) S) a =
        relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap
          (W := (W.unop : Set X)) (V := (V.unop : Set X)) (leOfHom g.unop) S)
          (relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap
            (W := (V.unop : Set X)) (V := (U.unop : Set X)) (leOfHom f.unop) S) a)
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, neighborhoodSupportInclusionPairMap_comp]

/-- Actual sheafification, not a presupposed sheaf property of relative cohomology. -/
def supportRelativeCohomologySheaf : TopCat.Sheaf AddCommGrpCat X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (supportRelativeCohomologyPresheaf X S n)

/-- The canonical map taking an actual relative class to its sheafified local section. -/
def supportRelativeCohomologyToSheaf :
    supportRelativeCohomologyPresheaf X S n ⟶ (supportRelativeCohomologySheaf X S n).obj :=
  toSheafify (Opens.grothendieckTopology X) _

/-- A point coclass gives a section on every neighborhood of a support containing the point. -/
def supportRelativeCohomologyPointSection {X : TopCat.{0}} {S : Set X} {n : ℕ}
    (V : Opens X) {x : X} (hx : x ∈ S)
    (a : RelativeCohomology ℚ (pointComplementPair x) n) :
    (supportRelativeCohomologySheaf X S n).obj.obj (op V) :=
  (supportRelativeCohomologyToSheaf X S n).app (op V)
    (relativeCohomologyMap ℚ n (neighborhoodSupportToPointPairMap V hx) a)

/-- Germ of an actual relative coclass in the sheafification. -/
def supportRelativeCohomologyGerm {X : TopCat.{0}} {S : Set X} {n : ℕ}
    (V : Opens X) (x : X) (hx : x ∈ V)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    (supportRelativeCohomologySheaf X S n).presheaf.stalk x :=
  (supportRelativeCohomologySheaf X S n).presheaf.germ V x hx
    ((supportRelativeCohomologyToSheaf X S n).app (op V) a)

end AlgebraicTopology.Singular
