/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionCoclass
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.MapOfLocalStalks
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

variable {M : Type} [TopologicalSpace M]

@[simp] theorem neighborhoodSupportInclusionPairMap_id (W S : Set M) :
    neighborhoodSupportInclusionPairMap (show W ⊆ W from le_refl W) S =
      𝟙 (neighborhoodSupportComplementPair W S) := rfl

@[simp] theorem neighborhoodSupportInclusionPairMap_comp {U V W : Set M}
    (hUV : U ⊆ V) (hVW : V ⊆ W) (S : Set M) :
    neighborhoodSupportInclusionPairMap hUV S ≫ neighborhoodSupportInclusionPairMap hVW S =
      neighborhoodSupportInclusionPairMap (hUV.trans hVW) S := rfl

variable (X : TopCat.{0}) (S : Set X) (n : ℕ)

/-- Let `X` be a topological space, `S ⊆ X` a subset, and `n` a natural number. This presheaf of
abelian groups assigns to each open `V` the rational relative singular cohomology `H^n(V, V \ S;
ℚ)`. A class is a rational singular cocycle vanishing on simplices in `V \ S`, modulo
coboundaries of such cochains. Restrictions are induced by inclusions of pairs. -/
def supportRelativeCohomologyPresheaf : TopCat.Presheaf AddCommGrpCat X where
  -- `V ↦ H^n(V, V \ S; ℚ)`.
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

/-- Let `X` be a topological space, `S ⊆ X` a subset, and `n` a natural number. The sheaf `𝓗^n_S` is
the sheafification of `V ↦ H^n(V, V \ S; ℚ)`, rational relative singular cohomology on open
subsets. Its sections are locally represented by these relative classes, with representatives
identified when they agree on smaller neighborhoods. -/
def supportRelativeCohomologySheaf : TopCat.Sheaf AddCommGrpCat X :=
  -- The sheaf associated with `V ↦ H^n(V, V \ S; ℚ)`; write it `𝓗^n_S`.
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (supportRelativeCohomologyPresheaf X S n)

/-- `𝓗_[S]^n(X; ℚ)` is the `n`-th rational relative-cohomology sheaf on `X` with support in `S`,
the sheaf associated with `V ↦ H^n(V, V \ S; ℚ)`. -/
scoped notation:max "𝓗_[" S "]^" n:max "(" X "; " "ℚ" ")" =>
  supportRelativeCohomologySheaf X S n

/-- Let `X` be a topological space, `S ⊆ X`, and `n` a natural number. This is the sheafification
map from the presheaf `V ↦ H^n(V, V \ S; ℚ)` to its associated sheaf `𝓗^n_S`. It sends a
relative singular class on an open `V` to the section represented by its germs. -/
def supportRelativeCohomologyToSheaf :
    supportRelativeCohomologyPresheaf X S n ⟶ (𝓗_[S]^n(X; ℚ)).obj :=
  toSheafify (Opens.grothendieckTopology X) _

/-- Let `X` be a topological space, `S ⊆ X`, `V ⊆ X` open, and `x ∈ V`. For a natural number `n`,
this sends a relative singular class in `H^n(V, V \ S; ℚ)` to its germ at `x` in the stalk of
the sheafification of `W ↦ H^n(W, W \ S; ℚ)`. -/
def supportRelativeCohomologyGerm (V : Opens X) (x : X) (hx : x ∈ V)
    -- A class in `H^n(V, V \ S; ℚ)`.
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    (𝓗_[S]^n(X; ℚ)).presheaf.stalk x :=
  (𝓗_[S]^n(X; ℚ)).presheaf.germ V x hx
    ((supportRelativeCohomologyToSheaf X S n).app (op V) a)

end AlgebraicTopology.Singular
