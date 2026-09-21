/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.NeighborhoodPairImage
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenSheafification

/-!
# Open-embedding transport of the relative-cohomology sheaf

The embedding homeomorphisms identify neighborhood/support pairs with their images, and
these identifications commute with pair inclusions, giving a presheaf isomorphism.
Sheafification then transports the normalized section, with the sheafification-unit
square displayed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

namespace AlgebraicTopology.Singular

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B)

/-- The pair-image identification respects neighborhood inclusions. -/
theorem neighborhoodSupportPairImageIso_naturality {U V : Opens Y} (hUV : U ≤ V) :
    neighborhoodSupportInclusionPairMap (W := (U : Set Y)) (V := (V : Set Y)) hUV B ≫
      (neighborhoodSupportPairImageIso f hf.isEmbedding (V : Set Y) B S
        (fun y _ => by rw [← hB]; rfl)).hom =
    (neighborhoodSupportPairImageIso f hf.isEmbedding (U : Set Y) B S
      (fun y _ => by rw [← hB]; rfl)).hom ≫
      neighborhoodSupportInclusionPairMap
        (W := (hf.functor.obj U : Set X)) (V := (hf.functor.obj V : Set X))
        (Set.image_mono hUV) S := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `f : Y → X` be an open embedding of topological spaces, let `S ⊆ X`, and put `B = f⁻¹(S)`.
For a natural number `n`, pullback identifies the presheaves on `Y` given by `V ↦ H^n(f(V), f(V)
\ S; ℚ)` and `V ↦ H^n(V, V \ B; ℚ)`. The groups are relative singular cohomology, with
restriction maps induced by inclusions. -/
def supportRelativeCohomologyPresheafOpenIso (n : ℕ) :
    hf.functor.op ⋙ supportRelativeCohomologyPresheaf X S n ≅
      supportRelativeCohomologyPresheaf Y B n :=
  NatIso.ofComponents (fun V =>
    (neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding (V.unop : Set Y) B S
      (fun y _ => by rw [← hB]; rfl) n).toAddEquiv.toAddCommGrpIso) (by
    intro U V g
    apply AddCommGrpCat.hom_ext
    ext a
    change relativeCohomologyMap ℚ n
        (neighborhoodSupportPairImageIso f hf.isEmbedding (V.unop : Set Y) B S
          (fun y _ => by rw [← hB]; rfl)).hom
        (relativeCohomologyMap ℚ n
          (neighborhoodSupportInclusionPairMap (Set.image_mono (leOfHom g.unop)) S) a) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (V.unop : Set Y))
          (V := (U.unop : Set Y)) (leOfHom g.unop) B)
        (relativeCohomologyMap ℚ n
          (neighborhoodSupportPairImageIso f hf.isEmbedding (U.unop : Set Y) B S
            (fun y _ => by rw [← hB]; rfl)).hom a)
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      ← neighborhoodSupportPairImageIso_naturality f hf S B hB (leOfHom g.unop),
      relativeCohomologyMap_comp]
    rfl)

/-- Let `f : Y → X` be an open embedding of topological spaces and `P` a presheaf of abelian groups
on `X`. Sheafifying the presheaf `V ↦ P(f(V))` gives the same sheaf on `Y` as restricting the
sheafification of `P` along `f`. This is the isomorphism induced by the sheafification unit. -/
def supportOpenEmbeddingSheafificationIso (P : TopCat.Presheaf AddCommGrpCat X) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj (hf.functor.op ⋙ P) ≅
      (hf.sheafPullback AddCommGrpCat).obj
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj P) :=
  letI : hf.functor.IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    hf.functor_isContinuous
  letI : hf.functor.IsCocontinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    hf.functor_isCocontinuous
  (hf.functor.pushforwardContinuousSheafificationCompatibility AddCommGrpCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).app P

/-- Let `f : Y → X` be an open embedding of topological spaces, let `S ⊆ X`, and put `B = f⁻¹(S)`.
Write `𝓗^n_S` for the sheafification of `V ↦ H^n(V, V \ S; ℚ)`, and define `𝓗^n_B` on `Y` in the
same way. Pullback of relative singular cohomology gives this sheaf isomorphism `𝓗^n_B ≅
f⁻¹𝓗^n_S`. -/
def supportRelativeCohomologySheafOpenIso (n : ℕ) :
    -- `𝓗^n_B` on `Y` is the restriction of `𝓗^n_S` along the open embedding `f`.
    𝓗_[B]^n(Y; ℚ) ≅
      -- Restriction of sheaves along `f`.
      (hf.sheafPullback AddCommGrpCat).obj 𝓗_[S]^n(X; ℚ) :=
  (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapIso
      (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).symm ≪≫
    supportOpenEmbeddingSheafificationIso f hf (supportRelativeCohomologyPresheaf X S n)

/-- Let `f : Y → X` be an open embedding of topological spaces, let `S ⊆ X`, and put `B = f⁻¹(S)`.
Write `𝓗^n_S` for the sheafification of `V ↦ H^n(V, V \ S; ℚ)`, and define `𝓗^n_B` on `Y` in the
same way. This sends a global section of `𝓗^n_B` to a section of `𝓗^n_S` on the open image
`f(Y)`, using the homeomorphism of pairs induced by `f`. -/
def supportRelativeCohomologySectionOpenImage (n : ℕ)
    -- A global section of `𝓗^n_B` on `Y`.
    (s : (𝓗_[B]^n(Y; ℚ)).obj.obj (op ⊤)) :
    -- A section of `𝓗^n_S` on the open `f(Y) ⊆ X`.
    (𝓗_[S]^n(X; ℚ)).obj.obj
      -- The open `f(Y)`.
      (op (hf.functor.obj ⊤)) :=
  (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op ⊤) s

/-- Let `f : Y → X` be an open embedding of topological spaces, let `S ⊆ X`, and put `B = f⁻¹(S)`.
Write `𝓗^n_S` for the sheafification of `V ↦ H^n(V, V \ S; ℚ)`, and define `𝓗^n_B` on `Y` in the
same way. For a specified open `U = f(Y)`, this sends a global section of `𝓗^n_B` to a section
of `𝓗^n_S` on `U`, using the homeomorphism induced by `f` and the given equality of opens. -/
def supportRelativeCohomologySectionOnOpen (n : ℕ) (U : Opens X)
    (hU : hf.functor.obj ⊤ = U)
    (s : (𝓗_[B]^n(Y; ℚ)).obj.obj (op ⊤)) :
    (𝓗_[S]^n(X; ℚ)).obj.obj (op U) :=
  (𝓗_[S]^n(X; ℚ)).obj.map (eqToHom hU.symm).op
    (supportRelativeCohomologySectionOpenImage f hf S B hB n s)

end AlgebraicTopology.Singular
