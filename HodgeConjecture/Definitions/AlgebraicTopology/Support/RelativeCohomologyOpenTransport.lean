/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NeighborhoodPairImage
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

variable {X Y : TopCat.{0}} {f : Y ⟶ X} (hf : IsOpenEmbedding f)
  {S : Set X} {B : Set Y} (hB : f ⁻¹' S = B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The presheaf comparison comes from the actual pair-image homeomorphisms. -/
def supportRelativeCohomologyPresheafOpenIso (n : ℕ) :
    hf.functor.op ⋙ supportRelativeCohomologyPresheaf X S n ≅
      supportRelativeCohomologyPresheaf Y B n :=
  NatIso.ofComponents (fun V => (forget₂ (ModuleCat ℚ) AddCommGrpCat).mapIso
    (neighborhoodSupportPairImageCohomologyIso ℚ hf.isEmbedding
      (fun y _ => by rw [← hB]; rfl) n)) (by
    intro U V g
    apply AddCommGrpCat.hom_ext
    ext a
    change relativeCohomologyMap ℚ n
        (neighborhoodSupportPairImageIso hf.isEmbedding
          (fun y _ => by rw [← hB]; rfl)).hom
        (relativeCohomologyMap ℚ n
          (neighborhoodSupportInclusionPairMap (Set.image_mono (leOfHom g.unop)) S) a) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (V.unop : Set Y))
          (V := (U.unop : Set Y)) (leOfHom g.unop) B)
        (relativeCohomologyMap ℚ n
          (neighborhoodSupportPairImageIso hf.isEmbedding
            (fun y _ => by rw [← hB]; rfl)).hom a)
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      ← neighborhoodSupportPairImageIso_hom_naturality hf.isEmbedding
        (leOfHom g.unop) (fun y _ => by rw [← hB]; rfl),
      relativeCohomologyMap_comp]
    rfl)

/-- Actual sheafification of the pair comparison identifies intrinsic local support
cohomology with restriction of the original ambient relative-cohomology sheaf. -/
def supportRelativeCohomologySheafOpenIso (n : ℕ) :
    supportRelativeCohomologySheaf Y B n ≅
      (hf.sheafPullback AddCommGrpCat).obj (supportRelativeCohomologySheaf X S n) :=
  (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapIso
      (supportRelativeCohomologyPresheafOpenIso hf hB n).symm ≪≫
    letI : hf.functor.IsContinuous
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
      hf.functor_isContinuous
    letI : hf.functor.IsCocontinuous
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
      hf.functor_isCocontinuous
    (hf.functor.pushforwardContinuousSheafificationCompatibility AddCommGrpCat
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).app
        (supportRelativeCohomologyPresheaf X S n)

end AlgebraicTopology.Singular
