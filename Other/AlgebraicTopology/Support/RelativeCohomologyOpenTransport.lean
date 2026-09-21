/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologyOpenTransport
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NeighborhoodPairImage

/-!
# Actual open-embedding transport of the relative-cohomology sheaf

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologyOpenTransport`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

namespace AlgebraicTopology.Singular

variable {X Y : TopCat.{0}} {f : Y ⟶ X} (hf : IsOpenEmbedding f)
  {S : Set X} {B : Set Y} (hB : f ⁻¹' S = B)

/-- Inverse transport is literal pullback along the inverse pair homeomorphism. -/
theorem supportRelativeCohomologyPresheafOpenIso_inv_app (n : ℕ) (V : Opens Y)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) B) n) :
    (supportRelativeCohomologyPresheafOpenIso hf hB n).inv.app (op V) a =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportPairImageIso hf.isEmbedding
          (fun y _ => by rw [← hB]; rfl)).inv a := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalization square: actual classes are transported through their literal
pair-homeomorphism pullbacks before application of the ambient sheafification unit. -/
@[reassoc]
theorem supportRelativeCohomologySheafOpenIso_unit (n : ℕ) :
    supportRelativeCohomologyToSheaf Y B n ≫
      (supportRelativeCohomologySheafOpenIso hf hB n).hom.hom =
    (supportRelativeCohomologyPresheafOpenIso hf hB n).inv ≫
      Functor.whiskerLeft hf.functor.op (supportRelativeCohomologyToSheaf X S n) := by
  let : hf.functor.IsContinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := hf.functor_isContinuous
  let : hf.functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := hf.functor_isCocontinuous
  have hunit := hf.functor.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (supportRelativeCohomologyPresheaf X S n)
  change toSheafify _ _ ≫ (sheafifyMap _ _ ≫ _) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  exact congrArg (fun k =>
    (supportRelativeCohomologyPresheafOpenIso hf hB n).inv ≫ k) hunit

/-- The open transport preserves the literal sheafification images of local classes. -/
theorem supportRelativeCohomologySheafOpenIso_unit_apply (n : ℕ) (V : Opens Y)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) B) n) :
    (supportRelativeCohomologySheafOpenIso hf hB n).hom.hom.app (op V)
      ((supportRelativeCohomologyToSheaf Y B n).app (op V) a) =
    (supportRelativeCohomologyToSheaf X S n).app (op (hf.functor.obj V))
      ((supportRelativeCohomologyPresheafOpenIso hf hB n).inv.app (op V) a) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (supportRelativeCohomologySheafOpenIso_unit hf hB n) (op V)) a
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Point-coclass sections commute with transport through an open embedding. -/
theorem supportRelativeCohomologyPointSection_open
    (n : ℕ) (V : Opens Y) {x : Y} (hx : x ∈ B)
    (a : RelativeCohomology ℚ (pointComplementPair (f x)) n) :
    (supportRelativeCohomologySheafOpenIso hf hB n).hom.hom.app (op V)
      (supportRelativeCohomologyPointSection V hx
        (relativeCohomologyMap ℚ n
          (pointComplementPairMap (f := f.hom) hf.injective x) a)) =
      supportRelativeCohomologyPointSection (hf.functor.obj V)
        (by change x ∈ f ⁻¹' S; rw [hB]; exact hx) a := by
  have hxS : f x ∈ S := by
    change x ∈ f ⁻¹' S
    rw [hB]
    exact hx
  rw [supportRelativeCohomologyPointSection,
    supportRelativeCohomologySheafOpenIso_unit_apply,
    supportRelativeCohomologyPresheafOpenIso_inv_app]
  apply congrArg ((supportRelativeCohomologyToSheaf X S n).app _)
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, Category.assoc,
    neighborhoodSupportPairImageIso_inv_comp_toPoint hf.isEmbedding
      (fun y _ => by rw [← hB]; rfl) hx hxS]
  rfl

/-- Transport from the full source commutes with restriction to an image open. -/
theorem supportRelativeCohomologySheafOpenIso_hom_app_top_restrict
    (n : ℕ) (U : Opens X) (hU : hf.functor.obj ⊤ = U)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤))
    (V : Opens Y) (hV : hf.functor.obj V ≤ U) :
    (supportRelativeCohomologySheaf X S n).obj.map (homOfLE hV).op
        ((supportRelativeCohomologySheaf X S n).obj.map (eqToHom hU.symm).op
          ((supportRelativeCohomologySheafOpenIso hf hB n).hom.hom.app (op ⊤) s)) =
      (supportRelativeCohomologySheafOpenIso hf hB n).hom.hom.app (op V)
        ((supportRelativeCohomologySheaf Y B n).obj.map
          (homOfLE (show V ≤ ⊤ from le_top)).op s) := by
  aesop

end AlgebraicTopology.Singular
