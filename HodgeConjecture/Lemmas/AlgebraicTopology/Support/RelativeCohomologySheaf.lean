/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologySheaf
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NeighborhoodPairCohomology

/-!
# The actual local relative-cohomology presheaf and its sheafification

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologySheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex
open TopCat.Presheaf

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]

variable (X : TopCat.{0}) (S : Set X) (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Point-coclass sections commute with restriction to a smaller neighborhood. -/
@[simp] theorem supportRelativeCohomologyPointSection_restrict
    {x : X} (hx : x ∈ S) (a : RelativeCohomology ℚ (pointComplementPair x) n)
    {U V : Opens X} (hUV : U ≤ V) :
    (supportRelativeCohomologySheaf X S n).obj.map (homOfLE hUV).op
      (supportRelativeCohomologyPointSection V hx a) =
      supportRelativeCohomologyPointSection U hx a := by
  have h := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf X S n).naturality (homOfLE hUV).op)
    (relativeCohomologyMap ℚ n (neighborhoodSupportToPointPairMap V hx) a)
  simp only [ConcreteCategory.comp_apply] at h
  refine h.symm.trans ?_
  change (supportRelativeCohomologyToSheaf X S n).app (op U)
    (relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (W := (U : Set X)) (V := (V : Set X)) hUV S)
      (relativeCohomologyMap ℚ n (neighborhoodSupportToPointPairMap V hx) a)) = _
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    neighborhoodSupportInclusionPairMap_toPoint]
  rfl

@[simp] theorem supportRelativeCohomologyPresheaf_map_apply {U V : Opens X}
    (hUV : U ≤ V) (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    (supportRelativeCohomologyPresheaf X S n).map (homOfLE hUV).op a =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (U : Set X)) (V := (V : Set X)) hUV S) a := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction followed by germ is the original germ; the restriction is the
literal pair-inclusion pullback. -/
theorem supportRelativeCohomologyGerm_restrict {U V : Opens X} (hUV : U ≤ V)
    (x : X) (hx : x ∈ U)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    supportRelativeCohomologyGerm U x hx
      (relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (U : Set X)) (V := (V : Set X)) hUV S) a) =
    supportRelativeCohomologyGerm V x (hUV hx) a := by
  have h := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf X S n).naturality (homOfLE hUV).op) a
  exact (congrArg ((supportRelativeCohomologySheaf X S n).presheaf.germ U x hx) h).trans
    ((supportRelativeCohomologySheaf X S n).presheaf.germ_res_apply (homOfLE hUV) x hx _)

/-- Equality after actual restriction to a common neighborhood gives equal sheaf germs. -/
theorem supportRelativeCohomologyGerm_eq_of_restrict_eq
    {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V) (x : X) (hx : x ∈ W)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set X) S) n)
    (b : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n)
    (h : relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (U : Set X)) hWU S) a =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (V : Set X)) hWV S) b) :
    supportRelativeCohomologyGerm U x (hWU hx) a =
      supportRelativeCohomologyGerm V x (hWV hx) b := by
  rw [← supportRelativeCohomologyGerm_restrict X S n hWU x hx,
    ← supportRelativeCohomologyGerm_restrict X S n hWV x hx, h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Off closed support, every actual local relative class has zero sheaf germ. -/
theorem supportRelativeCohomologyGerm_eq_zero_of_not_mem (hS : IsClosed S)
    (V : Opens X) (x : X) (hx : x ∈ V) (hxS : x ∉ S)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    supportRelativeCohomologyGerm V x hx a = 0 := by
  let W : Opens X := V ⊓ ⟨Sᶜ, hS.isOpen_compl⟩
  have hWV : W ≤ V := inf_le_left
  have hxW : x ∈ W := ⟨hx, hxS⟩
  let := neighborhoodSupportRelativeCohomology_subsingleton ℚ W S (fun _ hy => hy.2) n
  rw [← supportRelativeCohomologyGerm_restrict X S n hWV x hxW]
  have hz : relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (V : Set X)) hWV S) a = 0 :=
    Subsingleton.elim _ _
  rw [hz]
  simp only [supportRelativeCohomologyGerm, map_zero]

end AlgebraicTopology.Singular
