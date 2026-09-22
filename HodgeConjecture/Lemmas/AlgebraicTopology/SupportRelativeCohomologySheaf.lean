/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.SupportRelativeCohomologySheaf

/-!
# The actual local relative-cohomology presheaf and its sheafification

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.SupportRelativeCohomologySheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex
open TopCat.Presheaf

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]

variable (X : TopCat.{0}) (S : Set X) (n : ℕ)

/-- Transport a sheafified relative-cohomology section along an equality of the
displayed support sets. -/
def supportRelativeCohomologySectionTransport
    {S' : Set X} (hS : S' = S) (V : Opens X)
    (s : (supportRelativeCohomologySheaf X S' n).obj.obj (op V)) :
    (supportRelativeCohomologySheaf X S n).obj.obj (op V) := by
  subst S'
  exact s

/-- Transport a sheafified relative-cohomology section simultaneously along equalities of the
displayed support and the open on which the section is defined. -/
def supportRelativeCohomologySectionSupportOpenTransport
    {S' : Set X} (hS : S' = S) {U' U : Opens X} (hU : U' = U)
    (s : (supportRelativeCohomologySheaf X S' n).obj.obj (op U')) :
    (supportRelativeCohomologySheaf X S n).obj.obj (op U) := by
  subst S'
  subst U'
  exact s

@[simp] theorem supportRelativeCohomologySectionSupportOpenTransport_rfl
    (U : Opens X) (s : (supportRelativeCohomologySheaf X S n).obj.obj (op U)) :
    supportRelativeCohomologySectionSupportOpenTransport X S n rfl rfl s = s := rfl

@[simp] theorem supportRelativeCohomologySectionTransport_rfl
    (V : Opens X) (s : (supportRelativeCohomologySheaf X S n).obj.obj (op V)) :
    supportRelativeCohomologySectionTransport X S n rfl V s = s := rfl

/-- Successive transport first in the support and then simultaneously in the support and
the displayed open is the single transport along the composite equalities. -/
theorem supportRelativeCohomologySectionSupportOpenTransport_comp_support
    {S₀ S₁ : Set X} (h₀₁ : S₀ = S₁) (h₁S : S₁ = S)
    {U' U : Opens X} (hU : U' = U)
    (s : (supportRelativeCohomologySheaf X S₀ n).obj.obj (op U')) :
    supportRelativeCohomologySectionSupportOpenTransport X S n h₁S hU
        (supportRelativeCohomologySectionTransport X S₁ n h₀₁ U' s) =
      supportRelativeCohomologySectionSupportOpenTransport X S n (h₀₁.trans h₁S) hU s := by
  subst S₀
  subst S₁
  subst U'
  rfl

/-- Transport a stalk element along an equality of the displayed supports. -/
def supportRelativeCohomologyStalkTransport
    {S' : Set X} (hS : S' = S) (x : X)
    (a : (supportRelativeCohomologySheaf X S' n).presheaf.stalk x) :
    (supportRelativeCohomologySheaf X S n).presheaf.stalk x := by
  subst S'
  exact a

@[simp] theorem supportRelativeCohomologyStalkTransport_rfl
    (x : X) (a : (supportRelativeCohomologySheaf X S n).presheaf.stalk x) :
    supportRelativeCohomologyStalkTransport X S n rfl x a = a := rfl

@[simp] theorem supportRelativeCohomologyStalkTransport_zero
    {S' : Set X} (hS : S' = S) (x : X) :
    supportRelativeCohomologyStalkTransport X S n hS x
      (0 : (supportRelativeCohomologySheaf X S' n).presheaf.stalk x) = 0 := by
  subst S'
  rfl

/-- Germ formation commutes with transport of a section along an equality of supports. -/
theorem supportRelativeCohomologySectionTransport_germ
    {S' : Set X} (hS : S' = S) (V : Opens X) (x : X) (hx : x ∈ V)
    (s : (supportRelativeCohomologySheaf X S' n).obj.obj (op V)) :
    (supportRelativeCohomologySheaf X S n).presheaf.germ V x hx
      (supportRelativeCohomologySectionTransport X S n hS V s) =
    supportRelativeCohomologyStalkTransport X S n hS x
      ((supportRelativeCohomologySheaf X S' n).presheaf.germ V x hx s) := by
  subst S'
  rfl

/-- Global-section germs commute with support transport. -/
theorem supportRelativeCohomologySectionTransport_Γgerm
    {S' : Set X} (hS : S' = S) (x : X)
    (s : (supportRelativeCohomologySheaf X S' n).obj.obj (op ⊤)) :
    (supportRelativeCohomologySheaf X S n).presheaf.Γgerm x
      (supportRelativeCohomologySectionTransport X S n hS ⊤ s) =
    supportRelativeCohomologyStalkTransport X S n hS x
      ((supportRelativeCohomologySheaf X S' n).presheaf.Γgerm x s) := by
  subst S'
  rfl

/-- Sheafification of a local relative class is unchanged by transporting the displayed
support set along an equality.  Keeping this as a named lemma avoids exposing dependent
casts when two geometric presentations have been proved to have the same analytic image. -/
theorem supportRelativeCohomologyToSheaf_transport_support
    {S' : Set X} (hS : S' = S) (V : Opens X)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S') n) :
    hS ▸ ((supportRelativeCohomologyToSheaf X S' n).app (op V) a) =
      (supportRelativeCohomologyToSheaf X S n).app (op V) (hS ▸ a) := by
  subst S'
  rfl

/-- Germ formation commutes with transport along an equality of support sets. -/
theorem supportRelativeCohomologyGerm_transport_support
    {S' : Set X} (hS : S' = S) (V : Opens X) (x : X) (hx : x ∈ V)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S') n) :
    hS ▸ supportRelativeCohomologyGerm X S' n V x hx a =
      supportRelativeCohomologyGerm X S n V x hx (hS ▸ a) := by
  subst S'
  rfl

/-- The same germ-transport statement expressed through the named stalk transport. -/
theorem supportRelativeCohomologyStalkTransport_germ
    {S' : Set X} (hS : S' = S) (V : Opens X) (x : X) (hx : x ∈ V)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S') n) :
    supportRelativeCohomologyStalkTransport X S n hS x
      (supportRelativeCohomologyGerm X S' n V x hx a) =
    supportRelativeCohomologyGerm X S n V x hx (hS ▸ a) := by
  subst S'
  rfl

/-- Restriction of neighborhood relative cohomology commutes with transport of
the displayed support set. -/
theorem neighborhoodSupportRelativeCohomologyMap_transport_support
    {S' : Set X} (hS : S' = S) {U V : Opens X} (hUV : U ≤ V)
    (a : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (V : Set X) S') n) :
    relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap hUV S) (hS ▸ a) =
      hS ▸ relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap hUV S') a := by
  subst S'
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
    supportRelativeCohomologyGerm X S n U x hx
      (relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (U : Set X)) (V := (V : Set X)) hUV S) a) =
    supportRelativeCohomologyGerm X S n V x (hUV hx) a := by
  have h := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf X S n).naturality (homOfLE hUV).op) a
  simp only [ConcreteCategory.comp_apply] at h
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
    supportRelativeCohomologyGerm X S n U x (hWU hx) a =
      supportRelativeCohomologyGerm X S n V x (hWV hx) b := by
  rw [← supportRelativeCohomologyGerm_restrict X S n hWU x hx,
    ← supportRelativeCohomologyGerm_restrict X S n hWV x hx, h]

/-- When a neighborhood misses the support, its actual relative-chain complex is zero. -/
theorem neighborhoodSupportRelativeChains_isZero (V : Set X) (hV : ∀ x ∈ V, x ∉ S) :
    IsZero ((relativeChainFunctor ℚ).obj (neighborhoodSupportComplementPair V S)) := by
  have hset : {v : V | v.1 ∉ S} = Set.univ := Set.eq_univ_of_forall fun v => hV v.1 v.2
  change IsZero ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of V) _))
  rw [hset]
  let P := TopPair.ofSubset (X := TopCat.of V) (Set.univ : Set V)
  have hPi : IsIso P.map :=
    (TopCat.isIso_iff_isHomeomorph P.map).mpr (Homeomorph.Set.univ V).isHomeomorph
  have hchain : IsIso ((chainPairFunctor ℚ).obj P).hom := by
    change IsIso (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map P.map)
    infer_instance
  exact isZero_cokernel_of_epi ((chainPairFunctor ℚ).obj P).hom

/-- Relative cohomology vanishes on neighborhoods disjoint from the support. -/
theorem neighborhoodSupportRelativeCohomology_subsingleton
    (V : Set X) (hV : ∀ x ∈ V, x ∉ S) :
    Subsingleton (RelativeCohomology ℚ (neighborhoodSupportComplementPair V S) n) := by
  have hh : IsZero (RelativeHomology ℚ (neighborhoodSupportComplementPair V S) n) :=
    (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map_isZero
      (neighborhoodSupportRelativeChains_isZero X S V hV)
  let := ModuleCat.subsingleton_of_isZero hh
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Off closed support, every actual local relative class has zero sheaf germ. -/
theorem supportRelativeCohomologyGerm_eq_zero_of_not_mem (hS : IsClosed S)
    (V : Opens X) (x : X) (hx : x ∈ V) (hxS : x ∉ S)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    supportRelativeCohomologyGerm X S n V x hx a = 0 := by
  let W : Opens X := V ⊓ ⟨Sᶜ, hS.isOpen_compl⟩
  have hWV : W ≤ V := inf_le_left
  have hxW : x ∈ W := ⟨hx, hxS⟩
  let := neighborhoodSupportRelativeCohomology_subsingleton X S n W (fun _ hy => hy.2)
  rw [← supportRelativeCohomologyGerm_restrict X S n hWV x hxW]
  have hz : relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (V : Set X)) hWV S) a = 0 :=
    Subsingleton.elim _ _
  rw [hz]
  simp only [supportRelativeCohomologyGerm, map_zero]

end AlgebraicTopology.Singular
