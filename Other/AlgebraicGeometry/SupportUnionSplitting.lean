/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.FlasqueSupportedSections
public import Other.AlgebraicTopology.SupportedSectionRestrictionCone
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Splitting a closed support off an open piece of its complement

For two opens `U`, `U'` of a space `X` — equivalently two closed sets `Z = X ∖ U` and
`Z' = X ∖ U'` — the actual restriction of sections supported in `Z` from `X` to `U'` is onto
when the coefficients are flasque, and its kernel is exactly the sections supported in
`Z ∩ Z' = X ∖ (U ⊔ U')`. This gives the short exact sequence of section complexes

`0 → Γ(X, Γ̲_{Z ∩ Z'} K) → Γ(X, Γ̲_Z K) → Γ(U', Γ̲_Z K) → 0`

whose homology sequence is the only input needed for Mayer–Vietoris in a union of two closed
supports: taking `Z` to be one of the two closed sets and `U'` the complement of the other one,
the third term is insensitive to enlarging `Z` to the union (`supportedOutsideMap_app_bijective`),
so the resulting connecting maps identify the failure of
`H^n_{Z} ⊕ H^n_{Z'} → H^n_{Z ∪ Z'}` to be onto with `H^{n+1}_{Z ∩ Z'}`.

Nothing here is an obligation: every declaration is proved, for an arbitrary topological space
and arbitrary termwise-flasque coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-! ### Element-level API for supported sections -/

/-- The inclusion of supported sections into all sections is injective on every open. -/
theorem supportedOutsideInclusion_app_injective (U V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V)) := by
  apply (AddCommGrpCat.mono_iff_injective _).mp
  rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι X U V F]
  infer_instance

variable {X}

/-- A section supported outside `U` restricts to zero on every open contained in `U`. -/
theorem supportedOutsideSection_restrict_eq_zero {U V W : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X} (hWV : W ≤ V) (hWU : W ≤ U)
    (a : ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V)) :
    F.obj.map (homOfLE hWV).op
        (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) a) = 0 := by
  have h : F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op
      (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) a) = 0 := by
    simpa using ConcreteCategory.congr_hom
      (supportedOutsideInclusion_restrict_intersection X U V F) a
  calc F.obj.map (homOfLE hWV).op
        (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) a)
      = F.obj.map (homOfLE (le_inf hWV hWU)).op
          (F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op
            (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) a)) := by
        rw [← Functor.map_comp_apply]; rfl
    _ = 0 := by rw [h, map_zero]

/-- A section vanishing on an open squeezed between `V ⊓ U` and `V` is a supported section. -/
theorem exists_supportedOutsideSection_of_restrict_eq_zero' {U V W : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X} (hWV : W ≤ V) (hUW : V ⊓ U ≤ W)
    (s : F.obj.obj (op V)) (hs : F.obj.map (homOfLE hWV).op s = 0) :
    ∃ t : ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V),
      ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) t = s := by
  refine exists_supportedOutsideSection_of_restrict_eq_zero _ U V F s ?_
  calc F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s
      = F.obj.map (homOfLE hUW).op (F.obj.map (homOfLE hWV).op s) := by
        rw [← Functor.map_comp_apply]; rfl
    _ = 0 := by rw [hs, map_zero]

/-- Support enlargement, in element form: it does not change the underlying section. -/
theorem supportedOutsideMap_app_inclusion {U V : Opens X} (h : V ≤ U) (W : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X)
    (a : ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op W)) :
    ((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op W)
        (((sheafSectionsSupportedOutsideMap X h).app F).hom.app (op W) a) =
      ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op W) a := by
  have hcomp : (sheafSectionsSupportedOutsideMap X h).app F ≫
      (sheafSectionsSupportedOutsideInclusion X V).app F =
      (sheafSectionsSupportedOutsideInclusion X U).app F := by
    rw [← NatTrans.comp_app]
    exact NatTrans.congr_app (sheafSectionsSupportedOutsideMap_inclusion X h) F
  exact congrArg
    (fun f : (sheafSectionsSupportedOutside X U).obj F ⟶ F => f.hom.app (op W) a) hcomp


/-- Enlarging the support is bijective on the sections over an open on which the two supports
have the same trace: `V ≤ U` and `W ⊓ U ≤ V` force `W ⊓ U = W ⊓ V`. -/
theorem supportedOutsideMap_app_bijective {U V W : Opens X} (h : V ≤ U) (hW : W ⊓ U ≤ V)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Function.Bijective (((sheafSectionsSupportedOutsideMap X h).app F).hom.app (op W)) := by
  constructor
  · intro a b hab
    apply supportedOutsideInclusion_app_injective X U W F
    rw [← supportedOutsideMap_app_inclusion h W F a, ← supportedOutsideMap_app_inclusion h W F b,
      hab]
  · intro b
    have hs : F.obj.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op
        (((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op W) b) = 0 :=
      supportedOutsideSection_restrict_eq_zero inf_le_left inf_le_right b
    obtain ⟨t, ht⟩ := exists_supportedOutsideSection_of_restrict_eq_zero'
      (U := U) (V := W) (W := W ⊓ V) inf_le_left (le_inf inf_le_left hW) _ hs
    refine ⟨t, ?_⟩
    apply supportedOutsideInclusion_app_injective X V W F
    rw [supportedOutsideMap_app_inclusion, ht]

variable (X)

/-! ### The splitting short exact sequence -/

section Split

variable (U U' W : Opens X) (hUW : U ≤ W) (hU'W : U' ≤ W) (hcover : W ≤ U ⊔ U')

include hU'W in
/-- Restricting a section supported in `X ∖ W` to `U' ≤ W` gives zero. -/
theorem supportedOutsideMap_restrict_eq_zero (F : Sheaf AddCommGrpCat.{u} X)
    (a : ((sheafSectionsSupportedOutside X W).obj F).obj.obj (op ⊤)) :
    ((sheafSectionsSupportedOutside X U).obj F).obj.map (homOfLE (le_top : U' ≤ ⊤)).op
        (((sheafSectionsSupportedOutsideMap X hUW).app F).hom.app (op ⊤) a) = 0 := by
  apply supportedOutsideInclusion_app_injective X U U' F
  rw [map_zero]
  have hnat : ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op U')
      (((sheafSectionsSupportedOutside X U).obj F).obj.map (homOfLE (le_top : U' ≤ ⊤)).op
        (((sheafSectionsSupportedOutsideMap X hUW).app F).hom.app (op ⊤) a)) =
      F.obj.map (homOfLE (le_top : U' ≤ ⊤)).op
        (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op ⊤)
          (((sheafSectionsSupportedOutsideMap X hUW).app F).hom.app (op ⊤) a)) :=
    ConcreteCategory.congr_hom
      (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.naturality
        (homOfLE (le_top : U' ≤ ⊤)).op) _
  rw [hnat, supportedOutsideMap_app_inclusion]
  exact supportedOutsideSection_restrict_eq_zero le_top hU'W a

/-- The degreewise splitting sequence
`0 → Γ(X, Γ̲_{X∖W} F) → Γ(X, Γ̲_{X∖U} F) → Γ(U', Γ̲_{X∖U} F) → 0`. -/
def supportSplitSectionsShortComplexAux (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    (((sheafSectionsSupportedOutsideMap X hUW).app F).hom.app (op ⊤))
    (((sheafSectionsSupportedOutside X U).obj F).obj.map (homOfLE (le_top : U' ≤ ⊤)).op)
    (by ext a; exact supportedOutsideMap_restrict_eq_zero X U U' W hUW hU'W F a)

include hcover in
/-- The degreewise splitting sequence is short exact for flasque coefficients: restriction to
`U'` of the sections supported in `X ∖ U` is onto, and its kernel is exactly the sections
supported in `X ∖ W` for `W = U ⊔ U'`. -/
theorem supportSplitSectionsShortComplexAux_shortExact (F : Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] :
    (supportSplitSectionsShortComplexAux X U U' W hUW hU'W F).ShortExact where
  mono_f := by
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro a b hab
    apply supportedOutsideInclusion_app_injective X W ⊤ F
    rw [← supportedOutsideMap_app_inclusion hUW ⊤ F a, ← supportedOutsideMap_app_inclusion hUW ⊤ F b]
    exact congrArg _ hab
  epi_g := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact sheafSectionsSupportedOutside_restriction_surjective X U F (le_top : U' ≤ ⊤)
  exact := by
    rw [ShortComplex.ab_exact_iff]
    intro a ha
    have hU' : F.obj.map (homOfLE (le_top : U' ≤ ⊤)).op
        (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op ⊤) a) = 0 := by
      have hnat : ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op U')
          (((sheafSectionsSupportedOutside X U).obj F).obj.map
            (homOfLE (le_top : U' ≤ ⊤)).op a) =
          F.obj.map (homOfLE (le_top : U' ≤ ⊤)).op
            (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op ⊤) a) :=
        ConcreteCategory.congr_hom
          (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.naturality
            (homOfLE (le_top : U' ≤ ⊤)).op) a
      have ha' : ((sheafSectionsSupportedOutside X U).obj F).obj.map
          (homOfLE (le_top : U' ≤ ⊤)).op a = 0 := ha
      rw [← hnat, ha', map_zero]
    have hU : F.obj.map (homOfLE (le_top : U ≤ ⊤)).op
        (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op ⊤) a) = 0 :=
      supportedOutsideSection_restrict_eq_zero le_top le_rfl a
    have hsup : F.obj.map (homOfLE (le_top : W ≤ ⊤)).op
        (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op ⊤) a) = 0 := by
      refine F.eq_of_locally_eq₂ (homOfLE hUW) (homOfLE hU'W) hcover _ 0 ?_ ?_
      · rw [map_zero, ← hU, ← Functor.map_comp_apply]; rfl
      · rw [map_zero, ← hU', ← Functor.map_comp_apply]; rfl
    obtain ⟨t, ht⟩ := exists_supportedOutsideSection_of_restrict_eq_zero'
      (U := W) (V := ⊤) (W := W) le_top inf_le_right _ hsup
    refine ⟨t, ?_⟩
    show ((sheafSectionsSupportedOutsideMap X hUW).app F).hom.app (op ⊤) t = a
    apply supportedOutsideInclusion_app_injective X U ⊤ F
    rw [supportedOutsideMap_app_inclusion, ht]

end Split

/-! ### The splitting sequence of section complexes -/

section SplitComplex

variable (U U' W : Opens X) (hUW : U ≤ W) (hU'W : U' ≤ W) (hcover : W ≤ U ⊔ U')
  (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The complex of global sections supported in the closed set `X ∖ U`. -/
abbrev supportedSectionsComplex (V : Opens X) : CochainComplex AddCommGrpCat.{u} ℤ :=
  ((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).obj
    (((sheafSectionsSupportedOutside X V).mapHomologicalComplex (.up ℤ)).obj K)

/-- Cohomology with support in the closed set `X ∖ V`. -/
abbrev supportedSectionsHomology (V : Opens X) (n : ℤ) :=
  (supportedSectionsComplex X K V).homology n

/-- Enlarging the closed support from `X ∖ U` to `X ∖ V`, for `V ≤ U`. -/
def supportedSectionsEnlarge {U V : Opens X} (h : V ≤ U) (n : ℤ) :
    supportedSectionsHomology X K U n ⟶ supportedSectionsHomology X K V n :=
  HomologicalComplex.homologyMap
    (((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).map
      (((sheafSectionsSupportedOutsideMap X h).mapHomologicalComplex (.up ℤ)).app K)) n

/-- Enlarging the support twice is enlarging it once. -/
theorem supportedSectionsEnlarge_comp {V₁ V₂ V₃ : Opens X} (h : V₂ ≤ V₁) (h' : V₃ ≤ V₂)
    (n : ℤ) (a : supportedSectionsHomology X K V₁ n) :
    supportedSectionsEnlarge X K h' n (supportedSectionsEnlarge X K h n a) =
      supportedSectionsEnlarge X K (h'.trans h) n a := by
  have hmap : ((sheafSectionsSupportedOutsideMap X h).mapHomologicalComplex (.up ℤ)).app K ≫
      ((sheafSectionsSupportedOutsideMap X h').mapHomologicalComplex (.up ℤ)).app K =
      ((sheafSectionsSupportedOutsideMap X (h'.trans h)).mapHomologicalComplex (.up ℤ)).app K := by
    ext j
    exact NatTrans.congr_app (sheafSectionsSupportedOutsideMap_comp X h h') (K.X j)
  have key : supportedSectionsEnlarge X K h n ≫ supportedSectionsEnlarge X K h' n =
      supportedSectionsEnlarge X K (h'.trans h) n := by
    have h2 : HomologicalComplex.homologyMap
        ((((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).map
          (((sheafSectionsSupportedOutsideMap X h).mapHomologicalComplex (.up ℤ)).app K)) ≫
          (((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).map
            (((sheafSectionsSupportedOutsideMap X h').mapHomologicalComplex (.up ℤ)).app K))) n =
        supportedSectionsEnlarge X K h n ≫ supportedSectionsEnlarge X K h' n :=
      HomologicalComplex.homologyMap_comp _ _ n
    rw [← h2, ← Functor.map_comp, hmap]
    rfl
  exact ConcreteCategory.congr_hom key a

/-- The splitting sequence of section complexes
`0 → Γ(X, Γ̲_{X∖W} K) → Γ(X, Γ̲_{X∖U} K) → Γ(U', Γ̲_{X∖U} K) → 0`. -/
def supportSplitSectionsShortComplex : ShortComplex (CochainComplex AddCommGrpCat.{u} ℤ) :=
  ShortComplex.mk
    (((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).map
      (((sheafSectionsSupportedOutsideMap X hUW).mapHomologicalComplex (.up ℤ)).app K))
    (sectionComplexRestriction X (.up ℤ)
      (((sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).obj K)
      (homOfLE (le_top : U' ≤ ⊤)))
    (by
      ext n : 1
      exact (supportSplitSectionsShortComplexAux X U U' W hUW hU'W (K.X n)).zero)

include hcover in
/-- The splitting sequence is short exact on termwise flasque coefficients. -/
theorem supportSplitSectionsShortComplex_shortExact (hK : ∀ n, (K.X n).IsFlasque) :
    (supportSplitSectionsShortComplex X U U' W hUW hU'W K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have := hK n
  exact supportSplitSectionsShortComplexAux_shortExact X U U' W hUW hU'W hcover (K.X n)

end SplitComplex

/-! ### Mayer–Vietoris for a union of two closed supports -/

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Mayer–Vietoris in a union of two closed supports.** Let `Z₁ = X ∖ U₁` and `Z₂ = X ∖ U₂` be
closed, with union `X ∖ Uu` and intersection `X ∖ Ui`. If the cohomology supported in the
intersection vanishes in degree `n + 1`, then every degree-`n` class supported in the union is
the sum of a class supported in `Z₁` and a class supported in `Z₂`.

The hypotheses on the four opens are stated as inequalities, so that no transport along
equalities of supports is needed at the point of use. -/
theorem exists_supportedSectionsEnlarge_add_eq
    (U₁ U₂ Uu Ui : Opens X)
    (h₁ : Uu ≤ U₁) (h₂ : Uu ≤ U₂) (hmeet : U₁ ⊓ U₂ ≤ Uu)
    (h₁' : U₁ ≤ Ui) (h₂' : U₂ ≤ Ui) (hcover : Ui ≤ U₁ ⊔ U₂)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (hK : ∀ n, (K.X n).IsFlasque)
    (n m : ℤ) (hm : m = n + 1)
    (hvan : IsZero (supportedSectionsHomology X K Ui m))
    (β : supportedSectionsHomology X K Uu n) :
    ∃ (a : supportedSectionsHomology X K U₁ n) (b : supportedSectionsHomology X K U₂ n),
      β = supportedSectionsEnlarge X K h₁ n a + supportedSectionsEnlarge X K h₂ n b := by
  have hS₁ := supportSplitSectionsShortComplex_shortExact X U₁ U₂ Ui h₁' h₂' hcover K hK
  have hS₂ := supportSplitSectionsShortComplex_shortExact X Uu U₂ U₂ h₂ le_rfl le_sup_right K hK
  set S₁ := supportSplitSectionsShortComplex X U₁ U₂ Ui h₁' h₂' K with hS₁def
  set S₂ := supportSplitSectionsShortComplex X Uu U₂ U₂ h₂ le_rfl K with hS₂def
  -- the support enlargement, on sections over `U₂`, is an isomorphism of complexes
  let ψ : S₁.X₃ ⟶ S₂.X₃ :=
    ((supportEvaluation X U₂).mapHomologicalComplex (.up ℤ)).map
      (((sheafSectionsSupportedOutsideMap X h₁).mapHomologicalComplex (.up ℤ)).app K)
  have hψ : IsIso ψ := by
    have : ∀ j : ℤ, IsIso (ψ.f j) := fun j =>
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (supportedOutsideMap_app_bijective h₁ ((le_of_eq (inf_comm U₂ U₁)).trans hmeet) (K.X j))
    exact HomologicalComplex.Hom.isIso_of_components ψ
  -- the commuting square
  have hsquare : S₁.g ≫ ψ =
      ((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).map
        (((sheafSectionsSupportedOutsideMap X h₁).mapHomologicalComplex (.up ℤ)).app K) ≫ S₂.g :=
    (((supportEvaluationRestriction X (homOfLE (le_top : U₂ ≤ ⊤))).mapHomologicalComplex
      (.up ℤ)).naturality
      (((sheafSectionsSupportedOutsideMap X h₁).mapHomologicalComplex (.up ℤ)).app K)).symm
  have hepi : Epi (HomologicalComplex.homologyMap S₁.g n) :=
    (hS₁.homology_exact₃ n m (by simp [hm])).epi_f (hvan.eq_zero_of_tgt _)
  have hepi' : Epi (HomologicalComplex.homologyMap S₁.g n ≫
      HomologicalComplex.homologyMap ψ n) := epi_comp _ _
  obtain ⟨a, ha⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi'
    (HomologicalComplex.homologyMap S₂.g n β)
  refine ⟨a, ?_⟩
  have h1 : HomologicalComplex.homologyMap (S₁.g ≫ ψ) n =
      HomologicalComplex.homologyMap
        (((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).map
          (((sheafSectionsSupportedOutsideMap X h₁).mapHomologicalComplex (.up ℤ)).app K) ≫
          S₂.g) n :=
    congrArg (fun φ => HomologicalComplex.homologyMap φ n) hsquare
  have h2 : HomologicalComplex.homologyMap
      (((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).map
        (((sheafSectionsSupportedOutsideMap X h₁).mapHomologicalComplex (.up ℤ)).app K) ≫
        S₂.g) n =
      supportedSectionsEnlarge X K h₁ n ≫ HomologicalComplex.homologyMap S₂.g n :=
    HomologicalComplex.homologyMap_comp _ _ n
  have hcomm0 : HomologicalComplex.homologyMap S₁.g n ≫ HomologicalComplex.homologyMap ψ n =
      supportedSectionsEnlarge X K h₁ n ≫ HomologicalComplex.homologyMap S₂.g n :=
    (HomologicalComplex.homologyMap_comp S₁.g ψ n).symm.trans (h1.trans h2)
  have hcomm : HomologicalComplex.homologyMap S₂.g n (supportedSectionsEnlarge X K h₁ n a) =
      HomologicalComplex.homologyMap S₂.g n β := by
    rw [← ha]
    exact (ConcreteCategory.congr_hom hcomm0 a).symm
  have hker : HomologicalComplex.homologyMap S₂.g n
      (β - supportedSectionsEnlarge X K h₁ n a) = 0 := by
    simp only [map_sub, hcomm, sub_self]
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp (hS₂.homology_exact₂ n) _ hker
  refine ⟨b, ?_⟩
  have : supportedSectionsEnlarge X K h₂ n b = β - supportedSectionsEnlarge X K h₁ n a := hb
  rw [this, add_sub_cancel]

end TopCat.Sheaf
