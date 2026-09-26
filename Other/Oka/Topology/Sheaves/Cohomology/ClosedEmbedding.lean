/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.MayerVietoris
public import Other.Oka.Topology.Sheaves.Cohomology.Pullback
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Pushforward of abelian sheaves along a closed embedding

Let `f : Y ⟶ X` be a closed embedding of topological spaces and `f_*` the pushforward of abelian
sheaves. The stalk of `f_* G` at `f y` is the stalk of `G` at `y`, and the stalk at a point off the
image of `f` is zero. Consequently `f_*` is exact; it preserves injective objects since its left
adjoint `f⁻¹` is exact. Dimension shifting then identifies the cohomology of `G` with that of
`f_* G`:

`TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv : Hⁿ(Y, G) ≃+ Hⁿ(X, f_* G)`.

## Main results

- `TopCat.Sheaf.pushforwardAbStalkIso`: `(f_* G)_{f y} ≅ G_y` for `f` inducing, naturally in `G`.
- `TopCat.Sheaf.isZero_stalk_pushforwardAb`: `(f_* G)_x = 0` for `x` off the closed image of `f`.
- `TopCat.Sheaf.map_exact_pushforwardAb`, `preservesFiniteColimits_pushforwardAb`: `f_*` is
  exact.
- `TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv`: `Hⁿ(Y, G) ≃+ Hⁿ(X, f_* G)`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Abelian Topology

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}} (f : Y ⟶ X)

/-- The pushforward functor on abelian sheaves, typed as a functor between sheaf categories on
sites. -/
noncomputable abbrev pushforwardAb : AbSheaf Y ⥤ AbSheaf X :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f

instance : PreservesLimits (pushforwardAb f) :=
  (pullbackPushforwardAdjunction AddCommGrpCat.{u} f).rightAdjoint_preservesLimits

instance : (pushforwardAb f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The stalk of a pushforward along an inducing map** at `f y` is the stalk at `y`, naturally
in the sheaf. -/
noncomputable def pushforwardAbStalkIso (hf : IsInducing f) (y : Y) :
    pushforwardAb f ⋙ TopCat.Sheaf.stalkFunctor X (f y) ≅ TopCat.Sheaf.stalkFunctor Y y :=
  NatIso.ofComponents
    (fun G ↦ @asIso _ _ _ _ (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f G.obj y)
      (TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
        hf G.obj y))
    (fun {G G'} φ ↦ by
      refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
      change TopCat.Presheaf.germ ((pushforwardAb f).obj G).obj U (f y) hU ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f y)).map
            ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map φ.hom) ≫ _ =
        TopCat.Presheaf.germ ((pushforwardAb f).obj G).obj U (f y) hU ≫ _ ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ.hom
      simp only [asIso_hom]
      erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
        TopCat.Presheaf.stalkPushforward_germ, TopCat.Presheaf.stalkPushforward_germ_assoc,
        TopCat.Presheaf.stalkFunctor_map_germ]
      rfl)

/-- **Off the closed image of `f`, the stalks of a pushforward vanish.** -/
theorem isZero_stalk_pushforwardAb (hcl : IsClosed (Set.range f)) {x : X}
    (hx : x ∉ Set.range f) (G : AbSheaf Y) :
    IsZero ((TopCat.Sheaf.stalkFunctor X x).obj ((pushforwardAb f).obj G)) := by
  set U : Opens X := ⟨(Set.range f)ᶜ, hcl.isOpen_compl⟩
  have hxU : x ∈ U := hx
  have hbot : ∀ V : Opens X, V ≤ U → (Opens.map f).obj V = ⊥ := by
    intro V hV
    ext y
    simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot,
      Set.mem_empty_iff_false, iff_false]
    exact fun hy ↦ hV hy ⟨y, rfl⟩
  refine AddCommGrpCat.isZero_iff_subsingleton.2 ⟨fun a b ↦ ?_⟩
  suffices h : ∀ s : (TopCat.Sheaf.stalkFunctor X x).obj ((pushforwardAb f).obj G), s = 0 by
    rw [h a, h b]
  intro s
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq ((pushforwardAb f).obj G).obj s
  have hsub : Subsingleton ((((pushforwardAb f).obj G).obj).obj (op (V ⊓ U))) := by
    have := TopCat.Sheaf.isTerminalOfEqEmpty G (hbot (V ⊓ U) inf_le_right)
    exact AddCommGrpCat.isZero_iff_subsingleton.1 this.isZero
  have key := TopCat.Presheaf.germ_res_apply ((pushforwardAb f).obj G).obj
    (homOfLE (inf_le_left : V ⊓ U ≤ V)) x ⟨hxV, hxU⟩ t
  rw [← key, show ((pushforwardAb f).obj G).obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op t = 0
    from Subsingleton.elim _ _, map_zero]
  rfl

variable {f}

/-- **Pushforward along a closed embedding is exact**: it sends exact short complexes to exact
short complexes. -/
theorem map_exact_pushforwardAb (hf : IsClosedEmbedding f) (S : ShortComplex (AbSheaf Y))
    (hS : S.Exact) : (S.map (pushforwardAb f)).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalk_exact]
  intro x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨y, rfl⟩ := hx
    have e : (S.map (pushforwardAb f)).map (TopCat.Sheaf.stalkFunctor X (f y)) ≅
        S.map (TopCat.Sheaf.stalkFunctor Y y) :=
      ShortComplex.isoMk ((pushforwardAbStalkIso f hf.isInducing y).app _)
        ((pushforwardAbStalkIso f hf.isInducing y).app _)
        ((pushforwardAbStalkIso f hf.isInducing y).app _)
        ((pushforwardAbStalkIso f hf.isInducing y).hom.naturality S.f).symm
        ((pushforwardAbStalkIso f hf.isInducing y).hom.naturality S.g).symm
    exact (ShortComplex.exact_iff_of_iso e).2
      ((TopCat.Sheaf.exact_iff_stalk_exact S).1 hS y)
  · exact ShortComplex.exact_of_isZero_X₂ _
      (isZero_stalk_pushforwardAb f hf.isClosed_range hx S.X₂)

/-- Pushforward along a closed embedding preserves finite limits and finite colimits. -/
theorem preservesFiniteLimitsAndColimits_pushforwardAb (hf : IsClosedEmbedding f) :
    PreservesFiniteLimits (pushforwardAb f) ∧ PreservesFiniteColimits (pushforwardAb f) :=
  ((Functor.exact_tfae (pushforwardAb f)).out 1 3).1 (map_exact_pushforwardAb hf)

/-- **Pushforward along a closed embedding preserves finite colimits.** -/
theorem preservesFiniteColimits_pushforwardAb (hf : IsClosedEmbedding f) :
    PreservesFiniteColimits (pushforwardAb f) :=
  (preservesFiniteLimitsAndColimits_pushforwardAb hf).2

variable (f) in
/-- Pushforward preserves injective objects, its left adjoint `f⁻¹` being exact. -/
instance preservesInjectiveObjects_pushforwardAb :
    (pushforwardAb f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (pullbackPushforwardAdjunction AddCommGrpCat.{u} f)

variable (f) in
/-- The morphism `ℤ_X ⟶ f_* ℤ_Y` adjoint to `f⁻¹ ℤ_X ≅ ℤ_Y`. -/
noncomputable def constZToPushforward : constZ X ⟶ (pushforwardAb f).obj (constZ Y) :=
  (pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _ (pullbackConstZIso f).hom

lemma bijective_constZToPushforward_comp (B : AbSheaf Y) :
    Function.Bijective (fun x : constZ Y ⟶ B ↦
      constZToPushforward f ≫ (pushforwardAb f).map x) := by
  have : (fun x : constZ Y ⟶ B ↦ constZToPushforward f ≫ (pushforwardAb f).map x) =
      (pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _ ∘
        fun x ↦ (pullbackConstZIso f).hom ≫ x := by
    funext x
    exact ((pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv_naturality_right _ _).symm
  rw [this]
  exact (Equiv.bijective _).comp ((Iso.homCongr (pullbackConstZIso f) (Iso.refl B)).symm.bijective)

/-- **The cohomology of a sheaf on a closed subspace is the cohomology of its pushforward**:
`Hⁿ(Y, G) ≃+ Hⁿ(X, f_* G)`, `x ↦ (ℤ_X ⟶ f_* ℤ_Y) ∘ f_*(x)` (`CategoryTheory.extComparison`). -/
noncomputable def H.pushforwardClosedEmbeddingAddEquiv (hf : IsClosedEmbedding f) (G : AbSheaf Y)
    (n : ℕ) : H G n ≃+ H ((pushforwardAb f).obj G) n :=
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf).1
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf).2
  AddEquiv.ofBijective (extComparison (pushforwardAb f) (constZToPushforward f) G n)
    (extComparison_bijective _ _ bijective_constZToPushforward_comp G n)

end TopCat.Sheaf

end
