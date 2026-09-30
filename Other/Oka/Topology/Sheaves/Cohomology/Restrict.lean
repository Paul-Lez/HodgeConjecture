/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Other.Oka.Topology.Sheaves.Cohomology.Pullback

/-!
# Restriction of abelian sheaves to open subspaces and cohomology

For an open embedding `f : Y ⟶ X` the inverse image of a sheaf is computed naively,
`(f⁻¹ F)(V) = F(f '' V)` (Mathlib's `Topology.IsOpenEmbedding.sheafPullback`). We show:

* the naive restriction `TopCat.Sheaf.restrictAb hf` is exact and preserves constant sheaves, so
  it induces restriction maps `TopCat.Sheaf.H.restrict hf : Hⁿ(X, F) →+ Hⁿ(Y, F|_Y)`, natural in
  `F` and compatible with connecting homomorphisms;
* it preserves injective objects (`TopCat.Sheaf.injective_restrictAb`): its left adjoint, the
  extension by zero `sheafify ∘ Lan`, preserves monomorphisms, because the left Kan extension
  along `(IsOpenMap.functor f).op` is computed by colimits over categories which are empty or
  have a terminal object (`CategoryTheory.Functor.lan_preservesMonomorphisms_of_isTerminal`).

For `U : Opens X` we specialise to `TopCat.Sheaf.restrictOpen U` (a sheaf on the subspace `U`
with `(F|_U)(V) = F(V)` for `V ⊆ U` viewed in `X`), the restriction maps
`TopCat.Sheaf.H.restrictTo` and the identification `TopCat.Sheaf.H.restrictOpenEquiv₀` of
`H⁰(U, F|_U)` with `F(U)`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Abelian Topology

namespace CategoryTheory.Functor

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (G : C ⥤ D)
  (A : Type*) [Category.{u} A] [HasColimits A] [HasZeroMorphisms A] [HasPullbacks A]

/-- The left Kan extension along `G` preserves monomorphisms if every comma category
`CostructuredArrow G d` is empty or has a terminal object. -/
lemma lan_preservesMonomorphisms_of_isTerminal
    (hG : ∀ d : D, IsEmpty (CostructuredArrow G d) ∨
      ∃ t : CostructuredArrow G d, Nonempty (IsTerminal t)) :
    (G.lan : (C ⥤ A) ⥤ (D ⥤ A)).PreservesMonomorphisms where
  preserves {P Q} φ _ := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun d => ?_
    let e := lanEvaluationIsoColim A G d
    have h' := (Iso.eq_comp_inv (e.app Q)).2 (e.hom.naturality φ)
    change (G.lan.map φ).app d = _ at h'
    suffices Mono (((Functor.whiskeringLeft _ _ A).obj (CostructuredArrow.proj G d) ⋙
        colim).map φ) by
      rw [h']
      exact @mono_comp _ _ _ _ _ _ (@mono_comp _ _ _ _ _ (e.app P).hom inferInstance _ this) _
        inferInstance
    change Mono (colimMap (whiskerLeft (CostructuredArrow.proj G d) φ))
    rcases hG d with h | ⟨t, ⟨ht⟩⟩
    · apply IsZero.mono
      rw [IsZero.iff_id_eq_zero]
      exact colimit.hom_ext fun j => isEmptyElim j
    · have : IsIso (colimit.ι (CostructuredArrow.proj G d ⋙ P) t) :=
        (colimit.isColimit _).isIso_ι_app_of_isTerminal _ ht
      have : IsIso (colimit.ι (CostructuredArrow.proj G d ⋙ Q) t) :=
        (colimit.isColimit _).isIso_ι_app_of_isTerminal _ ht
      have hc : colimMap (whiskerLeft (CostructuredArrow.proj G d) φ) =
          CategoryTheory.inv (colimit.ι (CostructuredArrow.proj G d ⋙ P) t) ≫
            (whiskerLeft (CostructuredArrow.proj G d) φ).app t ≫
            colimit.ι (CostructuredArrow.proj G d ⋙ Q) t := by
        rw [IsIso.eq_inv_comp]
        exact ι_colimMap (whiskerLeft (CostructuredArrow.proj G d) φ) t
      have : Mono ((whiskerLeft (CostructuredArrow.proj G d) φ).app t) :=
        (NatTrans.mono_iff_mono_app φ).1 inferInstance t.left
      rw [hc]
      exact @mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ this _ inferInstance)

end CategoryTheory.Functor

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f)

/-- The restriction of abelian sheaves along an open embedding `f : Y ⟶ X`:
`(F|_Y)(V) = F(f '' V)`. -/
noncomputable abbrev restrictAb : AbSheaf X ⥤ AbSheaf Y :=
  hf.sheafPullback AddCommGrpCat.{u}

/-- The inverse image along an open embedding is the naive restriction. -/
noncomputable def pullbackAbIsoRestrictAb : pullbackAb f ≅ restrictAb hf :=
  hf.sheafPullbackIso AddCommGrpCat.{u}

instance : PreservesFiniteLimits (restrictAb hf) :=
  preservesFiniteLimits_of_natIso (pullbackAbIsoRestrictAb hf)

instance : PreservesFiniteColimits (restrictAb hf) :=
  preservesFiniteColimits_of_natIso (pullbackAbIsoRestrictAb hf)

instance : (restrictAb hf).Additive :=
  Functor.additive_of_iso (pullbackAbIsoRestrictAb hf)

/-- The restriction of `ℤ_X` along an open embedding is `ℤ_Y`. -/
noncomputable def restrictConstZIso : (restrictAb hf).obj (constZ X) ≅ constZ Y :=
  ((pullbackAbIsoRestrictAb hf).app _).symm ≪≫ pullbackConstZIso f

/-- The restriction map `Hⁿ(X, F) → Hⁿ(Y, F|_Y)` along an open embedding. -/
noncomputable def H.restrict {F : AbSheaf X} {n : ℕ} : H F n →+ H ((restrictAb hf).obj F) n :=
  H.mapOfExact (restrictAb hf) (restrictConstZIso hf)

/-- The restriction map is natural in the sheaf. -/
lemma H.restrict_map {F G : AbSheaf X} (φ : F ⟶ G) {n : ℕ} (x : H F n) :
    H.restrict hf (H.map φ n x) = H.map ((restrictAb hf).map φ) n (H.restrict hf x) :=
  H.mapOfExact_map _ _ φ x

/-- The restriction map commutes with the connecting homomorphisms. -/
lemma H.restrict_δ {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) :
    H.restrict hf (H.δ hS n₀ n₁ h x) =
      H.δ (hS.map_of_exact (restrictAb hf)) n₀ n₁ h (H.restrict hf x) :=
  H.mapOfExact_δ _ _ hS h x

/-- For an open embedding `f`, each comma category of `(IsOpenMap.functor f).op` is empty or has a
terminal object: over `W`, it is empty unless `W ⊆ range f`, in which case `f⁻¹ W` is
terminal. -/
lemma isEmpty_or_isTerminal_costructuredArrow (W : (Opens X)ᵒᵖ) :
    IsEmpty (CostructuredArrow hf.isOpenMap.functor.op W) ∨
      ∃ t : CostructuredArrow hf.isOpenMap.functor.op W, Nonempty (IsTerminal t) := by
  by_cases h : (W.unop : Set X) ⊆ Set.range f
  · right
    refine ⟨CostructuredArrow.mk (Y := op ((Opens.map f).obj W.unop)) (homOfLE ?_).op, ⟨?_⟩⟩
    · intro x hx
      obtain ⟨y, rfl⟩ := h hx
      exact ⟨y, hx, rfl⟩
    · refine IsTerminal.ofUniqueHom (fun T => CostructuredArrow.homMk (homOfLE ?_).op ?_) ?_
      · intro y hy
        obtain ⟨y', hy', e⟩ := leOfHom T.hom.unop hy
        rwa [hf.injective e] at hy'
      · rfl
      · intros
        apply CostructuredArrow.hom_ext
        exact Subsingleton.elim _ _
  · left
    refine ⟨fun T => h ?_⟩
    intro x hx
    obtain ⟨y, -, rfl⟩ := leOfHom T.hom.unop hx
    exact ⟨y, rfl⟩

/-- Restriction along an open embedding preserves injective sheaves. -/
instance preservesInjectiveObjects_restrictAb : (restrictAb hf).PreservesInjectiveObjects := by
  have := hf.functor_isContinuous
  have := Functor.lan_preservesMonomorphisms_of_isTerminal hf.isOpenMap.functor.op
    AddCommGrpCat.{u} (isEmpty_or_isTerminal_costructuredArrow hf)
  have : (Functor.sheafPullbackConstruction.sheafPullback hf.isOpenMap.functor
      AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).PreservesMonomorphisms := by
    unfold Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous hf.isOpenMap.functor
      AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))

instance injective_restrictAb (I : AbSheaf X) [Injective I] :
    Injective ((restrictAb hf).obj I) :=
  (restrictAb hf).injective_obj I

section Opens

variable (U : Opens X)

/-- The restriction `F ↦ F|_U` of abelian sheaves to the open subspace `U`. On sections,
`(F|_U)(V) = F(V)` where `V ⊆ U` is regarded as an open of `X`. -/
noncomputable abbrev restrictOpen : AbSheaf X ⥤ AbSheaf ((Opens.toTopCat X).obj U) :=
  restrictAb U.isOpenEmbedding

/-- The restriction map `Hⁿ(X, F) → Hⁿ(U, F|_U)`. -/
noncomputable abbrev H.restrictTo {F : AbSheaf X} {n : ℕ} :
    H F n →+ H ((restrictOpen U).obj F) n :=
  H.restrict U.isOpenEmbedding

/-- The image of the top open of `U` in `X` is `U`. -/
lemma functor_obj_top : U.isOpenEmbedding.isOpenMap.functor.obj ⊤ = U := by
  ext x
  simp

/-- The sections of `F|_U` over `V : Opens U` are the sections of `F` over `V`, viewed as an
open of `X`. -/
lemma restrictOpen_obj_obj (F : AbSheaf X) (V : Opens ((Opens.toTopCat X).obj U)) :
    ((restrictOpen U).obj F).obj.obj (op V) =
      F.obj.obj (op (U.isOpenEmbedding.isOpenMap.functor.obj V)) := rfl

/-- The global sections of `F|_U` are the sections of `F` over `U`. -/
noncomputable def restrictOpenGlobalSectionsIso (F : AbSheaf X) :
    ((restrictOpen U).obj F).obj.obj (op ⊤) ≅ F.obj.obj (op U) :=
  F.obj.mapIso (eqToIso (functor_obj_top U)).op.symm

/-- `H⁰(U, F|_U) ≅ F(U)`. -/
noncomputable def H.restrictOpenEquiv₀ (F : AbSheaf X) :
    H ((restrictOpen U).obj F) 0 ≃+ F.obj.obj (op U) :=
  (H.equiv₀ _).trans (restrictOpenGlobalSectionsIso U F).addCommGroupIsoToAddEquiv

/-- The identification `H⁰(U, F|_U) ≅ F(U)` is natural in `F`. -/
lemma H.restrictOpenEquiv₀_map {F G : AbSheaf X} (φ : F ⟶ G)
    (x : H ((restrictOpen U).obj F) 0) :
    H.restrictOpenEquiv₀ U G (H.map ((restrictOpen U).map φ) 0 x) =
      φ.hom.app (op U) (H.restrictOpenEquiv₀ U F x) := by
  simp only [H.restrictOpenEquiv₀, AddEquiv.trans_apply, H.equiv₀_map,
    Iso.addCommGroupIsoToAddEquiv_apply, restrictOpenGlobalSectionsIso, Functor.mapIso_hom]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  congr 2
  exact (φ.hom.naturality _).symm

end Opens

end TopCat.Sheaf

end
