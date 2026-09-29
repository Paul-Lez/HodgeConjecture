/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Functors
public import Other.Oka.Topology.Sheaves.Cohomology.Basic

/-!
# Functoriality of sheaf cohomology in the space

An exact functor `Φ` from abelian sheaves on `X` to abelian sheaves on `Y` together with an
isomorphism `Φ(ℤ_X) ≅ ℤ_Y` induces maps `Hⁿ(X, F) → Hⁿ(Y, Φ F)`
(`TopCat.Sheaf.H.mapOfExact`), natural in `F` and compatible with connecting homomorphisms.

The main instance is the inverse image `f⁻¹ = TopCat.Sheaf.pullback AddCommGrpCat f` along a
continuous map `f : Y ⟶ X`: it is exact (`Opens.map f` is representably flat) and preserves the
constant sheaf (`TopCat.Sheaf.pullbackConstZIso`), which gives the pullback map
`TopCat.Sheaf.H.pullback f : Hⁿ(X, F) →+ Hⁿ(Y, f⁻¹ F)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}

section ExactFunctor

variable (Φ : AbSheaf X ⥤ AbSheaf Y) [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] (e : Φ.obj (constZ X) ≅ constZ Y)

/-- The map `Hⁿ(X, F) → Hⁿ(Y, Φ F)` induced by an exact functor `Φ` with `Φ(ℤ_X) ≅ ℤ_Y`. -/
noncomputable def H.mapOfExact {F : AbSheaf X} {n : ℕ} :
    H F n →+ H (Φ.obj F) n where
  toFun x := (Ext.mk₀ e.inv).comp (x.mapExactFunctor Φ) (zero_add n)
  map_zero' := by simp
  map_add' x y := by simp [Ext.mapExactFunctor_add]

lemma H.mapOfExact_apply {F : AbSheaf X} {n : ℕ} (x : H F n) :
    H.mapOfExact Φ e x = (Ext.mk₀ e.inv).comp (x.mapExactFunctor Φ) (zero_add n) := rfl

/-- `TopCat.Sheaf.H.mapOfExact` is natural in the sheaf. -/
lemma H.mapOfExact_map {F G : AbSheaf X} (φ : F ⟶ G) {n : ℕ} (x : H F n) :
    H.mapOfExact Φ e (H.map φ n x) = H.map (Φ.map φ) n (H.mapOfExact Φ e x) := by
  simp only [H.mapOfExact_apply, H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc_of_third_deg_zero]

/-- `TopCat.Sheaf.H.mapOfExact` commutes with the connecting homomorphisms. -/
lemma H.mapOfExact_δ {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) :
    H.mapOfExact Φ e (H.δ hS n₀ n₁ h x) =
      H.δ (hS.map_of_exact Φ) n₀ n₁ h (H.mapOfExact Φ e x) := by
  simp only [H.mapOfExact_apply, H.δ_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n₀) h (by omega)).symm

end ExactFunctor

section Pullback

variable (f : Y ⟶ X)

/-- The inverse image functor `f⁻¹` on abelian sheaves, typed as a functor between sheaf
categories on sites. -/
noncomputable abbrev pullbackAb : AbSheaf X ⥤ AbSheaf Y :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} f

instance : PreservesFiniteLimits (pullbackAb f) :=
  Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat _ _ _ _

instance : PreservesColimits (pullbackAb f) :=
  (pullbackPushforwardAdjunction AddCommGrpCat.{u} f).leftAdjoint_preservesColimits

instance : PreservesFiniteColimits (pullbackAb f) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

instance : (pullbackAb f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The composite of the constant sheaf functor on `X` with `f⁻¹` is left adjoint to taking
global sections on `Y`. -/
noncomputable def pullbackConstantSheafAdj :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙ pullbackAb f) ⊣
      (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤) :=
  (constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop).comp
    (pullbackPushforwardAdjunction AddCommGrpCat.{u} f)

/-- `f⁻¹` commutes with constant sheaves. -/
noncomputable def pullbackConstantSheafIso :
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙ pullbackAb f ≅
      constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  (pullbackConstantSheafAdj f).leftAdjointUniq
    (constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop)

/-- `f⁻¹ ℤ_X ≅ ℤ_Y`. -/
noncomputable def pullbackConstZIso : (pullbackAb f).obj (constZ X) ≅ constZ Y :=
  (pullbackConstantSheafIso f).app _

/-- The pullback map `Hⁿ(X, F) → Hⁿ(Y, f⁻¹ F)` along a continuous map `f : Y ⟶ X`. -/
noncomputable def H.pullback {F : AbSheaf X} {n : ℕ} :
    H F n →+ H ((pullbackAb f).obj F) n :=
  H.mapOfExact (pullbackAb f) (pullbackConstZIso f)

/-- The pullback map is natural in the sheaf. -/
lemma H.pullback_map {F G : AbSheaf X} (φ : F ⟶ G) {n : ℕ} (x : H F n) :
    H.pullback f (H.map φ n x) = H.map ((pullbackAb f).map φ) n (H.pullback f x) :=
  H.mapOfExact_map _ _ φ x

/-- The pullback map commutes with the connecting homomorphisms. -/
lemma H.pullback_δ {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) :
    H.pullback f (H.δ hS n₀ n₁ h x) =
      H.δ (hS.map_of_exact (pullbackAb f)) n₀ n₁ h (H.pullback f x) :=
  H.mapOfExact_δ _ _ hS h x

end Pullback

end TopCat.Sheaf

end
