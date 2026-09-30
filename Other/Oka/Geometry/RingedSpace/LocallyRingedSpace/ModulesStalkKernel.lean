/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesClosedEmbedding
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkSurjective

/-!
# Kernels, monomorphisms and vanishing on stalks

For sheaves of modules on a locally ringed space `Y`:

- `AlgebraicGeometry.LocallyRingedSpace.exists_nhds_subsingleton_stalk`: a sheaf of finite type
  whose stalk at `y` vanishes has vanishing stalks near `y`;
- `AlgebraicGeometry.LocallyRingedSpace.exists_stalkFunctor_map_kernelι_eq`: the stalk of
  `kernel φ` maps onto the kernel of the stalk of `φ`;
- `AlgebraicGeometry.LocallyRingedSpace.mono_of_forall_injective_stalk`: a morphism which is
  injective on all stalks is a monomorphism;
- `AlgebraicGeometry.LocallyRingedSpace.Hom.bijective_stalkFunctor_map_pushforward_of_isInducing`:
  pushforward along an inducing map preserves bijectivity on stalks at points of the image.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- **Vanishing of a stalk spreads to a neighbourhood** for a sheaf of finite type. -/
lemma exists_nhds_subsingleton_stalk (M : SheafOfModules.{u} Y.ringSheaf) [M.IsFiniteType]
    (y : Y) (h : Subsingleton ((Y.stalkFunctor y).obj M)) :
    ∃ U : Opens Y, y ∈ U ∧ ∀ w ∈ U, Subsingleton ((Y.stalkFunctor w).obj M) := by
  obtain ⟨U, hyU, hZ⟩ := exists_isZero_restrictModules M y h
  refine ⟨U, hyU, fun w hw ↦ ?_⟩
  let w' : Y.restrict U.isOpenEmbedding := ⟨w, hw⟩
  haveI : Subsingleton (((Y.restrict U.isOpenEmbedding).stalkFunctor w').obj
      ((Y.restrictModules U).obj M)) :=
    ModuleCat.subsingleton_of_isZero (Functor.map_isZero _ hZ)
  exact ((Y.ofRestrict U.isOpenEmbedding).stalkPullbackModulesSemilinearEquiv w'
    M).toEquiv.subsingleton

/-- An element of a stalk killed by `φ` comes from the stalk of `kernel φ`. -/
lemma exists_stalkFunctor_map_kernelι_eq {A B : SheafOfModules.{u} Y.ringSheaf} (φ : A ⟶ B)
    (y : Y) (m : (Y.stalkFunctor y).obj A) (hm : (Y.stalkFunctor y).map φ m = 0) :
    ∃ k, (Y.stalkFunctor y).map (kernel.ι φ) k = m :=
  (exact_stalk (ShortComplex.mk _ _ (kernel.condition φ))
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ)) y m).1 hm

/-- **A morphism which is injective on all stalks is a monomorphism.** -/
lemma mono_of_forall_injective_stalk {A B : SheafOfModules.{u} Y.ringSheaf} (φ : A ⟶ B)
    (h : ∀ y : Y, Function.Injective ((Y.stalkFunctor y).map φ)) : Mono φ :=
  SheafOfModules.mono_of_forall_mono_stalkFunctor_map (hR := Y.isSheaf_ringSheaf) φ
    fun y ↦ (ModuleCat.mono_iff_injective _).2 (h y)

/-- **Pushforward along an inducing map preserves bijectivity on stalks** at points of the
image. -/
lemma Hom.bijective_stalkFunctor_map_pushforward_of_isInducing {X : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (hf : IsInducing f.base) {H H' : SheafOfModules.{u} X.ringSheaf} (φ : H ⟶ H')
    (x : X) (h : Function.Bijective ((X.stalkFunctor x).map φ)) :
    Function.Bijective ((Y.stalkFunctor (f.base x)).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ)) := by
  have key : f.stalkPushforwardModules H' x ∘ (Y.stalkFunctor (f.base x)).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ) =
      (X.stalkFunctor x).map φ ∘ f.stalkPushforwardModules H x :=
    funext fun m ↦ f.stalkPushforwardModules_naturality φ x m
  have h2 := h.comp (f.bijective_stalkPushforwardModules hf H x)
  rw [← key] at h2
  exact (Function.Bijective.of_comp_iff' (f.bijective_stalkPushforwardModules hf H' x) _).1 h2

/-- `(f, g) : A ⟶ B ⊞ C` is surjective on the stalk at `y` if `f` is and `C_y = 0`. -/
lemma surjective_stalkFunctor_map_biprod_lift {A B C : SheafOfModules.{u} Y.ringSheaf}
    (f : A ⟶ B) (g : A ⟶ C) (y : Y) (hf : Function.Surjective ((Y.stalkFunctor y).map f))
    [Subsingleton ((Y.stalkFunctor y).obj C)] :
    Function.Surjective ((Y.stalkFunctor y).map (biprod.lift f g)) := by
  haveI : PreservesBinaryBiproducts (Y.stalkFunctor y) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  haveI : (Y.stalkFunctor y).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have htot : ∀ t : (Y.stalkFunctor y).obj (B ⊞ C),
      t = (Y.stalkFunctor y).map biprod.inl ((Y.stalkFunctor y).map biprod.fst t) +
        (Y.stalkFunctor y).map biprod.inr ((Y.stalkFunctor y).map biprod.snd t) := by
    intro t
    have e1 : (Y.stalkFunctor y).map
        ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : B ⊞ C ⟶ _)) =
        (Y.stalkFunctor y).map biprod.fst ≫ (Y.stalkFunctor y).map biprod.inl +
          (Y.stalkFunctor y).map biprod.snd ≫ (Y.stalkFunctor y).map biprod.inr := by
      rw [Functor.map_add, Functor.map_comp, Functor.map_comp]
    calc t = (Y.stalkFunctor y).map (𝟙 (B ⊞ C)) t := by rw [CategoryTheory.Functor.map_id]; rfl
      _ = (Y.stalkFunctor y).map
          ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : B ⊞ C ⟶ _)) t := by
        rw [biprod.total]
      _ = _ := by rw [e1]; rfl
  intro t
  obtain ⟨a, ha⟩ := hf ((Y.stalkFunctor y).map biprod.fst t)
  refine ⟨a, ?_⟩
  have h1 : (Y.stalkFunctor y).map biprod.fst ((Y.stalkFunctor y).map (biprod.lift f g) a) =
      (Y.stalkFunctor y).map biprod.fst t := by
    rw [← ha, ← ConcreteCategory.comp_apply, ← Functor.map_comp, biprod.lift_fst]
  rw [htot ((Y.stalkFunctor y).map (biprod.lift f g) a), htot t, h1,
    Subsingleton.elim ((Y.stalkFunctor y).map biprod.snd ((Y.stalkFunctor y).map
      (biprod.lift f g) a)) ((Y.stalkFunctor y).map biprod.snd t)]

end AlgebraicGeometry.LocallyRingedSpace

end
