/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.LocallyFree

/-!
# Surjectivity of morphisms of sheaves of modules on stalks

For a morphism `f : A ⟶ M` of sheaves of modules on a locally ringed space `Y`:

- `AlgebraicGeometry.LocallyRingedSpace.subsingleton_stalk_cokernel_iff`: `f` is surjective on
  the stalk at `y` if and only if the stalk of `coker f` at `y` vanishes;
- `AlgebraicGeometry.LocallyRingedSpace.epi_of_forall_surjective_stalk`: `f` is an epimorphism if
  it is surjective on all stalks;
- `AlgebraicGeometry.LocallyRingedSpace.exists_nhds_surjective_stalk`: if `M` is of finite type
  and `f` is surjective on the stalk at `y`, then `f` is surjective on the stalks at all points
  of a neighbourhood of `y`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite Limits

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}} {A M : SheafOfModules.{u} Y.ringSheaf}

/-- **Surjectivity on a stalk is vanishing of the stalk of the cokernel.** -/
lemma subsingleton_stalk_cokernel_iff (f : A ⟶ M) (y : Y) :
    Subsingleton ((Y.stalkFunctor y).obj (cokernel f)) ↔
      Function.Surjective ((Y.stalkFunctor y).map f) := by
  have hex := exact_stalk (ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) y
  constructor
  · intro h m
    exact (hex m).1 (Subsingleton.elim _ _)
  · intro h
    refine ⟨fun q₁ q₂ ↦ ?_⟩
    have hzero : ∀ q : (Y.stalkFunctor y).obj (cokernel f), q = 0 := fun q ↦ by
      obtain ⟨m, rfl⟩ := surjective_stalk_of_epi (cokernel.π f) y q
      obtain ⟨a, rfl⟩ := h m
      exact stalkFunctor_map_map_eq_zero _ _ (cokernel.condition f) y a
    rw [hzero q₁, hzero q₂]

/-- **A morphism which is surjective on all stalks is an epimorphism.** -/
lemma epi_of_forall_surjective_stalk (f : A ⟶ M)
    (h : ∀ y : Y, Function.Surjective ((Y.stalkFunctor y).map f)) : Epi f :=
  Preadditive.epi_of_isZero_cokernel _ (isZero_of_forall_subsingleton_stalk _ fun y ↦
    (subsingleton_stalk_cokernel_iff f y).2 (h y))

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- **Surjectivity on stalks spreads to a neighbourhood** for a morphism into a sheaf of finite
type. -/
lemma exists_nhds_surjective_stalk [M.IsFiniteType] (f : A ⟶ M) (y : Y)
    (hf : Function.Surjective ((Y.stalkFunctor y).map f)) :
    ∃ U : Opens Y, y ∈ U ∧ ∀ w ∈ U, Function.Surjective ((Y.stalkFunctor w).map f) := by
  haveI : (cokernel f).IsFiniteType := SheafOfModules.isFiniteType_cokernel f
  obtain ⟨U, hyU, hZ⟩ := exists_isZero_restrictModules (cokernel f) y
    ((subsingleton_stalk_cokernel_iff f y).2 hf)
  refine ⟨U, hyU, fun w hw ↦ (subsingleton_stalk_cokernel_iff f w).1 ?_⟩
  let w' : Y.restrict U.isOpenEmbedding := ⟨w, hw⟩
  haveI : Subsingleton (((Y.restrict U.isOpenEmbedding).stalkFunctor w').obj
      ((Y.restrictModules U).obj (cokernel f))) :=
    ModuleCat.subsingleton_of_isZero (Functor.map_isZero _ hZ)
  exact ((Y.ofRestrict U.isOpenEmbedding).stalkPullbackModulesSemilinearEquiv w'
    (cokernel f)).toEquiv.subsingleton

end AlgebraicGeometry.LocallyRingedSpace

end
