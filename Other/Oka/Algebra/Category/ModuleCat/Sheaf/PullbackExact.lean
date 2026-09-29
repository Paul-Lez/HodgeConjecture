/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.PullbackStalk
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Exactness of pullback for sheaves of modules

Pullback along a morphism whose maps on ring stalks are flat preserves finite limits.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite ZeroObject

universe u

namespace SheafOfModules

section


variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  {hR : TopCat.Presheaf.IsSheaf (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}

/-- The module-valued stalk functor preserves monomorphisms. -/
instance preservesMonomorphisms_stalkFunctor (x : X) :
    (stalkFunctor (hR := hR) x).PreservesMonomorphisms where
  preserves {M N} g hg := by
    have h1 : Mono ((stalkFunctorAddCommGrp (R := ofCommRingCat R hR) x).map g) :=
      inferInstance
    exact (forget₂ (ModuleCat.{u} (R.stalk x)) AddCommGrpCat.{u}).mono_of_mono_map h1

/-- A morphism which is a monomorphism on every stalk is a monomorphism. -/
theorem mono_of_forall_mono_stalkFunctor_map {M N : SheafOfModules.{u} (ofCommRingCat R hR)}
    (g : M ⟶ N) (hm : ∀ x : X, Mono ((stalkFunctor (hR := hR) x).map g)) : Mono g := by
  have hS : (ShortComplex.mk (0 : (0 : SheafOfModules.{u} (ofCommRingCat R hR)) ⟶ M) g
      (by simp)).Exact := by
    refine exact_of_stalk_exact _ fun x ↦ ?_
    refine (ShortComplex.exact_iff_mono _ ?_).2 ?_
    · exact Functor.map_zero (stalkFunctorAddCommGrp (R := ofCommRingCat R hR) x) _ _
    · have := hm x
      exact inferInstanceAs (Mono ((forget₂ (ModuleCat.{u} (R.stalk x)) AddCommGrpCat.{u}).map
        ((stalkFunctor (hR := hR) x).map g)))
  exact (ShortComplex.exact_iff_mono _ (by simp)).1 hS

end

section

variable {X Y : TopCat.{u}} {f : X ⟶ Y} {S : Y.Presheaf CommRingCat.{u}}
  {R : X.Presheaf CommRingCat.{u}}
  {hS : TopCat.Presheaf.IsSheaf (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  {hR : TopCat.Presheaf.IsSheaf (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  (φ : S ⟶ (Opens.map f).op ⋙ R)

local instance :
    (PresheafOfModules.pushforward.{u}
      (sheafRingHom (hS := hS) (hR := hR) φ).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top
      (sheafRingHom (hS := hS) (hR := hR) φ).hom)

local instance :
    (pushforward.{u} (sheafRingHom (hS := hS) (hR := hR) φ)).IsRightAdjoint :=
  (PullbackConstruction.adjunction
    (sheafRingHom (hS := hS) (hR := hR) φ)).isRightAdjoint

/-- Flatness on ring stalks makes pullback preserve monomorphisms. -/
theorem preservesMonomorphisms_pullback
    (hflat : ∀ x : X, ((PresheafOfModules.ringStalkMap f φ x).hom).Flat) :
    (pullback.{u} (sheafRingHom (hS := hS) (hR := hR) φ)).PreservesMonomorphisms where
  preserves {M N} g hg := by
    refine mono_of_forall_mono_stalkFunctor_map _ fun x ↦ ?_
    have hfl := ModuleCat.preservesFiniteLimits_extendScalars_of_flat.{u} (hflat x)
    have h1 : (stalkFunctor (hR := hS) (f x) ⋙
        ModuleCat.extendScalars (PresheafOfModules.ringStalkMap f φ x).hom
          ).PreservesMonomorphisms := by
      have : (ModuleCat.extendScalars.{u, u, u}
          (PresheafOfModules.ringStalkMap f φ x).hom).PreservesMonomorphisms :=
        inferInstance
      infer_instance
    have h2 := Functor.PreservesMonomorphisms.of_iso
      (pullbackStalkIso (hS := hS) (hR := hR) φ x).symm
    exact h2.preserves g

/-- Flatness on ring stalks makes pullback preserve finite limits. -/
theorem preservesFiniteLimits_pullback
    (hflat : ∀ x : X, ((PresheafOfModules.ringStalkMap f φ x).hom).Flat) :
    PreservesFiniteLimits (pullback.{u} (sheafRingHom (hS := hS) (hR := hR) φ)) := by
  have h0 : (pullback.{u}
      (sheafRingHom (hS := hS) (hR := hR) φ)).PreservesMonomorphisms :=
    preservesMonomorphisms_pullback φ hflat
  have hp : (pushforward.{u}
      (sheafRingHom (hS := hS) (hR := hR) φ)).Additive := ⟨rfl⟩
  have h1 : (pullback.{u} (sheafRingHom (hS := hS) (hR := hR) φ)).Additive :=
    (pullbackPushforwardAdjunction.{u}
      (sheafRingHom (hS := hS) (hR := hR) φ)).left_adjoint_additive
  have h2 : (pullback.{u}
      (sheafRingHom (hS := hS) (hR := hR) φ)).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end


end SheafOfModules
