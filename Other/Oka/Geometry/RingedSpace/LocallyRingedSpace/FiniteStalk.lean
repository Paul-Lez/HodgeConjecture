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
# Finite stalks of finite-type sheaves

This is the finite-stalk part of Oka's `ModulesStalkNakayama` file. It is kept separate because
the line-bundle descent argument does not need the later Nakayama machinery.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}

/-- A semilinear surjection from a finite module has finite target. -/
private lemma finite_of_surjective_semilinear {R S M P : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [AddCommMonoid P] [Module R M] [Module S P] {σ : R →+* S}
    [Module.Finite R M] (f : M →ₛₗ[σ] P) (hf : Function.Surjective f) :
    Module.Finite S P := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  classical
  refine ⟨⟨s.image f, eq_top_iff.2 fun p _ ↦ ?_⟩⟩
  obtain ⟨m, rfl⟩ := hf p
  suffices ∀ m ∈ Submodule.span R (s : Set M), f m ∈ Submodule.span S (s.image f : Set P) from
    this m (hs ▸ Submodule.mem_top)
  intro m hm
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ha

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- The stalks of a sheaf of finite type are finitely generated. -/
theorem finite_stalk_of_isFiniteType (M : SheafOfModules.{u} Y.ringSheaf) [M.IsFiniteType]
    (y : Y) : Module.Finite (Y.presheaf.stalk y) ((Y.stalkFunctor y).obj M) := by
  classical
  obtain ⟨U, hyU, I, _, π, _⟩ := exists_epi_free_restrictModules M y
  let _ := Fintype.ofFinite I
  let y' : Y.restrict U.isOpenEmbedding := ⟨y, hyU⟩
  let : Module.Finite ((Y.restrict U.isOpenEmbedding).presheaf.stalk y')
      (((Y.restrict U.isOpenEmbedding).stalkFunctor y').obj ((Y.restrictModules U).obj M)) := by
    refine
      ⟨⟨(Set.finite_range fun i ↦ germTop _ y' (generatorSection π i)).toFinset, ?_⟩⟩
    rw [Set.Finite.coe_toFinset]
    exact span_germ_eq_top π y'
  exact finite_of_surjective_semilinear
    ((Y.ofRestrict U.isOpenEmbedding).stalkPullbackModulesSemilinearEquiv y' M).symm.toLinearMap
    ((Y.ofRestrict U.isOpenEmbedding).stalkPullbackModulesSemilinearEquiv y' M).symm.surjective

end AlgebraicGeometry.LocallyRingedSpace
