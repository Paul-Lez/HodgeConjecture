/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Rank-one descent along faithfully flat local ring maps
-/

public section

universe u

open TensorProduct

namespace Module

/-- A linear trivialization of a module gives it a basis indexed by `PUnit`. -/
noncomputable def basisPUnitOfLinearEquivSelf
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] R) : Basis PUnit R M :=
  (Basis.singleton PUnit R).map e.symm

/-- A finite module is free of rank one when a faithfully flat base change is free of
rank one. -/
theorem exists_linearEquiv_self_of_faithfullyFlat_baseChange
    (R S M : Type u) [CommRing R] [IsLocalRing R] [CommRing S]
    [Nontrivial S] [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.FaithfullyFlat R S]
    (e : (S ⊗[R] M) ≃ₗ[S] S) : Nonempty (M ≃ₗ[R] R) := by
  have : Module.Flat S (S ⊗[R] M) := Module.Flat.of_linearEquiv e
  have : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
  have : Module.Free R M := Module.free_of_flat_of_isLocalRing
  have h : Module.finrank S (S ⊗[R] M) = 1 := by
    rw [e.finrank_eq, Module.finrank_self]
  have hR : Module.finrank R M = 1 := by
    simpa only [Module.finrank_baseChange] using h
  exact ⟨(Module.nonempty_linearEquiv_of_finrank_eq_one hR).some.symm⟩

/-- The categorical extension-of-scalars form of rank-one faithfully flat descent. -/
theorem exists_linearEquiv_self_of_faithfullyFlat_extendScalars
    (R S : Type u) [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hf : f.FaithfullyFlat)
    (e : (ModuleCat.extendScalars f).obj M ≃ₗ[S] S) : Nonempty (M ≃ₗ[R] R) := by
  algebraize [f]
  let : Module.FaithfullyFlat R S := hf
  exact exists_linearEquiv_self_of_faithfullyFlat_baseChange R S M e

end Module
