/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.HolomorphicFrechet

/-!
# Continuous operations on the Fréchet space of holomorphic functions

For the topology of compact convergence on `OkaRing U`
(`Oka.Analytification.GAGA.HolomorphicFrechet`), the basic holomorphic operations are
continuous linear maps:

- `OkaRing.mulCLM g : OkaRing U →L[ℂ] OkaRing U`, multiplication by a fixed function;
- `OkaRing.compCLM φ hφ hmaps : OkaRing U →L[ℂ] OkaRing V`, composition `f ↦ f ∘ φ` with a
  holomorphic map `φ` sending the open `V ⊆ ℂ^κ` into the open `U ⊆ ℂ^ι` (a compact subset of
  `V` is mapped onto a compact subset of `U`);
- `Matrix.toOkaCLM A : (n → OkaRing U) →L[ℂ] (m → OkaRing U)`, the map `f ↦ A *ᵥ f` given by a
  matrix of holomorphic functions, i.e. a morphism of free `𝒪`-modules on sections over `U`.
-/

@[expose] public section

open Set Topology TopologicalSpace

universe u v

namespace OkaRing

variable {ι : Type u} [Fintype ι] {U : Opens (ι → ℂ)}

/-- Multiplication by a fixed holomorphic function, as a continuous `ℂ`-linear map. -/
noncomputable def mulCLM (g : OkaRing U) : OkaRing U →L[ℂ] OkaRing U where
  toLinearMap := LinearMap.mulLeft ℂ g
  cont := continuous_const.mul continuous_id

@[simp]
lemma mulCLM_apply (g f : OkaRing U) : mulCLM g f = g * f :=
  rfl

variable {κ : Type v} [Fintype κ] {V : Opens (κ → ℂ)}

/-- The composition `f ∘ φ` of `f : OkaRing U` with a holomorphic map `φ : V → U`. -/
noncomputable def comp (φ : (κ → ℂ) → ι → ℂ) (hφ : DifferentiableOn ℂ φ V)
    (hmaps : MapsTo φ V U) (f : OkaRing U) : OkaRing V :=
  ofDifferentiableOn (f.toGlobalFun U ∘ φ) (f.differentiableOn_toGlobalFun.comp hφ hmaps)

lemma comp_toFun (φ : (κ → ℂ) → ι → ℂ) (hφ : DifferentiableOn ℂ φ V)
    (hmaps : MapsTo φ V U) (f : OkaRing U) (y : V) :
    (comp φ hφ hmaps f).toFun V y = f.toFun U ⟨φ y, hmaps y.2⟩ := by
  rw [comp, ofDifferentiableOn_toFun, Function.comp_apply, toGlobalFun_apply]

/-- Composition with a holomorphic map `φ` sending `V` into `U`, as a continuous `ℂ`-linear map
`OkaRing U →L[ℂ] OkaRing V`. -/
noncomputable def compCLM (φ : (κ → ℂ) → ι → ℂ) (hφ : DifferentiableOn ℂ φ V)
    (hmaps : MapsTo φ V U) : OkaRing U →L[ℂ] OkaRing V where
  toFun := comp φ hφ hmaps
  map_add' f g := OkaRing.ext <| funext fun y ↦ by
    change _ = (comp φ hφ hmaps f).toFun V y + (comp φ hφ hmaps g).toFun V y
    simp only [comp_toFun]
    rfl
  map_smul' c f := OkaRing.ext <| funext fun y ↦ by
    change _ = c • (comp φ hφ hmaps f).toFun V y
    simp only [comp_toFun]
    rfl
  cont := by
    refine isEmbedding_toContinuousMap.continuous_iff.2 ?_
    let ψ : C(V, U) := ⟨fun y ↦ ⟨φ y, hmaps y.2⟩,
      hφ.continuousOn.mapsToRestrict hmaps⟩
    have h : (toContinuousMap V ∘ comp φ hφ hmaps) =
        (fun g : C(U, ℂ) ↦ g.comp ψ) ∘ toContinuousMap U := by
      funext f
      exact ContinuousMap.ext fun y ↦ comp_toFun φ hφ hmaps f y
    rw [h]
    exact (ContinuousMap.continuous_precomp ψ).comp continuous_toContinuousMap

@[simp]
lemma compCLM_apply (φ : (κ → ℂ) → ι → ℂ) (hφ : DifferentiableOn ℂ φ V)
    (hmaps : MapsTo φ V U) (f : OkaRing U) : compCLM φ hφ hmaps f = comp φ hφ hmaps f :=
  rfl

/-- The composition `f ∘ φ` is given pointwise by composing the functions. -/
lemma compCLM_toGlobalFun (φ : (κ → ℂ) → ι → ℂ) (hφ : DifferentiableOn ℂ φ V)
    (hmaps : MapsTo φ V U) (f : OkaRing U) {y : κ → ℂ} (hy : y ∈ V) :
    (compCLM φ hφ hmaps f).toGlobalFun V y = f.toGlobalFun U (φ y) := by
  rw [toGlobalFun_apply _ hy, compCLM_apply, comp_toFun, toGlobalFun_apply]

end OkaRing

namespace Matrix

variable {ι : Type u} [Fintype ι] {U : Opens (ι → ℂ)} {m n : Type*} [Fintype n]

/-- The continuous `ℂ`-linear map `f ↦ A *ᵥ f` on tuples of holomorphic functions given by a
matrix `A` of holomorphic functions on `U`. -/
noncomputable def toOkaCLM (A : Matrix m n (OkaRing U)) :
    (n → OkaRing U) →L[ℂ] (m → OkaRing U) where
  toLinearMap := (Matrix.mulVecLin A).restrictScalars ℂ
  cont := continuous_pi fun _ ↦ continuous_finsetSum _ fun j _ ↦
    continuous_const.mul (continuous_apply j)

@[simp]
lemma toOkaCLM_apply (A : Matrix m n (OkaRing U)) (f : n → OkaRing U) :
    toOkaCLM A f = A *ᵥ f :=
  rfl

end Matrix

end
