/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Finite free resolutions of sheaves of modules

`SheafOfModules.HasFreeResolutionLE M n` says that the sheaf of modules `M` has a resolution
`0 → Fₙ → ⋯ → F₀ → M → 0` of length `≤ n` by finite free sheaves of modules. It is defined
inductively: either `M` is isomorphic to a finite free sheaf, or there is a short exact sequence
`0 → K → 𝒪^I → M → 0` with `I` finite and `K` having such a resolution of length `≤ n - 1`.

## Main results

- `SheafOfModules.HasFreeResolutionLE.of_iso`: invariance under isomorphisms.
- `SheafOfModules.HasFreeResolutionLE.mono`: monotonicity in the length.
- `SheafOfModules.HasFreeResolutionLE.map`: an exact functor which sends finite free sheaves to
  finite free sheaves preserves finite free resolutions of length `≤ n`;
  `SheafOfModules.HasFreeResolutionLE.of_shortExact_map` is its inductive step.
-/

@[expose] public noncomputable section

universe u v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace SheafOfModules

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `HasFreeResolutionLE M n`: the sheaf of modules `M` has a resolution of length `≤ n` by
finite free sheaves of modules. -/
inductive HasFreeResolutionLE : SheafOfModules.{u} R → ℕ → Prop
  /-- A sheaf isomorphic to a finite free sheaf has a free resolution of any length. -/
  | free {M : SheafOfModules.{u} R} (n : ℕ) (I : Type u) [Finite I] (e : M ≅ free I) :
      HasFreeResolutionLE M n
  /-- If `0 → K → 𝒪^I → M → 0` is exact and `K` has a free resolution of length `≤ n`, then
  `M` has one of length `≤ n + 1`. -/
  | ext {M K : SheafOfModules.{u} R} {n : ℕ} (I : Type u) [Finite I] (i : K ⟶ free I)
      (p : free I ⟶ M) (w : i ≫ p = 0) (hS : (ShortComplex.mk i p w).ShortExact)
      (hK : HasFreeResolutionLE K n) : HasFreeResolutionLE M (n + 1)

namespace HasFreeResolutionLE

/-- Finite free resolutions are invariant under isomorphisms. -/
lemma of_iso {M N : SheafOfModules.{u} R} {n : ℕ} (e : M ≅ N) (h : HasFreeResolutionLE M n) :
    HasFreeResolutionLE N n := by
  cases h with
  | free n I f => exact .free n I (e.symm ≪≫ f)
  | ext I i p w hS hK =>
    refine .ext I i (p ≫ e.hom) (by rw [reassoc_of% w, zero_comp]) ?_ hK
    refine ShortComplex.shortExact_of_iso ?_ hS
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simp)

/-- A free resolution of length `≤ n` is one of length `≤ m` for `n ≤ m`. -/
lemma mono {M : SheafOfModules.{u} R} {n m : ℕ} (h : HasFreeResolutionLE M n) (hnm : n ≤ m) :
    HasFreeResolutionLE M m := by
  induction h generalizing m with
  | free n I e => exact .free m I e
  | ext I i p w hS hK ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .ext I i p w hS (ih (by omega))

end HasFreeResolutionLE

end

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The image of a short exact sequence `0 → K → 𝒪^I → M → 0` under an exact functor preserving
finite free sheaves: if the image of `K` has a free resolution of length `≤ n`, the image of `M`
has one of length `≤ n + 1`. -/
lemma HasFreeResolutionLE.of_shortExact_map (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : ∀ (I : Type u) [Finite I], F.obj (SheafOfModules.free I) ≅ SheafOfModules.free I)
    {K M : SheafOfModules.{u} R} {I : Type u} [Finite I] (i : K ⟶ SheafOfModules.free I)
    (p : SheafOfModules.free I ⟶ M) (w : i ≫ p = 0) (hS : (ShortComplex.mk i p w).ShortExact)
    {n : ℕ} (hK : HasFreeResolutionLE (F.obj K) n) : HasFreeResolutionLE (F.obj M) (n + 1) := by
  refine .ext I (F.map i ≫ (η I).hom) ((η I).inv ≫ F.map p)
    (by simp [← F.map_comp, w]) ?_ hK
  refine ShortComplex.shortExact_of_iso ?_ (hS.map_of_exact F)
  exact ShortComplex.isoMk (Iso.refl _) (η I) (Iso.refl _) (Category.id_comp _)
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)

/-- **Exact functors preserving finite free sheaves preserve finite free resolutions.** -/
lemma HasFreeResolutionLE.map (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : ∀ (I : Type u) [Finite I], F.obj (SheafOfModules.free I) ≅ SheafOfModules.free I)
    {M : SheafOfModules.{u} R}
    {n : ℕ} (h : HasFreeResolutionLE M n) : HasFreeResolutionLE (F.obj M) n := by
  induction h with
  | free n I e => exact .free n I (F.mapIso e ≪≫ η I)
  | ext I i p w hS hK ih => exact .of_shortExact_map F η i p w hS ih

end SheafOfModules
