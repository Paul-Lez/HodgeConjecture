/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwist
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Exactness of sequences of `𝒪_X`-modules from sections over small opens

A short complex `S : M₁ ⟶ M₂ ⟶ M₃` of `𝒪_X`-modules is exact as soon as every point has
arbitrarily small open neighbourhoods `W` on which `Γ(M₁, W) → Γ(M₂, W) → Γ(M₃, W)` is exact in
the middle; `M₂ ⟶ M₃` is an epimorphism as soon as it is surjective on sections over arbitrarily
small neighbourhoods of every point. Both follow from the stalk criterion
`SheafOfModules.exact_of_stalk_exact`, since stalks are colimits over neighbourhoods.

## Main results

- `Scheme.Modules.exact_of_locally_exact`
- `Scheme.Modules.epi_of_locally_surjective`
- `Scheme.Modules.shortExact_of_locally_exact`
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The stalk map of a morphism of `𝒪_X`-modules on germs. -/
lemma stalk_map_germ {M N : X.Modules} (φ : M ⟶ N) (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(M, U)) :
    (SheafOfModules.stalkFunctorAddCommGrp (X := X.toPresheafedSpace.carrier)
      (R := X.ringCatSheaf) x).map φ (M.presheaf.germ U x hx s) =
      N.presheaf.germ U x hx (φ.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf s

/-- A short complex of `𝒪_X`-modules which is exact in the middle on sections over arbitrarily
small neighbourhoods of every point is exact. -/
theorem exact_of_locally_exact (S : ShortComplex X.Modules)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W ≤ V, x ∈ W ∧
      ∀ b : Γ(S.X₂, W), S.g.app W b = 0 → ∃ a, S.f.app W a = b) : S.Exact := by
  refine SheafOfModules.exact_of_stalk_exact (X := X.toPresheafedSpace.carrier) S fun x ↦ ?_
  rw [ShortComplex.ab_exact_iff]
  intro b hb
  obtain ⟨U, hxU, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.presheaf b
  change (SheafOfModules.stalkFunctorAddCommGrp (X := X.toPresheafedSpace.carrier)
      (R := X.ringCatSheaf) x).map S.g _ = 0 at hb
  rw [stalk_map_germ] at hb
  obtain ⟨W, hxW, iU, _iV, e⟩ := TopCat.Presheaf.germ_eq S.X₃.presheaf x hxU hxU (S.g.app U b) 0
    (by rw [hb]; exact (map_zero _).symm)
  obtain ⟨W', hW', hxW', hex⟩ := h x W hxW
  obtain ⟨a, ha⟩ := hex (TopCat.Presheaf.restrictOpen b W' (hW'.trans iU.le)) (by
    rw [Hom.app_mres, ← mres_res _ iU.le hW']
    change TopCat.Presheaf.restrictOpen (S.X₃.presheaf.map iU.op _) W' hW' = 0
    rw [e]
    rw [map_zero]
    exact mres_zero _ _)
  refine ⟨S.X₁.presheaf.germ W' x hxW' a, ?_⟩
  change (SheafOfModules.stalkFunctorAddCommGrp (X := X.toPresheafedSpace.carrier)
      (R := X.ringCatSheaf) x).map S.f _ = _
  rw [stalk_map_germ, ha]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- A morphism of `𝒪_X`-modules which is surjective on sections over arbitrarily small
neighbourhoods of every point is an epimorphism. -/
theorem epi_of_locally_surjective {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W ≤ V, x ∈ W ∧ Function.Surjective (φ.app W)) :
    Epi φ := by
  have hS : (ShortComplex.mk φ (0 : N ⟶ 0) (by simp)).Exact := by
    refine exact_of_locally_exact _ fun x V hx ↦ ?_
    obtain ⟨W, hWV, hxW, hs⟩ := h x V hx
    exact ⟨W, hWV, hxW, fun b _ ↦ hs b⟩
  exact (ShortComplex.exact_iff_epi _ rfl).1 hS

/-- A short complex of `𝒪_X`-modules with `S.f` mono, which is exact in the middle and has `S.g`
surjective on sections over arbitrarily small neighbourhoods of every point, is short exact. -/
theorem shortExact_of_locally_exact (S : ShortComplex X.Modules) [Mono S.f]
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W ≤ V, x ∈ W ∧
      (∀ b : Γ(S.X₂, W), S.g.app W b = 0 → ∃ a, S.f.app W a = b) ∧
        Function.Surjective (S.g.app W)) : S.ShortExact := by
  have := epi_of_locally_surjective S.g fun x V hx ↦ by
    obtain ⟨W, hWV, hxW, -, hs⟩ := h x V hx
    exact ⟨W, hWV, hxW, hs⟩
  refine ⟨exact_of_locally_exact S fun x V hx ↦ ?_⟩
  obtain ⟨W, hWV, hxW, he, -⟩ := h x V hx
  exact ⟨W, hWV, hxW, he⟩

end AlgebraicGeometry.Scheme.Modules

end
