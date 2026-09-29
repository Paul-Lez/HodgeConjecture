/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.RelativeBaseChangeTwist

/-!
# Germs of sections of `G(n)^an` along the fibres of `P^an ⟶ ℂᵐ`

Let `P = ℙₒ(N; A)`, `A = ℂ[y₀, …, y_{m-1}]`, `N ≥ 1`, and `G` coherent on `P`. The canonical maps
`𝒪(D) ⊗_A Γ(P, G) → Γ(D × ℙᴺ, G^an)` (`ComplexAnalytic.relProjectiveSpaceAn.canMap`) are
compatible with restriction along `D' ⊆ D` (`canMap_restrict`). For `n ≥ n₀`, with `n₀` from
`ComplexAnalytic.relProjectiveSpaceAn.exists_bijective_canMap`, they are bijective on boxes, and
boxes form a neighbourhood basis of `ℂᵐ`; hence on germs at `y ∈ ℂᵐ`, i.e. in the colimits over
the opens `V ∋ y`,

  `colim_V Γ(V × ℙᴺ, G(n)^an) ≅ colim_V (𝒪(V) ⊗_A Γ(P, G(n))) = 𝒪_{ℂᵐ, y} ⊗_A Γ(P, G(n))`.

This is stated elementwise: every section of `G(n)^an` over `V × ℙᴺ` is, near the fibre over
`y`, in the image of the canonical map (`exists_canMap_eq_restrict`), and an element of
`𝒪(D) ⊗_A Γ(P, G(n))` whose image vanishes near the fibre over `y` vanishes on a box around `y`
(`exists_rTensor_restrict_eq_zero`).
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.LocallyRingedSpace
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic.relProjectiveSpaceAn

open ProjectiveSpace

variable {m N : ℕ}

lemma tube_mono {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) :
    tube.{u} (N := N) D' ≤ tube D :=
  fun _ hx ↦ h hx

/-- Restriction of holomorphic functions along `D' ⊆ D`, as a map of `A`-algebras. -/
noncomputable def restrictOka {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) :
    OkaRing D →ₐ[RelBase.{u} m] OkaRing D' :=
  { (OkaRing.restrict h).toRingHom with
    commutes' := fun a ↦ OkaRing.ext (funext fun y ↦ by
      change (polyToOka.{u} D a).toFun _ ⟨y.1, h y.2⟩ = (polyToOka.{u} D' a).toFun _ y
      rw [← OkaRing.toGlobalFun_apply _ (h y.2), ← OkaRing.toGlobalFun_apply _ y.2,
        toGlobalFun_polyToOka _ _ (h y.2), toGlobalFun_polyToOka _ _ y.2]) }

lemma toGlobalFun_restrictOka {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) (f : OkaRing D)
    {y : Fin m → ℂ} (hy : y ∈ D') :
    (restrictOka.{u} h f).toGlobalFun _ y = f.toGlobalFun _ y := by
  rw [OkaRing.toGlobalFun_apply _ hy, OkaRing.toGlobalFun_apply _ (h hy)]
  rfl

/-- The pullbacks of holomorphic functions on the base are compatible with restriction. -/
lemma restrict_baseRingHom {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) (f : OkaRing D) :
    TopCat.Presheaf.restrictOpen (F := (relProjectiveSpaceAn.{u} m N).presheaf)
      (baseRingHom.{u} N D f) (tube D') (tube_mono h) =
      baseRingHom.{u} N D' (restrictOka.{u} h f) := by
  refine eq_of_secFun fun p hp ↦ ?_
  rw [secFun_restrictOpen, Set.indicator_of_mem hp,
    secFun_baseRingHom D f (vecCone_mono (tube_mono h) hp), secFun_baseRingHom D' _ hp,
    toGlobalFun_restrictOka h f (baseY_mem_of_mem_vecCone hp)]

variable {G : ℙₒ(N; RelBase.{u} m).Modules}

/-- Restriction of sections of `G^an` along `D' × ℙᴺ ⊆ D × ℙᴺ`. -/
noncomputable def anSecRestrict {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) (x : AnSec D G) :
    AnSec D' G :=
  modRes (N := (analytificationModules (relProjectiveSpace.{u} m N)).obj G) x (tube D')
    (tube_mono h)

lemma anSecRestrict_smul {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) (f : OkaRing D)
    (x : AnSec D G) : anSecRestrict h (f • x) = restrictOka.{u} h f • anSecRestrict h x := by
  change modRes (baseRingHom.{u} N D f • x) _ _ = baseRingHom.{u} N D' (restrictOka.{u} h f) • _
  rw [← restrict_baseRingHom h f]
  exact modRes_smul _ _ _

lemma anSecRestrict_algSec {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) (s : AlgSec G) :
    anSecRestrict h (algSec D G s) = algSec D' G s :=
  modRes_res _ _ _

/-- **The canonical maps are compatible with restriction along `D' ⊆ D`.** -/
lemma canMap_restrict {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D)
    (x : OkaRing D ⊗[RelBase.{u} m] AlgSec G) :
    anSecRestrict h (canMap D G x) =
      canMap D' G ((restrictOka.{u} h).toLinearMap.rTensor (AlgSec G) x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact modRes_zero _
  | tmul f s =>
    rw [LinearMap.rTensor_tmul, canMap_tmul, canMap_tmul, anSecRestrict_smul,
      anSecRestrict_algSec]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, ← hx, ← hy]
    exact modRes_add _ _ _

variable (hN : 1 ≤ N)
include hN

/-- **Every section of `G(n)^an` is, near the fibre over `y`, in the image of the canonical
map**, for `n ≥ n₀` (uniformly in `y` and in the open): for `s ∈ Γ(V × ℙᴺ, G(n)^an)` and `y ∈ V`
there is an open box `B ∋ y`, `B ⊆ V`, with `s|_{B × ℙᴺ}` in the image of
`𝒪(B) ⊗_A Γ(P, G(n))`. -/
theorem exists_canMap_eq_restrict (G : ℙₒ(N; RelBase.{u} m).Modules) [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ (V : Opens (Fin m → ℂ)) (y : Fin m → ℂ), y ∈ V →
      ∀ s : AnSec V (twist G n), ∃ (a b : Fin m → ℂ) (B : Opens (Fin m → ℂ)) (hBV : B ≤ V),
        (B : Set (Fin m → ℂ)) = Complex.openBox a b ∧ y ∈ B ∧
          ∃ x : OkaRing B ⊗[RelBase.{u} m] AlgSec (twist G n),
            canMap B (twist G n) x = anSecRestrict hBV s := by
  obtain ⟨n₀, h⟩ := exists_bijective_canMap hN G
  refine ⟨n₀, fun n hn V y hy s ↦ ?_⟩
  obtain ⟨a, b, hyB, hBV⟩ := exists_openBox_subset V.isOpen hy
  let B : Opens (Fin m → ℂ) := boxOpens a b
  obtain ⟨x, hx⟩ := (h n hn a b B rfl).2 (anSecRestrict (G := twist G n) (D' := B) hBV s)
  exact ⟨a, b, B, hBV, rfl, hyB, x, hx⟩

/-- **The canonical map is injective on germs along the fibre over `y`**, for `n ≥ n₀`: if the
image of `x ∈ 𝒪(D) ⊗_A Γ(P, G(n))` vanishes on `V × ℙᴺ` for an open `V ∋ y`, `V ⊆ D`, then `x`
vanishes in `𝒪(B) ⊗_A Γ(P, G(n))` for an open box `B ∋ y`, `B ⊆ V`. -/
theorem exists_rTensor_restrict_eq_zero (G : ℙₒ(N; RelBase.{u} m).Modules) [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ (D V : Opens (Fin m → ℂ)) (hVD : V ≤ D) (y : Fin m → ℂ),
      y ∈ V → ∀ x : OkaRing D ⊗[RelBase.{u} m] AlgSec (twist G n),
        anSecRestrict hVD (canMap D (twist G n) x) = 0 →
          ∃ (B : Opens (Fin m → ℂ)) (hBV : B ≤ V), (∃ a b : Fin m → ℂ,
            (B : Set (Fin m → ℂ)) = Complex.openBox a b) ∧ y ∈ B ∧
            (restrictOka.{u} (hBV.trans hVD)).toLinearMap.rTensor (AlgSec (twist G n)) x = 0 := by
  obtain ⟨n₀, h⟩ := exists_bijective_canMap hN G
  refine ⟨n₀, fun n hn D V hVD y hy x hx ↦ ?_⟩
  obtain ⟨a, b, hyB, hBV⟩ := exists_openBox_subset V.isOpen hy
  let B : Opens (Fin m → ℂ) := boxOpens a b
  have hBV' : B ≤ V := hBV
  refine ⟨B, hBV', ⟨a, b, rfl⟩, hyB, (h n hn a b B rfl).1 ?_⟩
  rw [map_zero, ← canMap_restrict]
  have hres : anSecRestrict (G := twist G n) (hBV'.trans hVD) (canMap D (twist G n) x) =
      anSecRestrict (G := twist G n) hBV' (anSecRestrict hVD (canMap D (twist G n) x)) :=
    (modRes_res _ _ _).symm
  rw [hres, hx]
  exact modRes_zero _

end ComplexAnalytic.relProjectiveSpaceAn

end
