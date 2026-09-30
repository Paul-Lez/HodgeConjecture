/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Basic
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CohomologyModule

/-!
# Cohomology of sheaves of modules on complex analytic spaces is a `ℂ`-vector space

For a complex analytic space `Z` and a sheaf of `𝒪_Z`-modules `M`, the cohomology `Hᵠ(Z, M)` is a
module over `Γ(Z, 𝒪_Z)` (`AlgebraicGeometry.LocallyRingedSpace.H.module`), hence a `ℂ`-vector
space through the structure map `Z.algebraMap : ℂ →+* Γ(Z, 𝒪_Z)`
(`ComplexAnalytic.AnalyticSpace.moduleH`). Maps induced by morphisms of sheaves of modules,
connecting homomorphisms, and comparison maps along `ℂ`-linear morphisms of locally ringed spaces
are `ℂ`-linear.
-/

@[expose] public section

universe u

open CategoryTheory Opposite AlgebraicGeometry LocallyRingedSpace

namespace ComplexAnalytic

/-- The comparison map `Hᵠ(Y, M) → Hᵠ(X, i^* M)` along a morphism `i : X ⟶ Y` which is
`ℂ`-linear for `α` and `β` is `ℂ`-linear. -/
lemma IsCLinearHom.cohomologyMap_smul {X Y : LocallyRingedSpace.{u}} {i : X ⟶ Y}
    {α : ℂ →+* X.presheaf.obj (op ⊤)} {β : ℂ →+* Y.presheaf.obj (op ⊤)} (hi : IsCLinearHom i α β)
    (M : SheafOfModules.{u} Y.ringSheaf) {q : ℕ} (c : ℂ) (x : H M q) :
    i.cohomologyMap M q (β c • x) = α c • i.cohomologyMap M q x := by
  rw [Hom.cohomologyMap_smul]
  exact congrArg (· • i.cohomologyMap M q x) (hi c)

namespace AnalyticSpace

variable {Z : AnalyticSpace.{u}}

/-- **The cohomology of a sheaf of modules on a complex analytic space is a `ℂ`-vector space**,
through `Z.algebraMap : ℂ →+* Γ(Z, 𝒪_Z)`. -/
noncomputable instance moduleH (M : SheafOfModules.{u} Z.toLocallyRingedSpace.ringSheaf)
    (q : ℕ) : Module ℂ (H M q) :=
  Module.compHom _ Z.algebraMap

variable {M N : SheafOfModules.{u} Z.toLocallyRingedSpace.ringSheaf}

lemma smul_H_def {q : ℕ} (c : ℂ) (x : H M q) : c • x = Z.algebraMap c • x :=
  rfl

/-- Maps induced by morphisms of sheaves of modules are `ℂ`-linear. -/
lemma H_map_smul (φ : M ⟶ N) {q : ℕ} (c : ℂ) (x : H M q) :
    H.map φ q (c • x) = c • H.map φ q x :=
  H.map_smul φ (Z.algebraMap c) x

/-- The map `Hᵠ(Z, M) → Hᵠ(Z, N)` induced by a morphism of sheaves of modules, as a `ℂ`-linear
map. -/
noncomputable def hMapₗ (φ : M ⟶ N) (q : ℕ) : H M q →ₗ[ℂ] H N q where
  toFun := H.map φ q
  map_add' := map_add _
  map_smul' := H_map_smul φ

@[simp]
lemma hMapₗ_apply (φ : M ⟶ N) {q : ℕ} (x : H M q) : hMapₗ φ q x = H.map φ q x :=
  rfl

/-- The connecting homomorphisms are `ℂ`-linear. -/
lemma H_δ_smul {S : ShortComplex (SheafOfModules.{u} Z.toLocallyRingedSpace.ringSheaf)}
    (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (c : ℂ) (x : H S.X₃ n₀) :
    H.δ hS n₀ n₁ h (c • x) = c • H.δ hS n₀ n₁ h x :=
  H.δ_smul hS h (Z.algebraMap c) x

/-- The connecting homomorphism of a short exact sequence, as a `ℂ`-linear map. -/
noncomputable def hδₗ {S : ShortComplex (SheafOfModules.{u} Z.toLocallyRingedSpace.ringSheaf)}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : H S.X₃ n₀ →ₗ[ℂ] H S.X₁ n₁ where
  toFun := H.δ hS n₀ n₁ h
  map_add' := map_add _
  map_smul' := H_δ_smul hS h

/-- The comparison map along a morphism of complex analytic spaces is `ℂ`-linear. -/
lemma cohomologyMap_smul {W : AnalyticSpace.{u}} (g : Z ⟶ W)
    (M : SheafOfModules.{u} W.toLocallyRingedSpace.ringSheaf) {q : ℕ} (c : ℂ) (x : H M q) :
    g.toLRSHom.cohomologyMap M q (c • x) = c • g.toLRSHom.cohomologyMap M q x :=
  g.isCLinear.cohomologyMap_smul M c x

end AnalyticSpace

end ComplexAnalytic

end
