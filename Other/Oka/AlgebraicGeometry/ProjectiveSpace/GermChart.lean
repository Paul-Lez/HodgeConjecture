/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.TwistSections

/-!
# Germs on the charts of `ℙⁿ`, and twisting sheaves on `ℙ⁰`

- `ProjectiveSpace.germ_UI_injective`: over a domain `R`, the sections of `𝒪` over
  `UI I = D₊(∏_{i ∈ I} Xᵢ)` form a domain, so the germ map at any point of `UI I` is injective.
- `ProjectiveSpace.cocycle_zero_zpow`, `ProjectiveSpace.twistingSheafZeroIsoUnit`: `ℙ⁰` has a
  single chart, so every power of the standard cocycle is trivial and `O(k) ≅ 𝒪` on `ℙ⁰`.
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

/-- On `ℙⁿ` over a domain, the germ map at a point of `UI I` is injective on sections over
`UI I`: these form a domain, and the stalk is a localization. -/
lemma germ_UI_injective {n : ℕ} {R : Type u} [CommRing R] [IsDomain R]
    {I : Finset (Fin (n + 1))} (hI : I.Nonempty) (x : ℙₒ(n; R)) (hx : x ∈ UI n R I) :
    Function.Injective (ℙₒ(n; R).presheaf.germ (UI n R I) x hx) := by
  have hne : prodX R I ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ MvPolynomial.X_ne_zero j
  haveI : IsDomain (Localization.Away (prodX R I)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hne)
  haveI : IsDomain Γ(ℙₒ(n; R), UI n R I) := (toAway_injective hI).isDomain _
  obtain ⟨i, hi⟩ := hI
  have hU := isAffineOpen_UI (R := R) hi
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact @IsLocalization.injective _ _ _ _ _ (show _ from _) this
    (Ideal.primeCompl_le_nonZeroDivisors _)

/-- On `ℙ⁰` every power of the standard cocycle is trivial: there is only one chart. -/
lemma cocycle_zero_zpow {R : Type u} [CommRing R] (k : ℤ) : cocycle 0 R ^ k = 1 :=
  Scheme.Modules.Cocycle.ext fun i j ↦ by
    obtain rfl : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    rw [Scheme.Modules.Cocycle.self, Scheme.Modules.Cocycle.self]

/-- On `ℙ⁰` every twisting sheaf is trivial: `O(k) ≅ 𝒪`. -/
def twistingSheafZeroIsoUnit {R : Type u} [CommRing R] (k : ℤ) :
    twistingSheaf 0 R k ≅ SheafOfModules.unit _ :=
  (Scheme.Modules.twistFunctorCongr (cocycle_zero_zpow k)).app _ ≪≫
    Scheme.Modules.twistOneIso _ (iSup_U 0 R)

end AlgebraicGeometry.ProjectiveSpace

end
