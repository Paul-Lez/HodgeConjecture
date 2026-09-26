/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Other.Oka.RingTheory.Polynomial.ProjectiveDimension

/-!
# Global dimension of localisations

If every `R`-module has projective dimension at most `d`, then the same holds for every
localisation `R'` of `R`: an `R'`-module `M` satisfies `M ≅ R' ⊗[R] M`, and flat base change
does not increase projective dimension.

In particular every module over a localisation of `k[X₁, …, Xₙ]` (e.g. the coordinate ring
`k[X₁, …, Xₙ][1/f]` of a basic open subset of affine space) has projective dimension at most `n`.

## Main results

* `ModuleCat.HasGlobalDimensionLE.of_isLocalization`
* `ModuleCat.hasGlobalDimensionLE_of_isLocalization_mvPolynomial`
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace ModuleCat

/-- A localisation of a ring of global dimension `≤ d` has global dimension `≤ d`. -/
lemma HasGlobalDimensionLE.of_isLocalization {R : Type u} [CommRing R] (S : Submonoid R)
    (R' : Type u) [CommRing R'] [Algebra R R'] [IsLocalization S R'] {d : ℕ}
    (h : HasGlobalDimensionLE R d) : HasGlobalDimensionLE R' d := by
  intro M _ _
  letI : Module R M := Module.compHom M (algebraMap R R')
  haveI : IsScalarTower R R' M := ⟨fun r r' m ↦ by
    change (r • r') • m = (algebraMap R R' r) • (r' • m)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : Module.Flat R R' := IsLocalization.flat R' S
  have := h M
  have hT := hasProjectiveDimensionLE_baseChange (A := R) (B := R') d M
  have hb : IsBaseChange R' (LinearMap.id : M →ₗ[R] M) :=
    (isLocalizedModule_iff_isBaseChange S R' _).mp (isLocalizedModule_id S M R')
  exact hasProjectiveDimensionLE_of_linearEquiv.{u, u} (M := ModuleCat.of R' (R' ⊗[R] M))
    (N := ModuleCat.of R' M) hb.equiv d

/-- Every module over a localisation of `k[X₁, …, Xₙ]` has projective dimension at most `n`. -/
theorem hasGlobalDimensionLE_of_isLocalization_mvPolynomial (k : Type u) [Field k] (n : ℕ)
    (S : Submonoid (MvPolynomial (Fin n) k)) (R' : Type u) [CommRing R']
    [Algebra (MvPolynomial (Fin n) k) R'] [IsLocalization S R'] : HasGlobalDimensionLE R' n :=
  (hasGlobalDimensionLE_mvPolynomial k n).of_isLocalization S R'

end ModuleCat

end
