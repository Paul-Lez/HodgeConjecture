/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Other.Oka.Analytification.LocalRing
public import Other.Oka.Completion
public import Other.Oka.Polynomial.Germ
public import Other.Oka.RingTheory.Flat.Descent

/-!
# The germ ring is faithfully flat over the local ring of affine space

**The analytic input to GAGA**, at the origin: writing `𝒪_{𝔸^ι, 0} = ℂ[x]_{(x)}` for the local
ring of affine space and `𝒪_{ℂ^ι, 0} = ℂ{x}` for the ring of germs of holomorphic functions,

```
ComplexAnalytic.faithfullyFlat_polyLocalToGerm :
  (ComplexAnalytic.polyLocalToGerm (ι := ι)).toRingHom.FaithfullyFlat
```

so a system of equations with polynomial coefficients has a convergent solution as soon as it has
a formal one, and an ideal of `𝒪_{𝔸^ι, 0}` is recovered from the ideal it generates in the germs.

## What makes it short, and it is not the local criterion

The classical route to this statement is the local criterion for flatness: a local homomorphism
of Noetherian local rings is flat when the induced map of completions is. **That is not used
here, and it is not needed**, because the two completions are not merely isomorphic ; they are
the *same ring*:

* `ℂ⟦x⟧` is the completion of `ℂ{x}` and is **faithfully flat** over it
  (`LocalOkaRing.instFaithfullyFlat`, `Other/Oka/Completion.lean`);
* `ℂ⟦x⟧` is the completion of `ℂ[x]_{(x)}` and is therefore **flat** over it
  (`ComplexAnalytic.flat_polyLocalToMvPowerSeries`, `Other/Oka/Analytification/LocalRing.lean`).

Flatness of `ℂ[x]_{(x)} → ℂ{x}` then follows by descent along the *middle* ring:
`Module.Flat.of_faithfullyFlat_tower` in the mirror tree, which is Mathlib's
`cancelBaseChange` square plus the fact that a faithfully flat extension **reflects**
injectivity. Faithfulness is then free from `Module.FaithfullyFlat.of_flat_of_isLocalHom`, since
both rings are local and the map is local ; and *that* is inherited from the completion, where
Mathlib already knows `algebraMap R R̂` is a local hom.

## What is here

* `ComplexAnalytic.polyLocalToGerm`: the map itself, which did not exist before. A rational
  function regular at the origin has a germ, by `IsLocalization.liftAlgHom` and the fact that a
  polynomial not vanishing at the origin is an invertible germ.
* `ComplexAnalytic.coe_polyLocalToGerm`: the triangle ; the germ of such a function, read as a
  formal power series, is its Taylor expansion. This is what makes `ℂ[x]_{(x)} → ℂ{x} → ℂ⟦x⟧` a
  scalar tower, which is what the descent consumes.
* **Not** `LocalOkaRing.coe_ofMvPolynomial_zero`, *"at the origin the germ of a polynomial is
  the polynomial"*, which the scalar tower below runs on. It stood here until it acquired a
  second consumer, with a paragraph saying it did so *"only because the proof names
  `LocalOkaRing.coord`, which lives in `Other/Oka/MaximalIdeal.lean` and is not in that file's import
  closure"*. That was accurate and the obstacle it named costs one `Oka` module and no Mathlib
  module, so the declaration is now beside `LocalOkaRing.ofMvPolynomial` in
  `Other/Oka/Polynomial/Germ.lean`, which this file already imported and still does.

## What is *not* here

**Everything is at the origin.** The general-point statement is
`Other/Oka/Analytification/FlatnessAtAPoint.lean`, which deduces it from this one by translating: the
algebraic side by the automorphism `xᵢ ↦ xᵢ + zᵢ`, and the analytic side by the fact that the
germ at `z` of a polynomial is the germ at the origin of the shifted polynomial
(`LocalOkaRing.ofMvPolynomial_taylorAlgHom`).

An earlier version of this paragraph said the analytic side *could not* be translated, because
`LocalOkaRing ι` is the germs at `0` by construction and so there was no germ ring at any other
point to compare with. That was true of the definition and false of the development: `okaStalkEquiv`
identifies the stalk of `𝒪_{ℂ^ι}` at **every** point with `LocalOkaRing ι`, by Taylor expansion
there, and had done so since long before this file was written.

**This is not GAGA**, and it is not the exactness of analytification on coherent sheaves. It is
the local input those arguments consume.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open MvPowerSeries IsLocalRing

universe u

noncomputable section

namespace ComplexAnalytic

variable {ι : Type u} [Fintype ι]

/-! ### The local ring of affine space maps to the germs -/

/-- **A rational function regular at the origin has a germ**: the local ring of `𝔸^ι` at the
origin maps to the ring of germs of holomorphic functions.

This is the map whose flatness is the analytic input to GAGA, and it did not exist before: a
polynomial not vanishing at the origin is an invertible *germ*
(`LocalOkaRing.isUnit_ofMvPolynomial_iff`), so the localisation's universal property applies. -/
def polyLocalToGerm : polyLocal ι →ₐ[ℂ] LocalOkaRing ι :=
  IsLocalization.liftAlgHom (M := (MvPolynomial.idealOfVars ι ℂ).primeCompl)
    (f := LocalOkaRing.ofMvPolynomial (0 : ι → ℂ)) fun y ↦
      (LocalOkaRing.isUnit_ofMvPolynomial_iff _ _).mpr fun hcon ↦ y.2 (by
        have hy : (y : MvPolynomial ι ℂ) ∈ RingHom.ker (MvPolynomial.eval fun _ : ι ↦ (0 : ℂ)) :=
          RingHom.mem_ker.mpr hcon
        rwa [← MvPolynomial.idealOfVars_eq_ker_eval_zero] at hy)

@[simp]
theorem polyLocalToGerm_algebraMap (q : MvPolynomial ι ℂ) :
    polyLocalToGerm (algebraMap (MvPolynomial ι ℂ) (polyLocal ι) q) =
      LocalOkaRing.ofMvPolynomial (0 : ι → ℂ) q :=
  IsLocalization.lift_eq _ q

theorem val_comp_polyLocalToGerm :
    ((localOkaSubring ι).val.comp (polyLocalToGerm (ι := ι))).toRingHom =
      (polyLocalToMvPowerSeries (ι := ι)).toRingHom := by
  refine IsLocalization.ringHom_ext (MvPolynomial.idealOfVars ι ℂ).primeCompl ?_
  refine RingHom.ext fun q ↦ ?_
  change ((polyLocalToGerm (algebraMap (MvPolynomial ι ℂ) (polyLocal ι) q) :
    LocalOkaRing ι) : MvPowerSeries ι ℂ) = _
  rw [polyLocalToGerm_algebraMap, LocalOkaRing.coe_ofMvPolynomial_zero]
  exact (polyLocalToMvPowerSeries_algebraMap q).symm

/-- **The triangle**: the germ of a rational function regular at the origin is, as a formal
power series, its Taylor expansion.

Without this the two maps out of `ℂ[x]_{(x)}` ; into the germs and into the formal power series ;
would be unrelated, and there would be no scalar tower for the descent to run in. -/
theorem coe_polyLocalToGerm (a : polyLocal ι) :
    ((polyLocalToGerm a : LocalOkaRing ι) : MvPowerSeries ι ℂ) = polyLocalToMvPowerSeries a :=
  RingHom.congr_fun val_comp_polyLocalToGerm a

/-! ### Flatness -/

/-- An isomorphism is a local homomorphism. -/
theorem isLocalHom_polyLocalAdicCompletionEquiv {ι : Type u} [Finite ι] :
    IsLocalHom (polyLocalAdicCompletionEquiv (ι := ι)).toAlgHom.toRingHom :=
  ⟨fun a h ↦ by
    simpa using h.map (polyLocalAdicCompletionEquiv (ι := ι)).symm.toAlgHom.toRingHom⟩

/-- The Taylor expansion of a rational function regular at the origin is a **local**
homomorphism, because it is the canonical map into a completion read through an isomorphism. -/
theorem isLocalHom_polyLocalToMvPowerSeries {ι : Type u} [Finite ι] :
    IsLocalHom (polyLocalToMvPowerSeries (ι := ι)).toRingHom := by
  haveI := isLocalHom_polyLocalAdicCompletionEquiv (ι := ι)
  rw [← algHom_comp_algebraMap_eq]
  exact RingHom.isLocalHom_comp _ _

/-- A rational function regular at the origin whose germ is invertible does not vanish at the
origin: `ComplexAnalytic.polyLocalToGerm` is a local homomorphism. -/
theorem isLocalHom_polyLocalToGerm : IsLocalHom (polyLocalToGerm (ι := ι)).toRingHom := by
  haveI : IsLocalHom (((localOkaSubring ι).val.toRingHom).comp
      (polyLocalToGerm (ι := ι)).toRingHom) := by
    rw [show ((localOkaSubring ι).val.toRingHom).comp (polyLocalToGerm (ι := ι)).toRingHom =
      (polyLocalToMvPowerSeries (ι := ι)).toRingHom from val_comp_polyLocalToGerm]
    exact isLocalHom_polyLocalToMvPowerSeries
  exact isLocalHom_of_comp _ ((localOkaSubring ι).val.toRingHom)

/-- **The germs are flat over the local ring of `𝔸^ι` at the origin.**

By descent along the middle ring of `ℂ[x]_{(x)} → ℂ{x} → ℂ⟦x⟧`: the formal power series are flat
over the first and faithfully flat over the second, and a faithfully flat extension reflects
injectivity. No local criterion for flatness is used; see the module docstring. -/
theorem flat_polyLocalToGerm : (polyLocalToGerm (ι := ι)).toRingHom.Flat := by
  letI : Algebra (polyLocal ι) (LocalOkaRing ι) := (polyLocalToGerm (ι := ι)).toRingHom.toAlgebra
  letI : Algebra (polyLocal ι) (MvPowerSeries ι ℂ) :=
    (polyLocalToMvPowerSeries (ι := ι)).toRingHom.toAlgebra
  haveI : IsScalarTower (polyLocal ι) (LocalOkaRing ι) (MvPowerSeries ι ℂ) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (coe_polyLocalToGerm a).symm
  haveI : Module.Flat (polyLocal ι) (MvPowerSeries ι ℂ) := flat_polyLocalToMvPowerSeries
  exact Module.Flat.of_faithfullyFlat_tower (polyLocal ι) (LocalOkaRing ι) (MvPowerSeries ι ℂ)

/-- **The germs are faithfully flat over the local ring of `𝔸^ι` at the origin**: the analytic
input to GAGA, at the origin.

Faithfulness costs nothing beyond flatness here, because both rings are local and
`ComplexAnalytic.polyLocalToGerm` is a local homomorphism. -/
theorem faithfullyFlat_polyLocalToGerm : (polyLocalToGerm (ι := ι)).toRingHom.FaithfullyFlat := by
  letI : Algebra (polyLocal ι) (LocalOkaRing ι) := (polyLocalToGerm (ι := ι)).toRingHom.toAlgebra
  haveI : Module.Flat (polyLocal ι) (LocalOkaRing ι) := flat_polyLocalToGerm
  haveI : IsLocalHom (algebraMap (polyLocal ι) (LocalOkaRing ι)) := isLocalHom_polyLocalToGerm
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end ComplexAnalytic

end
