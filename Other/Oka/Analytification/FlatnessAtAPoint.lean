/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.AffineSpace
public import Other.Oka.Analytification.Flatness

/-!
# The stalk map of `ℂ^ι ⟶ 𝔸^ι_ℂ` is faithfully flat, at every point

**The analytic input to GAGA.** `Other/Oka/Analytification/Flatness.lean` proves that the germ ring
`ℂ{x}` is faithfully flat over the local ring `ℂ[x]_{(x)}` of affine space **at the origin**, as
a statement about honest rings. This file removes both of that file's restrictions:

```
ComplexAnalytic.faithfullyFlat_polyLocalToGermAt (z : ι → ℂ) :
  (ComplexAnalytic.polyLocalToGermAt z).toRingHom.FaithfullyFlat

ComplexAnalytic.faithfullyFlat_stalkMap_complexSpaceToSpec (z : ι → ℂ) :
  ((complexSpaceToSpec ι).stalkMap z).hom.FaithfullyFlat
```

The first is the statement about honest rings at an arbitrary point `z`; the second is the same
statement about the stalk map of the comparison morphism of locally ringed spaces itself, which
is the form a GAGA argument consumes and which no file in this development could state before.

## The germ ring at `z` is `LocalOkaRing ι`, and that is the whole of the general point

Three files on `master` said, in different words, that a general-point statement needed a
*construction* first, because `LocalOkaRing ι` is the germs at the origin by definition and so
there was nothing at `z` to compare `ℂ[x]_{ker (eval z)}` with. That is true of the definition
and false of the development: `okaStalkEquiv y` (`Other/Oka/StalkEquiv.lean`) identifies the stalk of
`𝒪_{ℂ^ι}` at an **arbitrary** `y` with `LocalOkaRing ι`, by Taylor expansion at `y`, and
`LocalOkaRing.ofMvPolynomial y` is likewise defined at an arbitrary point. The germ ring at `z`
was already there.

What was missing was one lemma, and it is not analysis:
`LocalOkaRing.ofMvPolynomial_taylorAlgHom` says the germ at `z` of a polynomial is the germ at
the origin of the shifted polynomial `p(x + z)`. Together with the fact that shifting the
variables carries the polynomials vanishing at `z` onto those vanishing at the origin
(`MvPolynomial.map_taylorEquiv_primeCompl`), it makes the square

```
ℂ[x]_{ker (eval z)}  ≅  ℂ[x]_{(x)}
        ↓                    ↓
    LocalOkaRing ι  =  LocalOkaRing ι
```

commute, and flatness at `z` is flatness at the origin read through the top isomorphism.
**Translation is affine, not linear, so `Other/Oka/ChangeOfCoordinates.lean` ; which handles
`(ι → ℂ) ≃L[ℂ] (κ → ℂ)` ; is not what does this.** The translation machinery used is
`TopologicalSpace.Opens.shift` and `OkaRing.shift` of `Other/Oka/StructureSheaf.lean`.

## Crossing to the geometric stalk map

`stalkMap_eq_lift` (`Other/Oka/Analytification/AffineSpace.lean`) already characterises
`(complexSpaceToSpec ι).stalkMap z` as the extension of `LocalOkaRing.ofMvPolynomial z` to the
localisation ; a rational function regular at `z` is the germ there of the holomorphic function
it defines. So the only work is to identify the source of that stalk map, which is the stalk of
`Spec ℂ[x]` under `z`, with `ComplexAnalytic.polyLocalAt z`. Both are localisations of
`MvPolynomial ι ℂ` at the same submonoid, so `IsLocalization.ringEquivOfRingEquiv` at
`RingEquiv.refl` does it.

**The transparency trap that `Other/Oka/Analytification/AffineSpace.lean` records does not bite here**,
because that file already restated Mathlib's `Algebra` and `IsLocalization.AtPrime` instances on
the stalk at this concrete point, which is exactly what they were restated for. One thing does
have to be avoided: `Ideal.primeCompl` takes the `Ideal.IsPrime` instance as an argument, so
rewriting with `complexSpaceToSpec_base_asIdeal` inside an `IsLocalization` goal fails on the
motive. `primeCompl_complexSpaceToSpec_base` proves the equality of the two submonoids instead,
which is what `IsLocalization.ringEquivOfRingEquiv` wants and needs no instance transported.

## What is *not* here

**This is not GAGA**, and it is not the exactness of analytification on coherent sheaves. It is
the local input those arguments consume, now available at every point of `ℂ^ι` rather than only
at the origin.

**Nor is it the stalk map of `X^an ⟶ X` for a presented algebra**, which is the map a GAGA
argument for an affine scheme other than `𝔸^ι` actually meets. That is
`Other/Oka/Analytification/PresentationFlatness.lean`, and it is a deduction from the statement here
by base change along `ℂ[x]_q ↠ (ℂ[x] ⧸ I)_q` rather than a new analytic input. What it needed on
top of `Other/Oka/Analytification/PresentationStalk.lean` was the identification of the **target**
`𝒪_{X^an, y}` with the germ ring modulo `I` ; which turned out to be the zero locus
construction's own stalk computation,
`AlgebraicGeometry.LocallyRingedSpace.surjective_stalkMap_zeroLocusιHom` and
`AlgebraicGeometry.LocallyRingedSpace.ker_stalkMap_zeroLocusιHom`, transported across the stalk
isomorphism of `(complexAffineSpace n).ofRestrict ⊤` ; and the compatibility of the two
identifications with the stalk map.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

variable {ι : Type u} [Fintype ι] (z : ι → ℂ)

/-! ### The local ring of affine space at a point -/

/-- **The local ring of `𝔸^ι_ℂ` at the point `z`**: the polynomials localised at the maximal
ideal of polynomials vanishing at `z`. At the origin this is `ComplexAnalytic.polyLocal`, but
not on the nose: the two ideals are equal only through
`MvPolynomial.idealOfVars_eq_ker_eval_zero`. -/
abbrev polyLocalAt : Type u :=
  Localization.AtPrime (RingHom.ker (MvPolynomial.eval z))

/-- **Translation identifies the local ring of `𝔸^ι` at `z` with the one at the origin**, by
substituting `x + z` for `x`. -/
def polyLocalAtEquiv : polyLocalAt z ≃ₐ[ℂ] polyLocal ι :=
  IsLocalization.algEquivOfAlgEquiv (A := ℂ) _ _ (MvPolynomial.taylorEquiv z)
    (MvPolynomial.map_taylorEquiv_primeCompl z)

/-- **A rational function regular at `z` has a germ at `z`**: the local ring of `𝔸^ι` at `z` maps
to the ring of germs of holomorphic functions there, which is `LocalOkaRing ι` by
`okaStalkEquiv`. As at the origin, this exists because a polynomial not vanishing at `z` has
invertible germ (`LocalOkaRing.isUnit_ofMvPolynomial_iff`). -/
def polyLocalToGermAt : polyLocalAt z →ₐ[ℂ] LocalOkaRing ι :=
  IsLocalization.liftAlgHom (M := (RingHom.ker (MvPolynomial.eval z)).primeCompl)
    (f := LocalOkaRing.ofMvPolynomial z) fun y ↦
      (LocalOkaRing.isUnit_ofMvPolynomial_iff _ _).mpr fun hcon ↦ y.2 (RingHom.mem_ker.mpr hcon)

@[simp]
theorem polyLocalToGermAt_algebraMap (q : MvPolynomial ι ℂ) :
    polyLocalToGermAt z (algebraMap (MvPolynomial ι ℂ) (polyLocalAt z) q) =
      LocalOkaRing.ofMvPolynomial z q :=
  IsLocalization.lift_eq _ q

/-- **The square commutes**: taking germs at `z` is taking germs at the origin after translating.

This is the whole content of the passage from the origin to a general point. Both sides are maps
out of a localisation, so it is enough to compare them on polynomials, where it is
`LocalOkaRing.ofMvPolynomial_taylorAlgHom`. -/
theorem polyLocalToGermAt_eq_comp :
    (polyLocalToGermAt z).toRingHom =
      (polyLocalToGerm (ι := ι)).toRingHom.comp (polyLocalAtEquiv z).toAlgHom.toRingHom := by
  refine IsLocalization.ringHom_ext (RingHom.ker (MvPolynomial.eval z)).primeCompl ?_
  refine RingHom.ext fun q ↦ ?_
  change polyLocalToGermAt z (algebraMap (MvPolynomial ι ℂ) (polyLocalAt z) q) =
    polyLocalToGerm (polyLocalAtEquiv z (algebraMap (MvPolynomial ι ℂ) (polyLocalAt z) q))
  rw [polyLocalToGermAt_algebraMap, polyLocalAtEquiv,
    IsLocalization.algEquivOfAlgEquiv_eq, polyLocalToGerm_algebraMap]
  exact (LocalOkaRing.ofMvPolynomial_taylorAlgHom z q).symm

/-! ### Flatness at a point, over honest rings -/

/-- **The germs at `z` are flat over the local ring of `𝔸^ι` at `z`.** -/
theorem flat_polyLocalToGermAt : (polyLocalToGermAt z).toRingHom.Flat := by
  rw [polyLocalToGermAt_eq_comp]
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (polyLocalAtEquiv z).bijective) flat_polyLocalToGerm

omit [Fintype ι] in
/-- An isomorphism is a local homomorphism. -/
theorem isLocalHom_polyLocalAtEquiv : IsLocalHom (polyLocalAtEquiv z).toAlgHom.toRingHom :=
  ⟨fun a h ↦ by simpa using h.map (polyLocalAtEquiv z).symm.toAlgHom.toRingHom⟩

/-- A rational function regular at `z` whose germ is invertible does not vanish at `z`. -/
theorem isLocalHom_polyLocalToGermAt : IsLocalHom (polyLocalToGermAt z).toRingHom := by
  haveI := isLocalHom_polyLocalAtEquiv z
  haveI := isLocalHom_polyLocalToGerm (ι := ι)
  rw [polyLocalToGermAt_eq_comp]
  exact RingHom.isLocalHom_comp _ _

/-- **The germs at `z` are faithfully flat over the local ring of `𝔸^ι` at `z`.**

As at the origin, faithfulness costs nothing beyond flatness: both rings are local and the map is
a local homomorphism. -/
theorem faithfullyFlat_polyLocalToGermAt :
    (polyLocalToGermAt z).toRingHom.FaithfullyFlat := by
  letI : Algebra (polyLocalAt z) (LocalOkaRing ι) := (polyLocalToGermAt z).toRingHom.toAlgebra
  haveI : Module.Flat (polyLocalAt z) (LocalOkaRing ι) := flat_polyLocalToGermAt z
  haveI : IsLocalHom (algebraMap (polyLocalAt z) (LocalOkaRing ι)) :=
    isLocalHom_polyLocalToGermAt z
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-! ### Flatness of the geometric stalk map -/

/-- The polynomials not in the point of `Spec (MvPolynomial ι ℂ)` underneath `z` are the
polynomials not vanishing at `z`.

Stated as an equality of *submonoids* rather than obtained by rewriting with
`complexSpaceToSpec_base_asIdeal`, because `Ideal.primeCompl` takes the `Ideal.IsPrime` instance
as an argument and the rewrite fails on the motive. -/
theorem primeCompl_complexSpaceToSpec_base :
    ((complexSpaceToSpec ι).base z).asIdeal.primeCompl =
      (RingHom.ker (MvPolynomial.eval z)).primeCompl := by
  refine Submonoid.ext fun x ↦ ?_
  change x ∉ ((complexSpaceToSpec ι).base z).asIdeal ↔ x ∉ RingHom.ker (MvPolynomial.eval z)
  rw [complexSpaceToSpec_base_asIdeal z]

/-- `primeCompl_complexSpaceToSpec_base` in the shape `IsLocalization.ringEquivOfRingEquiv`
consumes. -/
theorem map_primeCompl_complexSpaceToSpec_base :
    Submonoid.map (RingEquiv.refl (MvPolynomial ι ℂ)).toMonoidHom
        ((complexSpaceToSpec ι).base z).asIdeal.primeCompl =
      (RingHom.ker (MvPolynomial.eval z)).primeCompl :=
  (Submonoid.map_id _).trans (primeCompl_complexSpaceToSpec_base z)

/-- **The stalk of `Spec (MvPolynomial ι ℂ)` under `z` is the local ring of `𝔸^ι` at `z`.**

Both are localisations of `MvPolynomial ι ℂ` at the same submonoid ; the first by the instance
`Other/Oka/Analytification/AffineSpace.lean` restates at this concrete point, the second by
construction ; so this is `IsLocalization.ringEquivOfRingEquiv` at the identity. -/
def complexSpaceToSpecStalkEquiv : complexSpaceToSpecStalk z ≃+* polyLocalAt z :=
  IsLocalization.ringEquivOfRingEquiv _ _ (RingEquiv.refl (MvPolynomial ι ℂ))
    (map_primeCompl_complexSpaceToSpec_base z)

@[simp]
theorem complexSpaceToSpecStalkEquiv_algebraMap (p : MvPolynomial ι ℂ) :
    complexSpaceToSpecStalkEquiv z
        (algebraMap (MvPolynomial ι ℂ) (complexSpaceToSpecStalk z) p) =
      algebraMap (MvPolynomial ι ℂ) (polyLocalAt z) p :=
  IsLocalization.ringEquivOfRingEquiv_eq (map_primeCompl_complexSpaceToSpec_base z) p

/-- **The stalk map of `ℂ^ι ⟶ 𝔸^ι_ℂ` at `z` is the localisation-to-germs map at `z`**, once the
stalk of the source is named as a localisation and the stalk of the target as `LocalOkaRing ι`.

The mathematics is `stalkMap_eq_lift`, which this consumes; everything here is the identification
of the two ends. -/
theorem okaStalkEquiv_comp_stalkMap :
    (okaStalkEquiv z).toRingHom.comp ((complexSpaceToSpec ι).stalkMap z).hom =
      (polyLocalToGermAt z).toRingHom.comp (complexSpaceToSpecStalkEquiv z).toRingHom := by
  rw [stalkMap_eq_lift z]
  refine IsLocalization.ringHom_ext ((complexSpaceToSpec ι).base z).asIdeal.primeCompl ?_
  refine RingHom.ext fun p ↦ ?_
  simp only [RingHom.comp_apply]
  rw [IsLocalization.lift_eq]
  change _ = polyLocalToGermAt z (complexSpaceToSpecStalkEquiv z
    (algebraMap (MvPolynomial ι ℂ) (complexSpaceToSpecStalk z) p))
  rw [complexSpaceToSpecStalkEquiv_algebraMap, polyLocalToGermAt_algebraMap]
  rfl

/-- The stalk map, written as the map on honest rings between two isomorphisms. -/
theorem stalkMap_eq_comp :
    ((complexSpaceToSpec ι).stalkMap z).hom =
      (okaStalkEquiv z).symm.toRingHom.comp
        ((polyLocalToGermAt z).toRingHom.comp (complexSpaceToSpecStalkEquiv z).toRingHom) := by
  rw [← okaStalkEquiv_comp_stalkMap]
  exact RingHom.ext fun a ↦ ((okaStalkEquiv z).symm_apply_apply _).symm

/-- **The stalk map of the comparison morphism `ℂ^ι ⟶ 𝔸^ι_ℂ` is faithfully flat, at every point
of `ℂ^ι`.** This is the analytic input to GAGA, in the spelling a GAGA argument consumes: a
statement about `(complexSpaceToSpec ι).stalkMap`, not about a pair of rings chosen to be
comparable. -/
theorem faithfullyFlat_stalkMap_complexSpaceToSpec :
    ((complexSpaceToSpec ι).stalkMap z).hom.FaithfullyFlat := by
  rw [stalkMap_eq_comp]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.of_bijective (f := (complexSpaceToSpecStalkEquiv z).toRingHom)
        (complexSpaceToSpecStalkEquiv z).bijective)
      (faithfullyFlat_polyLocalToGermAt z))
    (RingHom.FaithfullyFlat.of_bijective (f := (okaStalkEquiv z).symm.toRingHom)
      (okaStalkEquiv z).symm.bijective)

/-- **The stalk map of the comparison morphism `ℂ^ι ⟶ 𝔸^ι_ℂ` is flat, at every point.** -/
theorem flat_stalkMap_complexSpaceToSpec :
    ((complexSpaceToSpec ι).stalkMap z).hom.Flat :=
  (faithfullyFlat_stalkMap_complexSpaceToSpec z).flat


/-! ### The germ of a polynomial, as a map out of `MvPolynomial ι ℂ`

The two lemmas below say that reading a polynomial as a germ at `z` is *injective*, i.e. that a
nonzero polynomial has nonzero germ at every point. That is not a new analytic fact ; it is a
corollary of the faithful flatness above, since a faithfully flat ring map is injective ; but it
is the statement a non-vacuity argument about a presented analytification needs, and there is no
other route to it in this development. -/

/-- **The germ at `z` of the holomorphic function a polynomial defines**, as a ring homomorphism
into the stalk of `𝒪_{ℂ^ι}` at `z`.

This is `okaGlobalOfMvPolynomial` followed by the germ map. Through `okaStalkEquiv` it is
`LocalOkaRing.ofMvPolynomial z`; it is stated on the stalk rather than on `LocalOkaRing ι`
because that is the ring the stalk map of `complexSpaceToSpec` lands in. -/
def germOfMvPolynomial : MvPolynomial ι ℂ →+* (complexSpace ι).presheaf.stalk z :=
  ((complexSpace ι).presheaf.Γgerm z).hom.comp (okaGlobalOfMvPolynomial ι).hom

/-- **The stalk map of `ℂ^ι ⟶ 𝔸^ι_ℂ` restricted along `toStalk` is the germ map.**

This is `toStalk_stalkMap_complexSpaceToSpec` with the structure map of the
localisation spelled as `algebraMap` rather than as `toStalk`, which is the form in which the
composite can be fed to `Ideal.map_map`. -/
theorem stalkMap_complexSpaceToSpec_comp_algebraMap :
    (((complexSpaceToSpec ι).stalkMap z).hom).comp
      (algebraMap (MvPolynomial ι ℂ) (complexSpaceToSpecStalk z)) = germOfMvPolynomial z := by
  refine RingHom.ext fun p ↦ ?_
  simp only [RingHom.comp_apply]
  rw [algebraMap_complexSpaceToSpecStalk]
  exact toStalk_stalkMap_complexSpaceToSpec _ p

/-- **A polynomial has invertible germ at `z` exactly when it does not vanish there**, on the
`ComplexAnalytic.germOfMvPolynomial` spelling.

`not_isUnit_germ_ofMvPolynomial_iff` states this on the `okaCommPresheaf`
spelling of the structure sheaf, which is definitionally but not syntactically the same; this
restatement is what a `rw` can use. -/
theorem not_isUnit_germOfMvPolynomial_iff (p : MvPolynomial ι ℂ) :
    ¬ IsUnit (germOfMvPolynomial z p) ↔ MvPolynomial.eval z p = 0 :=
  not_isUnit_germ_ofMvPolynomial_iff z p

/-- The stalk of `Spec (MvPolynomial ι ℂ)` under `z` contains the polynomials: it is a
localisation of a domain at a set of nonzero divisors. -/
theorem injective_algebraMap_complexSpaceToSpecStalk :
    Function.Injective (algebraMap (MvPolynomial ι ℂ) (complexSpaceToSpecStalk z)) :=
  IsLocalization.injective _
    (Ideal.primeCompl_le_nonZeroDivisors ((complexSpaceToSpec ι).base z).asIdeal)

/-- **A nonzero polynomial has nonzero germ at every point of `ℂ^ι`.**

The polynomials inject into the local ring of `𝔸^ι` at `z` because that is a localisation of a
domain, and the local ring injects into the germs because the map between them is faithfully
flat ; `Module.FaithfullyFlat` supplies `FaithfulSMul`, and a faithful scalar action by a
commutative ring is exactly injectivity of its structure map. So this is a consequence of
`ComplexAnalytic.faithfullyFlat_stalkMap_complexSpaceToSpec` rather than of anything about power
series. -/
theorem injective_germOfMvPolynomial : Function.Injective (germOfMvPolynomial z) := by
  rw [← stalkMap_complexSpaceToSpec_comp_algebraMap, RingHom.coe_comp]
  refine Function.Injective.comp ?_ (injective_algebraMap_complexSpaceToSpecStalk z)
  letI := (((complexSpaceToSpec ι).stalkMap z).hom).toAlgebra
  haveI : Module.FaithfullyFlat (complexSpaceToSpecStalk z)
      ((complexSpace ι).presheaf.stalk z) := faithfullyFlat_stalkMap_complexSpaceToSpec z
  exact FaithfulSMul.algebraMap_injective (complexSpaceToSpecStalk z)
    ((complexSpace ι).presheaf.stalk z)

end ComplexAnalytic

end
