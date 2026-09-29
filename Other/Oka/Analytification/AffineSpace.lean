/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Other.Oka.Polynomial.Germ
public import Other.Oka.StalkEquiv

/-!
# Comparing `ℂ^ι` with affine space over `ℂ`

The base case of analytification: the canonical morphism of locally ringed spaces from `ℂ^ι`,
with its sheaf of holomorphic functions, to affine `ι`-space over `ℂ`. Everything about the
analytification of an affine `ℂ`-scheme is pulled back along it.

The morphism costs nothing to build. Mathlib's Γ-Spec adjunction provides
`AlgebraicGeometry.LocallyRingedSpace.toΓSpec`, the canonical map from any locally ringed space
to the spectrum of its global sections; the global sections of `ℂ^ι` are `OkaRing ⊤`, and
`OkaRing.ofMvPolynomial` reads a polynomial as a holomorphic function, so composing with `Spec`
of that ring homomorphism lands in `Spec (MvPolynomial ι ℂ)`. All the content is in identifying
the result, and that is `mem_complexSpaceToSpec_base_asIdeal_iff`: the point of
`Spec (MvPolynomial ι ℂ)` under `z` is the ideal of polynomials vanishing at `z`.

## A universe remark, because the obvious statement does not typecheck

One would like to land in `𝔸(ι; Spec (CommRingCat.of ℂ))` directly for `ι : Type u`. That is
not a well-formed expression: `AlgebraicGeometry.AffineSpace n S` needs `S : Scheme.{u}`, so it
needs `CommRingCat.of ℂ : CommRingCat.{u}`, and `ℂ : Type 0`. Nor is the index the problem ;
replacing `ι` by `ULift (Fin n)` changes nothing.

Routing through `Spec (MvPolynomial ι ℂ)` avoids this entirely, because `MvPolynomial ι ℂ` is a
`Type u` as soon as `ι` is, so `complexSpaceToSpec` is universe-polymorphic. The comparison with
affine space in Mathlib's sense is then `complexAffineSpaceToAffineSpace`, which lives in
`Type 0` where `𝔸(-; Spec ℂ)` makes sense, and is obtained from the polymorphic map by
`AlgebraicGeometry.AffineSpace.SpecIso`.

## Main definitions

- `complexSpaceToSpec`: the comparison morphism `ℂ^ι ⟶ Spec (MvPolynomial ι ℂ)`, for any finite
  index type `ι` in any universe.
- `complexAffineSpaceToAffineSpace`: the same map, presented as
  `ℂ^n ⟶ 𝔸^n_ℂ` with Mathlib's affine space, necessarily in `Type 0`.

## Main results

- `mem_complexSpaceToSpec_base_asIdeal_iff` and `complexSpaceToSpec_base_asIdeal`: **the point
  under `z` is the ideal of polynomials vanishing at `z`**, i.e. `ker (eval z)`.
- `isMaximal_complexSpaceToSpec_base_asIdeal`: that ideal is maximal, so `ℂ^ι` maps into the
  closed points of `Spec (MvPolynomial ι ℂ)`.
- `complexSpaceToSpec_base_injective`: the map on points is injective.
- `toStalk_stalkMap_complexSpaceToSpec` and `okaStalkEquiv_stalkMap_complexSpaceToSpec`: **the
  map on stalks is the localisation-to-germs map** ; a polynomial goes to the germ at `z` of the
  holomorphic function it defines. Since the stalk of `Spec R` at `p` *is* the localisation of
  `R` at `p`, and `isUnit_ofMvPolynomial_of_mem_primeCompl` says the denominators become units,
  this determines the stalk map completely.
- `stalkMap_eq_lift`: the same, packaged as an `IsLocalization.lift`. Informally, a rational
  function regular at `z` is the germ at `z` of the holomorphic function it defines.

## Two traps around the stalk of a `Spec`, both of which cost time here

Mathlib registers `Algebra R ((Spec.structureSheaf R).presheaf.stalk p)` and
`IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk p) p.asIdeal`, but a morphism of
locally ringed spaces produces the stalk in the `Spec.locallyRingedSpaceObj R` spelling. The two
are definitionally equal, and `Spec.locallyRingedSpaceObj` is a `def`, so instance search ; which
unfolds only at reducible transparency ; never reaches the `stalk` head and finds neither.

The failure is **instant**, a keying miss during instance search rather than a defeq blow-up, and
a search that fails on keying can be routed around: transport the instances with
`inferInstanceAs`, as the `Stalk` section below does. What is essential is that they are
stated **at the concrete point** `(complexSpaceToSpec ι).base z`. A *generic* transported
instance, over `R : CommRingCat` and `p : PrimeSpectrum R`, is still not found, because search
would then have to see `(complexSpaceToSpec ι).base z` ; whose type is
`↥(Spec.locallyRingedSpaceObj _).toTopCat` ; as a `PrimeSpectrum`, and that is the same
reducibility wall one step further out. `complexSpaceToSpecStalk` being an `abbrev` is a
readability convenience and plays no part: demoting it to a `def` and restating the instances on
the full spelling builds unchanged.

Separately, `algebraMap _ (complexSpaceToSpecStalk z) = toStalk _ _` is `rfl`, Mathlib's instance
being literally `(toStalk R p).hom.toAlgebra`, and proving it by `rfl` is cheap. What is *not*
cheap is crossing that seam while the goal in `stalkMap_eq_lift` is still wrapped in
`RingHom.comp`: a `change` spelling the left-hand side with `toStalk`, put *in place of* the
`simp only [RingHom.comp_apply]` step, times out at `whnf` on the default heartbeat budget. The
same `change` placed *after* that `simp only` costs nothing. So the rule is not "never cross the
seam" but *unwrap the goal before you do* ; and rewriting with
`algebraMap_complexSpaceToSpecStalk` avoids the question altogether, which is why that lemma
exists. (Write it as `change`, not `show`: a goal-changing `show` is flagged by
`linter.style.show` and fails the build under `--wfail`.)

## What is not here

**Flatness of the stalk map is not here, but it is no longer missing.**
`Other/Oka/Analytification/Flatness.lean` shows that `ℂ{x}` is faithfully flat over `ℂ[x]_{(x)}` at the
origin, as a statement about honest rings with no `Spec` stalk in it, and
`Other/Oka/Analytification/FlatnessAtAPoint.lean` turns that into
`ComplexAnalytic.faithfullyFlat_stalkMap_complexSpaceToSpec`: **the stalk map of the morphism
defined here is faithfully flat at every point.** It is stated there rather than here only
because it needs the germ ring, which this file does not import.

**And that in turn is no longer the end of the line.**
`Other/Oka/Analytification/PresentationFlatness.lean` quotients it by a presentation:
`ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec` is the same statement for
`X^an ⟶ Spec (ℂ[x] ⧸ I)`, which is the map a GAGA argument for an affine `ℂ`-scheme of finite
type actually meets. It also has a corollary that belongs to this file's subject even though it
is stated downstream: **a nonzero polynomial has nonzero germ at every point of `ℂ^ι`**
(`ComplexAnalytic.injective_germOfMvPolynomial`), because a faithfully flat ring map is
injective.

**And the two instances in the `Stalk` section below have a second consumer.**
`Other/Oka/Analytification/PresentationStalk.lean` restates them for `Spec (ℂ[x] ⧸ I)` under a point of
`X^an`, word for word, and identifies the stalk map of `ComplexAnalytic.analytificationToSpec`
the way `stalkMap_eq_lift` below identifies this one. **The transparency problem
this file's docstring measures does not fire there either**, and for the same reason: what makes
instance search work is that the instances are stated at the concrete point rather than for a
general `PrimeSpectrum`.

The two instances in the `Stalk` section below are what made that possible, and they are not
decoration: `RingHom.Flat` of the stalk map can be *stated* without them, but identifying its
source as a localisation cannot, and that identification is the whole of the crossing. Reading
`complexSpaceToSpec_base_asIdeal` into an `IsLocalization` goal by `rw` does *not* work ;
`Ideal.primeCompl` takes the `Ideal.IsPrime` instance as an argument, so the motive is
ill-typed; `ComplexAnalytic.primeCompl_complexSpaceToSpec_base` gives the equality of submonoids
instead.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

variable (ι : Type u) [Fintype ι]

/-- A polynomial is a holomorphic function on all of `ℂ^ι`, as a morphism of `CommRingCat` into
the global sections of the structure sheaf of `ℂ^ι`. This is `OkaRing.ofMvPolynomial` at
`U = ⊤`, bundled for use with `Spec`. -/
def okaGlobalOfMvPolynomial :
    CommRingCat.of (MvPolynomial ι ℂ) ⟶ LocallyRingedSpace.Γ.obj (op (complexSpace ι)) :=
  CommRingCat.ofHom (OkaRing.ofMvPolynomial (⊤ : Opens (ι → ℂ))).toRingHom

/-- **The comparison morphism from `ℂ^ι` to affine `ι`-space over `ℂ`**, as a morphism of
locally ringed spaces into `Spec (MvPolynomial ι ℂ)`.

This is the canonical map to the spectrum of the global sections
(`AlgebraicGeometry.LocallyRingedSpace.toΓSpec`) composed with `Spec` of "a polynomial is a
holomorphic function". See the module docstring for why the target is spelled as a spectrum
rather than as `𝔸(ι; Spec ℂ)`. -/
def complexSpaceToSpec :
    complexSpace ι ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of (MvPolynomial ι ℂ)) :=
  (complexSpace ι).toΓSpec ≫ Spec.locallyRingedSpaceMap (okaGlobalOfMvPolynomial ι)

variable {ι}

/-- The germ at `z` of the holomorphic function attached to a polynomial `p` is a non-unit
exactly when `p` vanishes at `z`.

Stated on the `okaCommPresheaf` spelling of the structure sheaf rather than on
`(complexSpace ι).presheaf`: the two are definitionally equal, but `germ_mem_maximalIdeal_iff`
is phrased in the former and `rw` cannot cross that seam. -/
theorem not_isUnit_germ_ofMvPolynomial_iff (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    ¬ IsUnit ((okaCommPresheaf ι).germ ⊤ z trivial (OkaRing.ofMvPolynomial ⊤ p)) ↔
      MvPolynomial.eval z p = 0 :=
  ((IsLocalRing.mem_maximalIdeal _).trans mem_nonunits_iff).symm.trans
    (germ_mem_maximalIdeal_iff (U := ⊤) trivial (OkaRing.ofMvPolynomial ⊤ p))

/-- **The point of `Spec (MvPolynomial ι ℂ)` underneath `z` is the ideal of polynomials
vanishing at `z`.** This is what makes `complexSpaceToSpec` recognisable as the classical
comparison map; without it the morphism is only a formal composite. -/
theorem mem_complexSpaceToSpec_base_asIdeal_iff (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    p ∈ ((complexSpaceToSpec ι).base z).asIdeal ↔ MvPolynomial.eval z p = 0 := by
  refine Iff.trans ?_ (not_isUnit_germ_ofMvPolynomial_iff z p)
  rw [show (complexSpaceToSpec ι).base z = PrimeSpectrum.comap
      (okaGlobalOfMvPolynomial ι).hom ((complexSpace ι).toΓSpecFun z) from rfl,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, ← not_not
      (a := (okaGlobalOfMvPolynomial ι).hom p ∈ ((complexSpace ι).toΓSpecFun z).asIdeal),
    LocallyRingedSpace.notMem_prime_iff_unit_in_stalk]
  exact Iff.rfl

/-- `mem_complexSpaceToSpec_base_asIdeal_iff` as an equality of ideals: the point underneath `z`
is the kernel of evaluation at `z`. -/
theorem complexSpaceToSpec_base_asIdeal (z : ι → ℂ) :
    ((complexSpaceToSpec ι).base z).asIdeal = RingHom.ker (MvPolynomial.eval z) :=
  Ideal.ext fun p ↦ (mem_complexSpaceToSpec_base_asIdeal_iff z p).trans RingHom.mem_ker.symm

/-- The image of `ℂ^ι` consists of **closed** points of `Spec (MvPolynomial ι ℂ)`: evaluation at
`z` is a surjection onto the field `ℂ`, so its kernel is a maximal ideal. -/
theorem isMaximal_complexSpaceToSpec_base_asIdeal (z : ι → ℂ) :
    ((complexSpaceToSpec ι).base z).asIdeal.IsMaximal := by
  rw [complexSpaceToSpec_base_asIdeal]
  exact RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval z)
    fun c ↦ ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩

/-- **The comparison morphism is injective on points.** Two points of `ℂ^ι` with the same image
agree, because `X i - C (w i)` vanishes at `w` and hence at `z`. -/
theorem complexSpaceToSpec_base_injective :
    Function.Injective fun z : ι → ℂ ↦ (complexSpaceToSpec ι).base z := by
  intro z w h
  -- The equality `h` of points is fed to `congrArg` rather than to `rw`: the carrier of
  -- `complexSpace ι` and `ι → ℂ` are definitionally equal but not at `instances`
  -- transparency, and a `rw` across that seam is rejected outright.
  have key (p : MvPolynomial ι ℂ) :
      MvPolynomial.eval z p = 0 ↔ MvPolynomial.eval w p = 0 :=
    (mem_complexSpaceToSpec_base_asIdeal_iff z p).symm.trans
      ((Iff.of_eq (congrArg (fun q : PrimeSpectrum (MvPolynomial ι ℂ) ↦ p ∈ q.asIdeal) h)).trans
        (mem_complexSpaceToSpec_base_asIdeal_iff w p))
  funext i
  have hz := (key (MvPolynomial.X i - MvPolynomial.C (w i))).2 (by simp)
  simpa [sub_eq_zero] using hz

section AffineSpace

variable (n : ℕ)

/-- **The comparison morphism `ℂ^n ⟶ 𝔸^n_ℂ`**, with Mathlib's affine space over `Spec ℂ`.

This is `complexSpaceToSpec` transported along `AlgebraicGeometry.AffineSpace.SpecIso`. It is
necessarily stated in `Type 0`: `𝔸(-; Spec (CommRingCat.of ℂ))` is a `Scheme.{0}` because `ℂ`
is, so unlike `complexSpaceToSpec` it cannot be universe-polymorphic. -/
def complexAffineSpaceToAffineSpace :
    complexAffineSpace.{0} n ⟶
      (𝔸(ULift.{0} (Fin n); Spec (CommRingCat.of ℂ))).toLocallyRingedSpace :=
  complexSpaceToSpec _ ≫
    (AffineSpace.SpecIso (ULift.{0} (Fin n)) (CommRingCat.of ℂ)).inv.toLRSHom

end AffineSpace


section Stalk

open StructureSheaf

/-- **The stalk map, restricted along `toStalk`, is the germ map.** A polynomial, regarded as a
global section of the structure sheaf of `Spec (MvPolynomial ι ℂ)`, is carried to the germ at `z`
of the holomorphic function it defines.

This is the characterising property: the stalk of `Spec R` at `p` is the localisation of `R` at
`p` (`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`), so a ring homomorphism out of
it is determined by its restriction along `toStalk`. `stalkMap_complexSpaceToSpec` is that
statement.

The proof composes two Mathlib lemmas ; `AlgebraicGeometry.stalkMap_toStalk` for the `Spec` half
and `AlgebraicGeometry.LocallyRingedSpace.toStalk_stalkMap_toΓSpec` for the unit half ; and never
unfolds `toΓSpecSheafedSpace`. The final step uses `congrArg` rather than `rw` because the
rewrite is rejected across the `TopCat.of` transparency seam. -/
theorem toStalk_stalkMap_complexSpaceToSpec (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    (complexSpaceToSpec ι).stalkMap z
        (toStalk (MvPolynomial ι ℂ) ((complexSpaceToSpec ι).base z) p) =
      (complexSpace ι).presheaf.Γgerm z (okaGlobalOfMvPolynomial ι p) := by
  have h1 := stalkMap_toStalk_apply (okaGlobalOfMvPolynomial ι)
    ((complexSpace ι).toΓSpecFun z) p
  have h2 := ConcreteCategory.congr_hom ((complexSpace ι).toStalk_stalkMap_toΓSpec z)
    (okaGlobalOfMvPolynomial ι p)
  simp only [ConcreteCategory.comp_apply] at h1 h2
  have key : (complexSpaceToSpec ι).stalkMap z =
      (Spec.locallyRingedSpaceMap (okaGlobalOfMvPolynomial ι)).stalkMap
        ((complexSpace ι).toΓSpecFun z) ≫ (complexSpace ι).toΓSpec.stalkMap z :=
    LocallyRingedSpace.stalkMap_comp _ _ _
  rw [key]
  -- `change`, not `rw`: the two spellings of the base point differ across the `TopCat.of`
  -- seam and a rewrite is rejected there as not type-correct.
  change (complexSpace ι).toΓSpec.stalkMap z
      ((Spec.sheafedSpaceMap (okaGlobalOfMvPolynomial ι)).hom.stalkMap
        ((complexSpace ι).toΓSpecFun z)
        (toStalk (MvPolynomial ι ℂ)
          (PrimeSpectrum.comap (okaGlobalOfMvPolynomial ι).hom
            ((complexSpace ι).toΓSpecFun z)) p)) = _
  exact (congrArg ((complexSpace ι).toΓSpec.stalkMap z) h1).trans h2

/-- Transported along `okaStalkEquiv`, the previous statement reads: a polynomial goes to its
germ at `z` as an element of `LocalOkaRing ι`, which is `LocalOkaRing.ofMvPolynomial`. -/
theorem okaStalkEquiv_stalkMap_complexSpaceToSpec (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    okaStalkEquiv z ((complexSpaceToSpec ι).stalkMap z
        (toStalk (MvPolynomial ι ℂ) ((complexSpaceToSpec ι).base z) p)) =
      LocalOkaRing.ofMvPolynomial z p := by
  rw [toStalk_stalkMap_complexSpaceToSpec]
  exact okaStalkEquiv_germ (U := ⊤) trivial (OkaRing.ofMvPolynomial ⊤ p)

/-- A polynomial not in the point underneath `z` ; that is, one which does not vanish at `z` ;
has invertible germ. This is what lets the localisation of `MvPolynomial ι ℂ` at that point map
to the germs at all. -/
theorem isUnit_ofMvPolynomial_of_mem_primeCompl (z : ι → ℂ)
    (y : ((complexSpaceToSpec ι).base z).asIdeal.primeCompl) :
    IsUnit (LocalOkaRing.ofMvPolynomial z (y : MvPolynomial ι ℂ)) := by
  rw [LocalOkaRing.isUnit_ofMvPolynomial_iff]
  exact fun h ↦ y.2 ((mem_complexSpaceToSpec_base_asIdeal_iff z _).2 h)

/-- The stalk of `Spec (MvPolynomial ι ℂ)` at the point underneath `z`, in the spelling a
morphism of locally ringed spaces produces it.

An abbreviation for readability only; a `def` would do just as well. What matters is that the two
instances below are stated at *this concrete point* rather than for a general `PrimeSpectrum`,
which is what lets instance search find them at all. See the module docstring. -/
abbrev complexSpaceToSpecStalk (z : ι → ℂ) : CommRingCat.{u} :=
  (Spec.locallyRingedSpaceObj (CommRingCat.of (MvPolynomial ι ℂ))).presheaf.stalk
    ((complexSpaceToSpec ι).base z)

/-- Mathlib's `Algebra` instance on the stalk of `Spec R`, transported to the spelling of
`complexSpaceToSpecStalk`. -/
instance (z : ι → ℂ) : Algebra (MvPolynomial ι ℂ) (complexSpaceToSpecStalk z) :=
  inferInstanceAs (Algebra (MvPolynomial ι ℂ)
    ((Spec.structureSheaf (CommRingCat.of (MvPolynomial ι ℂ))).presheaf.stalk
      ((complexSpaceToSpec ι).base z)))

/-- The stalk of `Spec (MvPolynomial ι ℂ)` at the point underneath `z` **is** the localisation of
`MvPolynomial ι ℂ` there, transported the same way. -/
instance (z : ι → ℂ) :
    IsLocalization.AtPrime (complexSpaceToSpecStalk z) ((complexSpaceToSpec ι).base z).asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime
    ((Spec.structureSheaf (CommRingCat.of (MvPolynomial ι ℂ))).presheaf.stalk
      ((complexSpaceToSpec ι).base z)) _)

/-- The structure map of the localisation is `toStalk`.

Mathlib's instance is literally `(toStalk R p).hom.toAlgebra`, so this is `rfl`, and `rfl` proves
it cheaply; `StructureSheaf.stalkAlgebra_map` is the same equation and is preferred here only as
the more robust citation. **Having it as a named lemma is what matters**, so that
`stalkMap_eq_lift` can `rw` with it and never has to make the elaborator see through the equation
while the goal is still wrapped in `RingHom.comp` ; which is where the cost is. See the module
docstring. -/
lemma algebraMap_complexSpaceToSpecStalk (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    algebraMap (MvPolynomial ι ℂ) (complexSpaceToSpecStalk z) p =
      toStalk (MvPolynomial ι ℂ) ((complexSpaceToSpec ι).base z) p :=
  StructureSheaf.stalkAlgebra_map (MvPolynomial ι ℂ) ((complexSpaceToSpec ι).base z) p

/-- **The map on stalks is the localisation-to-germs map.**

The stalk of `Spec (MvPolynomial ι ℂ)` at the point underneath `z` is the localisation of
`MvPolynomial ι ℂ` at `ker (eval z)`, and the stalk of `ℂ^ι` at `z` is `LocalOkaRing ι`. Under
those identifications the stalk map is the unique extension of `LocalOkaRing.ofMvPolynomial z` ;
"a polynomial is the germ of the holomorphic function it defines" ; to the localisation, which
exists because a polynomial not vanishing at `z` has invertible germ
(`isUnit_ofMvPolynomial_of_mem_primeCompl`).

Informally: **a rational function regular at `z` is the germ at `z` of the holomorphic function
it defines.** The mathematics is `okaStalkEquiv_stalkMap_complexSpaceToSpec`, which this consumes
verbatim; everything else here is packaging. -/
theorem stalkMap_eq_lift (z : ι → ℂ) :
    (okaStalkEquiv z).toRingHom.comp ((complexSpaceToSpec ι).stalkMap z).hom =
      IsLocalization.lift (M := ((complexSpaceToSpec ι).base z).asIdeal.primeCompl)
        (g := (LocalOkaRing.ofMvPolynomial z).toRingHom)
        (isUnit_ofMvPolynomial_of_mem_primeCompl z) := by
  refine IsLocalization.ringHom_ext ((complexSpaceToSpec ι).base z).asIdeal.primeCompl
    (RingHom.ext fun p ↦ ?_)
  simp only [RingHom.comp_apply]
  rw [IsLocalization.lift_eq, algebraMap_complexSpaceToSpecStalk]
  exact okaStalkEquiv_stalkMap_complexSpaceToSpec z p

end Stalk

end

end
