/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.Presentation

/-!
# The stalk map of `X^an ⟶ X` for a presented affine `ℂ`-algebra

`Other/Oka/Analytification/Presentation.lean` builds the comparison morphism
`ComplexAnalytic.analytificationToSpec g : X^an ⟶ Spec (ℂ[x] ⧸ I)` and identifies its map on
*points*. This file identifies its map on *stalks*, which is what a local statement about the
comparison ; flatness, and hence GAGA ; consumes.

The two ends:

* the **source**, `𝒪_{X, φ(y)}`, is the localisation of `ℂ[x] ⧸ I` at the point underneath `y`,
  and ; since localisation commutes with quotients ; the localisation of `ℂ[x]` at the point
  underneath `y` in `𝔸^n`, modulo `I`;
* the **map** is the unique extension to that localisation of *"a class in `ℂ[x] ⧸ I` goes to the
  germ at `y` of the holomorphic function it defines"*.

## What this is the analogue of

`Other/Oka/Analytification/AffineSpace.lean` does the same for the ambient comparison morphism
`ℂ^ι ⟶ 𝔸^ι_ℂ`: `complexSpaceToSpecStalk` with its two transported instances,
and `stalkMap_eq_lift`. **Every statement here is that file's statement with a
quotient inserted, and every proof here is that file's proof**, because
`ComplexAnalytic.analytificationToSpec` is `complexSpaceToSpec`'s construction
with `ComplexAnalytic.quotientToGlobal` in place of `okaGlobalOfMvPolynomial`.

That is worth saying explicitly, because it is the answer to a question the issue this file
closes flagged as its schedule risk. The `Spec.locallyRingedSpaceObj` transparency problem
**does not fire here either**, for the same reason it did not fire for the ambient map: the
`Algebra` and `IsLocalization.AtPrime` instances are restated at the *concrete point*
`(analytificationToSpec g).base y`, where instance search can key on them, rather than for a
general `PrimeSpectrum`.

**Until 2026-08-31 that sentence described the problem as an `isDefEq` timing out at a million
heartbeats, and it is the description taxis #599 retracted.**
`Other/Oka/Analytification/AffineSpace.lean` is the file that documents this seam, and it says the
opposite in terms: the failure is *"instant,
a keying miss during instance search rather than a defeq blow-up"* ; which is the whole reason the
route around it exists, since a search that fails on keying can be routed around and a defeq
blow-up usually cannot. There is a real timeout on that line of work, and it is a different step:
crossing the seam while the goal is still wrapped in `RingHom.comp`. So this paragraph was
carrying, into a second file, the misattribution that #599 was rejected for and corrected in the
first; what makes the correction cheap to state is that the sentence it belongs to was already
right about *why* nothing fires here.

## Main definitions

- `ComplexAnalytic.analytificationToSpecStalk`: the stalk of `Spec (ℂ[x] ⧸ I)` under a point of
  `X^an`, with Mathlib's `Algebra` and `IsLocalization.AtPrime` instances transported to it.
- `ComplexAnalytic.quotientToGerm`: **a class in `ℂ[x] ⧸ I`, as a germ of a holomorphic function
  on `X^an`.**
- `ComplexAnalytic.analytificationStalkQuotEquiv`: **the stalk of `Spec (ℂ[x] ⧸ I)` under `y` is
  the stalk of `Spec ℂ[x]` under `y` modulo `I`.**

## Main results

- `ComplexAnalytic.toStalk_stalkMap_analytificationToSpec`: **the characterising property** ; the
  stalk map sends the image of `a` under `toStalk` to the germ of the holomorphic function `a`
  defines.
- `ComplexAnalytic.stalkMap_analytificationToSpec_eq_lift`: **the stalk map is
  `IsLocalization.lift` of `ComplexAnalytic.quotientToGerm`.** This is the analogue of
  `stalkMap_eq_lift` and it is the form a flatness argument consumes: a map out
  of a localisation, with no stalk left in the source.
- `ComplexAnalytic.isUnit_quotientToGerm_iff` and
  `ComplexAnalytic.isUnit_quotientToGerm_of_mem_primeCompl`: a class has invertible germ at `y`
  exactly when it does not vanish there ; the hypothesis of the lift.
- `ComplexAnalytic.algebraMapSubmonoid_primeCompl_eq`: the multiplicative set the quotient
  inherits is the one the quotient's own point defines. Stated as an equality of **submonoids**,
  for the reason `ComplexAnalytic.primeCompl_complexSpaceToSpec_base` is.

## What is not here

* **Flatness of this stalk map**, which is what the identifications above are for. It is not
  missing: `Other/Oka/Analytification/PresentationFlatness.lean` supplies the remaining piece ; the
  identification of the *target* `𝒪_{X^an, y}` with the germ ring modulo `I`, which is the
  zero locus construction's stalk computation transported across the restriction of `ℂ^n` to
  `⊤` ; together with the compatibility of the two identifications with
  the stalk map, and concludes `ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec`.
  **`ComplexAnalytic.analytificationStalkQuotEquiv` is the source half of that argument**, and is
  the reason this file exists in the shape it does.
* **Anything analytic.** The only analytic input used here is
  `ComplexAnalytic.AnalyticSpace.evalStalk_ne_zero_iff_isUnit`, i.e. that the residue field of an
  analytic space is `ℂ`; everything else is the `Γ`–`Spec` adjunction and localisation.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- The point of `ℂ^n` underlying a point of the analytification. -/
abbrev basePt (y : AnalyticSpace.analytification.{u} g) : ULift.{u} (Fin n) → ℂ := y.1.1

section Stalk

open StructureSheaf

/-- The stalk of `Spec (ℂ[x] ⧸ I)` at the point underneath `y`.

An abbreviation for readability only. What matters is that the two instances below are stated at
*this concrete point* rather than for a general `PrimeSpectrum`, which is what lets instance
search find them at all; see `Other/Oka/Analytification/AffineSpace.lean`, where the same is done for
the ambient comparison morphism and where the failure mode is measured. -/
abbrev analytificationToSpecStalk (y : AnalyticSpace.analytification.{u} g) : CommRingCat.{u} :=
  (Spec.locallyRingedSpaceObj (CommRingCat.of (PresentedAlgebra.{u} n k g))).presheaf.stalk
    ((analytificationToSpec g).base y)

/-- Mathlib's `Algebra` instance on the stalk of a `Spec`, transported to the spelling a morphism
of locally ringed spaces produces. -/
instance (y : AnalyticSpace.analytification.{u} g) :
    Algebra (PresentedAlgebra.{u} n k g) (analytificationToSpecStalk g y) :=
  inferInstanceAs (Algebra (PresentedAlgebra.{u} n k g)
    ((Spec.structureSheaf (CommRingCat.of (PresentedAlgebra.{u} n k g))).presheaf.stalk
      ((analytificationToSpec g).base y)))

/-- **The stalk of `Spec (ℂ[x] ⧸ I)` under `y` is the localisation of `ℂ[x] ⧸ I` there**,
transported the same way. -/
instance (y : AnalyticSpace.analytification.{u} g) :
    IsLocalization.AtPrime (analytificationToSpecStalk g y)
      ((analytificationToSpec g).base y).asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime
    ((Spec.structureSheaf (CommRingCat.of (PresentedAlgebra.{u} n k g))).presheaf.stalk
      ((analytificationToSpec g).base y)) _)

/-- The structure map of the localisation is `toStalk`. As for the ambient case this is `rfl`,
and it is stated so that the lift below never has to cross the spelling seam while the goal is
still wrapped in `RingHom.comp`. -/
lemma algebraMap_analytificationToSpecStalk (y : AnalyticSpace.analytification.{u} g)
    (a : PresentedAlgebra.{u} n k g) :
    algebraMap (PresentedAlgebra.{u} n k g) (analytificationToSpecStalk g y) a =
      toStalk (PresentedAlgebra.{u} n k g) ((analytificationToSpec g).base y) a :=
  StructureSheaf.stalkAlgebra_map (PresentedAlgebra.{u} n k g) ((analytificationToSpec g).base y) a

/-- **A class in `ℂ[x] ⧸ I`, as a germ of a holomorphic function on `X^an` at `y`.** -/
def quotientToGerm (y : AnalyticSpace.analytification.{u} g) :
    PresentedAlgebra.{u} n k g →+* (AnalyticSpace.analytification.{u} g).presheaf.stalk y :=
  ((AnalyticSpace.analytification.{u} g).presheaf.Γgerm y).hom.comp (quotientToGlobal g)

/-- **The characterising property of the stalk map**: the image of `a` under `toStalk` goes to the
germ at `y` of the holomorphic function `a` defines.

The stalk of `Spec R` at `p` is the localisation of `R` there, so a ring homomorphism out of it
is determined by its restriction along `toStalk`; this is that restriction.

The proof composes `AlgebraicGeometry.stalkMap_toStalk` for the `Spec` half with
`AlgebraicGeometry.LocallyRingedSpace.toStalk_stalkMap_toΓSpec` for the unit half, and is
`toStalk_stalkMap_complexSpaceToSpec`'s proof verbatim with
`ComplexAnalytic.quotientToGlobal` in place of `okaGlobalOfMvPolynomial`. The
last step uses `congrArg` rather than `rw` because the rewrite is rejected across the
`TopCat.of` transparency seam. -/
theorem toStalk_stalkMap_analytificationToSpec (y : AnalyticSpace.analytification.{u} g)
    (a : PresentedAlgebra.{u} n k g) :
    (analytificationToSpec g).stalkMap y
        (toStalk (PresentedAlgebra.{u} n k g) ((analytificationToSpec g).base y) a) =
      (AnalyticSpace.analytification.{u} g).presheaf.Γgerm y (quotientToGlobal g a) := by
  have h1 := stalkMap_toStalk_apply (CommRingCat.ofHom (quotientToGlobal g))
    ((AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.toΓSpecFun y) a
  have h2 := ConcreteCategory.congr_hom
    ((AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.toStalk_stalkMap_toΓSpec y)
    (quotientToGlobal g a)
  simp only [ConcreteCategory.comp_apply] at h1 h2
  have key : (analytificationToSpec g).stalkMap y =
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (quotientToGlobal g))).stalkMap
        ((AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.toΓSpecFun y) ≫
        (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.toΓSpec.stalkMap y :=
    LocallyRingedSpace.stalkMap_comp _ _ _
  rw [key]
  -- `change`, not `rw`: the two spellings of the base point differ across the `TopCat.of` seam
  -- and a rewrite is rejected there as not type-correct.
  change (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.toΓSpec.stalkMap y
      ((Spec.sheafedSpaceMap (CommRingCat.ofHom (quotientToGlobal g))).hom.stalkMap
        ((AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.toΓSpecFun y)
        (toStalk (PresentedAlgebra.{u} n k g)
          (PrimeSpectrum.comap (CommRingCat.ofHom (quotientToGlobal g)).hom
            ((AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.toΓSpecFun y)) a)) = _
  exact (congrArg ((AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.toΓSpec.stalkMap y)
    h1).trans h2

/-- The point of `Spec (ℂ[x] ⧸ I)` underneath `y` consists of the classes vanishing at `y`.

This is `ComplexAnalytic.AnalyticSpace.mem_toΓSpec_base_asIdeal_iff` ; *the prime of
`Spec Γ(Z)` under `z` is the ideal of global sections vanishing at `z`* ; applied on the nose,
which it is because the base map of `analytificationToSpec` is the comap of
`ComplexAnalytic.quotientToGlobal` along that of `toΓSpec`. -/
theorem mem_analytificationToSpec_base_asIdeal_iff_eval
    (y : AnalyticSpace.analytification.{u} g) (a : PresentedAlgebra.{u} n k g) :
    a ∈ ((analytificationToSpec g).base y).asIdeal ↔
      AnalyticSpace.eval (Z := AnalyticSpace.analytification.{u} g) (U := ⊤) y trivial
        (quotientToGlobal g a) = 0 :=
  AnalyticSpace.mem_toΓSpec_base_asIdeal_iff _ y (quotientToGlobal g a)

/-- **A class has invertible germ at `y` exactly when it does not vanish there.**

The analytic content is `ComplexAnalytic.AnalyticSpace.evalStalk_ne_zero_iff_isUnit`: the residue
field of a complex analytic space at a point is `ℂ`, so a germ is a unit exactly when its value
is nonzero. -/
theorem isUnit_quotientToGerm_iff (y : AnalyticSpace.analytification.{u} g)
    (a : PresentedAlgebra.{u} n k g) :
    IsUnit (quotientToGerm g y a) ↔ a ∉ ((analytificationToSpec g).base y).asIdeal := by
  rw [← AnalyticSpace.evalStalk_ne_zero_iff_isUnit,
    mem_analytificationToSpec_base_asIdeal_iff_eval]
  exact Iff.rfl

/-- **A class not vanishing at `y` has invertible germ**, which is what lets the localisation map
to the stalk of `X^an` at all. -/
theorem isUnit_quotientToGerm_of_mem_primeCompl (y : AnalyticSpace.analytification.{u} g)
    (a : ((analytificationToSpec g).base y).asIdeal.primeCompl) :
    IsUnit (quotientToGerm g y (a : PresentedAlgebra.{u} n k g)) :=
  (isUnit_quotientToGerm_iff g y a).2 a.2

/-- **The stalk map of `X^an ⟶ Spec (ℂ[x] ⧸ I)` is the localisation-to-germs map.**

Informally: *a fraction of classes whose denominator does not vanish at `y` is the germ at `y` of
the holomorphic function it defines.* This is the analogue of `stalkMap_eq_lift`
and, like it, is the form in which a flatness argument can consume the stalk map: the source is
an honest localisation and the map is determined by its restriction to `ℂ[x] ⧸ I`. -/
theorem stalkMap_analytificationToSpec_eq_lift (y : AnalyticSpace.analytification.{u} g) :
    ((analytificationToSpec g).stalkMap y).hom =
      IsLocalization.lift (M := ((analytificationToSpec g).base y).asIdeal.primeCompl)
        (g := quotientToGerm g y) (isUnit_quotientToGerm_of_mem_primeCompl g y) := by
  refine IsLocalization.ringHom_ext ((analytificationToSpec g).base y).asIdeal.primeCompl
    (RingHom.ext fun a ↦ ?_)
  simp only [RingHom.comp_apply]
  rw [IsLocalization.lift_eq, algebraMap_analytificationToSpecStalk]
  exact toStalk_stalkMap_analytificationToSpec g y a

end Stalk

section Quotient

/-- **The classes not vanishing at `y` are exactly the images of the polynomials not vanishing at
the underlying point of `ℂ^n`.**

Stated as an equality of *submonoids* rather than obtained by rewriting an equality of ideals,
because `Ideal.primeCompl` takes the `Ideal.IsPrime` instance as an argument and the rewrite
fails on the motive ; the same trap, and the same way round it, as
`ComplexAnalytic.primeCompl_complexSpaceToSpec_base`. -/
theorem algebraMapSubmonoid_primeCompl_eq (y : AnalyticSpace.analytification.{u} g) :
    Algebra.algebraMapSubmonoid (PresentedAlgebra.{u} n k g)
        ((complexSpaceToSpec (ULift.{u} (Fin n))).base (basePt g y)).asIdeal.primeCompl =
      ((analytificationToSpec g).base y).asIdeal.primeCompl := by
  ext u
  simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Ideal.primeCompl,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [show (algebraMap (MvPolynomial (ULift.{u} (Fin n)) ℂ) (PresentedAlgebra.{u} n k g) a) =
      Ideal.Quotient.mk (presentationIdeal g) a from rfl,
      mem_analytificationToSpec_base_asIdeal_iff]
    rwa [mem_complexSpaceToSpec_base_asIdeal_iff] at ha
  · intro hu
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨a, ?_, rfl⟩
    rw [mem_complexSpaceToSpec_base_asIdeal_iff]
    rwa [mem_analytificationToSpec_base_asIdeal_iff] at hu

/-- The stalk of `Spec ℂ[x]` under `y`, modulo the ideal `I` generates in it. -/
abbrev complexSpaceToSpecStalkQuot (y : AnalyticSpace.analytification.{u} g) : Type u :=
  complexSpaceToSpecStalk (basePt g y) ⧸
    (presentationIdeal g).map
      (algebraMap (MvPolynomial (ULift.{u} (Fin n)) ℂ) (complexSpaceToSpecStalk (basePt g y)))

/-- **The stalk of `Spec (ℂ[x] ⧸ I)` under `y` is the stalk of `Spec ℂ[x]` under `y` modulo
`I`** ; localisation commutes with the quotient.

Both sides are localisations of `ℂ[x] ⧸ I` at the same multiplicative set: the left by the
instance above, the right by Mathlib's `IsLocalization` instance for a quotient of a
localisation, once `ComplexAnalytic.algebraMapSubmonoid_primeCompl_eq` identifies the two
multiplicative sets. So this is `IsLocalization.algEquiv` and there is nothing to prove.

The `▸` transports a `Prop`-valued class along an equality of *submonoids*, which is an explicit
argument of `IsLocalization`; it is not a cast of data. It has to be a submonoid equality rather
than an ideal one for the reason `ComplexAnalytic.algebraMapSubmonoid_primeCompl_eq` records. -/
def analytificationStalkQuotEquiv (y : AnalyticSpace.analytification.{u} g) :
    analytificationToSpecStalk g y ≃ₐ[PresentedAlgebra.{u} n k g] complexSpaceToSpecStalkQuot g y :=
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid (PresentedAlgebra.{u} n k g)
        ((complexSpaceToSpec (ULift.{u} (Fin n))).base (basePt g y)).asIdeal.primeCompl)
      (analytificationToSpecStalk g y) := (algebraMapSubmonoid_primeCompl_eq g y) ▸ inferInstance
  IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid (PresentedAlgebra.{u} n k g)
      ((complexSpaceToSpec (ULift.{u} (Fin n))).base (basePt g y)).asIdeal.primeCompl)
    (analytificationToSpecStalk g y) (complexSpaceToSpecStalkQuot g y)

end Quotient

end

end ComplexAnalytic

end
