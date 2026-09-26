/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Other.Oka.RingTheory.Flat.Quotient

/-!
# Quotienting a faithfully flat ring map by an ideal of the source

Material for `Mathlib/RingTheory/RingHom/FaithfullyFlat.lean`; see `README.md` on the mirror tree.

`Other/Oka/RingTheory/Flat/Quotient.lean` says that if `B` is faithfully flat over `A` and `I` is an
ideal of `A` then `B ⧸ I B` is faithfully flat over `A ⧸ I`. That is a statement about
`Module.FaithfullyFlat` and about the `Algebra` instance; a consumer holding a bare ring
homomorphism `f : A →+* B` with `f.FaithfullyFlat` has to install `f.toAlgebra` before it
applies. This file does that once, so that the induced map on quotients can be fed to
`RingHom.FaithfullyFlat.stableUnderComposition` directly.

## Why this is not in `Other/Oka/RingTheory/Flat/Quotient.lean`

Because the two would go to different Mathlib files. That file's destination is
`Mathlib/RingTheory/Flat/Stability.lean`, which does not know about `RingHom.FaithfullyFlat` ;
adding `Mathlib.RingTheory.RingHom.FaithfullyFlat` to it would make its stated destination false,
which is the failure this project has already recorded once. A `RingHom.FaithfullyFlat` lemma
belongs where `RingHom.FaithfullyFlat` is defined.

## What is not here

* **The `RingHom.Flat` analogue.** It would go to `Mathlib/RingTheory/RingHom/Flat.lean`, a
  different file again, and nothing needs it: a consumer wanting flatness of the induced map gets
  it from `RingHom.FaithfullyFlat.flat`, and the hypothesis it would need ; `Module.Flat` rather
  than `Module.FaithfullyFlat` ; is not weaker in any use this development has.

## Main results

- `RingHom.FaithfullyFlat.quotIdealMap`: `A ⧸ I → B ⧸ I B` is faithfully flat.
-/

@[expose] public section

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **Quotienting a faithfully flat ring map by an ideal of the source keeps it faithfully
flat**: if `f : A →+* B` is faithfully flat and `I` is an ideal of `A`, then the induced map
`A ⧸ I → B ⧸ I B` is faithfully flat.

This is `Module.FaithfullyFlat.quotIdealMap` with `f.toAlgebra` installed. Nothing is assumed
about `I`, because faithful flatness is preserved by arbitrary base change. -/
theorem RingHom.FaithfullyFlat.quotIdealMap {f : A →+* B} (hf : f.FaithfullyFlat) (I : Ideal A) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).FaithfullyFlat := by
  letI := f.toAlgebra
  haveI : Module.FaithfullyFlat A B := hf
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr (Module.FaithfullyFlat.quotIdealMap A B I)

end
