/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Flatness is stable under quotienting by an ideal of the base

Material for `Mathlib/RingTheory/Flat/Stability.lean`, next to `Module.Flat.baseChange`; see
`README.md` on the mirror tree. `Other/Oka/RingTheory/Flat/Descent.lean` is bound for the same Mathlib
file and says the complementary thing ; cancellation on the right of a tower.

If `B` is flat over `A` and `I` is an ideal of `A`, then `B ⧸ I B` is flat over `A ⧸ I`, and the
same with "faithfully" throughout. This is base change along `A → A ⧸ I`, which Mathlib already
has; the only thing missing is that the base change of `B` *is* `B ⧸ I B`, which is
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`. So both proofs are one transport each.

## Why it is worth stating separately

Base change is usually applied with the *new base* in hand and the tensor product as the answer.
Here it is the other way round: the ring one has is `B ⧸ I B` ; a quotient of germs by an ideal
sheaf, a coordinate ring, a stalk of a closed subscheme ; and the tensor product is a step of the
proof one would rather not see in the statement.

## Main results

- `Module.Flat.quotIdealMap`: flatness of `A ⧸ I → B ⧸ I B`.
- `Module.FaithfullyFlat.quotIdealMap`: the same for faithful flatness.
-/

@[expose] public section

open TensorProduct

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

/-- **Flatness is stable under quotienting by an ideal of the base**: if `B` is flat over `A`
then `B ⧸ I B` is flat over `A ⧸ I`. -/
theorem Module.Flat.quotIdealMap [Module.Flat A B] :
    Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  haveI : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] B) := Module.Flat.baseChange A (A ⧸ I) B
  Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv

/-- **Faithful flatness is stable under quotienting by an ideal of the base.**

The unqualified statement, unlike the one for a general tower: faithful flatness is preserved by
*arbitrary* base change, so nothing has to be assumed about `I`. -/
theorem Module.FaithfullyFlat.quotIdealMap [Module.FaithfullyFlat A B] :
    Module.FaithfullyFlat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  haveI : Module.FaithfullyFlat (A ⧸ I) ((A ⧸ I) ⊗[A] B) := inferInstance
  Module.FaithfullyFlat.of_linearEquiv _ _
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv

end
