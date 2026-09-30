/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The kernel of a map into a binary biproduct

Material for `Mathlib/CategoryTheory/Limits/Shapes/BinaryBiproducts.lean`; see `README.md` on the
mirror tree.

A morphism into `A ⊞ B` is a pair `(p, q)`, and elementwise its kernel is the intersection
`ker p ∩ ker q`. Written as an iterated kernel that is

```
ker (biprod.lift p q) ≅ ker (ker q ↪ Z --p--> A)
```

which is `CategoryTheory.Limits.kernelBiprodLiftIso` below. **The point of the iterated form is
that it is an intersection computed one map at a time**, so a hypothesis of the shape "the kernel
of a map into `A` is small, and the kernel of a map into `B` is small" applies to it twice; the
intersection itself is not a kernel of anything with a single target.

Mathlib has neither this nor its `prod.lift` analogue: a search for `kernel` together with
`prod.lift` or `biprod.lift` finds only
`Mathlib/CategoryTheory/Limits/Shapes/NormalMono/Equalizers.lean`, where a fork of this shape is
built by hand for an unrelated purpose.

## Main definitions

- `CategoryTheory.Limits.kernelBiprodLiftIso`: the kernel of `biprod.lift p q` is the kernel of
  `p` restricted to the kernel of `q`, with `isLimitKernelForkBiprodLift` the underlying limit
  and `kernelBiprodLiftIso_hom_ι` identifying it over `Z`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasKernels C]

variable {Z A B : C} (p : Z ⟶ A) (q : Z ⟶ B) [HasBinaryBiproduct A B]

/-- The composite `ker (ker q ↪ Z --p--> A) ⟶ ker q ⟶ Z` kills `biprod.lift p q`. -/
lemma kernel_ι_comp_kernel_ι_comp_biprod_lift :
    (kernel.ι (kernel.ι q ≫ p) ≫ kernel.ι q) ≫ biprod.lift p q = 0 := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- **The kernel of a morphism into a binary biproduct, computed one component at a time.**

The universal property: a map killing `biprod.lift p q` kills `q`, hence factors through
`ker q`, and the factorisation kills `ker q ↪ Z --p--> A`. Uniqueness is the composite of two
kernel inclusions being a monomorphism. -/
noncomputable def isLimitKernelForkBiprodLift :
    IsLimit (KernelFork.ofι (kernel.ι (kernel.ι q ≫ p) ≫ kernel.ι q)
      (kernel_ι_comp_kernel_ι_comp_biprod_lift p q)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} m hm ↦ kernel.lift (kernel.ι q ≫ p)
      (kernel.lift q m (by simpa using hm =≫ biprod.snd))
      (by rw [kernel.lift_ι_assoc]; simpa using hm =≫ biprod.fst))
    (fun {_} m hm ↦ by rw [kernel.lift_ι_assoc, kernel.lift_ι])
    (fun {_} m hm l hl ↦ by
      rw [← cancel_mono (kernel.ι (kernel.ι q ≫ p) ≫ kernel.ι q), hl, kernel.lift_ι_assoc,
        kernel.lift_ι])

/-- **The kernel of `biprod.lift p q` is the kernel of `p` restricted to the kernel of `q`.**

This is the form in which a bound on kernels of maps into `A` and into `B` separately bounds
kernels of maps into `A ⊞ B`: apply it to `q` first and then to the restriction of `p`. -/
noncomputable def kernelBiprodLiftIso :
    kernel (kernel.ι q ≫ p) ≅ kernel (biprod.lift p q) :=
  IsLimit.conePointUniqueUpToIso (isLimitKernelForkBiprodLift p q) (limit.isLimit _)

@[reassoc (attr := simp)]
lemma kernelBiprodLiftIso_hom_ι :
    (kernelBiprodLiftIso p q).hom ≫ kernel.ι (biprod.lift p q) =
      kernel.ι (kernel.ι q ≫ p) ≫ kernel.ι q :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

end CategoryTheory.Limits
