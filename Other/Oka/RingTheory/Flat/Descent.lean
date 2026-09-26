/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Flatness descends along a faithfully flat extension of the middle ring

Material for `Mathlib/RingTheory/Flat/Stability.lean`; see `README.md` on the mirror tree.

For a tower `A → B → C`, if `C` is flat over `A` and **faithfully** flat over `B`, then `B` is
flat over `A`. Mathlib has flatness stable under composition (`Module.Flat.trans`) and under base
change, and it has faithfully flat descent along a change of *base* ring
(`Module.Flat.of_flat_tensorProduct`); what is missing is the cancellation on the right, which is
what one uses when `C` is a completion or a larger ring in which computations are easier than in
`B`.

## The proof

`B` is `A`-flat as soon as `N ⊗[A] B → P ⊗[A] B` is injective for every submodule `N ≤ P` of
`A`-modules. Tensoring that map with `C` over `B` gives, after
`AlgebraTensorModule.cancelBaseChange`, the map `N ⊗[A] C → P ⊗[A] C`, which is injective because
`C` is `A`-flat; and `Module.FaithfullyFlat.lTensor_injective_iff_injective` **reflects**
injectivity along `B → C`. The square that makes this work is Mathlib's
`AlgebraTensorModule.lTensor_comp_cancelBaseChange`.

## Main results

- `Module.Flat.of_faithfullyFlat_tower`: **flatness of `C` over `A` descends to `B`**, along a
  faithfully flat `B → C`.
-/

@[expose] public section

open TensorProduct LinearMap

/-- **Flatness descends along a faithfully flat extension of the middle ring**: if `C` is flat
over `A` and faithfully flat over `B`, then `B` is flat over `A`.

The classical use is `C` a completion: `B ⊗ -` is hard to see and `C ⊗ -` is not, and `B → C`
being faithfully flat is what lets the conclusion come back. -/
theorem Module.Flat.of_faithfullyFlat_tower (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat B C] [Module.Flat A C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  have hAC : Function.Injective ⇑(LinearMap.lTensor C N.subtype) :=
    (Module.Flat.iff_lTensor_injectiveₛ.mp inferInstance) N
  have hsq := AlgebraTensorModule.lTensor_comp_cancelBaseChange A B C (M := C) N.subtype
  have h1 : Function.Injective
      (⇑(AlgebraTensorModule.cancelBaseChange A B C C P) ∘
        ⇑((AlgebraTensorModule.lTensor C C) ((AlgebraTensorModule.lTensor B B) N.subtype))) := by
    have h2 : ⇑((AlgebraTensorModule.lTensor C C) N.subtype) ∘
        ⇑(AlgebraTensorModule.cancelBaseChange A B C C N) =
        ⇑(AlgebraTensorModule.cancelBaseChange A B C C P) ∘
        ⇑((AlgebraTensorModule.lTensor C C) ((AlgebraTensorModule.lTensor B B) N.subtype)) :=
      congrArg (fun f : _ →ₗ[C] _ ↦ ⇑f) hsq
    rw [← h2]
    exact hAC.comp (AlgebraTensorModule.cancelBaseChange A B C C N).injective
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective B C
    ((AlgebraTensorModule.lTensor B B) N.subtype)).mp (Function.Injective.of_comp h1)

end
