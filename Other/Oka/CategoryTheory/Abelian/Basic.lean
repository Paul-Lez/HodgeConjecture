/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Generating an object from a kernel and a lift

Material for `Mathlib/CategoryTheory/Abelian/Basic.lean`; see `README.md` on the mirror tree.

`CategoryTheory.Abelian.epi_biprod_desc_kernel_ι` is the categorical form of the elementary
statement that if `π : P ⟶ B` is surjective and `F ⟶ P` hits generators of `B`, then `F`
together with `ker π` generates `P`. It is the step that turns "an extension of two objects of
finite type is of finite type" from a plausible claim into a proof, and nothing about finite
generation appears in it.

## Main results

- `CategoryTheory.Abelian.epi_biprod_desc_kernel_ι`
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **If `u ≫ π` is an epimorphism and `π` is an epimorphism, then `u` and the kernel of `π`
jointly cover the source of `π`.**

Elementwise: if every element of `B` is `π` of something and is already hit by `u ≫ π`, then
every `p : P` differs from something in the image of `u` by an element of `ker π`. -/
lemma epi_biprod_desc_kernel_ι {P B F : A} (π : P ⟶ B) [Epi π] (u : F ⟶ P)
    (hu : Epi (u ≫ π)) : Epi (biprod.desc u (kernel.ι π)) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro T w hw
  have h1 : kernel.ι π ≫ w = 0 := by
    rw [← biprod.inr_desc u (kernel.ι π), Category.assoc, hw, comp_zero]
  have h2 : u ≫ w = 0 := by
    rw [← biprod.inl_desc u (kernel.ι π), Category.assoc, hw, comp_zero]
  have h3 : π ≫ Abelian.epiDesc π w h1 = w := Abelian.comp_epiDesc π w h1
  have h4 : (u ≫ π) ≫ Abelian.epiDesc π w h1 = 0 := by rw [Category.assoc, h3, h2]
  rw [← h3, (cancel_epi (u ≫ π)).1 (h4.trans (comp_zero (f := u ≫ π)).symm), comp_zero]

end CategoryTheory.Abelian
