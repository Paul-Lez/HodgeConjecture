/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Missing `Fin.init` and `Fin.append` lemmas

Material for `Mathlib/Data/Fin/Tuple/Basic.lean`; see the tracking issue on moving the
project's Mathlib-bound lemmas into this mirror tree.

The header names the two `Fin` operations this file has lemmas about rather than counting the
lemmas, so that appending one does not falsify it.
-/

@[expose] public section

namespace Fin

variable {n : ℕ} {α : Type*}

section Zero

variable [Zero α]

/-- Dropping the last coordinate of the zero tuple gives the zero tuple.

This is the `simp` normal form that `Fin.init` needs: without it a goal such as
`TopologicalSpace.Opens.zero_mem_extend'` normalises to `Fin.init 0 ∈ U` and `simp` gets
stuck one rewrite short of the answer. -/
@[simp]
lemma init_zero : Fin.init (0 : Fin (n + 1) → α) = 0 :=
  rfl

end Zero

/-- **The range of a concatenation of two tuples is the union of their ranges.**

`Fin.append_left` and `Fin.append_right` say what `Fin.append` does at each of the two families
of indices, and `Fin.addCases` says those are all the indices; this is the two of them read as a
statement about the image, which is the form a consumer indexing a span or a `∀` by a
concatenated family needs. -/
theorem range_append {m n : ℕ} (a : Fin m → α) (b : Fin n → α) :
    Set.range (Fin.append a b) = Set.range a ∪ Set.range b := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (motive := fun i ↦ Fin.append a b i ∈ Set.range a ∪ Set.range b)
      (fun l ↦ ?_) (fun r ↦ ?_) i
    · exact Or.inl ⟨l, (Fin.append_left a b l).symm⟩
    · exact Or.inr ⟨r, (Fin.append_right a b r).symm⟩
  · rintro (⟨l, rfl⟩ | ⟨r, rfl⟩)
    · exact ⟨Fin.castAdd n l, Fin.append_left a b l⟩
    · exact ⟨Fin.natAdd m r, Fin.append_right a b r⟩

end Fin


end
