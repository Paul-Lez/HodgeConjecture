/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-! # Covering the terminal object by domains in covering sieves -/

@[expose] public section

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- The domains of the arrows in a covering sieve over each object cover the terminal object. -/
lemma coversTop_of_sieves (J : GrothendieckTopology C) (S : ∀ Z : C, Sieve Z)
    (hS : ∀ Z, S Z ∈ J Z) :
    J.CoversTop (fun (t : Σ (Z : C), Σ (W : C), {g : W ⟶ Z // (S Z).arrows g}) ↦ t.2.1) := by
  intro Z
  refine J.superset_covering ?_ (hS Z)
  intro V g hg
  exact ⟨⟨Z, V, g, hg⟩, ⟨𝟙 V⟩⟩

end CategoryTheory.GrothendieckTopology
