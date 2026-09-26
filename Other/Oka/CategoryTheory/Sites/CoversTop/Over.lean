/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.CategoryTheory.Sites.Spaces

/-! # Covers of terminal objects in slice sites -/

@[expose] public section

universe v' u'

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

/-- A family covering the terminal object induces a covering family in every slice. -/
lemma CoversTop.over' {I : Type*} {X : I → C} (hX : J.CoversTop X) (W : C) :
    (J.over W).CoversTop
      (fun (t : (i : I) × (V : C) × (V ⟶ X i) × (V ⟶ W)) ↦ Over.mk t.2.2.2) := by
  intro U
  rw [mem_over_iff]
  refine J.superset_covering ?_ (hX U.left)
  rintro V g ⟨i, ⟨f⟩⟩
  exact ⟨Over.mk (g ≫ U.hom), Over.homMk g, 𝟙 _,
    ⟨⟨i, V, f, g ≫ U.hom⟩, ⟨Over.homMk (𝟙 _)⟩⟩, (Category.id_comp _).symm⟩

end CategoryTheory.GrothendieckTopology

open CategoryTheory

namespace TopologicalSpace.Opens

/-- A family of open subsets covering an open `X` covers the terminal object of its slice
site. -/
lemma coversTop_over {T : Type u'} [TopologicalSpace T] (X : Opens T) {A : Type u'}
    (V : A → Opens T) (hle : ∀ a, V a ≤ X) (hcov : ∀ x ∈ X, ∃ a, x ∈ V a) :
    ((Opens.grothendieckTopology T).over X).CoversTop (fun a ↦ Over.mk (homOfLE (hle a))) := by
  intro Z
  let S : Sieve Z.left :=
    ⟨fun W _ ↦ ∃ a, W ≤ V a, by rintro W₁ W₂ f ⟨a, ha⟩ g; exact ⟨a, (leOfHom g).trans ha⟩⟩
  have hS : S ∈ Opens.grothendieckTopology T Z.left := by
    intro x hx
    obtain ⟨a, ha⟩ := hcov x (leOfHom Z.hom hx)
    exact ⟨Z.left ⊓ V a, homOfLE inf_le_left, ⟨a, inf_le_right⟩, ⟨hx, ha⟩⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (GrothendieckTopology.overEquiv_symm_mem_over _ Z S hS)
  rintro W g ⟨a, ha⟩
  exact ⟨a, ⟨Over.homMk (homOfLE ha)⟩⟩

end TopologicalSpace.Opens
