/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.Pullback

/-!
# Connecting homomorphisms and the pullback map in degree zero

Two complements to `Other/Oka/Topology/Sheaves/Cohomology/Basic.lean` and
`Other/Oka/Topology/Sheaves/Cohomology/Pullback.lean`:

* `TopCat.Sheaf.H.δ_naturality`: the connecting homomorphisms are natural with respect to
  morphisms of short exact sequences of abelian sheaves.
* `TopCat.Sheaf.H.equiv₀_pullback`: in degree zero, the pullback map
  `H⁰(X, F) → H⁰(Y, f⁻¹ F)` along a continuous map `f : Y ⟶ X` is, on global sections, the
  unit `F(X) → (f⁻¹ F)(f⁻¹ X) = (f⁻¹ F)(Y)` of the adjunction `f⁻¹ ⊣ f_*`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}

/-- `H.equiv₀` unfolded: evaluate the adjoint `ℤ → F(X)` of a morphism `ℤ_X ⟶ F` at `1`. -/
lemma H.equiv₀_apply (F : AbSheaf X) (x : H F 0) :
    H.equiv₀ F x = AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop).homEquiv _ F (Ext.addEquiv₀ x)) :=
  rfl

/-- The connecting homomorphisms are natural with respect to morphisms of short exact
sequences. -/
lemma H.δ_naturality {S₁ S₂ : ShortComplex (AbSheaf X)} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S₁.X₃ n₀) :
    H.δ h₂ n₀ n₁ h (H.map φ.τ₃ n₀ x) = H.map φ.τ₁ n₁ (H.δ h₁ n₀ n₁ h x) := by
  rw [H.δ_apply, H.δ_apply, H.map_apply, H.map_apply,
    Ext.comp_assoc_of_second_deg_zero, ← ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ,
    Ext.comp_assoc_of_third_deg_zero]

variable (f : Y ⟶ X)

/-- In degree zero the pullback map `H⁰(X, F) → H⁰(Y, f⁻¹ F)` is the map on global sections
given by the unit `F ⟶ f_* f⁻¹ F` of the adjunction `f⁻¹ ⊣ f_*`. -/
lemma H.equiv₀_pullback {F : AbSheaf X} (x : H F 0) :
    H.equiv₀ _ (H.pullback f x) =
      ((pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom.app (op ⊤)
        (H.equiv₀ F x) := by
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  set adjX := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
  set adjY := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop
  set P := pullbackPushforwardAdjunction AddCommGrpCat.{u} f
  have key : Ext.addEquiv₀ (H.pullback f (Ext.addEquiv₀.symm g)) =
      (pullbackConstZIso f).inv ≫ (pullbackAb f).map g := by
    apply Ext.addEquiv₀.symm.injective
    simp only [AddEquiv.symm_apply_apply]
    change (Ext.mk₀ _).comp (Ext.mapExactFunctor (pullbackAb f) (Ext.mk₀ g)) (zero_add 0) =
      Ext.mk₀ _
    rw [Ext.mapExactFunctor_mk₀]
    exact Ext.mk₀_comp_mk₀ _ _
  have hinv : adjY.homEquiv _ _ (pullbackConstZIso f).inv =
      (adjX.comp P).unit.app (AddCommGrpCat.of (ULift ℤ)) :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app adjY (adjX.comp P) _
  have hmor : adjY.homEquiv _ _ ((pullbackConstZIso f).inv ≫ (pullbackAb f).map g) =
      adjX.homEquiv _ _ g ≫
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).map
          (P.unit.app F) := by
    rw [Adjunction.homEquiv_naturality_right, hinv, Adjunction.comp_unit_app,
      adjX.homEquiv_unit]
    ext s
    exact (congr_arg (fun φ => φ.hom.app (op ⊤) (adjX.unit.app _ s))
      (P.unit.naturality g)).symm
  rw [H.equiv₀_apply, H.equiv₀_apply, key, hmor, AddEquiv.apply_symm_apply]
  rfl

end TopCat.Sheaf

end
