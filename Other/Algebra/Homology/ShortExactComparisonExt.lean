/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.ShortExactComparisonCochain
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# The Ext connecting-class comparison

For a short exact sequence `A → B → C`, a map `B → K⁰` whose differential descends
to a closed map `C → K¹` compares the connecting class with that degree-one
cocycle. Cancelling the actual mapping-cone quasi-isomorphism in the cochain
comparison proves the identity, including its minus sign.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace CategoryTheory.ShortComplex

universe w w' v u

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  (K : CochainComplex C ℤ)

/-- Cancelling the cone quasi-isomorphism turns the explicit cochain comparison into
the connecting-map identity for the short exact sequence. -/
theorem comparisonTriangle_derived [HasDerivedCategory.{w'} C] (hS : S.ShortExact)
    (b : S.X₂ ⟶ K.X 0) (c : S.X₃ ⟶ K.X 1)
    (hbc : b ≫ K.d 0 1 = S.g ≫ c) (hc : c ≫ K.d 1 2 = 0) :
    DerivedCategory.triangleOfSESδ
        (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) ≫
      (DerivedCategory.Q.map (S.comparisonKernelMap K b c hbc))⟦(1 : ℤ)⟧' =
    -DerivedCategory.Q.map
        (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk c (show 0 + 1 = 1 from rfl) 2 rfl hc)) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K := by
  have : _root_.QuasiIso
      (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor C 0))) :=
    mappingCone.quasiIso_descShortComplex
    (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0))
  apply (cancel_epi (DerivedCategory.Q.map
    (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor C 0))))).mp
  rw [← Category.assoc, DerivedCategory.descShortComplex_triangleOfSESδ]
  rw [Category.assoc, ← Functor.commShiftIso_hom_naturality]
  rw [← Category.assoc, ← Functor.map_comp, S.comparisonCone_derived K b c hbc hc]
  simp only [Functor.map_comp, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
  rfl

/-- The actual Ext class, viewed in the derived category and followed by the kernel
comparison, is the negative of the degree-one comparison cocycle. -/
theorem comparisonExt_hom [HasExt.{w} C] [HasDerivedCategory.{w'} C]
    (hS : S.ShortExact) (b : S.X₂ ⟶ K.X 0) (c : S.X₃ ⟶ K.X 1)
    (hbc : b ≫ K.d 0 1 = S.g ≫ c) (hc : c ≫ K.d 1 2 = 0) :
    hS.extClass.hom ≫
      (DerivedCategory.Q.map (S.comparisonKernelMap K b c hbc))⟦(1 : ℤ)⟧' =
    -DerivedCategory.Q.map
        (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk c (show 0 + 1 = 1 from rfl) 2 rfl hc)) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K := by
  rw [ShortExact.extClass_hom]
  simpa [ShortExact.singleδ, DerivedCategory.singleFunctorsPostcompQIso_hom_hom,
    DerivedCategory.singleFunctorsPostcompQIso_inv_hom, CochainComplex.singleFunctors,
    SingleFunctors.postcomp]
    using S.comparisonTriangle_derived K hS b c hbc hc

open Localization

local notation "W" => HomologicalComplex.quasiIso C (ComplexShape.up ℤ)

/-- The connecting-class comparison in the small-localization model itself. This
form can be used for hypercohomology without choosing an identification with derived
category morphisms; the minus sign is retained in the representative cocycle. -/
theorem comparisonExt [HasExt.{w} C]
    [HasSmallLocalizedShiftedHom.{w} W ℤ ((CochainComplex.singleFunctor C 0).obj S.X₁) K]
    [HasSmallLocalizedShiftedHom.{w} W ℤ ((CochainComplex.singleFunctor C 0).obj S.X₃) K]
    [HasSmallLocalizedShiftedHom.{w} W ℤ K K]
    (hS : S.ShortExact) (b : S.X₂ ⟶ K.X 0) (c : S.X₃ ⟶ K.X 1)
    (hbc : b ≫ K.d 0 1 = S.g ≫ c) (hc : c ≫ K.d 1 2 = 0) :
    SmallShiftedHom.comp hS.extClass
      (SmallShiftedHom.mk₀ W 0 rfl (S.comparisonKernelMap K b c hbc))
        (show 0 + 1 = 1 from rfl) =
      SmallShiftedHom.mk W
        (-Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk c (show 0 + 1 = 1 from rfl) 2 rfl hc)) := by
  let := HasDerivedCategory.standard C
  apply (SmallShiftedHom.equiv W DerivedCategory.Q).injective
  rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, ShiftedHom.comp_mk₀,
    SmallShiftedHom.equiv_mk]
  simp only [ShiftedHom.map, Functor.map_neg, Preadditive.neg_comp]
  exact S.comparisonExt_hom K hS b c hbc hc

end CategoryTheory.ShortComplex
