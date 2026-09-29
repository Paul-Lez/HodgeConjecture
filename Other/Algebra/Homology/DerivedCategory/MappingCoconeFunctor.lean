/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingConeMapNaturality

/-! # Additive functors preserve the shifted short-complex lift -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCocone

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical lift into the cone commutes with an additive functor, with its
prescribed shift and cone comparisons. -/
@[reassoc]
lemma map_shiftedLiftShortComplex (F : C ⥤ D) [F.Additive]
    (S : ShortComplex (CochainComplex C ℤ)) :
    (F.mapHomologicalComplex (.up ℤ)).map (shiftedLiftShortComplex S) ≫
      (mappingCone.mapHomologicalComplexIso S.g F).hom =
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app S.X₁ ≫
      shiftedLiftShortComplex (S.map (F.mapHomologicalComplex (.up ℤ))) := by
  ext n
  simp [shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
    mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso,
    mappingCone.mapHomologicalComplexIso, mappingCone.mapHomologicalComplexXIso,
    mappingCone.mapHomologicalComplexXIso']
  simp only [← Functor.map_comp_assoc, mappingCone.inl_v_desc_f_assoc,
    mappingCone.inr_f_desc_f_assoc, HomologicalComplex.comp_f,
    mappingCone.inl_v_descShortComplex_f_assoc, Category.assoc,
    Functor.map_zero, zero_comp, add_zero, neg_zero]
  simp only [mappingCone.inl_v_fst_v, mappingCone.inl_v_snd_v,
    Category.comp_id, comp_zero, Functor.map_zero, zero_comp, add_zero]
  have hz := mappingCone.inl_v_descShortComplex_f
    (S.map (F.mapHomologicalComplex (.up ℤ))) (n + 1) n (by omega)
  simp only [ShortComplex.map_f] at hz
  simp [← Category.assoc, hz]

end CochainComplex.mappingCocone
