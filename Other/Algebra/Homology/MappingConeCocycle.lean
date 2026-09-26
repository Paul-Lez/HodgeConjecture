/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
/-!
# A cochain lift computes a connecting class, with its sign

For a short complex `A → B → D`, a cochain on `B` whose restriction is a cocycle on `A`
and whose differential descends to `D` gives a cocycle on `D`. On the cone of `A → B`,
its class is the positive projection to `A[1]` followed by the given coefficient map.
Mathlib's distinguished cone triangle uses the negative projection, so the resulting
connecting-class formula has a minus sign.

No exactness assumption is needed for the cone identity. Short exactness is used later
when the cone-to-quotient map is inverted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace CochainComplex.mappingCone
variable {C : Type*} [Category* C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ)) (J : CochainComplex C ℤ)
  (a : S.X₁ ⟶ J) (α : Cochain S.X₂ J 0) (b : Cocycle S.X₃ J 1)
  (ha : (Cochain.ofHom S.f).comp α (zero_add 0) = Cochain.ofHom a)
  (hb : δ 0 1 α = (b.precomp S.g).1)

include ha hb in
set_option backward.isDefEq.respectTransparency false in
/-- A lifted cochain represents the positive cone projection on cohomology.
Since the triangle boundary is the negative projection, this fixes the connecting-class sign. -/
theorem cocycleClass_precomp_descShortComplex_eq :
    CohomologyClass.mk (b.precomp (descShortComplex S)) =
      CohomologyClass.mk ((fst S.f).postcomp a) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  apply (mem_coboundaries_iff (n := 1) _ 0 rfl).2
  refine ⟨descCochain S.f (0 : Cochain S.X₁ J (-1)) α (by norm_num), ?_⟩
  rw [δ_descCochain _ _ _ _ 1 rfl, δ_zero, zero_add, Int.negOnePow_one, Units.neg_smul,
    ha, hb]
  simp only [Cochain.comp_neg, Cocycle.coe_sub, Cocycle.postcomp_coe,
    Cocycle.precomp_coe, descShortComplex, ofHom_desc, descCochain, Cochain.comp_zero, zero_add, one_smul]
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain]
  abel
include ha hb in
set_option backward.isDefEq.respectTransparency false in
/-- In the homotopy category, the cocycle obtained by differentiating a lift represents the
negative of the mapping-cone connecting morphism, followed by the coefficient map. -/
theorem quotient_map_descShortComplex_comp_cocycle_eq_neg :
    (HomotopyCategory.quotient C (.up ℤ)).map (descShortComplex S) ≫
        (HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.equivHomShift.symm b) =
      -(HomotopyCategory.quotient C (.up ℤ)).map
        ((triangle S.f).mor₃ ≫ a⟦(1 : ℤ)⟧') := by
  have h := congrArg CohomologyClass.toHom (cocycleClass_precomp_descShortComplex_eq S J a α b ha hb)
  rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Cocycle.equivHomShift_symm_postcomp] at h
  rw [← Functor.map_comp, h, ← Functor.map_neg, ← Preadditive.neg_comp]
  congr 2
  change Cocycle.equivHomShift.symm (fst S.f) =
    -(Cocycle.equivHomShift.symm (-fst S.f))
  rw [map_neg, neg_neg]

end CochainComplex.mappingCone
