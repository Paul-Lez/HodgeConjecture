/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The cochain identity underlying a short exact comparison

For a short complex `A → B → C` and compatible maps `B → K⁰`, `C → K¹`, an explicit
degree-zero cochain on the mapping cone compares the boundary followed by `A → K⁰`
with the displayed map `C → K¹`. This fixes the sign in the exponential/de Rham
comparison at the cochain level.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C)
  (K : CochainComplex C ℤ)

/-- The explicit cone cochain built from the degree-zero comparison map. -/
def comparisonConeCochain (b : S.X₂ ⟶ K.X 0) :
    Cochain (mappingCone (S.map (CochainComplex.singleFunctor C 0)).f) K 0 :=
  mappingCone.descCochain (S.map (CochainComplex.singleFunctor C 0)).f
    (0 : Cochain ((CochainComplex.singleFunctor C 0).obj S.X₁) K (-1))
    (Cochain.fromSingleMk b (show 0 + 0 = 0 from rfl)) (show -1 + 1 = 0 from rfl)

/-- The derivative of the explicit cochain is precisely the difference of the two boundary
comparisons. No chosen comparison in a derived category is used as an assumption. -/
theorem comparisonConeCochain_differential (b : S.X₂ ⟶ K.X 0) (c : S.X₃ ⟶ K.X 1)
    (hbc : b ≫ K.d 0 1 = S.g ≫ c) :
    δ 0 1 (S.comparisonConeCochain K b) =
      -((mappingCone.fst (S.map (CochainComplex.singleFunctor C 0)).f).1.comp
        (Cochain.fromSingleMk (S.f ≫ b) (show 0 + 0 = 0 from rfl))
          (show 1 + 0 = 1 from rfl)) +
      (Cochain.ofHom (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor C 0)))).comp
        (Cochain.fromSingleMk c (show 0 + 1 = 1 from rfl)) (show 0 + 1 = 1 from rfl) := by
  have hb : (Cochain.ofHom (S.map (CochainComplex.singleFunctor C 0)).f).comp
      (Cochain.fromSingleMk b (show 0 + 0 = 0 from rfl)) (show 0 + 0 = 0 from rfl) =
        Cochain.fromSingleMk (S.f ≫ b) (show 0 + 0 = 0 from rfl) :=
    (Cochain.fromSingleMk_precomp S.f b (show 0 + 0 = 0 from rfl)).symm
  have hc : δ 0 1 (Cochain.fromSingleMk b (show 0 + 0 = 0 from rfl)) =
      (Cochain.ofHom (S.map (CochainComplex.singleFunctor C 0)).g).comp
        (Cochain.fromSingleMk c (show 0 + 1 = 1 from rfl)) (show 0 + 1 = 1 from rfl) := by
    rw [Cochain.δ_fromSingleMk _ _ 1 1 (show 0 + 1 = 1 from rfl), hbc,
      Cochain.fromSingleMk_precomp]
    rfl
  rw [comparisonConeCochain, mappingCone.δ_descCochain _ _ _ _ 1 rfl]
  simp only [δ_zero, zero_add, Int.negOnePow_one, Units.neg_smul, one_smul, hb,
    Cochain.comp_neg, hc]
  congr 1
  simp only [mappingCone.descShortComplex, mappingCone.ofHom_desc, mappingCone.descCochain,
    Cochain.comp_zero, zero_add, Cochain.comp_assoc_of_second_is_zero_cochain]

/-- The kernel term maps to the comparison complex in degree zero. -/
def comparisonKernelMap (b : S.X₂ ⟶ K.X 0) (c : S.X₃ ⟶ K.X 1)
    (hbc : b ≫ K.d 0 1 = S.g ≫ c) : (CochainComplex.singleFunctor C 0).obj S.X₁ ⟶ K :=
  (Cocycle.fromSingleMk (S.f ≫ b) (show 0 + 0 = 0 from rfl) 1 rfl (by
    rw [Category.assoc, hbc, ← Category.assoc, S.zero, zero_comp])).homOf

/-- The two compared cocycles represent the same class in the actual complex of morphisms.
The witness is the explicit cone cochain, so the equality also holds in the homotopy category. -/
theorem comparisonConeCohomologyClass (b : S.X₂ ⟶ K.X 0) (c : S.X₃ ⟶ K.X 1)
    (hbc : b ≫ K.d 0 1 = S.g ≫ c) (hc : c ≫ K.d 1 2 = 0) :
    CohomologyClass.mk
      ((mappingCone.fst (S.map (CochainComplex.singleFunctor C 0)).f).postcomp
        (S.comparisonKernelMap K b c hbc)) =
    CohomologyClass.mk
      ((Cocycle.fromSingleMk c (show 0 + 1 = 1 from rfl) 2 rfl hc).precomp
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor C 0)))) := by
  symm
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨0, rfl, S.comparisonConeCochain K b, ?_⟩
  simp only [Cocycle.coe_sub, Cocycle.precomp_coe, Cocycle.postcomp_coe,
    comparisonKernelMap, Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.fromSingleMk_coe]
  rw [S.comparisonConeCochain_differential K b c hbc]
  abel

/-- In the derived category, the mapping-cone boundary gives the negative of the displayed
degree-one cocycle. The sign is forced by the library's triangle convention `-fst`. -/
theorem comparisonCone_derived [HasDerivedCategory C]
    (b : S.X₂ ⟶ K.X 0) (c : S.X₃ ⟶ K.X 1)
    (hbc : b ≫ K.d 0 1 = S.g ≫ c) (hc : c ≫ K.d 1 2 = 0) :
    DerivedCategory.Q.map
      ((mappingCone.triangle (S.map (CochainComplex.singleFunctor C 0)).f).mor₃ ≫
        (S.comparisonKernelMap K b c hbc)⟦(1 : ℤ)⟧') =
      -DerivedCategory.Q.map
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor C 0)) ≫
          Cocycle.equivHomShift.symm
            (Cocycle.fromSingleMk c (show 0 + 1 = 1 from rfl) 2 rfl hc)) := by
  have hclass := S.comparisonConeCohomologyClass K b c hbc hc
  have hhom := congrArg CohomologyClass.toHom hclass
  have h := DerivedCategory.Q_map_eq_of_homotopy C
    (HomotopyCategory.homotopyOfEq _ _ hhom)
  let φ : (CochainComplex.singleFunctor C 0).obj S.X₁ ⟶
      (CochainComplex.singleFunctor C 0).obj S.X₂ := (CochainComplex.singleFunctor C 0).map S.f
  let q : mappingCone φ ⟶ (CochainComplex.singleFunctor C 0).obj S.X₃ :=
    mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor C 0))
  change DerivedCategory.Q.map (Cocycle.equivHomShift.symm
    ((mappingCone.fst φ).postcomp (S.comparisonKernelMap K b c hbc))) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm
        ((Cocycle.fromSingleMk c (show 0 + 1 = 1 from rfl) 2 rfl hc).precomp q)) at h
  change DerivedCategory.Q.map
    (Cocycle.equivHomShift.symm (-(mappingCone.fst φ)) ≫
      (S.comparisonKernelMap K b c hbc)⟦(1 : ℤ)⟧') =
        -DerivedCategory.Q.map (q ≫ Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk c (show 0 + 1 = 1 from rfl) 2 rfl hc))
  simp only [Cocycle.equivHomShift_symm_postcomp, Cocycle.equivHomShift_symm_precomp] at h
  rw [map_neg]
  exact (congrArg DerivedCategory.Q.map (Preadditive.neg_comp _ _)).trans
    ((Functor.map_neg _).trans (congrArg Neg.neg h))

end CategoryTheory.ShortComplex
