import Other.AlgebraicGeometry.DerivedGlobalHypercohomologyComparison
import Other.AlgebraicGeometry.FilteredDerivedSupport

@[expose] noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

theorem testFilteredPlusObject_eq_zeroBound (p : ℕ) :
    hodgeFilteredDeRhamPlusObject X (p : ℤ) =
      letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE (p : ℤ) := by
        unfold hodgeFilteredDeRhamComplex
        infer_instance
      letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE 0 :=
        (hodgeFilteredDeRhamComplex X (p : ℤ)).isStrictlyGE_of_ge
          0 (p : ℤ) (by omega)
      TopCat.Sheaf.supportCoefficientPlus
        (TopCat.of (ComplexPoint X))
          (hodgeFilteredDeRhamComplex X (p : ℤ)) 0 := by
  rfl

theorem testDeRhamPlusObject_eq_zeroBound :
    holomorphicDeRhamPlusObject X =
      letI : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
        unfold holomorphicDeRhamComplexInt
        infer_instance
      TopCat.Sheaf.supportCoefficientPlus
        (TopCat.of (ComplexPoint X)) (holomorphicDeRhamComplexInt X) 0 := by
  rfl

def testDerivedGlobalFilteredDeRhamAddEquivHypercohomology
    (p : ℕ) (n : ℤ) :
    DerivedGlobalFilteredDeRhamHypercohomology X (p : ℤ) n ≃+
      FilteredDeRhamHypercohomology X (p : ℤ) n := by
  letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE (p : ℤ) := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE 0 :=
    (hodgeFilteredDeRhamComplex X (p : ℤ)).isStrictlyGE_of_ge
      0 (p : ℤ) (by omega)
  exact derivedGlobalSectionsAddEquivHypercohomology X
    (hodgeFilteredDeRhamComplex X (p : ℤ)) n

def testDerivedGlobalDeRhamAddEquivHypercohomology (n : ℤ) :
    DerivedGlobalDeRhamHypercohomology X n ≃+
      DeRhamHypercohomology X n := by
  letI : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
    unfold holomorphicDeRhamComplexInt
    infer_instance
  exact derivedGlobalSectionsAddEquivHypercohomology X
    (holomorphicDeRhamComplexInt X) n

theorem testHodgeFilteredDeRhamPlusInclusion_eq_nonnegativeCoefficientPlusMap
    (p : ℕ) :
    hodgeFilteredDeRhamPlusInclusion X (p : ℤ) =
      letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE (p : ℤ) := by
        unfold hodgeFilteredDeRhamComplex
        infer_instance
      letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE 0 :=
        (hodgeFilteredDeRhamComplex X (p : ℤ)).isStrictlyGE_of_ge
          0 (p : ℤ) (by omega)
      letI : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
        unfold holomorphicDeRhamComplexInt
        infer_instance
      nonnegativeCoefficientPlusMap X
        (hodgeFilteredDeRhamInclusion X (p : ℤ)) := by
  rfl

theorem testDerivedGlobalFilteredToDeRham_naturality
    (p : ℕ) (n : ℤ)
    (a : DerivedGlobalFilteredDeRhamHypercohomology X (p : ℤ) n) :
    testDerivedGlobalDeRhamAddEquivHypercohomology X n
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
          ((TopCat.Sheaf.derivedGlobalSections
            (TopCat.of (ComplexPoint X))).map
              (hodgeFilteredDeRhamPlusInclusion X (p : ℤ))) a) =
      filteredToDeRhamCohomology X (p : ℤ) n
        (testDerivedGlobalFilteredDeRhamAddEquivHypercohomology X p n a) := by
  letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE (p : ℤ) := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE 0 :=
    (hodgeFilteredDeRhamComplex X (p : ℤ)).isStrictlyGE_of_ge
      0 (p : ℤ) (by omega)
  letI : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
    unfold holomorphicDeRhamComplexInt
    infer_instance
  exact derivedGlobalSectionsAddEquivHypercohomology_naturality X
    (hodgeFilteredDeRhamInclusion X (p : ℤ)) n a

theorem testDerivedGlobalFilteredRange_mem_hodgeFiltration
    (p : ℕ) (n : ℤ) {a : DerivedGlobalDeRhamHypercohomology X n}
    (ha : a ∈
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (hodgeFilteredDeRhamPlusInclusion X (p : ℤ)))).hom.range) :
    testDerivedGlobalDeRhamAddEquivHypercohomology X n a ∈
      hodgeFiltration X (p : ℤ) n := by
  obtain ⟨b, rfl⟩ := ha
  refine ⟨testDerivedGlobalFilteredDeRhamAddEquivHypercohomology X p n b, ?_⟩
  exact (testDerivedGlobalFilteredToDeRham_naturality X p n b).symm

end AlgebraicGeometry.ComplexPoint
