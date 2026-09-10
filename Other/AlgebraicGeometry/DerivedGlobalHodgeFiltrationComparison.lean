/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DerivedGlobalHypercohomologyComparison
public import Other.AlgebraicGeometry.FilteredDerivedSupport

/-!
# Actual derived global sections and the public Hodge filtration

This file specializes the natural comparison between actual bounded-below
derived global sections and the public Ext-valued hypercohomology API to the
filtered and full holomorphic de Rham complexes.  In particular, membership
in the range of the actual derived filtered-to-full map implies membership in
the public `hodgeFiltration`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance derivedGlobalHodgeSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance derivedGlobalHodgeGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- For a natural filtration index, the existing filtered derived object is
definitionally the same coefficient object bundled with lower bound zero. -/
theorem hodgeFilteredDeRhamPlusObject_eq_zeroBound (p : ℕ) :
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

/-- The existing full de Rham derived object is the lower-bound-zero
coefficient object used by the generic comparison. -/
theorem holomorphicDeRhamPlusObject_eq_zeroBound :
    holomorphicDeRhamPlusObject X =
      letI : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
        unfold holomorphicDeRhamComplexInt
        infer_instance
      TopCat.Sheaf.supportCoefficientPlus
        (TopCat.of (ComplexPoint X)) (holomorphicDeRhamComplexInt X) 0 := by
  rfl

/-- Actual derived global sections of the Hodge-filtered de Rham complex agree
additively with the public filtered de Rham hypercohomology group. -/
def derivedGlobalFilteredDeRhamAddEquivHypercohomology
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

/-- Actual derived global sections of the full holomorphic de Rham complex
agree additively with the public de Rham hypercohomology group. -/
def derivedGlobalDeRhamAddEquivHypercohomology (n : ℤ) :
    DerivedGlobalDeRhamHypercohomology X n ≃+
      DeRhamHypercohomology X n := by
  letI : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
    unfold holomorphicDeRhamComplexInt
    infer_instance
  exact derivedGlobalSectionsAddEquivHypercohomology X
    (holomorphicDeRhamComplexInt X) n

/-- At a natural filtration index, the existing bounded-below filtration
inclusion is the generic coefficient morphism used by the comparison. -/
theorem hodgeFilteredDeRhamPlusInclusion_eq_nonnegativeCoefficientPlusMap
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

/-- The actual derived-global filtered-to-full map becomes the public
filtered-to-de Rham map under the two canonical comparisons. -/
theorem derivedGlobalFilteredToDeRham_naturality
    (p : ℕ) (n : ℤ)
    (a : DerivedGlobalFilteredDeRhamHypercohomology X (p : ℤ) n) :
    derivedGlobalDeRhamAddEquivHypercohomology X n
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
          ((TopCat.Sheaf.derivedGlobalSections
            (TopCat.of (ComplexPoint X))).map
              (hodgeFilteredDeRhamPlusInclusion X (p : ℤ))) a) =
      filteredToDeRhamCohomology X (p : ℤ) n
        (derivedGlobalFilteredDeRhamAddEquivHypercohomology X p n a) := by
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

/-- Any class in the range of the actual derived-global `F^p` inclusion maps
to a member of the public Ext-valued Hodge filtration. -/
theorem derivedGlobalFilteredRange_mem_hodgeFiltration
    (p : ℕ) (n : ℤ) {a : DerivedGlobalDeRhamHypercohomology X n}
    (ha : a ∈
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (hodgeFilteredDeRhamPlusInclusion X (p : ℤ)))).hom.range) :
    derivedGlobalDeRhamAddEquivHypercohomology X n a ∈
      hodgeFiltration X (p : ℤ) n := by
  obtain ⟨b, rfl⟩ := ha
  refine ⟨derivedGlobalFilteredDeRhamAddEquivHypercohomology X p n b, ?_⟩
  exact (derivedGlobalFilteredToDeRham_naturality X p n b).symm

end AlgebraicGeometry.ComplexPoint
