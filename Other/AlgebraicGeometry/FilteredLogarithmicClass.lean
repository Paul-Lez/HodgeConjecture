/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicLogarithmicForms
public import Other.Algebra.Homology.StupidTruncationLift
public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration

/-!
# Filtered logarithmic classes

The actual logarithmic differential is a map from holomorphic units, placed in degree one,
to the holomorphic de Rham complex. Its source is supported in degree one, so this map factors
through the first Hodge filtration. Taking hypercohomology gives logarithmic classes together
with constructed filtered lifts. This does not identify them with the topological cycle classes;
that comparison requires the exponential sequence and its local orientation normalization.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The sheaf of holomorphic units placed in integer cochain degree one. -/
def holomorphicUnitsComplexInt : CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 1).obj
    (holomorphicUnitsSheaf X (dim X.left))

instance holomorphicUnitsComplexInt_isStrictlyGE :
    (holomorphicUnitsComplexInt X).IsStrictlyGE 1 := by
  unfold holomorphicUnitsComplexInt
  infer_instance

/-- The actual logarithmic derivative, extended to integer-indexed complexes. -/
def holomorphicDlogComplexInt :
    holomorphicUnitsComplexInt X ⟶ holomorphicDeRhamComplexInt X :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (holomorphicUnitsSheaf X (dim X.left)) 1 1 rfl).inv ≫
      HomologicalComplex.extendMap (holomorphicDlogComplex X (dim X.left))
        ComplexShape.embeddingUpNat

/-- The constructed logarithmic derivative with values in the first filtered de Rham complex. -/
def holomorphicDlogFilteredComplexInt :
    holomorphicUnitsComplexInt X ⟶ hodgeFilteredDeRhamComplex X 1 :=
  HomologicalComplex.liftStupidTrunc (ComplexShape.embeddingUpIntGE 1)
    (holomorphicDlogComplexInt X)

/-- The filtered logarithmic derivative forgets to the original derivative. -/
@[reassoc (attr := simp)]
theorem holomorphicDlogFilteredComplexInt_comp_inclusion :
    holomorphicDlogFilteredComplexInt X ≫ hodgeFilteredDeRhamInclusion X 1 =
      holomorphicDlogComplexInt X :=
  HomologicalComplex.liftStupidTrunc_inclusion _ _

/-- The filtered logarithmic class map on hypercohomology. Its degree-two domain is the
hypercohomology of holomorphic units placed in degree one. -/
def filteredLogarithmicClass (n : ℤ) :
    Hypercohomology X (holomorphicUnitsComplexInt X) n →+
      FilteredDeRhamHypercohomology X 1 n :=
  hypercohomologyMap X (holomorphicDlogFilteredComplexInt X) n

/-- The logarithmic class in the full holomorphic de Rham hypercohomology. -/
def logarithmicClass (n : ℤ) :
    Hypercohomology X (holomorphicUnitsComplexInt X) n →+ DeRhamHypercohomology X n :=
  hypercohomologyMap X (holomorphicDlogComplexInt X) n

/-- The constructed filtered logarithmic class lifts its full de Rham class. -/
@[simp]
theorem filteredToDeRhamCohomology_filteredLogarithmicClass (n : ℤ)
    (α : Hypercohomology X (holomorphicUnitsComplexInt X) n) :
    filteredToDeRhamCohomology X 1 n (filteredLogarithmicClass X n α) =
      logarithmicClass X n α := by
  unfold filteredToDeRhamCohomology filteredLogarithmicClass logarithmicClass
  rw [← hypercohomologyMap_comp_apply,
    holomorphicDlogFilteredComplexInt_comp_inclusion]

/-- Every logarithmic class belongs to the actual first Hodge filtration. -/
theorem logarithmicClass_mem_hodgeFiltration (n : ℤ)
    (α : Hypercohomology X (holomorphicUnitsComplexInt X) n) :
    logarithmicClass X n α ∈ hodgeFiltration X 1 n :=
  ⟨filteredLogarithmicClass X n α,
    filteredToDeRhamCohomology_filteredLogarithmicClass X n α⟩

end AlgebraicGeometry.ComplexPoint
