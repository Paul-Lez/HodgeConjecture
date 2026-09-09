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

variable {X : Scheme} [IsIntegral X] (s : X ⟶ Spec ↧ℂ) [Smooth s]

/-- The sheaf of holomorphic units placed in integer cochain degree one. -/
def holomorphicUnitsComplexInt : CochainComplex (AnalyticAdditiveSheaf s) ℤ :=
  (CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 1).obj
    (holomorphicUnitsSheaf s (dim X))

instance holomorphicUnitsComplexInt_isStrictlyGE :
    (holomorphicUnitsComplexInt s).IsStrictlyGE 1 := by
  unfold holomorphicUnitsComplexInt
  infer_instance

/-- The actual logarithmic derivative, extended to integer-indexed complexes. -/
def holomorphicDlogComplexInt :
    holomorphicUnitsComplexInt s ⟶ holomorphicDeRhamComplexInt s :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (holomorphicUnitsSheaf s (dim X)) 1 1 rfl).inv ≫
      HomologicalComplex.extendMap (holomorphicDlogComplex s (dim X))
        ComplexShape.embeddingUpNat

/-- The constructed logarithmic derivative with values in the first filtered de Rham complex. -/
def holomorphicDlogFilteredComplexInt :
    holomorphicUnitsComplexInt s ⟶ hodgeFilteredDeRhamComplex s 1 :=
  HomologicalComplex.liftStupidTrunc (ComplexShape.embeddingUpIntGE 1)
    (holomorphicDlogComplexInt s)

/-- The filtered logarithmic derivative forgets to the original derivative. -/
@[reassoc (attr := simp)]
theorem holomorphicDlogFilteredComplexInt_comp_inclusion :
    holomorphicDlogFilteredComplexInt s ≫ hodgeFilteredDeRhamInclusion s 1 =
      holomorphicDlogComplexInt s :=
  HomologicalComplex.liftStupidTrunc_inclusion _ _

/-- The filtered logarithmic class map on hypercohomology. Its degree-two domain is the
hypercohomology of holomorphic units placed in degree one. -/
def filteredLogarithmicClass (n : ℤ) :
    Hypercohomology s (holomorphicUnitsComplexInt s) n →+
      FilteredDeRhamHypercohomology s 1 n :=
  hypercohomologyMap s (holomorphicDlogFilteredComplexInt s) n

/-- The logarithmic class in the full holomorphic de Rham hypercohomology. -/
def logarithmicClass (n : ℤ) :
    Hypercohomology s (holomorphicUnitsComplexInt s) n →+ DeRhamHypercohomology s n :=
  hypercohomologyMap s (holomorphicDlogComplexInt s) n

/-- The constructed filtered logarithmic class lifts its full de Rham class. -/
@[simp]
theorem filteredToDeRhamCohomology_filteredLogarithmicClass (n : ℤ)
    (α : Hypercohomology s (holomorphicUnitsComplexInt s) n) :
    filteredToDeRhamCohomology s 1 n (filteredLogarithmicClass s n α) =
      logarithmicClass s n α := by
  unfold filteredToDeRhamCohomology filteredLogarithmicClass logarithmicClass
  rw [← hypercohomologyMap_comp_apply,
    holomorphicDlogFilteredComplexInt_comp_inclusion]

/-- Every logarithmic class belongs to the actual first Hodge filtration. -/
theorem logarithmicClass_mem_hodgeFiltration (n : ℤ)
    (α : Hypercohomology s (holomorphicUnitsComplexInt s) n) :
    logarithmicClass s n α ∈ hodgeFiltration s 1 n :=
  ⟨filteredLogarithmicClass s n α,
    filteredToDeRhamCohomology_filteredLogarithmicClass s n α⟩

end AlgebraicGeometry.ComplexPoint
