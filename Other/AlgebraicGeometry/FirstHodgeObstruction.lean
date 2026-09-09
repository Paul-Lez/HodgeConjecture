/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicZeroForms
public import Other.AlgebraicGeometry.HypercohomologyExact
public import Other.Algebra.Homology.FirstStupidTruncation

/-!
# The first Hodge filtration and holomorphic-function cohomology

The quotient of the actual holomorphic de Rham complex by its first stupid truncation is the
sheaf of holomorphic functions in degree zero. Exactness identifies the first Hodge filtration
with the kernel of the resulting cohomological obstruction map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} [IsIntegral X] (s : X ⟶ Spec ↧ℂ) [Smooth s]

instance holomorphicDeRhamComplexInt_isStrictlyGE_zero :
    (holomorphicDeRhamComplexInt s).IsStrictlyGE 0 := by
  unfold holomorphicDeRhamComplexInt
  infer_instance

/-- The degree-zero term of the actual de Rham complex is the holomorphic-function sheaf. -/
def deRhamDegreeZeroIsoFunctions :
    (holomorphicDeRhamComplexInt s).X 0 ≅ holomorphicAdditiveFunctionSheaf s (dim X) :=
  (holomorphicDeRhamComplex s (dim X)).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl ≪≫
    (asIso (holomorphicFunctionToZeroFormSheaf s (dim X))).symm

/-- Holomorphic functions in integer cochain degree zero. -/
def holomorphicFunctionComplexInt : CochainComplex (AnalyticAdditiveSheaf s) ℤ :=
  (CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).obj
    (holomorphicAdditiveFunctionSheaf s (dim X))

/-- The actual degree-zero projection, with holomorphic functions as target. -/
def deRhamToHolomorphicFunctions :
    holomorphicDeRhamComplexInt s ⟶ holomorphicFunctionComplexInt s :=
  (holomorphicDeRhamComplexInt s).toDegreeZero ≫
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).map
      (deRhamDegreeZeroIsoFunctions s).hom

@[reassoc (attr := simp)]
theorem hodgeFilteredDeRhamInclusion_comp_functions :
    hodgeFilteredDeRhamInclusion s 1 ≫ deRhamToHolomorphicFunctions s = 0 := by
  unfold deRhamToHolomorphicFunctions hodgeFilteredDeRhamInclusion
  rw [← Category.assoc, CochainComplex.stupidTruncInclusion_comp_toDegreeZero, zero_comp]

/-- The first Hodge filtration sequence on the actual analytic variety. -/
def firstHodgeFiltrationSequence : ShortComplex (CochainComplex (AnalyticAdditiveSheaf s) ℤ) :=
  ShortComplex.mk (hodgeFilteredDeRhamInclusion s 1) (deRhamToHolomorphicFunctions s)
    (hodgeFilteredDeRhamInclusion_comp_functions s)

/-- The first Hodge filtration sequence is short exact, including its actual function target. -/
theorem firstHodgeFiltrationSequence_shortExact :
    (firstHodgeFiltrationSequence s).ShortExact := by
  let e := (CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).mapIso
    (deRhamDegreeZeroIsoFunctions s)
  apply ShortComplex.shortExact_of_iso
    (S₁ := (holomorphicDeRhamComplexInt s).firstStupidTruncationSequence)
    (ShortComplex.isoMk
      (S₁ := (holomorphicDeRhamComplexInt s).firstStupidTruncationSequence)
      (S₂ := firstHodgeFiltrationSequence s) (Iso.refl _) (Iso.refl _) e (by
        simp [firstHodgeFiltrationSequence, CochainComplex.firstStupidTruncationSequence,
          hodgeFilteredDeRhamInclusion]) (by
      simp [firstHodgeFiltrationSequence, deRhamToHolomorphicFunctions,
        CochainComplex.firstStupidTruncationSequence, e]))
  exact (holomorphicDeRhamComplexInt s).firstStupidTruncationSequence_shortExact

/-- Holomorphic-function cohomology, using the same actual hypercohomology construction. -/
abbrev HolomorphicFunctionCohomology (n : ℤ) :=
  Hypercohomology s (holomorphicFunctionComplexInt s) n

/-- The obstruction to a de Rham class belonging to the first Hodge filtration. -/
def firstHodgeObstruction (n : ℤ) :
    DeRhamHypercohomology s n →+ HolomorphicFunctionCohomology s n :=
  hypercohomologyMap s (deRhamToHolomorphicFunctions s) n

/-- Membership in the first filtration is exactly vanishing of the actual holomorphic-function
cohomology obstruction. -/
theorem mem_firstHodgeFiltration_iff (n : ℤ) (α : DeRhamHypercohomology s n) :
    α ∈ hodgeFiltration s 1 n ↔ firstHodgeObstruction s n α = 0 :=
  hypercohomologyMap_exact s (firstHodgeFiltrationSequence s)
    (firstHodgeFiltrationSequence_shortExact s) n α

/-- A rational degree-two class is Hodge exactly when its holomorphic-function obstruction
vanishes. No purity or Hodge-decomposition hypothesis is used. -/
theorem isHodgeClass_one_iff (α : FieldCohomology ℚ s 2) :
    IsHodgeClass ℚ s 1 α ↔
      firstHodgeObstruction s 2 (fieldToDeRhamCohomology ℚ s 2 α) = 0 :=
  mem_firstHodgeFiltration_iff s 2 _

end AlgebraicGeometry.ComplexPoint
