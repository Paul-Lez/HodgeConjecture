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

open Point

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

instance holomorphicDeRhamComplexInt_isStrictlyGE_zero :
    (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
  unfold holomorphicDeRhamComplexInt
  infer_instance

/-- The degree-zero term of the actual de Rham complex is the holomorphic-function sheaf. -/
def deRhamDegreeZeroIsoFunctions :
    (holomorphicDeRhamComplexInt X).X 0 ≅ holomorphicAdditiveFunctionSheaf X (dim X.left) :=
  (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl ≪≫
    (asIso (holomorphicFunctionToZeroFormSheaf X (dim X.left))).symm

/-- Holomorphic functions in integer cochain degree zero. -/
def holomorphicFunctionComplexInt : CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
    (holomorphicAdditiveFunctionSheaf X (dim X.left))

/-- The actual degree-zero projection, with holomorphic functions as target. -/
def deRhamToHolomorphicFunctions :
    holomorphicDeRhamComplexInt X ⟶ holomorphicFunctionComplexInt X :=
  (holomorphicDeRhamComplexInt X).toDegreeZero ≫
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
      (deRhamDegreeZeroIsoFunctions X).hom

@[reassoc (attr := simp)]
theorem hodgeFilteredDeRhamInclusion_comp_functions :
    hodgeFilteredDeRhamInclusion X 1 ≫ deRhamToHolomorphicFunctions X = 0 := by
  unfold deRhamToHolomorphicFunctions hodgeFilteredDeRhamInclusion
  rw [← Category.assoc, CochainComplex.stupidTruncInclusion_comp_toDegreeZero, zero_comp]

/-- The first Hodge filtration sequence on the actual analytic variety. -/
def firstHodgeFiltrationSequence : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ) :=
  ShortComplex.mk (hodgeFilteredDeRhamInclusion X 1) (deRhamToHolomorphicFunctions X)
    (hodgeFilteredDeRhamInclusion_comp_functions X)

/-- The first Hodge filtration sequence is short exact, including its actual function target. -/
theorem firstHodgeFiltrationSequence_shortExact :
    (firstHodgeFiltrationSequence X).ShortExact := by
  let e := (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).mapIso
    (deRhamDegreeZeroIsoFunctions X)
  apply ShortComplex.shortExact_of_iso
    (S₁ := (holomorphicDeRhamComplexInt X).firstStupidTruncationSequence)
    (ShortComplex.isoMk
      (S₁ := (holomorphicDeRhamComplexInt X).firstStupidTruncationSequence)
      (S₂ := firstHodgeFiltrationSequence X) (Iso.refl _) (Iso.refl _) e (by
        simp [firstHodgeFiltrationSequence, CochainComplex.firstStupidTruncationSequence,
          hodgeFilteredDeRhamInclusion]) (by
      simp [firstHodgeFiltrationSequence, deRhamToHolomorphicFunctions,
        CochainComplex.firstStupidTruncationSequence, e]))
  exact (holomorphicDeRhamComplexInt X).firstStupidTruncationSequence_shortExact

/-- Holomorphic-function cohomology, using the same actual hypercohomology construction. -/
abbrev HolomorphicFunctionCohomology (n : ℤ) :=
  Hypercohomology X (holomorphicFunctionComplexInt X) n

/-- The obstruction to a de Rham class belonging to the first Hodge filtration. -/
def firstHodgeObstruction (n : ℤ) :
    DeRhamHypercohomology X n →+ HolomorphicFunctionCohomology X n :=
  hypercohomologyMap X (deRhamToHolomorphicFunctions X) n

/-- Membership in the first filtration is exactly vanishing of the actual holomorphic-function
cohomology obstruction. -/
theorem mem_firstHodgeFiltration_iff (n : ℤ) (α : DeRhamHypercohomology X n) :
    α ∈ hodgeFiltration X 1 n ↔ firstHodgeObstruction X n α = 0 :=
  hypercohomologyMap_exact X (firstHodgeFiltrationSequence X)
    (firstHodgeFiltrationSequence_shortExact X) n α

/-- A rational degree-two class is Hodge exactly when its holomorphic-function obstruction
vanishes. No purity or Hodge-decomposition hypothesis is used. -/
theorem isHodgeClass_one_iff (α : FieldCohomology ℚ X 2) :
    IsHodgeClass ℚ X 1 α ↔
      firstHodgeObstruction X 2 (fieldToDeRhamCohomology ℚ X 2 α) = 0 :=
  mem_firstHodgeFiltration_iff X 2 _

end AlgebraicGeometry.ComplexPoint
