import Other.AlgebraicGeometry.LefschetzOneOneProof

/-!
# Proper-GAGA axiom report

This diagnostic report follows the public GAGA-to-Lefschetz spine. The build-enforced whitelist
for the two final theorems lives in `CheckLefschetzOneOneAxioms.lean`.

Run: `lake env lean scripts/gaga_axiom_audit.lean`.
-/

#print axioms AlgebraicGeometry.ComplexPoint.comparisonToCanonical_isLocalIso
#print axioms AlgebraicGeometry.ComplexPoint.holomorphicAnalytificationπ_isAnalytification
#print axioms AlgebraicGeometry.ComplexPoint.faithfullyFlat_stalkMap_holomorphicAnalytificationπ
#print axioms ComplexAnalytic.coherent_algebraizes_of_isAnalytification
#print axioms AlgebraicGeometry.ComplexPoint.analyticCoherentSheavesAlgebraize
#print axioms AlgebraicGeometry.ComplexPoint.analyticLineBundlesAlgebraize

#print axioms AlgebraicGeometry.ComplexPoint.hasAlgebraicModel_of_analyticLineBundlesAlgebraize
#print axioms RationalLefschetzOneOne.of_algebraicModel
#print axioms RationalLefschetzOneOne.of_analyticLineBundlesAlgebraize
#print axioms AlgebraicGeometry.ComplexPoint.rationalSheafCycleClassOnCycles_mem_algebraicCycleClassSpan
#print axioms RationalLefschetzOneOne.to_lefschetzOneOne
#print axioms rationalLefschetzOneOne
#print axioms lefschetzOneOne
