/- Run after `lake build HodgeConjecture` with `lake env lean scripts/AuditBorelMoore.lean`. -/
import HodgeConjecture.Other
import Lean.Util.CollectAxioms

open AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular

#print axioms ambientSheafBorelMooreObject
#print axioms AmbientSheafBorelMooreHomology
#print axioms IntrinsicSheafBorelMooreHomology
#print axioms ambientSheafBorelMooreOrientationIso
#print axioms ambientSheafBorelMooreTargetIso
#print axioms derivedHypercohomologyAddEquivOfShiftedTargetIso
#print axioms ambientSheafBorelMooreEquivCohomologyWithSupport
#print axioms borelMoore_cycle_degree
#print axioms ambientSheafBorelMooreCycleDegreeEquiv
#print axioms RationalCycleComponentSheafBorelMooreComparisonInputs.orientationInducedComparisonAddEquiv
#print axioms RationalCycleComponentSheafBorelMooreComparisonInputs.toAuxiliaryBorelMooreComparisonData
#print axioms ComplexOrientedRationalCycleComponentSheafBorelMooreData.alexanderPoincare
#print axioms ComplexOrientedRationalCycleComponentSheafBorelMooreData.supportedFundamentalClass_unique
#print axioms ComplexOrientedRationalBorelMooreCycleClassConstruction.ofSheaf
#print axioms ComplexOrientedRationalBorelMooreCycleClassConstruction.cycleClass
#print axioms existsUnique_cycleComponentBorelMooreFundamentalClass_of_coheight_eq_dimension
#print axioms maximalCodimensionAlexanderDuality_fundamentalClass
#print axioms maximalCodimensionComponentClass_eq_forgetSupport_pointCoclass
#print axioms RationalCycleComponentGlobalFundamentalClassInputs.existsUnique_fundamentalClass
#print axioms RationalCycleComponentBorelMooreData.ofBoundedModelInputs
#print axioms localClassOfChart_localChart_eq
#print axioms manifoldOrientation
#print axioms supportCapCohomologyLinear
#print axioms triadCapCohomologyLinear
#print axioms unionRelativeTriadCapCohomologyLinear
#print axioms triadToUnionRelativeChainMap_quasiIso_of_openCover
#print axioms cohomologyMap_forgetSupport
#print axioms maximalCodimensionPrincipalDivisorClassVanishes_of_coefficientSum
#print axioms AlgebraicGeometry.cycleClassOnAlgebraicCycles
#print axioms AlgebraicGeometry.cycleClassOnAlgebraicCyclesOfComponents
#print axioms AlgebraicGeometry.ChowGroup.cycleClassOfComponents
#print axioms AlgebraicGeometry.ChowGroup.rationalCycleClassOfComponents

-- Audit every declaration (including generated auxiliaries) in the material Borel–Moore tranche.
-- Mathematical hypotheses passed as arguments remain hypotheses; this checks foundational axioms.
set_option maxHeartbeats 0 in
run_cmd do
  let modules : List String := [
    "AlgebraicGeometry.BorelMooreCycleClass",
    "AlgebraicGeometry.ChowCycleClassDescent",
    "AlgebraicGeometry.ComplexLocalOrientation",
    "AlgebraicGeometry.ComplexLocalOrientationCoherence",
    "AlgebraicGeometry.ComplexManifoldOrientation",
    "AlgebraicGeometry.CycleComponentAnalyticImmersion",
    "AlgebraicGeometry.CycleComponentBorelMoore",
    "AlgebraicGeometry.CycleComponentGlobalFundamentalClass",
    "AlgebraicGeometry.CycleComponentLocalGenerator",
    "AlgebraicGeometry.CycleComponentLocalOrientation",
    "AlgebraicGeometry.CycleComponentLocalOrientationCoherence",
    "AlgebraicGeometry.CycleComponentPurity",
    "AlgebraicGeometry.DimensionedSmoothProjective",
    "AlgebraicGeometry.PrincipalDivisorDegreeReduction",
    "AlgebraicGeometry.SheafBorelMoore",
    "AlgebraicTopology.ChartLocalFundamentalClassDifferentiableInvariance",
    "AlgebraicTopology.ChartLocalFundamentalClassGenerator",
    "AlgebraicTopology.CompactificationBorelMoore",
    "AlgebraicTopology.ComplexLinearLocalClassInvariance",
    "AlgebraicTopology.GlobalFundamentalClass",
    "AlgebraicTopology.SingularCapProduct",
    "AlgebraicTopology.SingularCohomologySupportNaturality",
    "AlgebraicTopology.SingularSupportCapProduct",
    "AlgebraicTopology.SingularTriadCapProduct",
    "AlgebraicTopology.SingularTriadExcision",
    "Geometry.Manifold.Orientation",
    "LinearAlgebra.ComplexOrientation"]
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  let mut count : Nat := 0
  let mut found : List Lean.Name := []
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index]!.toString
      if modules.any (fun suffix => moduleName == "HodgeConjecture.Other." ++ suffix) then
        count := count + 1
        for axiomName in ← Lean.collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}"
          unless found.contains axiomName do
            found := axiomName :: found
  if count == 0 then
    throwError "No declarations audited"
  Lean.logInfo m!"Audited {count} declarations across {modules.length} modules; axioms: {found}"
