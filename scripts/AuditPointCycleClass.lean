/- Run with `lake env lean scripts/AuditPointCycleClass.lean` after building PointCycleClass. -/
import HodgeConjecture.Other.AlgebraicGeometry.PointCycleClass
import Lean.Util.CollectAxioms

open AlgebraicGeometry.ComplexPoint

#print axioms maximalCodimensionComplexOrientedComponentClassData_ordinary
#print axioms pointCycleClassOnCycles
#print axioms pointCycleClassOnCycles_single
#print axioms pointCycleClassOnCycles_single_closedPoint
#print axioms pointCycleClassOnCycles_single_eq_forgetSupport_pointCoclass
#print axioms pointCycleClassOnCycles_sum_single
#print axioms pointCycleClassOnCycles_apply
#print axioms pointCycleClassRationalExtensionBilinear
#print axioms rationalPointCycleClassOnCycles
#print axioms rationalPointCycleClassOnCycles_tmul
#print axioms rationalPointCycleClassOnCycles_tmul_single
#print axioms rationalPointCycleClassOnCycles_sum_tmul_single

-- Inspect every declaration introduced by this module, including generated auxiliaries.
-- This is an axiom audit, not a replacement for inspecting mathematical parameters.
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let moduleName := `HodgeConjecture.Other.AlgebraicGeometry.PointCycleClass
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    if env.header.moduleNames[moduleIdx]! != moduleName then continue
    count := count + 1
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name} depends on unexpected axiom {axiomName}"
  if count = 0 then
    throwError "No PointCycleClass declarations were audited"
  Lean.logInfo m!"Audited {count} PointCycleClass declarations; only foundational axioms occur."
