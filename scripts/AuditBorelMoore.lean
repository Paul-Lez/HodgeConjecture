/- Run after `lake build HodgeConjecture` with `lake env lean scripts/AuditBorelMoore.lean`. -/
import HodgeConjecture
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
#print axioms AlgebraicTopology.Simplicial.coboundary_cochainMap
#print axioms AlgebraicTopology.Simplicial.cocycleMap
#print axioms AlgebraicTopology.Simplicial.capHomologyMap_naturality
#print axioms CategoryTheory.ShortComplex.moduleCatHomologyClass_naturality
#print axioms CategoryTheory.ShortComplex.linearDualMap
#print axioms CategoryTheory.ShortComplex.linearDualHomologyEquiv_naturality
#print axioms AlgebraicTopology.Simplicial.cochainCohomologyMap
#print axioms AlgebraicTopology.Simplicial.capCohomologyLinear_naturality
#print axioms AlgebraicTopology.Singular.cocycleMap
#print axioms AlgebraicTopology.Singular.capHomologyMap_naturality
#print axioms AlgebraicTopology.Singular.cochainCohomologyEquiv_naturality
#print axioms AlgebraicTopology.Singular.capCohomologyLinear_naturality
#print axioms standardCapCohomologyLinear
#print axioms standardCapCohomologyLinear_naturality
#print axioms relativeCochainMap
#print axioms relativeCoboundary_relativeCochainMap
#print axioms relativeCocycleMap
#print axioms relativeCochainToAbsolute_relativeCochainMap
#print axioms relativeCapHom_naturality
#print axioms relativeCapHomologyMap_naturality
#print axioms pointCycleClassOnCycles
#print axioms pointCycleClassOnCycles_single_eq_forgetSupport_pointCoclass
#print axioms pointCycleClassOnCycles_sum_single
#print axioms rationalPointCycleClassOnCycles
#print axioms rationalPointCycleClassOnCycles_sum_tmul_single
#print axioms singularMayerVietorisShortComplex_shortExact
#print axioms singularMayerVietorisBoundary
#print axioms singularMayerVietoris_exact_sum
#print axioms singularMayerVietoris_exact_ambient
#print axioms singularMayerVietoris_exact_overlap
#print axioms singularMayerVietoris_overlap_map_eq
#print axioms singularMayerVietoris_sum_map_eq
#print axioms singularChainPresheafComplex
#print axioms singularChainSheafComplex
#print axioms singularChainSheafificationStalkIso
#print axioms singularChainSheafCochainComplex
#print axioms singularChainSheafCochainComplex_d
#print axioms TopCat.Sheaf.sheafSectionsWithClosedSupport
#print axioms TopCat.Sheaf.sheafSectionsSupportedOutsideOnOpenIso
#print axioms TopCat.Sheaf.derivedSheafSectionsWithClosedSupport
#print axioms TopCat.Sheaf.derivedSheafSectionsWithClosedSupport_isRightDerivedFunctor
#print axioms TopCat.Sheaf.derivedClosedSupportSections
#print axioms TopCat.Sheaf.derivedClosedSupportSections_isRightDerivedFunctor
#print axioms CategoryTheory.Functor.rightDerivedFunctorPlusCommShift
#print axioms CategoryTheory.Functor.rightDerivedFunctorPlusUnitCommShift
#print axioms TopCat.Sheaf.derivedClosedSupportSectionsShiftIso
#print axioms TopCat.Sheaf.derivedSheafSectionsWithClosedSupportShiftIso
#print axioms SSet.homology₀ε_naturality
#print axioms TopCat.singularHomologyMap_zero_isIso
#print axioms standardLocalHomology_isZero_of_ne
#print axioms localHomology_isZero_of_ne
#print axioms singularChainHomologySheaf_isZero_of_ne
#print axioms singularChainSheafStalkIso
#print axioms singularChainHomologySheafStalkIso
#print axioms DerivedCategory.concentratedOrientationIso_homology
#print axioms singularChainSheafDerivedOrientationIso
#print axioms singularChainSheafPlusObject
#print axioms complexChainSheafCohomology_concentrated
#print axioms complexChainSheafPlusObject
#print axioms complexAmbientSheafBorelMooreObject
#print axioms ComplexAmbientSheafBorelMooreHomology
#print axioms complexChainSheafPlusIsoOfOrientation
#print axioms complexAmbientSheafBorelMooreHomologyIsoOfOrientation
#print axioms complexAmbientSheafBorelMooreCycleDegreeIsoOfOrientation
#print axioms complexOrientationHomologySheafIso
#print axioms complexOrientationHomologySheafIso_stalk_one
#print axioms complexChainSheafDerivedSingleOrientationIso_homology
#print axioms complexChainSheafPlusOrientationIso
#print axioms complexAmbientSheafBorelMooreOrientationIso
#print axioms complexAmbientSheafBorelMooreHomologyIso
#print axioms complexAmbientSheafBorelMooreCycleDegreeIso
#print axioms complexAmbientSheafBorelMooreSupportMap
#print axioms complexAmbientSheafBorelMooreSupportMap_comp
#print axioms complexAmbientSheafBorelMooreForgetSupport
#print axioms maximalCodimensionPrincipalDivisorClassVanishes_of_coefficientSum
#print axioms AlgebraicGeometry.cycleClassOnAlgebraicCycles
#print axioms AlgebraicGeometry.cycleClassOnAlgebraicCyclesOfComponents
#print axioms AlgebraicGeometry.ChowGroup.cycleClassOfComponents
#print axioms AlgebraicGeometry.ChowGroup.rationalCycleClassOfComponents

-- Audit every declaration (including generated auxiliaries) in the changed auxiliary modules.
-- Mathematical hypotheses passed as arguments remain hypotheses; this checks foundational axioms.
set_option maxHeartbeats 0 in
run_cmd do
  let otherModules : List String := [
    "Algebra.Homology.LinearDualNaturality",
    "AlgebraicGeometry.BorelMooreCycleClass",
    "AlgebraicGeometry.ChowCycleClassDescent",
    "AlgebraicGeometry.CompactlySupportedCohomology",
    "AlgebraicGeometry.ComplexLocalOrientation",
    "AlgebraicGeometry.ComplexLocalOrientationCoherence",
    "AlgebraicGeometry.ComplexLocalOrientationNeighborhood",
    "AlgebraicGeometry.ComplexLocalHomologyVanishing",
    "AlgebraicGeometry.ComplexManifoldOrientation",
    "AlgebraicGeometry.ComplexOrientationHomologySheaf",
    "AlgebraicGeometry.ComplexSheafBorelMoore",
    "AlgebraicGeometry.CycleComponentAnalyticImmersion",
    "AlgebraicGeometry.CycleComponentBorelMoore",
    "AlgebraicGeometry.CycleComponentGlobalFundamentalClass",
    "AlgebraicGeometry.CycleComponentLocalGenerator",
    "AlgebraicGeometry.CycleComponentLocalOrientation",
    "AlgebraicGeometry.CycleComponentLocalOrientationCoherence",
    "AlgebraicGeometry.CycleComponentPurity",
    "AlgebraicGeometry.DimensionedSmoothProjective",
    "AlgebraicGeometry.PrincipalDivisorCycleClass",
    "AlgebraicGeometry.PrincipalDivisorDegreeReduction",
    "AlgebraicGeometry.PointCycleClass",
    "AlgebraicGeometry.SheafBorelMoore",
    "AlgebraicGeometry.SingularCycleClass",
    "AlgebraicTopology.ChartLocalFundamentalClass",
    "AlgebraicTopology.CenteredComplexEmbeddingOrientation",
    "AlgebraicTopology.ChartLocalFundamentalClassDifferentiableInvariance",
    "AlgebraicTopology.ChartLocalFundamentalClassGenerator",
    "AlgebraicTopology.ChartLocalFundamentalClassInvariance",
    "AlgebraicTopology.ChartNeighborhoodOrientation",
    "AlgebraicTopology.ClosedEmbeddingSheafification",
    "AlgebraicTopology.CompactificationBorelMoore",
    "AlgebraicTopology.ComplexDifferentiableLocalClassInvariance",
    "AlgebraicTopology.ComplexLinearLocalClassInvariance",
    "AlgebraicTopology.ComplexOrientation",
    "AlgebraicTopology.ComplexNeighborhoodOrientation",
    "AlgebraicTopology.DerivedSheafSupport",
    "AlgebraicTopology.DerivedSheafSupportLocalization",
    "AlgebraicTopology.DerivedSheafSupportNaturality",
    "AlgebraicTopology.DerivedSheafSupportShift",
    "AlgebraicTopology.DerivedConcentratedOrientation",
    "AlgebraicTopology.EuclideanLocalHomology",
    "AlgebraicTopology.EuclideanLocalHomologyVanishing",
    "AlgebraicTopology.EuclideanNeighborhoodOrientation",
    "AlgebraicTopology.GlobalFundamentalClass",
    "AlgebraicTopology.HomologyZeroNaturality",
    "AlgebraicTopology.HomologySheafSection",
    "AlgebraicTopology.LocalFundamentalClass",
    "AlgebraicTopology.LocalFundamentalClassGenerator",
    "AlgebraicTopology.OpenSheafRestriction",
    "AlgebraicTopology.RelativeHomologyEmpty",
    "AlgebraicTopology.RelativeHomotopyInvariance",
    "AlgebraicTopology.RelativeMayerVietoris",
    "AlgebraicTopology.RelativePairExcision",
    "AlgebraicTopology.SheafCohomologyWithSupport",
    "AlgebraicTopology.SheafMapOfLocallyRepresentableStalks",
    "AlgebraicTopology.SingularCapNaturality",
    "AlgebraicTopology.SingularCapProduct",
    "AlgebraicTopology.SingularChainSheaf",
    "AlgebraicTopology.SingularChainSheafStalk",
    "AlgebraicTopology.SingularChainHomologySheaf",
    "AlgebraicTopology.SingularChainSheafOrientation",
    "AlgebraicTopology.SingularChainSheafPushforward",
    "AlgebraicTopology.SingularChainSheafClosedSupport",
    "AlgebraicTopology.SingularCochainCohomology",
    "AlgebraicTopology.SingularCochainSheaf",
    "AlgebraicTopology.SingularCoefficientBaseChange",
    "AlgebraicTopology.SingularCohomology",
    "AlgebraicTopology.SingularCohomologySupportNaturality",
    "AlgebraicTopology.SingularCohomologyZero",
    "AlgebraicTopology.SingularHomologyVanishing",
    "AlgebraicTopology.SingularMayerVietoris",
    "AlgebraicTopology.SingularSupportCapProduct",
    "AlgebraicTopology.SingularTriadCapProduct",
    "AlgebraicTopology.SingularTriadExcision",
    "AlgebraicTopology.StandardSphereAffineBoundary",
    "Geometry.Manifold.Orientation",
    "LinearAlgebra.ComplexOrientation"]
  let modules := otherModules.map ("HodgeConjecture.Other." ++ ·) ++
    ["HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusShift",
     "HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNaturality",
     "HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.MappingCoconeShortExact"]
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for moduleName in modules do
    unless env.header.moduleNames.any (fun name => name.toString == moduleName) do
      throwError "Audit module not imported: {moduleName}"
  let mut count : Nat := 0
  let mut found : List Lean.Name := []
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index]!.toString
      if modules.contains moduleName then
        count := count + 1
        for axiomName in ← Lean.collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}"
          unless found.contains axiomName do
            found := axiomName :: found
  if count == 0 then
    throwError "No declarations audited"
  Lean.logInfo m!"Audited {count} declarations across {modules.length} modules; axioms: {found}"
