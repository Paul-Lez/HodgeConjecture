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
#print axioms CategoryTheory.NatTrans.rightDerivedFunctorPlusCommShift
#print axioms TopCat.Sheaf.derivedClosedSupportSectionsMap_shift
#print axioms complexDerivedSupportedCohomologySupportMap
#print axioms complexAmbientSheafBorelMooreOrientationIso_naturality
#print axioms complexAmbientSheafBorelMooreHomologyIso_naturality
#print axioms TopCat.Sheaf.derivedClosedSupportSectionsTopIso
#print axioms TopCat.Sheaf.derivedForgetClosedSupport_unit_app
#print axioms complexAmbientSheafBorelMooreToCohomology
#print axioms complexAmbientSheafBorelMooreToCohomology_eq_forgetSupport
#print axioms derivedRationalSupportAddEquiv
#print axioms complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport
#print axioms complexAmbientSheafBorelMooreCycleDegreeToFieldCohomology
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
    "AlgebraicGeometry.ComplexSheafBorelMooreForget",
    "AlgebraicGeometry.ComplexSheafBorelMooreRationalComparison",
    "AlgebraicGeometry.CycleComponentAnalyticImmersion",
    "AlgebraicGeometry.CycleComponentBorelMoore",
    "AlgebraicGeometry.CycleComponentGlobalFundamentalClass",
    "AlgebraicGeometry.CycleComponentLocalGenerator",
    "AlgebraicGeometry.CycleComponentLocalOrientation",
    "AlgebraicGeometry.CycleComponentLocalOrientationCoherence",
    "AlgebraicGeometry.CycleComponentPurity",
    "AlgebraicGeometry.DimensionedSmoothProjective",
    "AlgebraicGeometry.DerivedSupportRationalComparison",
    "AlgebraicGeometry.DerivedSupportRationalConeComparison",
    "AlgebraicGeometry.HypercohomologyGlobalSectionsNaturality",
    "AlgebraicGeometry.PrincipalDivisorCycleClass",
    "AlgebraicGeometry.PrincipalDivisorDegreeReduction",
    "AlgebraicGeometry.PointCycleClass",
    "AlgebraicGeometry.ReducedSmoothStratification",
    "AlgebraicGeometry.SheafBorelMoore",
    "AlgebraicGeometry.SingularCycleClass",
    "AlgebraicGeometry.SingularLocusDimension",
    "AlgebraicGeometry.SmoothStratificationAnalytification",
    "AlgebraicGeometry.SmoothClosedCycleMorphism",
    "AlgebraicGeometry.SmoothClosedCycleClass",
    "AlgebraicGeometry.SmoothClosedCycleClassRationalComparison",
    "AlgebraicGeometry.SmoothClosedSupportedCycleMorphism",
    "AlgebraicGeometry.ClosedImmersionAnalyticLeftInverse",
    "AlgebraicGeometry.ClosedImmersionNormalCoordinates",
    "AlgebraicTopology.SplitDerivativeNormalChart",
    "AlgebraicTopology.ChartLocalFundamentalClass",
    "AlgebraicTopology.CenteredComplexEmbeddingOrientation",
    "AlgebraicTopology.ChartLocalFundamentalClassDifferentiableInvariance",
    "AlgebraicTopology.ChartLocalFundamentalClassGenerator",
    "AlgebraicTopology.ChartLocalFundamentalClassInvariance",
    "AlgebraicTopology.ChartNeighborhoodOrientation",
    "AlgebraicTopology.ClosedEmbeddingSheafification",
    "AlgebraicTopology.ClosedEmbeddingSheafExact",
    "AlgebraicTopology.ClosedEmbeddingDerivedPushforward",
    "AlgebraicTopology.ClosedEmbeddingConstantSectionClass",
    "AlgebraicTopology.DerivedSheafSectionClass",
    "AlgebraicTopology.ClosedSubsetDimensionDrop",
    "AlgebraicTopology.CompactificationBorelMoore",
    "AlgebraicTopology.ComplexDifferentiableLocalClassInvariance",
    "AlgebraicTopology.ComplexLinearLocalClassInvariance",
    "AlgebraicTopology.ComplexOrientation",
    "AlgebraicTopology.ComplexNeighborhoodOrientation",
    "AlgebraicTopology.DerivedSheafSupport",
    "AlgebraicTopology.DerivedSheafSupportLocalization",
    "AlgebraicTopology.DerivedSheafSupportForget",
    "AlgebraicTopology.DerivedSheafSupportNaturality",
    "AlgebraicTopology.DerivedSheafSupportShift",
    "AlgebraicTopology.DerivedSheafSupportTruncation",
    "AlgebraicTopology.SingularChainSheafDerivedPushforward",
    "AlgebraicTopology.DerivedConcentratedOrientation",
    "AlgebraicTopology.EuclideanLocalHomology",
    "AlgebraicTopology.EuclideanLocalHomologyVanishing",
    "AlgebraicTopology.EuclideanNeighborhoodOrientation",
    "AlgebraicTopology.GlobalFundamentalClass",
    "AlgebraicTopology.GraphNormalSlicePurity",
    "AlgebraicTopology.HomologyZeroNaturality",
    "AlgebraicTopology.HomologySheafSection",
    "AlgebraicTopology.LocalFundamentalClass",
    "AlgebraicTopology.LocalFundamentalClassGenerator",
    "AlgebraicTopology.NormalSlicePurity",
    "AlgebraicTopology.NestedSheafSupportLocalization",
    "AlgebraicTopology.OpenSheafRestriction",
    "AlgebraicTopology.OpenInjectiveResolutionComparison",
    "AlgebraicTopology.OpenRestrictionStalk",
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
    "AlgebraicTopology.SingularChainSheafOpenExcision",
    "AlgebraicTopology.SingularChainSheafOpenRestriction",
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
     "HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusShiftNaturality",
     "HodgeConjecture.Mathlib.Algebra.Homology.MapExtend",
     "HodgeConjecture.Mathlib.Algebra.Homology.MapExtendNaturality",
     "HodgeConjecture.Mathlib.Algebra.Homology.HomComplexPostcompNaturality",
     "HodgeConjecture.Mathlib.CategoryTheory.Abelian.KernelCompositionShortExact",
     "HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.MappingCoconeShortExact",
     "HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality",
     "HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusInjectiveModel",
     "HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.ShortExactQuasiIso",
     "HodgeConjecture.Mathlib.Algebra.Homology.HomComplexShiftNaturality",
     "HodgeConjecture.Other.AlgebraicGeometry.ClosedImmersionPointNormalCoordinates",
     "HodgeConjecture.Other.AlgebraicGeometry.ComplexPointCoclassOrientationComparison",
     "HodgeConjecture.Other.AlgebraicGeometry.ComplexSupportedSingularModel",
     "HodgeConjecture.Other.AlgebraicGeometry.DerivedSupportRationalConeForget",
     "HodgeConjecture.Other.AlgebraicGeometry.DerivedSupportRationalForget",
     "HodgeConjecture.Other.AlgebraicGeometry.HolomorphicClosedImmersionCharts",
     "HodgeConjecture.Other.AlgebraicGeometry.HypercohomologyGlobalSectionsShift",
     "HodgeConjecture.Other.AlgebraicGeometry.SheafBorelMoorePointClass",
     "HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedPointPurityNormalization",
     "HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportLocalHomology",
     "HodgeConjecture.Other.AlgebraicTopology.ChartTargetPointClassNormalization",
     "HodgeConjecture.Other.AlgebraicTopology.CohomologySheafStalkVanishing",
     "HodgeConjecture.Other.AlgebraicTopology.CohomologySheafSection",
     "HodgeConjecture.Other.AlgebraicTopology.DerivedClosedSupportTruncation",
     "HodgeConjecture.Other.AlgebraicTopology.FlasqueSheafSupportComparison",
     "HodgeConjecture.Other.AlgebraicTopology.FlattenedSupportLocalHomology",
     "HodgeConjecture.Other.AlgebraicTopology.HolomorphicNormalTransition",
     "HodgeConjecture.Other.AlgebraicTopology.PointSupportedChainSection",
     "HodgeConjecture.Other.AlgebraicTopology.SingularAmbientCapSheaf",
     "HodgeConjecture.Other.AlgebraicTopology.SingularFlasqueSupportModel",
     "HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSingularClosedFiltration",
     "HodgeConjecture.Other.AlgebraicGeometry.ReducedSmoothClosedFiltration",
     "HodgeConjecture.Other.AlgebraicGeometry.ReducedSmoothClosedFiltrationDimension",
     "HodgeConjecture.Other.AlgebraicGeometry.SmoothAffineRelativeDimension",
     "HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportCoclassOverlap",
     "HodgeConjecture.Other.AlgebraicTopology.FlasqueCohomologyLowerVanishing",
     "HodgeConjecture.Other.AlgebraicTopology.FlasqueSupportedSections",
     "HodgeConjecture.Other.AlgebraicTopology.NormalProjectionCoclass",
     "HodgeConjecture.Other.AlgebraicTopology.NormalProjectionOverlap",
     "HodgeConjecture.Other.AlgebraicTopology.NowhereDenseDimensionDrop",
     "HodgeConjecture.Other.AlgebraicTopology.OpenSheafification",
     "HodgeConjecture.Other.AlgebraicTopology.SingularCochainOpenRestriction",
     "HodgeConjecture.Other.AlgebraicTopology.SingularCochainOpenSections",
     "HodgeConjecture.Other.AlgebraicTopology.SingularCochainOpenCone",
     "HodgeConjecture.Other.AlgebraicTopology.FlasqueCokernelPreservation",
     "HodgeConjecture.Other.AlgebraicTopology.LowestFlasqueCohomology",
     "HodgeConjecture.Other.AlgebraicTopology.NestedSheafSupportOnOpen",
     "HodgeConjecture.Other.AlgebraicTopology.FiniteSheafSupportVanishing",
     "HodgeConjecture.Other.AlgebraicTopology.SupportedSectionRestrictionCone",
     "HodgeConjecture.Other.AlgebraicTopology.SupportedSingularSectionCohomology",
     "HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportCohomologySheaf",
     "HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportLowestCohomology",
     "HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality",
     "HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.MappingConeMapNaturality",
     "HodgeConjecture.Other.AlgebraicGeometry.ClosedImmersionSourceOpen",
     "HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSmoothClosedLift",
     "HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSmoothSupportPurity",
     "HodgeConjecture.Other.AlgebraicGeometry.SingularFiltrationLocalSupportVanishing",
     "HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedPointCoclassSectionNormalization",
     "HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportCoclassSection",
     "HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportOpenTransport",
     "HodgeConjecture.Other.AlgebraicTopology.LinearDualHomologyNaturality",
     "HodgeConjecture.Other.AlgebraicTopology.NeighborhoodSupportPairImage",
     "HodgeConjecture.Other.AlgebraicTopology.OpenRestrictedCohomologyVanishing",
     "HodgeConjecture.Other.AlgebraicTopology.OpenRestrictedLowestCohomology",
     "HodgeConjecture.Other.AlgebraicTopology.RelativeCochainConeForgetComparison",
     "HodgeConjecture.Other.AlgebraicTopology.RelativeCochainConeNaturality",
     "HodgeConjecture.Other.AlgebraicTopology.SingularCochainOpenConeNaturality",
     "HodgeConjecture.Other.AlgebraicTopology.SupportRelativeCohomologySheaf",
     "HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSupportExtension",
     "HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSmoothSupportCoclassSection",
     "HodgeConjecture.Other.AlgebraicTopology.SupportRelativeCohomologyOpenTransport",
     "HodgeConjecture.Other.AlgebraicGeometry.HypercohomologyFlasqueNaturality",
     "HodgeConjecture.Other.AlgebraicGeometry.BettiSupportedOrdinaryConeComparison"]
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
