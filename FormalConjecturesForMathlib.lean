/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module  -- shake: keep-all

public import FormalConjecturesForMathlib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import FormalConjecturesForMathlib.Algebra.DeRham.Complex
public import FormalConjecturesForMathlib.AlgebraicGeometry.BettiGlobalSectionsAdditivity
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexAnalyticMaps
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexLocalOrientation
public import FormalConjecturesForMathlib.AlgebraicGeometry.BorelMooreCycleClass
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentMaximalCodimensionPurity
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentRegularImmersion
public import FormalConjecturesForMathlib.AlgebraicGeometry.HodgeCodimensionZero
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationIntegralConnected
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveSingularCoefficientBaseChange
public import FormalConjecturesForMathlib.AlgebraicGeometry.PrincipalDivisorCycleClass
public import FormalConjecturesForMathlib.AlgebraicTopology.CompactManifoldFiniteGoodCover
public import FormalConjecturesForMathlib.AlgebraicTopology.ComplexDifferentiableLocalClassInvariance
public import FormalConjecturesForMathlib.AlgebraicTopology.ComplexLinearLocalClassInvariance
public import FormalConjecturesForMathlib.AlgebraicTopology.FiniteGoodCoverNerveHomology
public import FormalConjecturesForMathlib.AlgebraicTopology.GlobalFundamentalClass
public import FormalConjecturesForMathlib.AlgebraicTopology.RelativeHomologyEmpty
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCohomologyZeroConnectedness
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCapProduct
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularOpenCoverSmallChains
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularSubdivisionIteration
public import FormalConjecturesForMathlib.AlgebraicTopology.StandardSimplexSingularComparison
public import FormalConjecturesForMathlib.CommutativeAlgebra.RegularLocalQuotientKernel

/-!
# Support library for the Hodge conjecture formalisation

This umbrella imports every support module extracted for the standalone Hodge conjecture
project. The smaller endpoint list is the set of roots of the local import graph.
-/
