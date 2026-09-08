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

public import HodgeConjecture.Other.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import HodgeConjecture.Other.Algebra.DeRham.Complex
public import HodgeConjecture.Other.AlgebraicGeometry.BettiGlobalSectionsAdditivity
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexAnalyticMaps
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexLocalOrientation
public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentMaximalCodimensionPurity
public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentRegularImmersion
public import HodgeConjecture.Other.AlgebraicGeometry.HodgeCodimensionZero
public import HodgeConjecture.Other.AlgebraicGeometry.PrincipalDivisorCycleClass
public import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveSingularCoefficientBaseChange
public import HodgeConjecture.Other.AlgebraicTopology.ChartLocalFundamentalClassInvariance
public import HodgeConjecture.Other.AlgebraicTopology.CompactificationBorelMoore
public import HodgeConjecture.Other.AlgebraicTopology.ComplexDifferentiableLocalClassInvariance
public import HodgeConjecture.Other.AlgebraicTopology.ComplexLinearLocalClassInvariance
public import HodgeConjecture.Other.AlgebraicTopology.FiniteGoodCoverNerveHomology
public import HodgeConjecture.Other.AlgebraicTopology.GlobalFundamentalClass
public import HodgeConjecture.Other.AlgebraicTopology.RelativeHomologyEmpty
public import HodgeConjecture.Other.AlgebraicTopology.RelativeHomotopyInvariance
public import HodgeConjecture.Other.AlgebraicTopology.SingularCapProduct
public import HodgeConjecture.Other.AlgebraicTopology.SingularCohomologyZeroConnectedness
public import HodgeConjecture.Other.AlgebraicTopology.SingularHomologyVanishing
public import HodgeConjecture.Other.AlgebraicTopology.SingularOpenCoverSmallChains
public import HodgeConjecture.Other.AlgebraicTopology.SingularSubdivisionIteration
public import HodgeConjecture.Other.AlgebraicTopology.StandardSimplexSingularComparison
public import HodgeConjecture.Other.CommutativeAlgebra.RegularLocalQuotientKernel

/-!
# Other support material for the Hodge conjecture formalisation

This umbrella imports material not needed in the transitive source closure of
`HodgeConjecture.Statement`. Its endpoint list is the set of roots of that part of the local
import graph.
-/
