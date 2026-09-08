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

public import HodgeConjecture.Definitions.Algebra.DeRham.Basic
public import HodgeConjecture.Definitions.AlgebraicGeometry.AlgebraicCycleSupport
public import HodgeConjecture.Definitions.AlgebraicGeometry.AnalyticDifferentialForms
public import HodgeConjecture.Definitions.AlgebraicGeometry.ChowGroup
public import HodgeConjecture.Definitions.AlgebraicGeometry.CohomologyWithSupport
public import HodgeConjecture.Definitions.AlgebraicGeometry.CompactlySupportedCohomology
public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexAnalyticSheaf
public import HodgeConjecture.Definitions.AlgebraicGeometry.Points
public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleClass
public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import HodgeConjecture.Definitions.AlgebraicGeometry.HolomorphicDeRham
public import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
public import HodgeConjecture.Definitions.AlgebraicTopology.SingularCohomology
public import HodgeConjecture.Definitions.AlgebraicTopology.SheafCohomologyWithSupport
public import HodgeConjecture.Definitions.LinearAlgebra.HodgeStructure

/-!
# Definitions used by the Hodge conjecture statement

This umbrella contains the construction and definition modules in the transitive source closure
of `HodgeConjecture.Statement`. The statement itself imports only its three immediate definition
modules rather than this keep-all umbrella.
-/
