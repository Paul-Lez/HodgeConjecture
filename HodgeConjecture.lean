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
module  -- shake: keep-all --deprecated_module: ignore

public import HodgeConjecture.Definitions.Algebra.DeRham.Basic
public import HodgeConjecture.Definitions.AlgebraicGeometry.AlgebraicCycleSupport
public import HodgeConjecture.Definitions.AlgebraicGeometry.AnalyticDifferentialForms
public import HodgeConjecture.Definitions.AlgebraicGeometry.ChowGroup
public import HodgeConjecture.Definitions.AlgebraicGeometry.CohomologyWithSupport
public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexAnalyticSheaf
public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleClass
public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import HodgeConjecture.Definitions.AlgebraicGeometry.HolomorphicDeRham
public import HodgeConjecture.Definitions.AlgebraicGeometry.Points
public import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
public import HodgeConjecture.Definitions.LinearAlgebra.HodgeStructure
public import HodgeConjecture.Definitions.Topology.Dimension
public import HodgeConjecture.Lemmas.Algebra.Homology.ShiftedExact
public import HodgeConjecture.Lemmas.Algebra.Homology.StupidTruncation
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAffineScheme
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAffineSpace
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexEtale
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexLocalization
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexOpen
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexStandardEtale
public import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentDimension
public import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicPoincare
public import HodgeConjecture.Lemmas.AlgebraicGeometry.OrderOfVanishing
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothDimensionFormula
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothEquidimensional
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothLocus
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension
public import HodgeConjecture.Lemmas.Analysis.Calculus.DifferentialForm.Poincare
public import HodgeConjecture.Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import HodgeConjecture.Mathlib.RingTheory.Smooth.StandardSmooth
public import HodgeConjecture.Mathlib.Topology.Algebra.IsOpenUnits
public import HodgeConjecture.Mathlib.Topology.KrullDimension
public import HodgeConjecture.Statement
