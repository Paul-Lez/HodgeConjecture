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

public import HodgeConjecture.Lemmas.Algebra.Homology.ShiftedExact
public import HodgeConjecture.Lemmas.Algebra.Homology.StupidTruncation
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAffineScheme
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAffineSpace
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexEtale
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexLocalization
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexOpen
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexStandardEtale
public import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicPoincare
public import HodgeConjecture.Lemmas.AlgebraicGeometry.OrderOfVanishing
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothLocus
public import HodgeConjecture.Lemmas.Analysis.Calculus.DifferentialForm.Poincare

/-!
# Lemmas supporting the Hodge conjecture statement

These modules provide the theorem and instance infrastructure used by the construction modules
in `HodgeConjecture.Definitions`. Imports between individual definition and lemma modules follow
the dependency DAG; the two umbrella modules are documentation and discovery entry points only.
-/
