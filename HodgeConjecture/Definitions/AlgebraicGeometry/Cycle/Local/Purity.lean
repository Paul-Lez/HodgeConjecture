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
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.LocalGenerator

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean

/-!
# Local dual classes on cycle components

The local fundamental class obtained from exact coordinates on the smooth locus of a cycle
component is nonzero.  Since it generates local homology, there is a unique local cohomology
class evaluating to one on it, and that normalized dual class generates cohomology supported at
the chosen point.

This is intrinsic purity on the smooth component neighborhood.  It does not yet give ambient
purity in codimension `p`: that requires a Thom or Gysin comparison between the intrinsic local
homology in degree `2 * (d - p)` and ambient cohomology supported on the component in degree
`2 * p`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- Let `M` be a vector space over a field `R` and `z ∈ M` a nonzero vector. This is a chosen linear
functional `M → R` taking `z` to `1`. In dimensions greater than one, this condition need not
determine the functional uniquely. -/
def normalizedDual (z : M) (hz : z ≠ 0) : Module.Dual R M :=
  Classical.choose (Module.Projective.exists_dual_eq_one R hz)

/-- Let `R` be a field, `(X, A)` a topological pair, and `z` a nonzero class in relative singular
homology `H_n(X, A; R)`. Choose a linear functional on this homology group taking `z` to `1`,
and use the universal-coefficient equivalence to obtain a class in `H^n(X, A; R)`. This is the
resulting coclass; the normalization alone is unique when the homology is one-dimensional. -/
def normalizedRelativeCoclass {R : Type*} [Field R] {X : TopPair} {n : ℕ}
    (z : RelativeHomology R X n) (hz : z ≠ 0) : RelativeCohomology R X n :=
  (relativeCohomologyEquivDualHomology R X n).symm (normalizedDual z hz)

end AlgebraicTopology.Singular
