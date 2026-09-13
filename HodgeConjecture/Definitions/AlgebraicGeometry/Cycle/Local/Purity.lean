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

/-- The normalized dual of a nonzero vector. -/
def normalizedDual (z : M) (hz : z ≠ 0) : Module.Dual R M :=
  Classical.choose (Module.Projective.exists_dual_eq_one R hz)

/-- The relative cohomology class normalized to pair to one with a given nonzero relative
homology class. Cohomology is the homology of the dual cochain complex rather than the dual of
homology, so the normalized functional is transported along the universal-coefficient
equivalence. -/
def normalizedRelativeCoclass {R : Type*} [Field R] {X : TopPair} {n : ℕ}
    (z : RelativeHomology R X n) (hz : z ≠ 0) : RelativeCohomology R X n :=
  (relativeCohomologyEquivDualHomology R X n).symm (normalizedDual z hz)

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.CycleComponentSeparateLocalCoordinates

open AlgebraicTopology.Singular

variable {d n : ℕ} {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom] {x : X.left}
  [SmoothOfRelativeDimension d X.hom]
  (C : CycleComponentSeparateLocalCoordinates X x d n)

end AlgebraicGeometry.CycleComponentSeparateLocalCoordinates
