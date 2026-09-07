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

public import FormalConjecturesForMathlib.AlgebraicGeometry.BettiSupportSingularHypercohomologyComparison
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleClass
public import FormalConjecturesForMathlib.AlgebraicGeometry.DimensionedSmoothProjective
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationParacompact
import Lean.Elab.Tactic.Omega

/-!
# The Hodge conjecture

The Hodge conjecture says that every rational Hodge class of degree `2p` on a nonsingular
complex projective variety is a rational linear combination of classes of algebraic subvarieties
of codimension `p`.

The proposition below also includes the standard cycle-class foundation which has not yet been
constructed in this development. It asks for a linear map from the rational Chow group which
sends every irreducible component to the nonzero image of a generator of its full supported
cohomology group. Thus purity, compatibility with rational equivalence, and existence of the
cycle-class map are conclusions inside the proposition, not assumptions. Once such a map is
given, its range is the rational span of the algebraic cycle classes, independently of the
choice of nonzero rational normalization.

This file names an open proposition. It does not assert or prove that proposition.

*Reference:*
- [P. Deligne, *The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
-/

open AlgebraicGeometry Order

namespace HodgeConjecture

open ComplexPoint

/-- A candidate rational cycle-class map has the scale-independent component property needed by
the Hodge conjecture if every irreducible component maps to the nonzero image of a generator of
its full degree-`2p` cohomology with support.

The rational vector-space structure on supported sheaf cohomology is transported across the
proved comparison with rational singular cohomology. Because `cl` starts on the rational Chow
group, compatibility with rational equivalence is part of its type. Requiring both a generator
of the full supported group and a nonzero forgotten image rules out the degenerate zero class.
Complex orientation chooses a preferred generator, but its normalization is irrelevant to the
rational line occurring in the conjecture. -/
public def IsRationalCycleClassMap
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ)
    (cl : RationalChowGroup V.scheme p →ₗ[ℚ]
      RationalCohomology V.structureMap (2 * (p : ℤ))) : Prop :=
  ∀ (x : V.scheme) (hx : coheight x = p),
    let Z := cycleComponentSupport V.toSmoothProjectiveComplexVariety x
    let e : RationalCohomologyWithSupport V.structureMap Z (2 * (p : ℤ)) ≃+
        AlgebraicTopology.Singular.CohomologyWithSupport ℚ
          (TopCat.of V.analyticPoint) Z (2 * p) := by
      rw [show 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) by omega]
      exact rationalCohomologyWithSupportAddEquivSingular
        V.structureMap V.dimension Z
          (isClosed_cycleComponentSupport V.toSmoothProjectiveComplexVariety x) (2 * p)
    let _ : Module ℚ (RationalCohomologyWithSupport V.structureMap Z (2 * (p : ℤ))) :=
      e.module ℚ
    ∃ β : RationalCohomologyWithSupport V.structureMap Z (2 * (p : ℤ)),
      Submodule.span ℚ {β} = ⊤ ∧
        forgetSupport V.structureMap Z (2 * (p : ℤ)) β =
          cl (rationalComponentChowClass
            V.toSmoothProjectiveComplexVariety p x hx) ∧
        cl (rationalComponentChowClass
          V.toSmoothProjectiveComplexVariety p x hx) ≠ 0

/-- The Hodge conjecture, packaged together with the standard cycle-class foundation needed to
state it without an unconstructed global cycle-class map. For every nonsingular complex
projective variety and every codimension, there must exist a rational Chow-to-cohomology map
which has the scale-independent component fundamental-class property and whose range contains
every rational Hodge class.

This definition is a proposition, not a proof. It is deliberately untagged because the current
problem metadata treats a sorry-free definition as a solved declaration. -/
public def hodgeConjecture : Prop :=
  ∀ (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ),
    ∃ cl : RationalChowGroup V.scheme p →ₗ[ℚ]
        RationalCohomology V.structureMap (2 * (p : ℤ)),
      IsRationalCycleClassMap V p cl ∧
        rationalHodgeClasses V.structureMap V.dimension p ≤ LinearMap.range cl

end HodgeConjecture
