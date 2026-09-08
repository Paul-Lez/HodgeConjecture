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
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentBorelMoore
public import FormalConjecturesForMathlib.AlgebraicGeometry.DimensionedSmoothProjective
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationParacompact
import Lean.Elab.Tactic.Omega

/-!
# Cycle classes from Borel--Moore fundamental classes

For an irreducible codimension-`p` component `Z` of a smooth projective complex `d`-fold, the
complex orientation fixes a unique class

`[Z]ᴮᴹ ∈ Hᴮᴹ_{2(d-p)}(Z; ℚ)`.

Alexander--Poincaré duality sends this exact class to supported cohomology in degree `2p`.
Forgetting support gives the ordinary component cycle class.  Extending these classes linearly
and proving that principal divisors vanish produces the map from the rational Chow group.

This file packages those constructions without reverting to a statement that merely chooses a
nonzero rational generator.  The Borel--Moore class is fixed by its complex local orientation,
and the supported class is definitionally its image under the supplied Alexander duality
equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

/-- Rational singular cohomology of the ambient analytic space supported on one irreducible
cycle component. -/
abbrev RationalSingularCycleComponentCohomologyWithSupport
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ) :=
  CohomologyWithSupport ℚ
    (@TopCat.of V.analyticPoint ComplexPoint.analyticTopology)
    (cycleComponentSupport V x) n

/-- The Borel--Moore and Alexander-duality data for one irreducible codimension-`p` component. -/
structure RationalCycleComponentBorelMooreClassData
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ)
    (x : V.scheme) (hx : coheight x = p) where
  /-- The uniquely normalized Borel--Moore fundamental class construction. -/
  borelMoore : RationalCycleComponentBorelMooreData
    V.toSmoothProjectiveComplexVariety x V.dimension p hx
  /-- Alexander--Poincaré duality for the closed analytic support of the component. -/
  alexanderDuality :
    CycleComponentBorelMooreHomology ℚ
        V.toSmoothProjectiveComplexVariety x (2 * (V.dimension - p)) ≃ₗ[ℚ]
      RationalSingularCycleComponentCohomologyWithSupport
        V.toSmoothProjectiveComplexVariety x (2 * p)

namespace RationalCycleComponentBorelMooreClassData

variable {V : DimensionedSmoothProjectiveComplexVariety} {p : ℕ}
  {x : V.scheme} {hx : coheight x = p}

/-- The exact Borel--Moore fundamental class of the component. -/
def fundamentalClass
    (D : RationalCycleComponentBorelMooreClassData V p x hx) :
    CycleComponentBorelMooreHomology ℚ
      V.toSmoothProjectiveComplexVariety x (2 * (V.dimension - p)) :=
  D.borelMoore.fundamentalClass

/-- The singular cohomology class with support obtained by Alexander duality from the exact
Borel--Moore fundamental class. -/
def singularSupportedFundamentalClass
    (D : RationalCycleComponentBorelMooreClassData V p x hx) :
    RationalSingularCycleComponentCohomologyWithSupport
      V.toSmoothProjectiveComplexVariety x (2 * p) :=
  D.alexanderDuality D.fundamentalClass

/-- The comparison between rational constant-sheaf cohomology with support and rational
singular cohomology with support in the component's cycle-class degree. -/
def supportedComparison
    (_D : RationalCycleComponentBorelMooreClassData V p x hx) :
    RationalCohomologyWithSupport V.structureMap
        (cycleComponentSupport V.toSmoothProjectiveComplexVariety x) (2 * (p : ℤ)) ≃+
      RationalSingularCycleComponentCohomologyWithSupport
        V.toSmoothProjectiveComplexVariety x (2 * p) := by
  let _ : TopologicalSpace V.analyticPoint := ComplexPoint.analyticTopology
  let _ : T2Space V.analyticPoint :=
    ProjectiveSpace.Presentation.complexPoint_t2Space
      (Classical.choice V.toSmoothProjectiveComplexVariety.projective)
  let _ : CompactSpace V.analyticPoint :=
    ProjectiveSpace.IsProjective.complexPoint_compactSpace
      V.toSmoothProjectiveComplexVariety.projective
  let _ : ChartedSpace (Fin V.dimension → ℂ) V.analyticPoint :=
    analyticChartedSpace V.structureMap V.dimension
  let _ : ∀ U : Opens V.analyticPoint, ParacompactSpace U := fun U =>
    opens_paracompactSpace_of_compact_chartedSpace
      (H := Fin V.dimension → ℂ) U
  rw [show 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) by omega]
  exact rationalCohomologyWithSupportAddEquivSingular
    V.structureMap V.dimension
      (cycleComponentSupport V.toSmoothProjectiveComplexVariety x)
      (isClosed_cycleComponentSupport V.toSmoothProjectiveComplexVariety x) (2 * p)

/-- The canonical rational constant-sheaf cohomology class with support associated to the
component. -/
def supportedFundamentalClass
    (D : RationalCycleComponentBorelMooreClassData V p x hx) :
    RationalCohomologyWithSupport V.structureMap
      (cycleComponentSupport V.toSmoothProjectiveComplexVariety x) (2 * (p : ℤ)) :=
  D.supportedComparison.symm D.singularSupportedFundamentalClass

/-- Forgetting support gives the ordinary rational cohomology class of the component. -/
def ordinaryFundamentalClass
    (D : RationalCycleComponentBorelMooreClassData V p x hx) :
    RationalCohomology V.structureMap (2 * (p : ℤ)) :=
  forgetSupport V.structureMap
    (cycleComponentSupport V.toSmoothProjectiveComplexVariety x) (2 * (p : ℤ))
    D.supportedFundamentalClass

end RationalCycleComponentBorelMooreClassData

/-- The geometric input for the rational Chow-to-cohomology cycle-class construction.  Every
irreducible component is assigned its exactly normalized Borel--Moore fundamental class, and the
only compatibility retained as data is the geometric theorem that the resulting componentwise
class kills principal divisors.  The linear map on the Chow group and its value on component
classes are constructed below from the quotient universal property. -/
structure RationalBorelMooreCycleClassConstruction
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ) where
  /-- The Borel--Moore construction for every codimension-`p` component. -/
  component : ∀ (x : V.scheme) (hx : coheight x = p),
    RationalCycleComponentBorelMooreClassData V p x hx
  /-- Principal divisors have zero componentwise Borel--Moore cycle class.  This is the geometric
  rational-equivalence theorem; descent to the Chow quotient is not stored as additional data. -/
  principalDivisor_class : ∀ D : PrincipalDivisor V.scheme p,
    cycleClassOnAlgebraicCyclesOfComponents
        (fun x hx ↦ (component x hx).ordinaryFundamentalClass)
        D.pushforwardCycle = 0

namespace RationalBorelMooreCycleClassConstruction

/-- The ordinary cohomology class assigned to an irreducible codimension-`p` component. -/
def componentClass
    {V : DimensionedSmoothProjectiveComplexVariety} {p : ℕ}
    (C : RationalBorelMooreCycleClassConstruction V p)
    (x : V.scheme) (hx : coheight x = p) :
    RationalCohomology V.structureMap (2 * (p : ℤ)) :=
  (C.component x hx).ordinaryFundamentalClass

/-- The rational Chow-group cycle-class map derived from component classes.  Its construction
first extends additively to cycles, proves that the principal-divisor subgroup is in the kernel,
descends through the integral Chow quotient, and finally extends scalars to `ℚ`. -/
def cycleClass
    {V : DimensionedSmoothProjectiveComplexVariety} {p : ℕ}
    (C : RationalBorelMooreCycleClassConstruction V p) :
    RationalChowGroup V.scheme p →ₗ[ℚ]
      RationalCohomology V.structureMap (2 * (p : ℤ)) :=
  ChowGroup.rationalCycleClassOfComponents C.componentClass C.principalDivisor_class

/-- The derived Chow cycle-class map sends a component with coefficient one to the class obtained
from its Borel--Moore fundamental class by Alexander duality and forgetting support. -/
@[simp] theorem cycleClass_component
    {V : DimensionedSmoothProjectiveComplexVariety} {p : ℕ}
    (C : RationalBorelMooreCycleClassConstruction V p)
    (x : V.scheme) (hx : coheight x = p) :
    C.cycleClass (rationalComponentChowClass
      V.toSmoothProjectiveComplexVariety p x hx) = C.componentClass x hx := by
  exact ChowGroup.rationalCycleClassOfComponents_component
    C.componentClass C.principalDivisor_class x hx

/-- The Borel--Moore component class is in the range of the constructed Chow cycle-class map. -/
lemma ordinaryFundamentalClass_mem_range
    {V : DimensionedSmoothProjectiveComplexVariety} {p : ℕ}
    (C : RationalBorelMooreCycleClassConstruction V p)
    (x : V.scheme) (hx : coheight x = p) :
    (C.component x hx).ordinaryFundamentalClass ∈ LinearMap.range C.cycleClass := by
  refine ⟨rationalComponentChowClass
    V.toSmoothProjectiveComplexVariety p x hx, ?_⟩
  exact C.cycleClass_component x hx

end RationalBorelMooreCycleClassConstruction

end AlgebraicGeometry.ComplexPoint
