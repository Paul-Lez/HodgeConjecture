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

public import Other.AlgebraicGeometry.BorelMooreCycleClass
public import Other.Mathlib.Algebra.Module.LinearMap.Rat

import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula

/-!
# Sheaf-theoretic Borel--Moore homology

This file isolates the presently missing six-functor input needed for the sheaf-theoretic
definition

`Hᵇᵐ_i(Z ⊂ X; ℚ) = ℌ⁻ⁱ_Z(X, ω_X)`.

Mathlib currently supplies derived categories, shifts, and sheaf pushforward, but not dualizing
complexes, exceptional pullback, Verdier duality, or a derived sections-with-support functor.
Accordingly, `RationalDualizingComplex` and `DerivedSectionsWithSupportInput` below are explicit
inputs,
not typeclasses or existence assertions.  The latter includes the exact comparison with the
mapping-cone model already used by `RationalCohomologyWithSupport`.

Once these inputs and an isomorphism `ω_X ≅ ℚ_X[2d]` are supplied, the resulting group
equivalence is constructed by mapping that isomorphism through the support functor, applying
shift compatibility, and evaluating on hypercohomology.  This constructs the formal
degree-shifted comparison; identifying the supplied isomorphism with the normalized complex
orientation is a separate, presently unproved theorem.  No group-level duality equivalence is
retained as input.

The construction here is ambient.  `IntrinsicSheafBorelMooreHomology` separately records what
the intrinsic definition on a space carrying its own dualizing complex means; no compactification
independence or closed-embedding comparison is claimed.

## Inventory: the hypothesis structures of the Borel--Moore layer

The Borel--Moore development is this file together with `BorelMooreCycleClass.lean`,
`CycleComponentBorelMoore.lean` and `CycleComponentGlobalFundamentalClass.lean`, all under
`Other/AlgebraicGeometry/`.  Everything proved there is conditional on the thirteen hypothesis
structures listed below: each packages data and theorems Mathlib does not supply, so the results
read "given such a package, ...".  The grouping is by producer -- which packages some declaration
actually builds, and out of what.  Issue #57 tracks this inventory; issue #14 tracks redefining
Borel--Moore homology through hypercohomology, after which how many of the thirteen become
constructible measures the progress made.

### Instantiated, but only in maximal codimension `p = d`

* `CycleComponentBorelMoore.lean`: `RationalCycleComponentBorelMooreData`, by
  `rationalCycleComponentBorelMooreDataOfCoheightEqDimension`
* `BorelMooreCycleClass.lean`: `AuxiliaryRationalCycleComponentBorelMooreComparisonData`, by
  `auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension`
* `BorelMooreCycleClass.lean`: `RationalCycleComponentLocalThomCapInput`, by
  `maximalCodimensionLocalThomCapInput`
* `BorelMooreCycleClass.lean`: `ComplexOrientedRationalCycleComponentClassData`, by
  `maximalCodimensionComplexOrientedComponentClassData`

For a point component the Borel--Moore group, the local orientation and Alexander duality are
computed outright, so these four witnesses take no input beyond the variety and the point.  Away
from `p = d` the same packages await the global Borel--Moore fundamental-class theorem for
oriented manifolds and the Thom/costalk operation normalizing the comparison, neither of which
Mathlib provides.  Three of the four -- `RationalCycleComponentBorelMooreData`,
`AuxiliaryRationalCycleComponentBorelMooreComparisonData` and
`ComplexOrientedRationalCycleComponentClassData` -- also have adapters out of other packages of
this list, which add nothing their source package does not already provide.

### Constructible only from other structures of this list

* `CycleComponentGlobalFundamentalClass.lean`:
  `RationalCycleComponentGlobalFundamentalClassInputs`, out of
  `RationalCycleComponentInjectiveBoundaryInputs` or `RationalCycleComponentBoundedModelInputs`
* `CycleComponentGlobalFundamentalClass.lean`: `RationalCycleComponentInjectiveBoundaryInputs`,
  out of `RationalCycleComponentBoundedModelInputs`

These producers only move work between packages -- boundary vanishing is derived from injectivity
of the punctured-space inclusion, and that in turn from a bounded chain model -- so each inherits
whatever its source package is still missing, and every source package is itself in this list.

### No producer

* `SheafBorelMoore.lean`: `RationalDualizingComplex`
* `SheafBorelMoore.lean`: `RationalDualizingComplexOrientationInput`
* `SheafBorelMoore.lean`: `DerivedSectionsWithSupportInput`
* `SheafBorelMoore.lean`: `RationalCycleComponentSheafBorelMooreComparisonInputs`
* `SheafBorelMoore.lean`: `ComplexOrientedRationalCycleComponentSheafBorelMooreData`
* `CycleComponentGlobalFundamentalClass.lean`: `RationalCycleComponentGlobalFundamentalClassCore`,
  reached only through the `extends` clauses of the three packages sharing it
* `CycleComponentGlobalFundamentalClass.lean`: `RationalCycleComponentBoundedModelInputs`

The five in this file await the six-functor input described above: a dualizing complex, the
Verdier-duality predicate with which to say that it is dualizing, the orientation isomorphism
`ω_X ≅ ℚ_X[2d]` together with its normalization by the complex orientation, derived sections with
support, and the costalk comparison identifying the sheaf model with the compactification-relative
one.  For the first two, inhabitation would be weaker than construction: nothing in their fields
asserts that the object is dualizing or that the isomorphism is the normalized one.  The last two
await the local-to-global geometry of a positive-dimensional component: relative Mayer--Vietoris
propagation of the local orientation from one smooth anchor point, and a dimension-bounded chain
model for the punctured component.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))

local instance sheafBorelMooreTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance sheafBorelMooreHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The derived category of additive sheaves on the analytic complex-point space. -/
abbrev AnalyticDerivedCategory :=
  DerivedCategory (AnalyticAdditiveSheaf X)

/-- A rational dualizing object on the analytic complex-point space.

The assertion that this object is dualizing is presently mathematical input: Mathlib has no
Verdier-duality predicate with which to express it.  Keeping the object in a named structure makes
that boundary explicit without fabricating a six-functor API. -/
structure RationalDualizingComplex where
  /-- A complex representing the rational dualizing object `ω_X`. -/
  dualizingComplex : CochainComplex (AnalyticAdditiveSheaf X) ℤ

/-- Explicit input consisting of a proposed rational dualizing complex and an isomorphism with
the shifted constant sheaf in dimension `d`.

The field alone does **not** assert that the isomorphism is the one normalized by complex
orientation: it may be rescaled by a rational automorphism.  A future Verdier-duality/costalk
normalization theorem must construct this datum and prove that compatibility. -/
structure RationalDualizingComplexOrientationInput (d : ℕ)
    extends RationalDualizingComplex X where
  /-- The supplied derived-category isomorphism `ω_X ≅ ℚ_X[2d]`. -/
  orientationIso :
    DerivedCategory.Q.obj dualizingComplex ≅
      (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X))⟦2 * (d : ℤ)⟧

/-- The normalized derived object representing rational sections with support.

`rationalCohomologyWithSupportComplex` is the mapping cone of restriction.  It represents the
homotopy fiber only after shifting by `-1`, which is displayed here rather than hidden in a degree
convention. -/
def rationalDerivedSectionsWithSupportObject
    (Z : Set (ComplexPoint X)) : AnalyticDerivedCategory X :=
  (DerivedCategory.Q.obj
    (rationalCohomologyWithSupportComplex X Z))⟦(-1 : ℤ)⟧

/-- Explicit input for the missing derived sections-with-support functor `RΓ_Z`.

Besides the functor, the data records its shift compatibility and rigidly identifies its value on
the rational constant sheaf with the existing restriction-cone construction.  The latter is an
object equality, so the construction below uses `eqToIso` and cannot conceal a scalar
automorphism in an arbitrary comparison isomorphism.  These are precisely the facts needed to
transport an orientation; no equivalence between Borel--Moore homology and supported cohomology
is stored. -/
structure DerivedSectionsWithSupportInput
    (Z : Set (ComplexPoint X)) where
  /-- The local-cohomology/derived-sections-with-support endofunctor. -/
  functor : AnalyticDerivedCategory X ⥤ AnalyticDerivedCategory X
  /-- Derived sections with support commute coherently with cohomological shifts. -/
  commShift : functor.CommShift ℤ
  /-- Normalization of `RΓ_Z(ℚ_X)` as the project's mapping-cone support object.  An equality is
  deliberately required here: an unconstrained isomorphism could rescale supported classes. -/
  constantObject_eq :
    functor.obj (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X)) =
      rationalDerivedSectionsWithSupportObject X Z

/-- Hypercohomology of an object already in the derived category. -/
abbrev DerivedHypercohomology
    (K : AnalyticDerivedCategory X) (n : ℤ) :=
  ShiftedHom
    (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X)) K n

/-- The group `ℌ⁻ⁱ(X, ω_X)` associated to the supplied intrinsic dualizing-object candidate.
It is intentionally separate from an ambient support.  Calling it intrinsic Borel--Moore
homology requires the still-unavailable theorem that the candidate is genuinely dualizing. -/
abbrev IntrinsicSheafBorelMooreHomology
    (ω : RationalDualizingComplex X) (i : ℤ) :=
  DerivedHypercohomology X (DerivedCategory.Q.obj ω.dualizingComplex) (-i)

/-- The ambient Borel--Moore object `RΓ_Z(ω_X)` in the derived category. -/
def ambientSheafBorelMooreObject
    {Z : Set (ComplexPoint X)}
    (ω : RationalDualizingComplex X)
    (support : DerivedSectionsWithSupportInput X Z) :
    AnalyticDerivedCategory X :=
  support.functor.obj (DerivedCategory.Q.obj ω.dualizingComplex)

/-- The ambient group `ℌ⁻ⁱ_Z(X, ω_X)` associated to the supplied support and dualizing inputs. -/
abbrev AmbientSheafBorelMooreHomology
    {Z : Set (ComplexPoint X)}
    (ω : RationalDualizingComplex X)
    (support : DerivedSectionsWithSupportInput X Z) (i : ℤ) :=
  DerivedHypercohomology X
    (ambientSheafBorelMooreObject X ω support) (-i)

/-- Applying derived sections with support to the orientation gives
`RΓ_Z(ω_X) ≅ RΓ_Z(ℚ_X)[2d]`.

This is the categorical source of the degree-shifted Borel--Moore/cohomology equivalence below. -/
def ambientSheafBorelMooreOrientationIso
    {Z : Set (ComplexPoint X)} {d : ℕ}
    (ω : RationalDualizingComplexOrientationInput X d)
    (support : DerivedSectionsWithSupportInput X Z) :
    ambientSheafBorelMooreObject X ω.toRationalDualizingComplex support ≅
      (rationalDerivedSectionsWithSupportObject X Z)⟦2 * (d : ℤ)⟧ := by
  letI : support.functor.CommShift ℤ := support.commShift
  exact support.functor.mapIso ω.orientationIso ≪≫
    (support.functor.commShiftIso (2 * (d : ℤ))).app _ ≪≫
      (shiftFunctor (AnalyticDerivedCategory X) (2 * (d : ℤ))).mapIso
        (eqToIso support.constantObject_eq)

/-- The target-object isomorphism which displays all shifts in
`Hᵇᵐ_i(Z ⊂ X; ℚ) ≅ H_Z^{2d-i}(X; ℚ)`.

The final exponent `(2d-i)-1` is exactly the `-1` used by the mapping-cone definition of
`RationalCohomologyWithSupport`. -/
def ambientSheafBorelMooreTargetIso
    {Z : Set (ComplexPoint X)} {d : ℕ}
    (ω : RationalDualizingComplexOrientationInput X d)
    (support : DerivedSectionsWithSupportInput X Z) (i : ℤ) :
    (ambientSheafBorelMooreObject X ω.toRationalDualizingComplex support)⟦-i⟧ ≅
      (DerivedCategory.Q.obj
        (rationalCohomologyWithSupportComplex X Z))⟦
          (2 * (d : ℤ) - i) - 1⟧ :=
  (shiftFunctor (AnalyticDerivedCategory X) (-i)).mapIso
      (ambientSheafBorelMooreOrientationIso X ω support) ≪≫
    (shiftFunctorAdd' (AnalyticDerivedCategory X)
      (2 * (d : ℤ)) (-i) (2 * (d : ℤ) - i) (by omega)).symm.app _ ≪≫
    (shiftFunctorAdd' (AnalyticDerivedCategory X)
      (-1 : ℤ) (2 * (d : ℤ) - i) ((2 * (d : ℤ) - i) - 1) (by omega)).symm.app
        (DerivedCategory.Q.obj
          (rationalCohomologyWithSupportComplex X Z))

/-- Derived hypercohomology is invariant under a possibly degree-reindexing isomorphism of its
shifted target objects. -/
def derivedHypercohomologyAddEquivOfShiftedTargetIso
    {K L : AnalyticDerivedCategory X} {n m : ℤ}
    (e : K⟦n⟧ ≅ L⟦m⟧) :
    DerivedHypercohomology X K n ≃+
      DerivedHypercohomology X L m where
  toEquiv := (Iso.refl
    (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))).homCongr e
  map_add' f g := by simp

/-- The equivalence induced by the supplied orientation isomorphism
`Hᵇᵐ_i(Z ⊂ X; ℚ) ≅ H_Z^{2d-i}(X; ℚ)`.

It is a composite of the supported isomorphism, categorical shift arithmetic, and the existing
small-hom presentation of hypercohomology.  Its construction is formal; its identification with
normalized Alexander--Poincaré duality needs the missing orientation/costalk theorem. -/
def ambientSheafBorelMooreEquivCohomologyWithSupport
    {Z : Set (ComplexPoint X)} {d : ℕ}
    (ω : RationalDualizingComplexOrientationInput X d)
    (support : DerivedSectionsWithSupportInput X Z) (i : ℤ) :
    AmbientSheafBorelMooreHomology X
        ω.toRationalDualizingComplex support i ≃+
      RationalCohomologyWithSupport X Z (2 * (d : ℤ) - i) :=
  (derivedHypercohomologyAddEquivOfShiftedTargetIso X
      (ambientSheafBorelMooreTargetIso X ω support i)).trans
    (hypercohomologyAddEquivDerived X
      (rationalCohomologyWithSupportComplex X Z)
      ((2 * (d : ℤ) - i) - 1)).symm

/-- Arithmetic specialization of the orientation shift in cycle-class degree. -/
lemma borelMoore_cycle_degree {d p : ℕ} (hp : p ≤ d) :
    2 * (d : ℤ) - ((2 * (d - p) : ℕ) : ℤ) = 2 * (p : ℤ) := by
  omega

/-- The cycle-degree specialization
`Hᵇᵐ_{2(d-p)}(Z ⊂ X; ℚ) ≅ H_Z^{2p}(X; ℚ)`.

Unlike the old group-level comparison field, this is obtained functorially from the supplied
derived-category orientation isomorphism.  Normalization of that input is not proved here. -/
def ambientSheafBorelMooreCycleDegreeEquiv
    {Z : Set (ComplexPoint X)} {d p : ℕ} (hp : p ≤ d)
    (ω : RationalDualizingComplexOrientationInput X d)
    (support : DerivedSectionsWithSupportInput X Z) :
    AmbientSheafBorelMooreHomology X ω.toRationalDualizingComplex support
        ((2 * (d - p) : ℕ) : ℤ) ≃+
      RationalCohomologyWithSupport X Z (2 * (p : ℤ)) :=
  (ambientSheafBorelMooreEquivCohomologyWithSupport X ω support
    ((2 * (d - p) : ℕ) : ℤ)).trans
      (AddEquiv.cast (borelMoore_cycle_degree hp))

/-! ### Conditional adapter for the existing component comparison scaffold -/

/-- Explicit sheaf-theoretic comparison inputs for one cycle component.

The only comparison with the earlier compactification-relative model is explicitly named
`compactificationComparison`.  The supported-cohomology map is not data: it is constructed from
this comparison and `ambientSheafBorelMooreCycleDegreeEquiv`.  Because neither the proposed
orientation isomorphism nor `sheafToLocal` is canonically constructed, this structure does not
claim a normalized general cycle class. -/
structure RationalCycleComponentSheafBorelMooreComparisonInputs
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = p) where
  /-- The exactly complex-oriented compactification-relative fundamental class. -/
  borelMoore : RationalCycleComponentBorelMooreData V x d p hx
  /-- The proposed dualizing complex and its supplied shift isomorphism. -/
  dualizing : RationalDualizingComplexOrientationInput V.over d
  /-- Derived sections with support in the analytic cycle component. -/
  support : DerivedSectionsWithSupportInput V.over
    (cycleComponentSupport V.over x)
  /-- The unconstructed comparison between the compactification-relative singular model and the
  ambient sheaf model.  This is the exact API boundary replacing an arbitrary Alexander-duality
  equivalence. -/
  compactificationComparison :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) ≃+
      AmbientSheafBorelMooreHomology V.over
        dualizing.toRationalDualizingComplex support
        ((2 * (d - p) : ℕ) : ℤ)
  /-- Costalk/local-homology evaluation of an ambient sheaf Borel--Moore class.  Constructing this
  map is part of the missing closed-embedding/costalk comparison. -/
  sheafToLocal : ∀ z : CycleComponentAnalyticPoint V x,
    AmbientSheafBorelMooreHomology V.over
        dualizing.toRationalDualizingComplex support
        ((2 * (d - p) : ℕ) : ℤ) →+
      RelativeHomology ℚ (pointComplementPair z) (2 * (d - p))
  /-- The compactification/sheaf comparison commutes with every supplied local evaluation.  This
  exposes the missing costalk/model-compatibility theorem and proves normalization relative to
  `sheafToLocal`; canonicity of that costalk map is not asserted by the present API. -/
  compactificationComparison_toLocal : ∀
      (z : CycleComponentAnalyticPoint V x)
      (c : CycleComponentBorelMooreHomology ℚ V x (2 * (d - p))),
    sheafToLocal z (compactificationComparison c) =
      cycleComponentBorelMooreToLocal ℚ V x (2 * (d - p)) z c

namespace RationalCycleComponentSheafBorelMooreComparisonInputs

variable {V : SmoothProjectiveComplexVariety} {d p : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]
  {x : V.scheme} {hx : coheight x = p}

/-- Codimension does not exceed ambient dimension for a component of a smooth complex variety. -/
lemma codimension_le_dimension
    (_D : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx) :
    p ≤ d := by
  have h := SmoothOfRelativeDimension.coheight_le_complex
    (f := V.structureMap) (d := d) x
  rw [hx] at h
  exact_mod_cast h

/-- The old compactification-relative fundamental class, still normalized by the exact complex
local orientation. -/
def compactificationFundamentalClass
    (D : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx) :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) :=
  D.borelMoore.fundamentalClass

/-- The compactification-relative class transported to ambient sheaf Borel--Moore homology.  Its
local normalization relative to the supplied costalk map is proved below. -/
def sheafBorelMooreClassOfComparisons
    (D : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx) :
    AmbientSheafBorelMooreHomology V.over
      D.dualizing.toRationalDualizingComplex D.support
      ((2 * (d - p) : ℕ) : ℤ) :=
  D.compactificationComparison D.compactificationFundamentalClass

/-- Relative to `sheafToLocal`, the transported sheaf Borel--Moore class has exactly the
constructed positive complex local orientation at every smooth point. -/
lemma sheafToLocal_sheafBorelMooreClassOfComparisons
    (D : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus
      V.over x) :
    D.sheafToLocal z D.sheafBorelMooreClassOfComparisons =
      D.borelMoore.localOrientation z hz := by
  rw [sheafBorelMooreClassOfComparisons,
    D.compactificationComparison_toLocal]
  exact D.borelMoore.toLocal_fundamentalClass z hz

/-- The additive equivalence obtained by composing the supplied compactification comparison,
the orientation-induced sheaf comparison, and the proved singular comparison.  This is only
identified with normalized Alexander--Poincaré duality after the missing compatibility theorem. -/
def orientationInducedComparisonAddEquiv
    (D : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx) :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) ≃+
      RationalSingularComponentCohomologyWithSupport V.over x (2 * p) := by
  let : TopologicalSpace V.analyticPoint := Point.analyticTopology
  let : T2Space V.analyticPoint := inferInstance
  let : CompactSpace V.analyticPoint := inferInstance
  let : ChartedSpace (Fin d → ℂ) V.analyticPoint :=
    inferInstance
  let : ∀ U : Opens V.analyticPoint, ParacompactSpace U := fun U =>
    opens_paracompactSpace_of_compact_chartedSpace
      (H := Fin d → ℂ) U
  exact D.compactificationComparison |>.trans
    (ambientSheafBorelMooreCycleDegreeEquiv V.over
      D.codimension_le_dimension D.dualizing D.support) |>.trans
    (rationalCohomologyWithSupportAddEquivSingular
      V.over
        (cycleComponentSupport V.over x)
        (isClosed_cycleComponentSupport V.over x) (2 * p))

/-- The singular supported class obtained from all supplied comparisons. -/
def singularSupportedClassOfComparisons
    (D : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx) :
    RationalSingularComponentCohomologyWithSupport V.over x (2 * p) :=
  D.orientationInducedComparisonAddEquiv D.compactificationFundamentalClass

/-- The comparison composite sends the compactification-relative fundamental class to the
comparison-dependent singular supported class. -/
@[simp] lemma orientationInducedComparisonAddEquiv_fundamentalClass
    (D : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx) :
    D.orientationInducedComparisonAddEquiv D.compactificationFundamentalClass =
      D.singularSupportedClassOfComparisons := rfl

/-- Adapter to the previous cycle-class package.

The old API asks for a rational `LinearEquiv`.  Its underlying additive equivalence is now the
constructed sheaf-theoretic composite.  Although the present derived category is only visibly
additive, no extra linearity hypothesis is needed: every additive homomorphism between rational
vector spaces preserves rational scalar multiplication (`map_rat_smul`). -/
def toAuxiliaryBorelMooreComparisonData
    (D : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx) :
    AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx where
  borelMoore := D.borelMoore
  auxiliaryComparison := D.orientationInducedComparisonAddEquiv.toRatLinearEquiv

/-- Passing through the adapter does not change the comparison-dependent singular class. -/
@[simp] lemma toAuxiliaryBorelMooreComparisonData_auxiliarySingularSupportedClass
    (D : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx) :
    D.toAuxiliaryBorelMooreComparisonData.auxiliarySingularSupportedClass =
      D.singularSupportedClassOfComparisons := by
  simp only [AuxiliaryRationalCycleComponentBorelMooreComparisonData.auxiliarySingularSupportedClass,
    toAuxiliaryBorelMooreComparisonData, singularSupportedClassOfComparisons,
    AuxiliaryRationalCycleComponentBorelMooreComparisonData.fundamentalClass,
    compactificationFundamentalClass, AddEquiv.coe_toRatLinearEquiv]

end RationalCycleComponentSheafBorelMooreComparisonInputs

/-! ### Conditional normalized sheaf route -/

/-- The sheaf comparison inputs together with the missing theorem that the orientation-induced
comparison is normalized by the actual local Thom-cap operation.

`orientationComparison_local` is the explicit Verdier/Thom compatibility boundary.  It is not
implied by `compactificationComparison_toLocal`: the latter sees only the Borel--Moore side and
allows simultaneous inverse rescaling of the orientation and costalk maps. -/
structure ComplexOrientedRationalCycleComponentSheafBorelMooreData
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = p) where
  comparisonInputs : RationalCycleComponentSheafBorelMooreComparisonInputs V d p x hx
  localThomCap : RationalCycleComponentLocalThomCapInput V d p x hx
  orientationComparison_local : ∀
      (c : CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)))
      (z : CycleComponentAnalyticPoint V x)
      (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x),
    localThomCap.capWithAmbientComplexOrientation z hz
        (comparisonInputs.orientationInducedComparisonAddEquiv c) =
      cycleComponentBorelMooreToLocal ℚ V x (2 * (d - p)) z c

namespace ComplexOrientedRationalCycleComponentSheafBorelMooreData

variable {V : SmoothProjectiveComplexVariety} {d p : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]
  {x : V.scheme} {hx : coheight x = p}

/-- The general complex-oriented component package induced by the sheaf comparison and the
independent Verdier/Thom normalization theorem. -/
def toComplexOrientedComponentClassData
    (D : ComplexOrientedRationalCycleComponentSheafBorelMooreData V d p x hx) :
    ComplexOrientedRationalCycleComponentClassData V d p x hx where
  borelMoore := D.comparisonInputs.borelMoore
  localThomCap := D.localThomCap
  comparison := D.comparisonInputs.orientationInducedComparisonAddEquiv.toRatLinearEquiv
  comparison_isComplexOriented := D.orientationComparison_local

/-- The sheaf route together with the local Verdier/Thom normalization theorem supplies the general
complex-oriented component class data. -/
theorem nonempty_complexOrientedRationalCycleComponentClassData
    (h : Nonempty (ComplexOrientedRationalCycleComponentSheafBorelMooreData V d p x hx)) :
    Nonempty (ComplexOrientedRationalCycleComponentClassData V d p x hx) :=
  h.map toComplexOrientedComponentClassData

/-- The normalized Alexander--Poincaré equivalence obtained from the sheaf construction and the
explicit local Verdier/Thom compatibility theorem. -/
def alexanderPoincare
    (D : ComplexOrientedRationalCycleComponentSheafBorelMooreData V d p x hx) :=
  D.toComplexOrientedComponentClassData.alexanderPoincare

/-- The singular supported fundamental class with exact local Thom-cap normalization. -/
def supportedFundamentalClass
    (D : ComplexOrientedRationalCycleComponentSheafBorelMooreData V d p x hx) :=
  D.toComplexOrientedComponentClassData.supportedFundamentalClass

/-- The normalized supported class has the exact constructed complex local orientation. -/
theorem alexanderPoincare_fundamentalClass_local
    (D : ComplexOrientedRationalCycleComponentSheafBorelMooreData V d p x hx)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x) :
    D.localThomCap.capWithAmbientComplexOrientation z hz D.supportedFundamentalClass =
      cycleComponentComplexLocalOrientation V x d p hx z hz :=
  D.toComplexOrientedComponentClassData.alexanderPoincare_fundamentalClass_local z hz

/-- Local Thom-cap normalization uniquely determines the sheaf-route supported class. -/
theorem supportedFundamentalClass_unique
    (D : ComplexOrientedRationalCycleComponentSheafBorelMooreData V d p x hx)
    (α : RationalSingularComponentCohomologyWithSupport V.over x (2 * p))
    (hα : ∀ (z : CycleComponentAnalyticPoint V x)
      (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x),
      D.localThomCap.capWithAmbientComplexOrientation z hz α =
        cycleComponentComplexLocalOrientation V x d p hx z hz) :
    α = D.supportedFundamentalClass :=
  D.toComplexOrientedComponentClassData.supportedFundamentalClass_unique α hα

/-- The normalized rational constant-sheaf supported fundamental class. -/
def constantSheafSupportedFundamentalClass
    (D : ComplexOrientedRationalCycleComponentSheafBorelMooreData V d p x hx) :=
  D.toComplexOrientedComponentClassData.constantSheafSupportedFundamentalClass

/-- The normalized ordinary rational component class supplied by the conditional sheaf route. -/
def ordinaryFundamentalClass
    (D : ComplexOrientedRationalCycleComponentSheafBorelMooreData V d p x hx) :=
  D.toComplexOrientedComponentClassData.ordinaryFundamentalClass

end ComplexOrientedRationalCycleComponentSheafBorelMooreData

end AlgebraicGeometry.ComplexPoint
