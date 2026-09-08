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

public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentAnalyticEmbedding
public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentLocalOrientation
public import HodgeConjecture.Other.AlgebraicTopology.CompactificationBorelMoore
public import HodgeConjecture.Other.AlgebraicTopology.RelativeHomologyEmpty

import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytification

/-!
# Borel--Moore fundamental classes of cycle components

The analytification of a projective cycle component is compact.  Its Borel--Moore homology is
therefore represented by `H_*(Z, ∅)`.  A top-dimensional class is the component fundamental
class when its local value at every point of the smooth locus is exactly the class selected by
the complex orientation.

This file records that choice-free interface.  Existence and uniqueness are the global
Borel--Moore fundamental-class theorem: restrict to the smooth locus, construct its oriented
class, and extend uniquely across the lower-dimensional singular locus using localization.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

/-- The analytic space underlying the reduced closure of one point of a projective variety. -/
abbrev CycleComponentAnalyticPoint
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :=
  ComplexPoint (cycleComponent V.scheme x)
    (cycleComponentι V.scheme x ≫ V.structureMap)

noncomputable local instance cycleComponentAnalyticTopology
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    TopologicalSpace (CycleComponentAnalyticPoint V x) :=
  Point.analyticTopology

/-- Integral Borel--Moore homology of a projective analytic cycle component. -/
abbrev IntegralCycleComponentBorelMooreHomology
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ) : AddCommGrpCat :=
  IntegralCompactificationBorelMooreHomology
    (Set.univᶜ : Set (CycleComponentAnalyticPoint V x)) n

/-- A family of exactly normalized integral local orientation classes on the component's smooth
analytic locus. -/
abbrev IntegralCycleComponentLocalOrientation
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ) :=
  ∀ (z : CycleComponentAnalyticPoint V x),
    z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x →
      IntegralRelativeHomology (pointComplementPair z) n

/-- The local value of an integral Borel--Moore class of a compact cycle component. -/
def integralCycleComponentBorelMooreToLocal
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ)
    (z : CycleComponentAnalyticPoint V x) :
    IntegralCycleComponentBorelMooreHomology V x n →+
      IntegralRelativeHomology (pointComplementPair z) n :=
  integralCompactificationBorelMooreToLocal Set.univ n z (Set.mem_univ z)

/-- An integral component class is fundamental when its local values at smooth points are the
specified positive complex-orientation generators. -/
def IsIntegralCycleComponentBorelMooreFundamentalClass
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ)
    (orientation : IntegralCycleComponentLocalOrientation V x n)
    (c : IntegralCycleComponentBorelMooreHomology V x n) : Prop :=
  ∀ (z : CycleComponentAnalyticPoint V x)
      (hz : z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x),
    integralCycleComponentBorelMooreToLocal V x n z c = orientation z hz

/-- The uniquely normalized integral Borel--Moore fundamental class of a projective cycle
component, once the global existence and uniqueness theorem has been proved. -/
def integralCycleComponentBorelMooreFundamentalClass
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ)
    (orientation : IntegralCycleComponentLocalOrientation V x n)
    (h : ∃! c, IsIntegralCycleComponentBorelMooreFundamentalClass V x n orientation c) :
    IntegralCycleComponentBorelMooreHomology V x n :=
  Classical.choose h.exists

/-- The selected integral component class has its exact local normalization. -/
lemma integralCycleComponentBorelMooreFundamentalClass_isFundamental
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ)
    (orientation : IntegralCycleComponentLocalOrientation V x n)
    (h : ∃! c, IsIntegralCycleComponentBorelMooreFundamentalClass V x n orientation c) :
    IsIntegralCycleComponentBorelMooreFundamentalClass V x n orientation
      (integralCycleComponentBorelMooreFundamentalClass V x n orientation h) :=
  Classical.choose_spec h.exists

/-- Exact local normalization determines the integral component class uniquely. -/
lemma eq_integralCycleComponentBorelMooreFundamentalClass
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ)
    (orientation : IntegralCycleComponentLocalOrientation V x n)
    (h : ∃! c, IsIntegralCycleComponentBorelMooreFundamentalClass V x n orientation c)
    (c : IntegralCycleComponentBorelMooreHomology V x n)
    (hc : IsIntegralCycleComponentBorelMooreFundamentalClass V x n orientation c) :
    c = integralCycleComponentBorelMooreFundamentalClass V x n orientation h :=
  h.unique hc
    (integralCycleComponentBorelMooreFundamentalClass_isFundamental V x n orientation h)

/-- Borel--Moore homology of a projective analytic cycle component.  Compactness identifies it
with ordinary homology, presented uniformly as relative homology modulo the empty boundary. -/
abbrev CycleComponentBorelMooreHomology
    (R : Type) [Field R] (V : SmoothProjectiveComplexVariety)
    (x : V.scheme) (n : ℕ) : ModuleCat R :=
  CompactificationBorelMooreHomology R
    (Set.univᶜ : Set (CycleComponentAnalyticPoint V x)) n

/-- For a projective cycle component, the chosen compactification has empty boundary, so its
Borel--Moore homology is canonically ordinary singular homology. -/
def cycleComponentHomologyBorelMooreIso
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ) :
    Homology ℚ (TopCat.of (CycleComponentAnalyticPoint V x)) n ≅
      CycleComponentBorelMooreHomology ℚ V x n := by
  change Homology ℚ (TopCat.of (CycleComponentAnalyticPoint V x)) n ≅
    RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of (CycleComponentAnalyticPoint V x)) Set.univᶜ) n
  rw [Set.compl_univ]
  exact homologyEmptySubspaceIso ℚ
    (TopCat.of (CycleComponentAnalyticPoint V x)) n

/-- A family of exactly normalized local orientation classes on the smooth analytic locus of a
cycle component. -/
abbrev CycleComponentLocalOrientation
    (R : Type) [Field R] (V : SmoothProjectiveComplexVariety)
    (x : V.scheme) (n : ℕ) :=
  ∀ (z : CycleComponentAnalyticPoint V x),
    z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x →
      RelativeHomology R (pointComplementPair z) n

/-- The local value of a Borel--Moore class of a compact cycle component. -/
def cycleComponentBorelMooreToLocal
    (R : Type) [Field R] (V : SmoothProjectiveComplexVariety)
    (x : V.scheme) (n : ℕ) (z : CycleComponentAnalyticPoint V x) :
    CycleComponentBorelMooreHomology R V x n →ₗ[R]
      RelativeHomology R (pointComplementPair z) n :=
  compactificationBorelMooreToLocal R Set.univ n z (Set.mem_univ z)

/-- A component class is its oriented Borel--Moore fundamental class when its local value at
every smooth point is exactly the specified complex-orientation class. -/
def IsCycleComponentBorelMooreFundamentalClass
    (R : Type) [Field R] (V : SmoothProjectiveComplexVariety)
    (x : V.scheme) (n : ℕ)
    (orientation : CycleComponentLocalOrientation R V x n)
    (c : CycleComponentBorelMooreHomology R V x n) : Prop :=
  ∀ (z : CycleComponentAnalyticPoint V x)
      (hz : z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x),
    cycleComponentBorelMooreToLocal R V x n z c = orientation z hz

/-- The Borel--Moore fundamental class of a projective cycle component, selected after the
existence and uniqueness theorem has established its exact local normalization. -/
def cycleComponentBorelMooreFundamentalClass
    (R : Type) [Field R] (V : SmoothProjectiveComplexVariety)
    (x : V.scheme) (n : ℕ)
    (orientation : CycleComponentLocalOrientation R V x n)
    (h : ∃! c, IsCycleComponentBorelMooreFundamentalClass R V x n orientation c) :
    CycleComponentBorelMooreHomology R V x n :=
  Classical.choose h.exists

/-- The selected component class has the required local orientation at every smooth point. -/
lemma cycleComponentBorelMooreFundamentalClass_isFundamental
    (R : Type) [Field R] (V : SmoothProjectiveComplexVariety)
    (x : V.scheme) (n : ℕ)
    (orientation : CycleComponentLocalOrientation R V x n)
    (h : ∃! c, IsCycleComponentBorelMooreFundamentalClass R V x n orientation c) :
    IsCycleComponentBorelMooreFundamentalClass R V x n orientation
      (cycleComponentBorelMooreFundamentalClass R V x n orientation h) :=
  Classical.choose_spec h.exists

/-- Exact local normalization determines the component fundamental class uniquely. -/
lemma eq_cycleComponentBorelMooreFundamentalClass
    (R : Type) [Field R] (V : SmoothProjectiveComplexVariety)
    (x : V.scheme) (n : ℕ)
    (orientation : CycleComponentLocalOrientation R V x n)
    (h : ∃! c, IsCycleComponentBorelMooreFundamentalClass R V x n orientation c)
    (c : CycleComponentBorelMooreHomology R V x n)
    (hc : IsCycleComponentBorelMooreFundamentalClass R V x n orientation c) :
    c = cycleComponentBorelMooreFundamentalClass R V x n orientation h :=
  h.unique hc
    (cycleComponentBorelMooreFundamentalClass_isFundamental R V x n orientation h)

@[simp]
lemma cycleComponentBorelMooreToLocal_fundamentalClass
    (R : Type) [Field R] (V : SmoothProjectiveComplexVariety)
    (x : V.scheme) (n : ℕ)
    (orientation : CycleComponentLocalOrientation R V x n)
    (h : ∃! c, IsCycleComponentBorelMooreFundamentalClass R V x n orientation c)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x) :
    cycleComponentBorelMooreToLocal R V x n z
        (cycleComponentBorelMooreFundamentalClass R V x n orientation h) =
      orientation z hz :=
  cycleComponentBorelMooreFundamentalClass_isFundamental R V x n orientation h z hz

/-! ### Fundamental classes of zero-dimensional components -/

/-- A codimension-`d` component in a smooth complex `d`-fold has at most one complex point.
This is derived from the component's Krull dimension, rather than imposed as data. -/
lemma cycleComponentAnalyticPoint_subsingleton_of_coheight_eq_dimension
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = d) :
    Subsingleton (CycleComponentAnalyticPoint V x) := by
  have hdim : Order.krullDim (cycleComponent V.scheme x) = 0 := by
    simpa using orderKrullDim_cycleComponent_eq_zero_of_coheight_eq_dimension
      (f := V.structureMap) (d := d) x hx
  let : Subsingleton (cycleComponent V.scheme x) := by
    constructor
    intro a b
    have hallMin : ∀ q : cycleComponent V.scheme x, IsMin q :=
      Order.krullDim_nonpos_iff_forall_isMin.mp hdim.le
    have htopLe (q : cycleComponent V.scheme x) :
        (⊤ : cycleComponent V.scheme x) ≤ q :=
      hallMin ⊤ le_top
    have hab : a ≤ b := le_top.trans (htopLe b)
    have hba : b ≤ a := le_top.trans (htopLe a)
    apply inseparable_iff_eq.mp
    rw [inseparable_iff_specializes_and, ← Scheme.le_iff_specializes,
      ← Scheme.le_iff_specializes]
    exact ⟨hba, hab⟩
  constructor
  intro a b
  apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
  exact Subsingleton.elim a.underlying b.underlying

/-- In maximal codimension the global Borel--Moore fundamental class is constructed directly.
The component is a one-point space, so restriction from its homology to local homology is an
isomorphism; the inverse sends the explicit complex local orientation to the required global
class.  No global fundamental-class theorem is used. -/
theorem existsUnique_cycleComponentBorelMooreFundamentalClass_of_coheight_eq_dimension
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = d) :
    ∃! c, IsCycleComponentBorelMooreFundamentalClass
      ℚ V x (2 * (d - d))
        (cycleComponentComplexLocalOrientation V x d d hx) c := by
  let : TopologicalSpace (CycleComponentAnalyticPoint V x) :=
    Point.analyticTopology
  let : Subsingleton (CycleComponentAnalyticPoint V x) :=
    cycleComponentAnalyticPoint_subsingleton_of_coheight_eq_dimension V x d hx
  obtain ⟨z, hz⟩ := exists_cycleComponent_smooth_complexPoint V.structureMap x
  let orientation := cycleComponentComplexLocalOrientation V x d d hx
  let e := compactificationBorelMooreToLocalEquivOfSubsingleton ℚ z (2 * (d - d))
  let c : CycleComponentBorelMooreHomology ℚ V x (2 * (d - d)) :=
    e.symm (orientation z hz)
  have hc : IsCycleComponentBorelMooreFundamentalClass
      ℚ V x (2 * (d - d)) orientation c := by
    intro w hw
    have hwz : w = z := Subsingleton.elim w z
    subst w
    have hproof : hw = hz := Subsingleton.elim hw hz
    subst hw
    change e c = orientation z hz
    exact e.apply_symm_apply (orientation z hz)
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply e.injective
  change e c' = e c
  exact (hc' z hz).trans (hc z hz).symm

/-- The remaining rational Borel--Moore fundamental-class theorem for a codimension-`p`
component of a smooth complex `d`-fold. The exact local complex orientation is constructed, not
stored in this structure; this field is only the global existence-and-uniqueness theorem which
must be discharged by oriented-manifold Borel--Moore homology. -/
structure RationalCycleComponentBorelMooreData
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p) where
  /-- The localization and dimension theorem producing a unique global Borel--Moore class. -/
  existsUnique_fundamentalClass :
    ∃! c, IsCycleComponentBorelMooreFundamentalClass
      ℚ V x (2 * (d - p))
        (cycleComponentComplexLocalOrientation V x d p hx) c

/-- The rational Borel--Moore data of a maximal-codimension component is constructed from the
one-point calculation, with no theorem-valued input. -/
theorem rationalCycleComponentBorelMooreDataOfCoheightEqDimension
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = d) :
    RationalCycleComponentBorelMooreData V x d d hx where
  existsUnique_fundamentalClass :=
    existsUnique_cycleComponentBorelMooreFundamentalClass_of_coheight_eq_dimension
      V x d hx

namespace RationalCycleComponentBorelMooreData

/-- The constructed exact local complex orientation used to normalize the component class. -/
def localOrientation
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (_D : RationalCycleComponentBorelMooreData V x d p hx) :
    CycleComponentLocalOrientation ℚ V x (2 * (d - p)) :=
  cycleComponentComplexLocalOrientation V x d p hx

/-- Every value of the constructed local orientation is an exact generator of top local
homology; this property is proved from the explicit complex chart class. -/
theorem span_localOrientation_eq_top
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentBorelMooreData V x d p hx)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x) :
    Submodule.span ℚ {D.localOrientation z hz} = ⊤ :=
  span_cycleComponentComplexLocalOrientation_eq_top V x d p hx z hz

/-- The distinguished rational Borel--Moore fundamental class supplied by the global
existence-and-uniqueness theorem and normalized by the constructed local orientation. -/
def fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentBorelMooreData V x d p hx) :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) :=
  cycleComponentBorelMooreFundamentalClass ℚ V x (2 * (d - p))
    D.localOrientation D.existsUnique_fundamentalClass

/-- The distinguished class has exactly the positive complex local orientation. -/
lemma fundamentalClass_isFundamental
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentBorelMooreData V x d p hx) :
    IsCycleComponentBorelMooreFundamentalClass
      ℚ V x (2 * (d - p)) D.localOrientation D.fundamentalClass :=
  cycleComponentBorelMooreFundamentalClass_isFundamental ℚ V x (2 * (d - p))
    D.localOrientation D.existsUnique_fundamentalClass

/-- Any class with the same exact local complex orientation is the distinguished fundamental
class.  In particular, the construction does not retain a choice up to a nonzero rational
multiple. -/
lemma eq_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentBorelMooreData V x d p hx)
    (c : CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)))
    (hc : IsCycleComponentBorelMooreFundamentalClass
      ℚ V x (2 * (d - p)) D.localOrientation c) :
    c = D.fundamentalClass :=
  eq_cycleComponentBorelMooreFundamentalClass ℚ V x (2 * (d - p))
    D.localOrientation D.existsUnique_fundamentalClass c hc

@[simp]
lemma toLocal_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentBorelMooreData V x d p hx)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x) :
    cycleComponentBorelMooreToLocal ℚ V x (2 * (d - p)) z D.fundamentalClass =
      D.localOrientation z hz :=
  D.fundamentalClass_isFundamental z hz

end RationalCycleComponentBorelMooreData

end AlgebraicGeometry.ComplexPoint
