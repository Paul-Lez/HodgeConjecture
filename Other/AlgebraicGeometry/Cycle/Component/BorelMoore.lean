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

public import Other.AlgebraicGeometry.Cycle.Component.AnalyticEmbedding
public import Other.AlgebraicGeometry.Cycle.Component.LocalOrientation
public import Other.AlgebraicTopology.Singular.BorelMoore
public import Other.AlgebraicTopology.Singular.EmptySubspace

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
public import Other.AlgebraicGeometry.ComplexPoint.ClosedImmersion
public import Other.AlgebraicGeometry.Cycle.Component.NormalCoordinates
public import Other.AlgebraicGeometry.Cycle.Support

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
abbrev ClosedEmbeddingAnalyticPoint
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] :=
  ComplexPoint (Y)

/-- Integral Borel--Moore homology of a projective analytic cycle component. -/
abbrev IntegralClosedEmbeddingBorelMooreHomology
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ) : AddCommGrpCat :=
  IntegralCompactificationBorelMooreHomology
    (Set.univᶜ : Set (ClosedEmbeddingAnalyticPoint V i)) n

/-- A family of exactly normalized integral local orientation classes on the component's smooth
analytic locus. -/
abbrev IntegralClosedEmbeddingLocalOrientation
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ) :=
  ∀ (z : ClosedEmbeddingAnalyticPoint V i),
    z ∈ closedEmbeddingSmoothAnalyticLocus i →
      IntegralRelativeHomology (pointComplementPair z) n

/-- The local value of an integral Borel--Moore class of a compact cycle component. -/
def integralClosedEmbeddingBorelMooreToLocal
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (z : ClosedEmbeddingAnalyticPoint V i) :
    IntegralClosedEmbeddingBorelMooreHomology V i n →+
      IntegralRelativeHomology (pointComplementPair z) n :=
  integralCompactificationBorelMooreToLocal Set.univ n z (Set.mem_univ z)

/-- An integral component class is fundamental when its local values at smooth points are the
specified positive complex-orientation generators. -/
def IsIntegralClosedEmbeddingBorelMooreFundamentalClass
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (orientation : IntegralClosedEmbeddingLocalOrientation V i n)
    (c : IntegralClosedEmbeddingBorelMooreHomology V i n) : Prop :=
  ∀ (z : ClosedEmbeddingAnalyticPoint V i)
      (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i),
    integralClosedEmbeddingBorelMooreToLocal V i n z c = orientation z hz

/-- The uniquely normalized integral Borel--Moore fundamental class of a projective cycle
component, once the global existence and uniqueness theorem has been proved. -/
def integralClosedEmbeddingBorelMooreFundamentalClass
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (orientation : IntegralClosedEmbeddingLocalOrientation V i n)
    (h : ∃! c, IsIntegralClosedEmbeddingBorelMooreFundamentalClass V i n orientation c) :
    IntegralClosedEmbeddingBorelMooreHomology V i n :=
  Classical.choose h.exists

/-- The selected integral component class has its exact local normalization. -/
lemma integralClosedEmbeddingBorelMooreFundamentalClass_isFundamental
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (orientation : IntegralClosedEmbeddingLocalOrientation V i n)
    (h : ∃! c, IsIntegralClosedEmbeddingBorelMooreFundamentalClass V i n orientation c) :
    IsIntegralClosedEmbeddingBorelMooreFundamentalClass V i n orientation
      (integralClosedEmbeddingBorelMooreFundamentalClass V i n orientation h) :=
  Classical.choose_spec h.exists

/-- Exact local normalization determines the integral component class uniquely. -/
lemma eq_integralClosedEmbeddingBorelMooreFundamentalClass
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (orientation : IntegralClosedEmbeddingLocalOrientation V i n)
    (h : ∃! c, IsIntegralClosedEmbeddingBorelMooreFundamentalClass V i n orientation c)
    (c : IntegralClosedEmbeddingBorelMooreHomology V i n)
    (hc : IsIntegralClosedEmbeddingBorelMooreFundamentalClass V i n orientation c) :
    c = integralClosedEmbeddingBorelMooreFundamentalClass V i n orientation h :=
  h.unique hc
    (integralClosedEmbeddingBorelMooreFundamentalClass_isFundamental V i n orientation h)

/-- Borel--Moore homology of a projective analytic cycle component.  Compactness identifies it
with ordinary homology, presented uniformly as relative homology modulo the empty boundary. -/
abbrev ClosedEmbeddingBorelMooreHomology
    (R : Type) [CommRing R] (V : SmoothProjectiveComplexVariety)
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ) : ModuleCat R :=
  CompactificationBorelMooreHomology R
    (Set.univᶜ : Set (ClosedEmbeddingAnalyticPoint V i)) n

/-- A family of exactly normalized local orientation classes on the smooth analytic locus of a
cycle component. -/
abbrev ClosedEmbeddingLocalOrientation
    (R : Type) [CommRing R] (V : SmoothProjectiveComplexVariety)
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ) :=
  ∀ (z : ClosedEmbeddingAnalyticPoint V i),
    z ∈ closedEmbeddingSmoothAnalyticLocus i →
      RelativeHomology R (pointComplementPair z) n

/-- The local value of a Borel--Moore class of a compact cycle component. -/
def closedEmbeddingBorelMooreToLocal
    (R : Type) [CommRing R] (V : SmoothProjectiveComplexVariety)
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ) (z : ClosedEmbeddingAnalyticPoint V i) :
    ClosedEmbeddingBorelMooreHomology R V i n →ₗ[R]
      RelativeHomology R (pointComplementPair z) n :=
  compactificationBorelMooreToLocal R Set.univ n z (Set.mem_univ z)

/-- A component class is its oriented Borel--Moore fundamental class when its local value at
every smooth point is exactly the specified complex-orientation class. -/
def IsClosedEmbeddingBorelMooreFundamentalClass
    (R : Type) [CommRing R] (V : SmoothProjectiveComplexVariety)
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (orientation : ClosedEmbeddingLocalOrientation R V i n)
    (c : ClosedEmbeddingBorelMooreHomology R V i n) : Prop :=
  ∀ (z : ClosedEmbeddingAnalyticPoint V i)
      (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i),
    closedEmbeddingBorelMooreToLocal R V i n z c = orientation z hz

/-- The Borel--Moore fundamental class of a projective cycle component, selected after the
existence and uniqueness theorem has established its exact local normalization. -/
def closedEmbeddingBorelMooreFundamentalClass
    (R : Type) [CommRing R] (V : SmoothProjectiveComplexVariety)
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (orientation : ClosedEmbeddingLocalOrientation R V i n)
    (h : ∃! c, IsClosedEmbeddingBorelMooreFundamentalClass R V i n orientation c) :
    ClosedEmbeddingBorelMooreHomology R V i n :=
  Classical.choose h.exists

/-- The selected component class has the required local orientation at every smooth point. -/
lemma closedEmbeddingBorelMooreFundamentalClass_isFundamental
    (R : Type) [CommRing R] (V : SmoothProjectiveComplexVariety)
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (orientation : ClosedEmbeddingLocalOrientation R V i n)
    (h : ∃! c, IsClosedEmbeddingBorelMooreFundamentalClass R V i n orientation c) :
    IsClosedEmbeddingBorelMooreFundamentalClass R V i n orientation
      (closedEmbeddingBorelMooreFundamentalClass R V i n orientation h) :=
  Classical.choose_spec h.exists

/-- Exact local normalization determines the component fundamental class uniquely. -/
lemma eq_closedEmbeddingBorelMooreFundamentalClass
    (R : Type) [CommRing R] (V : SmoothProjectiveComplexVariety)
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (orientation : ClosedEmbeddingLocalOrientation R V i n)
    (h : ∃! c, IsClosedEmbeddingBorelMooreFundamentalClass R V i n orientation c)
    (c : ClosedEmbeddingBorelMooreHomology R V i n)
    (hc : IsClosedEmbeddingBorelMooreFundamentalClass R V i n orientation c) :
    c = closedEmbeddingBorelMooreFundamentalClass R V i n orientation h :=
  h.unique hc
    (closedEmbeddingBorelMooreFundamentalClass_isFundamental R V i n orientation h)

@[simp]
lemma closedEmbeddingBorelMooreToLocal_fundamentalClass
    (R : Type) [CommRing R] (V : SmoothProjectiveComplexVariety)
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ)
    (orientation : ClosedEmbeddingLocalOrientation R V i n)
    (h : ∃! c, IsClosedEmbeddingBorelMooreFundamentalClass R V i n orientation c)
    (z : ClosedEmbeddingAnalyticPoint V i)
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    closedEmbeddingBorelMooreToLocal R V i n z
        (closedEmbeddingBorelMooreFundamentalClass R V i n orientation h) =
      orientation z hz :=
  closedEmbeddingBorelMooreFundamentalClass_isFundamental R V i n orientation h z hz

/-! ### Fundamental classes of zero-dimensional components -/

/-- A codimension-`d` closed subvariety of a smooth complex `d`-fold has at most one complex
point. This is derived from its Krull dimension, rather than imposed as data. -/
lemma closedEmbeddingAnalyticPoint_subsingleton_of_coheight_eq_dimension
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = d) :
    Subsingleton (ClosedEmbeddingAnalyticPoint V i) := by
  have hdim : Order.krullDim (Y.left) = 0 := by
    simpa using orderKrullDim_closedEmbedding_eq_zero_of_coheight_eq_dimension
      (f := V.structureMap) (d := d) i.left hi
  let hcomponent : Subsingleton (Y.left) := by
    constructor
    intro a b
    have htopLe (q : Y.left) :
        (⊤ : Y.left) ≤ q :=
      Order.krullDim_nonpos_iff_forall_isMin.mp hdim.le ⊤ le_top
    apply inseparable_iff_eq.mp
    rw [inseparable_iff_specializes_and, ← Scheme.le_iff_specializes,
      ← Scheme.le_iff_specializes]
    exact ⟨le_top.trans (htopLe a), le_top.trans (htopLe b)⟩
  constructor
  intro a b
  let : LocallyOfFiniteType Y.hom := by
    rw [show Y.hom = i.left ≫ V.over.hom from (Over.w i).symm]
    infer_instance
  exact ComplexPoint.underlying_injective_of_locallyOfFiniteType
    (Subsingleton.elim a.underlying b.underlying)

/-- In maximal codimension the global Borel--Moore fundamental class is constructed directly.
The component is a one-point space, so restriction from its homology to local homology is an
isomorphism; the inverse sends the explicit complex local orientation to the required global
class.  No global fundamental-class theorem is used. -/
theorem existsUnique_closedEmbeddingBorelMooreFundamentalClass_of_coheight_eq_dimension
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = d) :
    ∃! c, IsClosedEmbeddingBorelMooreFundamentalClass
      ℚ V i (2 * (d - d))
        (closedEmbeddingComplexLocalOrientation V i d d hi) c := by
  let : TopologicalSpace (ClosedEmbeddingAnalyticPoint V i) :=
    Point.analyticTopology
  let : Subsingleton (ClosedEmbeddingAnalyticPoint V i) :=
    closedEmbeddingAnalyticPoint_subsingleton_of_coheight_eq_dimension V i d hi
  obtain ⟨z, hz⟩ := exists_closedEmbedding_smooth_complexPoint i
  let orientation := closedEmbeddingComplexLocalOrientation V i d d hi
  let e := compactificationBorelMooreToLocalEquivOfSubsingleton ℚ z (2 * (d - d))
  let c : ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - d)) :=
    e.symm (orientation z hz)
  have hc : IsClosedEmbeddingBorelMooreFundamentalClass
      ℚ V i (2 * (d - d)) orientation c := by
    intro w hw
    have hwz : w = z := Subsingleton.elim w z
    subst w
    have hproof : hw = hz := Subsingleton.elim hw hz
    subst hw
    exact e.apply_symm_apply (orientation z hz)
  exact ⟨c, hc, fun c' hc' ↦ e.injective ((hc' z hz).trans (hc z hz).symm)⟩

/-- The remaining rational Borel--Moore fundamental-class theorem for a codimension-`p`
component of a smooth complex `d`-fold. The exact local complex orientation is constructed, not
stored in this structure; this field is only the global existence-and-uniqueness theorem which
must be discharged by oriented-manifold Borel--Moore homology. -/
structure RationalClosedEmbeddingBorelMooreData
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = p) where
  /-- The localization and dimension theorem producing a unique global Borel--Moore class. -/
  existsUnique_fundamentalClass :
    ∃! c, IsClosedEmbeddingBorelMooreFundamentalClass
      ℚ V i (2 * (d - p))
        (closedEmbeddingComplexLocalOrientation V i d p hi) c

/-- The rational Borel--Moore data of a maximal-codimension component is constructed from the
one-point calculation, with no theorem-valued input. -/
theorem rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = d) :
    RationalClosedEmbeddingBorelMooreData V i d d hi where
  existsUnique_fundamentalClass :=
    existsUnique_closedEmbeddingBorelMooreFundamentalClass_of_coheight_eq_dimension
      V i d hi

/-- A maximal-codimension component carries rational Borel--Moore data.  The witness is the
one-point construction, so this existence statement holds for every smooth projective variety
and every point of maximal coheight. -/
theorem nonempty_rationalClosedEmbeddingBorelMooreData_of_coheight_eq_dimension
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = d) :
    Nonempty (RationalClosedEmbeddingBorelMooreData V i d d hi) :=
  ⟨rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi⟩

namespace RationalClosedEmbeddingBorelMooreData

/-- The constructed exact local complex orientation used to normalize the component class. -/
def localOrientation
    {V : SmoothProjectiveComplexVariety} {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over}
  [IsIntegral Y.left] [IsClosedImmersion i.left] {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hi : Order.coheight (closedEmbeddingGenericPoint i) = p}
    (_D : RationalClosedEmbeddingBorelMooreData V i d p hi) :
    ClosedEmbeddingLocalOrientation ℚ V i (2 * (d - p)) :=
  closedEmbeddingComplexLocalOrientation V i d p hi

/-- Every value of the constructed local orientation is an exact generator of top local
homology; this property is proved from the explicit complex chart class. -/
theorem span_localOrientation_eq_top
    {V : SmoothProjectiveComplexVariety} {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over}
  [IsIntegral Y.left] [IsClosedImmersion i.left] {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hi : Order.coheight (closedEmbeddingGenericPoint i) = p}
    (D : RationalClosedEmbeddingBorelMooreData V i d p hi)
    (z : ClosedEmbeddingAnalyticPoint V i)
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    Submodule.span ℚ {D.localOrientation z hz} = ⊤ :=
  span_closedEmbeddingComplexLocalOrientation_eq_top V i d p hi z hz

/-- The distinguished rational Borel--Moore fundamental class supplied by the global
existence-and-uniqueness theorem and normalized by the constructed local orientation. -/
def fundamentalClass
    {V : SmoothProjectiveComplexVariety} {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over}
  [IsIntegral Y.left] [IsClosedImmersion i.left] {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hi : Order.coheight (closedEmbeddingGenericPoint i) = p}
    (D : RationalClosedEmbeddingBorelMooreData V i d p hi) :
    ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - p)) :=
  closedEmbeddingBorelMooreFundamentalClass ℚ V i (2 * (d - p))
    D.localOrientation D.existsUnique_fundamentalClass

/-- The distinguished class has exactly the positive complex local orientation. -/
lemma fundamentalClass_isFundamental
    {V : SmoothProjectiveComplexVariety} {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over}
  [IsIntegral Y.left] [IsClosedImmersion i.left] {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hi : Order.coheight (closedEmbeddingGenericPoint i) = p}
    (D : RationalClosedEmbeddingBorelMooreData V i d p hi) :
    IsClosedEmbeddingBorelMooreFundamentalClass
      ℚ V i (2 * (d - p)) D.localOrientation D.fundamentalClass :=
  closedEmbeddingBorelMooreFundamentalClass_isFundamental ℚ V i (2 * (d - p))
    D.localOrientation D.existsUnique_fundamentalClass

/-- Any class with the same exact local complex orientation is the distinguished fundamental
class.  In particular, the construction does not retain a choice up to a nonzero rational
multiple. -/
lemma eq_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over}
  [IsIntegral Y.left] [IsClosedImmersion i.left] {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hi : Order.coheight (closedEmbeddingGenericPoint i) = p}
    (D : RationalClosedEmbeddingBorelMooreData V i d p hi)
    (c : ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - p)))
    (hc : IsClosedEmbeddingBorelMooreFundamentalClass
      ℚ V i (2 * (d - p)) D.localOrientation c) :
    c = D.fundamentalClass :=
  eq_closedEmbeddingBorelMooreFundamentalClass ℚ V i (2 * (d - p))
    D.localOrientation D.existsUnique_fundamentalClass c hc

@[simp]
lemma toLocal_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over}
  [IsIntegral Y.left] [IsClosedImmersion i.left] {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hi : Order.coheight (closedEmbeddingGenericPoint i) = p}
    (D : RationalClosedEmbeddingBorelMooreData V i d p hi)
    (z : ClosedEmbeddingAnalyticPoint V i)
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    closedEmbeddingBorelMooreToLocal ℚ V i (2 * (d - p)) z D.fundamentalClass =
      D.localOrientation z hz :=
  D.fundamentalClass_isFundamental z hz

end RationalClosedEmbeddingBorelMooreData

end AlgebraicGeometry.ComplexPoint
