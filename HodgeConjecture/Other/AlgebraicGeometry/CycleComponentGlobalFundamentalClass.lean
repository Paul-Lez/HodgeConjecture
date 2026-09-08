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

public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentBorelMoore
public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentLocalOrientationCoherence
public import HodgeConjecture.Other.AlgebraicTopology.GlobalFundamentalClass
public import HodgeConjecture.Other.AlgebraicTopology.RelativeHomotopyInvariance

/-!
# Global cycle-component classes from one local class

This file reduces the rational Borel--Moore fundamental class of a positive-dimensional cycle
component to explicit local-to-global inputs.  Exactness constructs an absolute class from the
boundary-zero local orientation at one smooth point.  Vanishing of top homology of the punctured
component makes that lift unique.  A separately named propagation statement, normally proved by
relative Mayer--Vietoris on the smooth locus, identifies its local values at all smooth points.

No global class or existence-and-uniqueness assertion is included among the inputs.

The remaining geometric inputs are visible in
`RationalCycleComponentGlobalFundamentalClassInputs`:

* a smooth anchor and vanishing of the boundary of its explicit chart-constructed local class;
* vanishing of top homology of the component punctured at that anchor;
* `CycleComponentLocalOrientationPropagatesFrom`, the relative Mayer--Vietoris propagation
  theorem from the anchor to every smooth point.

The successor witness for the top degree restricts this construction to positive-dimensional
components.  A degree-zero analogue needs the bottom end of the relative long exact sequence,
which is not presently exposed by the singular-homology API used here.

Two stronger input packages remove derived conclusions from the stored data:

* `RationalCycleComponentInjectiveBoundaryInputs` replaces boundary-zero by injectivity of the
  punctured-space inclusion in the preceding degree;
* `RationalCycleComponentBoundedModelInputs` additionally replaces punctured top-homology
  vanishing by a quasi-isomorphic chain model whose top chain group is zero.

Both packages continue to retain propagation explicitly, since producing that theorem is the
remaining dimension-controlled Mayer--Vietoris or triangulation argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

noncomputable local instance cycleComponentAnalyticTopology'
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    TopologicalSpace (CycleComponentAnalyticPoint V x) :=
  Point.analyticTopology

/-- Passing from ordinary homology to the empty-boundary Borel--Moore presentation commutes
with restriction to local homology at a point. -/
lemma cycleComponentBorelMooreToLocal_relativeHomologyProjection
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ)
    (z : CycleComponentAnalyticPoint V x)
    (c : Homology ℚ (TopCat.of (CycleComponentAnalyticPoint V x)) n) :
    cycleComponentBorelMooreToLocal ℚ V x n z
        ((relativeHomologyProjection ℚ
          (TopPair.ofSubset (X := TopCat.of (CycleComponentAnalyticPoint V x))
            Set.univᶜ) n).hom c) =
      pointLocalHomologyRestriction n z c := by
  let a := compactificationToPointComplementPair
    (Set.univ : Set (CycleComponentAnalyticPoint V x)) z (Set.mem_univ z)
  have hnat := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) a
  have hhom := congrArg (fun f ↦ HomologicalComplex.homologyMap f n) hnat
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hhom
  change (relativeHomologyMap ℚ n a)
      ((relativeHomologyProjection ℚ
        (TopPair.ofSubset (X := TopCat.of (CycleComponentAnalyticPoint V x)) Set.univᶜ) n).hom c) =
    (relativeHomologyProjection ℚ (pointComplementPair z) n).hom c
  have happ := ConcreteCategory.congr_hom hhom c
  simp only [ModuleCat.hom_comp] at happ
  change (relativeHomologyMap ℚ n a)
      ((relativeHomologyProjection ℚ
        (TopPair.ofSubset (X := TopCat.of (CycleComponentAnalyticPoint V x)) Set.univᶜ) n).hom c) =
    (relativeHomologyProjection ℚ (pointComplementPair z) n).hom
      (homologyMap ℚ n (TopPair.Hom.fst a) c) at happ
  have hafst : TopPair.Hom.fst a =
      𝟙 (TopCat.of (CycleComponentAnalyticPoint V x)) := by rfl
  rw [hafst] at happ
  have hid : homologyMap ℚ n
      (𝟙 (TopCat.of (CycleComponentAnalyticPoint V x))) c = c := by
    simp only [homologyMap_id, LinearMap.id_apply]
  exact happ.trans (congrArg
    (fun u ↦ (relativeHomologyProjection ℚ (pointComplementPair z) n).hom u) hid)

/-- The absolute-to-relative map for the empty boundary of a projective component is
surjective. -/
lemma cycleComponent_relativeHomologyProjection_surjective
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ) :
    Function.Surjective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := TopCat.of (CycleComponentAnalyticPoint V x)) Set.univᶜ) n).hom := by
  rw [Set.compl_univ]
  exact (ConcreteCategory.isIso_iff_bijective
    (homologyEmptySubspaceIso ℚ
      (TopCat.of (CycleComponentAnalyticPoint V x)) n).hom).mp
        (homologyEmptySubspaceIso ℚ
          (TopCat.of (CycleComponentAnalyticPoint V x)) n).isIso_hom |>.2

/-- A local orientation propagates from a fixed smooth point when every absolute class having
the prescribed value there has the prescribed value at every smooth point.  This is the precise
relative Mayer--Vietoris input needed below; it does not assert that such an absolute class
exists. -/
def CycleComponentLocalOrientationPropagatesFrom
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ)
    (orientation : CycleComponentLocalOrientation ℚ V x n)
    (anchor : CycleComponentAnalyticPoint V x)
    (hanchor : anchor ∈ cycleComponentSmoothAnalyticLocus V.structureMap x) : Prop :=
  ∀ c : Homology ℚ (TopCat.of (CycleComponentAnalyticPoint V x)) n,
    pointLocalHomologyRestriction n anchor c = orientation anchor hanchor →
      ∀ (z : CycleComponentAnalyticPoint V x)
        (hz : z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x),
        pointLocalHomologyRestriction n z c = orientation z hz

/-- Geometric context shared by the alternative global fundamental-class input packages.  It
chooses an anchor, identifies the predecessor of the positive top degree, and retains the
Mayer--Vietoris propagation theorem. -/
structure RationalCycleComponentGlobalFundamentalClassCore
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p) where
  /-- A smooth point at which the global class is first lifted. -/
  anchor : CycleComponentAnalyticPoint V x
  /-- The anchor lies in the smooth analytic locus. -/
  anchor_mem_smoothLocus : anchor ∈ cycleComponentSmoothAnalyticLocus V.structureMap x
  /-- The degree immediately below the positive top degree. -/
  boundaryDegree : ℕ
  /-- The component top degree is the successor of the boundary degree. -/
  boundaryDegree_succ : boundaryDegree + 1 = 2 * (d - p)
  /-- The local orientation propagates from the anchor through the smooth locus. -/
  localOrientation_propagates :
    CycleComponentLocalOrientationPropagatesFrom V x (2 * (d - p))
      (cycleComponentComplexLocalOrientation V x d p hx)
      anchor anchor_mem_smoothLocus

/-- Explicit geometric inputs for constructing the rational Borel--Moore fundamental class of
a positive-dimensional cycle component.  The fields contain no global class and no
existence-and-uniqueness assertion. -/
structure RationalCycleComponentGlobalFundamentalClassInputs
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p)
    extends RationalCycleComponentGlobalFundamentalClassCore V x d p hx where
  /-- The explicitly constructed local orientation at the anchor is a relative cycle. -/
  anchor_boundary_eq_zero :
    (relativeSingularBoundary (pointComplementPair anchor) boundaryDegree).hom
      (boundaryDegree_succ.symm ▸
        cycleComponentComplexLocalOrientation V x d p hx
          anchor anchor_mem_smoothLocus) = 0
  /-- Top homology of the punctured component vanishes, making restriction at the anchor
  injective. -/
  puncturedTopHomology_isZero :
    IsZero (Homology ℚ (pointComplementPair anchor).snd (2 * (d - p)))

/-- Alternative input package in which boundary vanishing is derived from injectivity of the
point-complement inclusion one degree below the top local class. -/
structure RationalCycleComponentInjectiveBoundaryInputs
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p)
    extends RationalCycleComponentGlobalFundamentalClassCore V x d p hx where
  /-- Inclusion of the punctured component into the component is injective in the boundary
  degree. -/
  complementInclusion_injective :
    Function.Injective (pointComplementHomologyInclusion boundaryDegree anchor)
  /-- Top homology of the punctured component vanishes. -/
  puncturedTopHomology_isZero :
    IsZero (Homology ℚ (pointComplementPair anchor).snd (2 * (d - p)))

/-- Stronger geometric input package in which punctured top-homology vanishing is itself derived
from a bounded chain model quasi-isomorphic to singular chains. -/
structure RationalCycleComponentBoundedModelInputs
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p)
    extends RationalCycleComponentGlobalFundamentalClassCore V x d p hx where
  /-- Inclusion of the punctured component is injective in the boundary degree. -/
  complementInclusion_injective :
    Function.Injective (pointComplementHomologyInclusion boundaryDegree anchor)
  /-- A dimension-bounded chain model for the punctured component. -/
  chainModel : ChainComplex (ModuleCat ℚ) ℕ
  /-- Comparison from the bounded model to rational singular chains. -/
  chainModelMap : chainModel ⟶
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj (pointComplementPair anchor).snd
  /-- The bounded-model comparison is a quasi-isomorphism. -/
  chainModelMap_quasiIso : QuasiIso chainModelMap
  /-- The chain model has no chains in the component's top degree. -/
  topChainGroup_isZero : IsZero (chainModel.X (2 * (d - p)))

namespace RationalCycleComponentInjectiveBoundaryInputs

/-- Convert injective puncture-inclusion data to the boundary-cycle input package.  Boundary
vanishing is a consequence of the pair long exact sequence. -/
def toGlobalInputs
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentInjectiveBoundaryInputs V x d p hx) :
    RationalCycleComponentGlobalFundamentalClassInputs V x d p hx where
  toRationalCycleComponentGlobalFundamentalClassCore :=
    D.toRationalCycleComponentGlobalFundamentalClassCore
  anchor_boundary_eq_zero := by
    have hδ := pointRelativeSingularBoundary_eq_zero_of_injective_complementInclusion
      D.boundaryDegree D.anchor D.complementInclusion_injective
    simpa using ConcreteCategory.congr_hom hδ
      (D.boundaryDegree_succ.symm ▸
        cycleComponentComplexLocalOrientation V x d p hx
          D.anchor D.anchor_mem_smoothLocus)
  puncturedTopHomology_isZero := D.puncturedTopHomology_isZero

end RationalCycleComponentInjectiveBoundaryInputs

namespace RationalCycleComponentBoundedModelInputs

/-- A bounded punctured-space chain model supplies the top-homology vanishing field of the
injective-boundary package. -/
def toInjectiveBoundaryInputs
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentBoundedModelInputs V x d p hx) :
    RationalCycleComponentInjectiveBoundaryInputs V x d p hx where
  toRationalCycleComponentGlobalFundamentalClassCore :=
    D.toRationalCycleComponentGlobalFundamentalClassCore
  complementInclusion_injective := D.complementInclusion_injective
  puncturedTopHomology_isZero := by
    let : QuasiIso D.chainModelMap := D.chainModelMap_quasiIso
    exact pointComplementHomology_isZero_of_bounded_chainModel
      (2 * (d - p)) D.anchor D.chainModel D.chainModelMap D.topChainGroup_isZero

/-- Convert bounded-model inputs all the way to the boundary-cycle package used by the global
construction. -/
def toGlobalInputs
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentBoundedModelInputs V x d p hx) :
    RationalCycleComponentGlobalFundamentalClassInputs V x d p hx :=
  D.toInjectiveBoundaryInputs.toGlobalInputs

end RationalCycleComponentBoundedModelInputs

namespace RationalCycleComponentGlobalFundamentalClassInputs

/-- The exact chart-constructed local orientation used by the global construction. -/
abbrev localOrientation
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (_D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx) :
    CycleComponentLocalOrientation ℚ V x (2 * (d - p)) :=
  cycleComponentComplexLocalOrientation V x d p hx

/-- By chart coherence, the orientation used in the global construction can be computed from
any exact component-coordinate package centered at the point. -/
lemma localOrientation_eq_componentLocalOrientationClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x)
    (C : CycleComponentSeparateLocalCoordinates V.structureMap x d (d - p))
    (hpoint : C.point = z) :
    D.localOrientation z hz = hpoint ▸ C.componentLocalOrientationClass :=
  (AlgebraicGeometry.CycleComponentSeparateLocalCoordinates.componentLocalOrientationClass_eq_cycleComponentComplexLocalOrientation
    p C hx z hz hpoint).symm

private lemma pointLocalHomologyRestriction_transport_degree
    {M : Type} [TopologicalSpace M] {m n : ℕ} (h : m = n)
    (z : M) (c : Homology ℚ (TopCat.of M) m) :
    pointLocalHomologyRestriction n z (h ▸ c) =
      h ▸ pointLocalHomologyRestriction m z c := by
  subst n
  rfl

private lemma transport_symm
    {A : Type} (F : A → Type) {a b : A} (h : a = b) (u : F b) :
    h ▸ (h.symm ▸ u) = u := by
  subst b
  rfl

/-- The absolute top-homology class obtained by lifting the anchor's local orientation through
the long exact sequence of its point-complement pair. -/
def ordinaryFundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx) :
    Homology ℚ (TopCat.of (CycleComponentAnalyticPoint V x)) (2 * (d - p)) :=
  D.boundaryDegree_succ ▸
    globalClassOfPointLocalClass D.boundaryDegree D.anchor
      (D.boundaryDegree_succ.symm ▸
        D.localOrientation D.anchor D.anchor_mem_smoothLocus)
      D.anchor_boundary_eq_zero

/-- The exactness lift has the prescribed local value at its anchor. -/
lemma pointLocalHomologyRestriction_ordinaryFundamentalClass_anchor
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx) :
    pointLocalHomologyRestriction (2 * (d - p)) D.anchor
        D.ordinaryFundamentalClass =
      D.localOrientation D.anchor D.anchor_mem_smoothLocus := by
  let h := D.boundaryDegree_succ
  let c := h.symm ▸ D.localOrientation D.anchor D.anchor_mem_smoothLocus
  let g := globalClassOfPointLocalClass D.boundaryDegree D.anchor c
    D.anchor_boundary_eq_zero
  change pointLocalHomologyRestriction (2 * (d - p)) D.anchor (h ▸ g) = _
  calc
    _ = h ▸ pointLocalHomologyRestriction (D.boundaryDegree + 1) D.anchor g :=
      pointLocalHomologyRestriction_transport_degree h D.anchor g
    _ = h ▸ c := congrArg (fun u ↦ h ▸ u)
      (pointLocalHomologyRestriction_globalClassOfPointLocalClass
        D.boundaryDegree D.anchor c D.anchor_boundary_eq_zero)
    _ = D.localOrientation D.anchor D.anchor_mem_smoothLocus :=
      transport_symm
        (fun k ↦ RelativeHomology ℚ (pointComplementPair D.anchor) k)
        h (D.localOrientation D.anchor D.anchor_mem_smoothLocus)

/-- The anchor normalization propagates to every smooth point. -/
lemma pointLocalHomologyRestriction_ordinaryFundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x) :
    pointLocalHomologyRestriction (2 * (d - p)) z
        D.ordinaryFundamentalClass = D.localOrientation z hz :=
  D.localOrientation_propagates D.ordinaryFundamentalClass
    D.pointLocalHomologyRestriction_ordinaryFundamentalClass_anchor z hz

/-- The Borel--Moore class is the image of the exactness lift under the absolute-to-relative map
for the component's empty boundary. -/
def fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx) :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) :=
  (relativeHomologyProjection ℚ
    (TopPair.ofSubset (X := TopCat.of (CycleComponentAnalyticPoint V x)) Set.univᶜ)
      (2 * (d - p))).hom D.ordinaryFundamentalClass

@[simp]
lemma cycleComponentBorelMooreToLocal_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.structureMap x) :
    cycleComponentBorelMooreToLocal ℚ V x (2 * (d - p)) z D.fundamentalClass =
      D.localOrientation z hz := by
  rw [fundamentalClass,
    cycleComponentBorelMooreToLocal_relativeHomologyProjection]
  exact D.pointLocalHomologyRestriction_ordinaryFundamentalClass z hz

/-- Restriction of Borel--Moore top homology to the anchor is injective.  This is derived from
punctured top-homology vanishing, not retained as a separate input. -/
theorem cycleComponentBorelMooreToLocal_anchor_injective
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx) :
    Function.Injective (cycleComponentBorelMooreToLocal ℚ V x
      (2 * (d - p)) D.anchor) := by
  intro c c' hcc'
  obtain ⟨a, rfl⟩ := cycleComponent_relativeHomologyProjection_surjective
    V x (2 * (d - p)) c
  obtain ⟨a', rfl⟩ := cycleComponent_relativeHomologyProjection_surjective
    V x (2 * (d - p)) c'
  change Homology ℚ (TopCat.of (CycleComponentAnalyticPoint V x))
    (2 * (d - p)) at a a'
  rw [cycleComponentBorelMooreToLocal_relativeHomologyProjection,
    cycleComponentBorelMooreToLocal_relativeHomologyProjection] at hcc'
  have haa' : a = a' :=
    relativeHomologyProjection_injective_of_isZero_subspace_degree
      (pointComplementPair D.anchor) (2 * (d - p))
        D.puncturedTopHomology_isZero hcc'
  exact congrArg (fun u ↦ (relativeHomologyProjection ℚ
    (TopPair.ofSubset (X := TopCat.of (CycleComponentAnalyticPoint V x)) Set.univᶜ)
      (2 * (d - p))).hom u) haa'

/-- The constructed Borel--Moore class has exactly the prescribed orientation at every smooth
point. -/
theorem fundamentalClass_isFundamental
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx) :
    IsCycleComponentBorelMooreFundamentalClass ℚ V x (2 * (d - p))
      D.localOrientation D.fundamentalClass :=
  D.cycleComponentBorelMooreToLocal_fundamentalClass

/-- Exact local normalization determines the class constructed from the geometric inputs. -/
theorem eq_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx)
    (c : CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)))
    (hc : IsCycleComponentBorelMooreFundamentalClass ℚ V x (2 * (d - p))
      D.localOrientation c) :
    c = D.fundamentalClass := by
  apply D.cycleComponentBorelMooreToLocal_anchor_injective
  exact (hc D.anchor D.anchor_mem_smoothLocus).trans
    (D.cycleComponentBorelMooreToLocal_fundamentalClass
      D.anchor D.anchor_mem_smoothLocus).symm

/-- The explicit geometric inputs imply existence and uniqueness of the normalized
Borel--Moore fundamental class. -/
theorem existsUnique_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx) :
    ∃! c, IsCycleComponentBorelMooreFundamentalClass ℚ V x (2 * (d - p))
      D.localOrientation c := by
  refine ⟨D.fundamentalClass, D.fundamentalClass_isFundamental, ?_⟩
  exact D.eq_fundamentalClass

end RationalCycleComponentGlobalFundamentalClassInputs

namespace RationalCycleComponentBorelMooreData

/-- Compatibility constructor for downstream code phrased using
`RationalCycleComponentBorelMooreData`.  Its `∃!` theorem is derived from the geometric inputs
rather than supplied as one of them. -/
theorem ofGlobalInputs
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx) :
    RationalCycleComponentBorelMooreData V x d p hx where
  existsUnique_fundamentalClass := D.existsUnique_fundamentalClass

/-- Construct the legacy Borel--Moore data interface from puncture-inclusion injectivity,
punctured top-homology vanishing, and propagation. -/
theorem ofInjectiveBoundaryInputs
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentInjectiveBoundaryInputs V x d p hx) :
    RationalCycleComponentBorelMooreData V x d p hx :=
  ofGlobalInputs D.toGlobalInputs

/-- Construct the legacy Borel--Moore data interface when punctured top-homology vanishing is
certified by a bounded chain model. -/
theorem ofBoundedModelInputs
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentBoundedModelInputs V x d p hx) :
    RationalCycleComponentBorelMooreData V x d p hx :=
  ofGlobalInputs D.toGlobalInputs

/-- The compatibility constructor selects the class built directly from exactness and
propagation. -/
lemma ofGlobalInputs_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentGlobalFundamentalClassInputs V x d p hx) :
    (ofGlobalInputs D).fundamentalClass = D.fundamentalClass := by
  symm
  apply (ofGlobalInputs D).eq_fundamentalClass
  exact D.fundamentalClass_isFundamental

/-- The injective-boundary adapter selects the exactness-and-propagation construction. -/
lemma ofInjectiveBoundaryInputs_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentInjectiveBoundaryInputs V x d p hx) :
    (ofInjectiveBoundaryInputs D).fundamentalClass =
      D.toGlobalInputs.fundamentalClass :=
  ofGlobalInputs_fundamentalClass D.toGlobalInputs

/-- The bounded-model adapter selects the exactness-and-propagation construction. -/
lemma ofBoundedModelInputs_fundamentalClass
    {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] {hx : Order.coheight x = p}
    (D : RationalCycleComponentBoundedModelInputs V x d p hx) :
    (ofBoundedModelInputs D).fundamentalClass =
      D.toGlobalInputs.fundamentalClass :=
  ofGlobalInputs_fundamentalClass D.toGlobalInputs

end RationalCycleComponentBorelMooreData

end AlgebraicGeometry.ComplexPoint
