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

public import HodgeConjecture.Mathlib.Algebra.Category.Ring.Basic
public import HodgeConjecture.Definitions.AlgebraicGeometry.ChowGroup
public import HodgeConjecture.Definitions.AlgebraicGeometry.Points
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothLocus
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Geometric support of algebraic cycles

An algebraic cycle in Mathlib is indexed by the generic points of its irreducible components.
This file constructs the reduced integral closed subscheme attached to such a point and the
corresponding closed subset of complex points. It also constructs the geometric support of a
whole cycle as the union of the closures of the generic points with nonzero coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

/-- An algebraic cycle on a projective complex variety has finite support. Algebraic cycles are
locally finite by definition, and the underlying Zariski space is compact. -/
lemma algebraicCycle_support_finite {R : Type*} [Zero R]
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (c : AlgebraicCycle X R) :
    c.support.Finite := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace structureMap
  have h := c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (W := Set.univ) isCompact_univ
  simpa using h

/-- The reduced closed subscheme whose underlying space is the closure of `x`. -/
def cycleComponent (X : Scheme) (x : X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subscheme

/-- The canonical closed immersion of the reduced closure of `x`. -/
def cycleComponentι (X : Scheme) (x : X) : cycleComponent X x ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι

instance (X : Scheme) (x : X) : IsClosedImmersion (cycleComponentι X x) := by
  change IsClosedImmersion
    ((Scheme.IdealSheafData.vanishingIdeal
      (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι)
  infer_instance

instance (X : Scheme) (x : X) : IsReduced (cycleComponent X x) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩
  change IsReduced I.subscheme
  rw [IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover]
  intro U
  let U' : X.affineOpens := U
  change IsReduced (Spec ↧(Γ(X, U') ⧸ I.ideal U'))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  change (PrimeSpectrum.vanishingIdeal (U'.2.fromSpec ⁻¹' closure {x})).IsRadical
  exact PrimeSpectrum.isRadical_vanishingIdeal _

instance (X : Scheme) (x : X) : IrreducibleSpace (cycleComponent X x) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩
  change IrreducibleSpace I.subscheme
  exact Subtype.irreducibleSpace isIrreducible_singleton.closure

instance (X : Scheme) (x : X) : IsIntegral (cycleComponent X x) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

@[simp]
lemma range_cycleComponentι (X : Scheme) (x : X) :
    Set.range (cycleComponentι X x) = closure {x} := by
  change Set.range
    ((Scheme.IdealSheafData.vanishingIdeal
      (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι) = closure {x}
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The kernel of a complex point is the vanishing ideal of the closure of its underlying scheme
point. -/
lemma complexPoint_ker_eq_vanishingIdeal_closure
    {X : Scheme} {structureMap : X ⟶ Spec ↧ℂ}
    (z : ComplexPoint X structureMap) :
    z.1.ker = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {z.underlying}, isClosed_closure⟩ := by
  have hrange : Set.range z.1 = {z.underlying} := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      have hs : s = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      subst s
      rfl
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨IsLocalRing.closedPoint ℂ, rfl⟩
  have h := Scheme.IdealSheafData.map_vanishingIdeal z.1
    (⊤ : TopologicalSpace.Closeds (Spec ↧ℂ))
  rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
    Scheme.IdealSheafData.map_bot] at h
  have himage : z.1 '' (↑(⊤ : TopologicalSpace.Closeds (Spec ↧ℂ)) :
      Set (Spec ↧ℂ)) = {z.underlying} := by
    simpa only [TopologicalSpace.Closeds.coe_top, Set.image_univ] using hrange
  rw [himage] at h
  exact h

/-- A cycle component of a projective variety is projective over `ℂ`. -/
instance cycleComponent_projective
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    IsProjective (cycleComponentι X x ≫ structureMap) := by
  rcases ‹IsProjective structureMap›.nonempty_presentation with ⟨P⟩
  exact ⟨⟨
    { ambientDimension := P.ambientDimension
      immersion := cycleComponentι X x ≫ P.immersion
      isClosedImmersion := by
        let _ := P.isClosedImmersion
        infer_instance
      immersion_toBase := by rw [Category.assoc, P.immersion_toBase] }
  ⟩⟩

/-- A cycle component of a projective complex variety is proper over `ℂ`. -/
noncomputable instance cycleComponent_isProper
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    IsProper (cycleComponentι X x ≫ structureMap) :=
  inferInstance

/-- A cycle component of a projective complex variety is locally of finite presentation over
`ℂ`. -/
noncomputable instance cycleComponent_locallyOfFinitePresentation
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    LocallyOfFinitePresentation (cycleComponentι X x ≫ structureMap) :=
  inferInstance

/-- The integral projective variety defined by one generic point of a smooth projective variety. -/
def cycleComponentVariety
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    IntegralProjectiveComplexVariety where
  scheme := cycleComponent X x
  isIntegral := inferInstance
  structureMap := cycleComponentι X x ≫ structureMap
  projective := cycleComponent_projective structureMap x

/-- The reduced closure of a point in a projective complex variety is Noetherian.

This is not an instance: the component does not determine the structure morphism carrying the
projectivity hypothesis. -/
theorem cycleComponent_isNoetherian
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    IsNoetherian (cycleComponent X x) := by
  change IsNoetherian (cycleComponentVariety structureMap x).scheme
  infer_instance

/-- The smooth locus of an integral cycle component is a smooth complex scheme. -/
theorem cycleComponent_smoothLocus_smooth
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    Smooth
      ((cycleComponentι X x ≫ structureMap).smoothLocus.ι ≫
        (cycleComponentι X x ≫ structureMap)) :=
  (cycleComponentι X x ≫ structureMap).smooth_restrict_smoothLocus

/-- Every integral cycle component has a complex point in its smooth locus. The smooth locus is
dense over the perfect field `ℂ`, and a projective complex variety has a closed point there. -/
theorem exists_cycleComponent_smooth_complexPoint
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    ∃ z : ComplexPoint (cycleComponent X x)
        (cycleComponentι X x ≫ structureMap),
      z.underlying ∈
        (cycleComponentι X x ≫ structureMap).smoothLocus := by
  let f := cycleComponentι X x ≫ structureMap
  let _ : JacobsonSpace (cycleComponent X x) :=
    LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty
    f.smoothLocus.2.isLocallyClosed
  let z := (pointEquivClosedPoint f).symm ⟨y, hyClosed⟩
  refine ⟨z, ?_⟩
  have hz := (pointEquivClosedPoint f).apply_symm_apply ⟨y, hyClosed⟩
  have hz' : z.1 (IsLocalRing.closedPoint ℂ) = y := congrArg Subtype.val hz
  rw [show Point.underlying z =
      z.1 (IsLocalRing.closedPoint ℂ) by rfl, hz']
  exact hy

/-- The complex points supported on the irreducible closed subset with generic point `x`. -/
def cycleComponentSupport
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    Set (ComplexPoint X structureMap) :=
  Point.underlying ⁻¹' closure {x}

/-- The complex points over a Zariski-closed subset form an analytically closed set. -/
lemma isClosed_complexPoint_underlying_preimage
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap]
    (Z : TopologicalSpace.Closeds X) :
    IsClosed ((@Point.underlying ℂ _ _ X structureMap) ⁻¹'
      (Z : Set X)) := by
  rw [← isOpen_compl_iff]
  let U : X.Opens := ⟨(Z : Set X)ᶜ,
    isOpen_compl_iff.mpr Z.2⟩
  change @IsOpen (ComplexPoint X structureMap) Point.analyticTopology
    ((@Point.underlying ℂ _ _ X structureMap) ⁻¹' (Z : Set X))ᶜ
  rw [show ((@Point.underlying ℂ _ _ X structureMap) ⁻¹'
      (Z : Set X))ᶜ = Point.overOpen U by
    apply Set.ext
    intro z
    change (¬Point.underlying z ∈ Z) ↔
      Point.underlying z ∈ (Z : Set X)ᶜ
    rfl]
  exact Point.isOpen_overOpen U

lemma isClosed_cycleComponentSupport
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    IsClosed (cycleComponentSupport structureMap x) :=
  isClosed_complexPoint_underlying_preimage structureMap
    ⟨closure {x}, isClosed_closure⟩

/-- The map on complex points induced by the canonical inclusion of a cycle component. -/
def cycleComponentMap
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    ComplexPoint (cycleComponent X x)
      (cycleComponentι X x ≫ structureMap) → (ComplexPoint X structureMap) :=
  Point.map (cycleComponentι X x) rfl

/-- The inclusion of a cycle component on complex points, bundled as a continuous map. -/
def cycleComponentContinuousMap
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    @ContinuousMap
      (ComplexPoint (cycleComponent X x) (cycleComponentι X x ≫ structureMap))
      (ComplexPoint X structureMap) Point.analyticTopology Point.analyticTopology :=
  Point.continuousMap (cycleComponentι X x) rfl

lemma range_cycleComponentMap_subset
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    Set.range (cycleComponentMap structureMap x) ⊆ cycleComponentSupport structureMap x := by
  rintro z ⟨w, rfl⟩
  change Point.underlying
    (Point.map (cycleComponentι X x) rfl w) ∈ closure {x}
  rw [Point.underlying_map, ← range_cycleComponentι X x]
  exact ⟨w.underlying, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A complex point in the support of a component annihilates the defining ideal of that
component. -/
lemma cycleComponent_vanishingIdeal_le_complexPoint_ker
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X)
    (z : (ComplexPoint X structureMap)) (hz : z.underlying ∈ closure {x}) :
    (cycleComponentι X x).ker ≤ z.1.ker := by
  unfold cycleComponentι
  rw [Scheme.IdealSheafData.ker_subschemeι]
  change Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {x}, isClosed_closure⟩ ≤ z.1.ker
  rw [complexPoint_ker_eq_vanishingIdeal_closure z]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  exact closure_minimal (Set.singleton_subset_iff.mpr hz) isClosed_closure

/-- Lift a complex point in a component support through the reduced closed component. -/
def cycleComponentComplexPointLift
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X)
    (z : (ComplexPoint X structureMap)) (hz : z ∈ cycleComponentSupport structureMap x) :
    ComplexPoint (cycleComponent X x)
      (cycleComponentι X x ≫ structureMap) :=
  have hz' : z.underlying ∈ closure {x} := hz
  ⟨IsClosedImmersion.lift (cycleComponentι X x) z.1
      (cycleComponent_vanishingIdeal_le_complexPoint_ker structureMap x z hz'), by
    rw [← Category.assoc, IsClosedImmersion.lift_fac, z.2]⟩

@[simp]
lemma cycleComponentMap_lift
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X)
    (z : (ComplexPoint X structureMap)) (hz : z ∈ cycleComponentSupport structureMap x) :
    cycleComponentMap structureMap x (cycleComponentComplexPointLift structureMap x z hz) = z := by
  apply Subtype.ext
  exact IsClosedImmersion.lift_fac _ _ _

/-- The complex points of a reduced cycle component map onto exactly its closed analytic
support. -/
lemma range_cycleComponentMap
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    Set.range (cycleComponentMap structureMap x) = cycleComponentSupport structureMap x := by
  apply Set.Subset.antisymm (range_cycleComponentMap_subset structureMap x)
  intro z hz
  exact ⟨cycleComponentComplexPointLift structureMap x z hz,
    cycleComponentMap_lift structureMap x z hz⟩

/-- A closed immersion of a cycle component is injective on complex points. -/
lemma cycleComponentMap_injective
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    Function.Injective (cycleComponentMap structureMap x) := by
  intro a b hab
  apply Subtype.ext
  apply (cancel_mono (cycleComponentι X x)).mp
  exact congrArg Subtype.val hab

/-- Map the complex points of a cycle component into its analytic support. -/
def cycleComponentSupportMap
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    ComplexPoint (cycleComponent X x)
        (cycleComponentι X x ≫ structureMap) →
      cycleComponentSupport structureMap x :=
  fun z => ⟨cycleComponentMap structureMap x z,
    range_cycleComponentMap_subset structureMap x ⟨z, rfl⟩⟩

/-- Complex points of the reduced component are equivalent to the points in its analytic
support. -/
def cycleComponentPointEquivSupport
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    ComplexPoint (cycleComponent X x)
        (cycleComponentι X x ≫ structureMap) ≃
      cycleComponentSupport structureMap x :=
  Equiv.ofBijective (cycleComponentSupportMap structureMap x) ⟨
    fun _ _ h => cycleComponentMap_injective structureMap x (congrArg Subtype.val h),
    fun z => ⟨cycleComponentComplexPointLift structureMap x z z.2, by
      apply Subtype.ext
      exact cycleComponentMap_lift structureMap x z z.2⟩⟩

/-- The analytic complex points in the smooth locus of a reduced cycle component. -/
def cycleComponentSmoothAnalyticLocus
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    Set (ComplexPoint (cycleComponent X x)
      (cycleComponentι X x ≫ structureMap)) :=
  Point.overOpen
    (cycleComponentι X x ≫ structureMap).smoothLocus

/-- The smooth locus of a cycle component is analytically open in that component. -/
lemma isOpen_cycleComponentSmoothAnalyticLocus
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    @IsOpen
      (ComplexPoint (cycleComponent X x)
        (cycleComponentι X x ≫ structureMap))
      Point.analyticTopology
      (cycleComponentSmoothAnalyticLocus structureMap x) :=
  Point.isOpen_overOpen _

/-- The analytic smooth locus of every reduced integral cycle component is nonempty. -/
lemma cycleComponentSmoothAnalyticLocus_nonempty
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    (cycleComponentSmoothAnalyticLocus structureMap x).Nonempty := by
  obtain ⟨z, hz⟩ := exists_cycleComponent_smooth_complexPoint structureMap x
  exact ⟨z, hz⟩

/-- The image in the ambient analytic space of the smooth locus of a cycle component. -/
def cycleComponentSmoothSupport
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (x : X) : Set (ComplexPoint X structureMap) :=
  cycleComponentMap structureMap x '' cycleComponentSmoothAnalyticLocus structureMap x

/-- The smooth part of a component lies in its closed analytic support. -/
lemma cycleComponentSmoothSupport_subset
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    cycleComponentSmoothSupport structureMap x ⊆ cycleComponentSupport structureMap x := by
  rintro z ⟨w, -, rfl⟩
  exact range_cycleComponentMap_subset structureMap x ⟨w, rfl⟩

/-- Every reduced integral cycle component has a smooth point in its analytic support. -/
lemma cycleComponentSmoothSupport_nonempty
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    (cycleComponentSmoothSupport structureMap x).Nonempty := by
  obtain ⟨z, hz⟩ := cycleComponentSmoothAnalyticLocus_nonempty structureMap x
  exact ⟨cycleComponentMap structureMap x z, z, hz, rfl⟩

/-- Membership in the smooth part of a component support can be checked on the canonical lift
to the reduced component. -/
lemma mem_cycleComponentSmoothSupport_iff
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X)
    (z : (ComplexPoint X structureMap)) :
    z ∈ cycleComponentSmoothSupport structureMap x ↔
      ∃ hz : z ∈ cycleComponentSupport structureMap x,
        (cycleComponentComplexPointLift structureMap x z hz).underlying ∈
          (cycleComponentι X x ≫ structureMap).smoothLocus := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    let hz : cycleComponentMap structureMap x w ∈ cycleComponentSupport structureMap x :=
      range_cycleComponentMap_subset structureMap x ⟨w, rfl⟩
    refine ⟨hz, ?_⟩
    have heq : cycleComponentComplexPointLift structureMap x
        (cycleComponentMap structureMap x w) hz = w := by
      apply cycleComponentMap_injective structureMap x
      exact cycleComponentMap_lift structureMap x _ hz
    rw [heq]
    exact hw
  · rintro ⟨hz, hsmooth⟩
    exact ⟨cycleComponentComplexPointLift structureMap x z hz, hsmooth,
      cycleComponentMap_lift structureMap x z hz⟩

/-- The underlying closed support of an algebraic cycle: the union of the closures of all generic
points having nonzero coefficient. -/
def algebraicCycleSupport {R : Type*} [Zero R] (X : Scheme)
    (c : AlgebraicCycle X R) : Set X :=
  ⋃ x ∈ c.support, closure {x}

/-- The support of the pushforward of a principal divisor lies in the image of its carrier. -/
lemma PrincipalDivisor.pushforwardCycle_support_subset_range
    {X : Scheme} {p : ℕ} (D : PrincipalDivisor X p) :
    D.pushforwardCycle.support ⊆ Set.range D.inclusion := by
  unfold PrincipalDivisor.pushforwardCycle AlgebraicCycle.map
  apply Function.locallyFinsupp.support_map_subset_of_forall_mem
    (s := Set.univ) (t := Set.range D.inclusion)
  · exact Set.subset_univ _
  · intro x _ _
    exact ⟨x, rfl⟩

/-- The geometric support of a pushed-forward principal divisor lies in its closed carrier. -/
lemma PrincipalDivisor.algebraicCycleSupport_pushforwardCycle_subset_range
    {X : Scheme} {p : ℕ} (D : PrincipalDivisor X p) :
    algebraicCycleSupport X D.pushforwardCycle ⊆ Set.range D.inclusion := by
  let _ := D.isClosedImmersion
  rw [algebraicCycleSupport]
  rw [Set.iUnion₂_subset_iff]
  intro x hx
  apply closure_minimal
  · simpa only [Set.singleton_subset_iff] using
      D.pushforwardCycle_support_subset_range hx
  · exact D.inclusion.isClosedEmbedding.isClosed_range

/-- The complex points lying over the geometric support of an algebraic cycle. -/
def analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap]
    (c : AlgebraicCycle X R) : Set (ComplexPoint X structureMap) :=
  Point.underlying ⁻¹' algebraicCycleSupport X c

/-- The complex points lying over the closed carrier of a principal divisor. -/
def principalDivisorCarrierSupport
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap]
    {p : ℕ} (D : PrincipalDivisor X p) : Set (ComplexPoint X structureMap) :=
  (@Point.underlying ℂ _ _ X structureMap) ⁻¹' Set.range D.inclusion

/-- The analytic support of a principal-divisor carrier is closed. -/
lemma isClosed_principalDivisorCarrierSupport
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap]
    {p : ℕ} (D : PrincipalDivisor X p) :
    IsClosed (principalDivisorCarrierSupport structureMap D) := by
  let _ := D.isClosedImmersion
  let Z : TopologicalSpace.Closeds X :=
    ⟨Set.range D.inclusion, D.inclusion.isClosedEmbedding.isClosed_range⟩
  exact isClosed_complexPoint_underlying_preimage structureMap Z

/-- The analytic support of a pushed-forward principal divisor lies over its carrier. -/
lemma analyticCycleSupport_pushforwardCycle_subset_carrierSupport
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap]
    {p : ℕ} (D : PrincipalDivisor X p) :
    analyticCycleSupport structureMap D.pushforwardCycle ⊆
      principalDivisorCarrierSupport structureMap D := by
  intro z hz
  exact D.algebraicCycleSupport_pushforwardCycle_subset_range hz

/-- The analytic support of a cycle is the union of the analytic supports of its nonzero
components. -/
lemma analyticCycleSupport_eq_iUnion {R : Type*} [Zero R]
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (c : AlgebraicCycle X R) :
    analyticCycleSupport structureMap c =
      ⋃ x ∈ c.support, cycleComponentSupport structureMap x := by
  ext z
  simp [analyticCycleSupport, algebraicCycleSupport, cycleComponentSupport]

/-- The analytic support of an algebraic cycle on a projective variety is closed. -/
lemma isClosed_analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (c : AlgebraicCycle X R) :
    IsClosed (analyticCycleSupport structureMap c) := by
  rw [analyticCycleSupport_eq_iUnion]
  exact (algebraicCycle_support_finite structureMap c).isClosed_biUnion fun x _ =>
    isClosed_cycleComponentSupport structureMap x

lemma cycleComponentSupport_subset_analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (c : AlgebraicCycle X R)
    (x : X) (hx : c x ≠ 0) :
    cycleComponentSupport structureMap x ⊆ analyticCycleSupport structureMap c := by
  intro z hz
  change z.underlying ∈ ⋃ y ∈ c.support, closure {y}
  exact Set.mem_iUnion₂.mpr ⟨x, Function.mem_support.mpr hx, hz⟩

@[simp]
lemma algebraicCycleSupport_zero {R : Type*} [Zero R] (X : Scheme) :
    algebraicCycleSupport X (0 : AlgebraicCycle X R) = ∅ := by
  have hs : (0 : AlgebraicCycle X R).support = ∅ := by
    ext x
    change (0 : R) ≠ 0 ↔ False
    simp
  rw [algebraicCycleSupport, hs]
  simp

@[simp]
lemma analyticCycleSupport_zero {R : Type*} [Zero R]
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    analyticCycleSupport structureMap (0 : AlgebraicCycle X R) = ∅ := by
  simp [analyticCycleSupport]

end AlgebraicGeometry
