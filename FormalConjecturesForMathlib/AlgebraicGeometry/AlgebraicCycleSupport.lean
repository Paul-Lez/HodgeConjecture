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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ChowGroup
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexPoints
public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothLocus
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

/-- An algebraic cycle on a projective complex variety has finite support. Algebraic cycles are
locally finite by definition, and the underlying Zariski space is compact. -/
lemma algebraicCycle_support_finite {R : Type*} [Zero R]
    (V : SmoothProjectiveComplexVariety) (c : AlgebraicCycle V.scheme R) :
    c.support.Finite := by
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
  change IsReduced (Spec (.of (Γ(X, U') ⧸ I.ideal U')))
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
    {X : Scheme} {structureMap : X ⟶ Spec (.of ℂ)}
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
    (⊤ : TopologicalSpace.Closeds (Spec (.of ℂ)))
  rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
    Scheme.IdealSheafData.map_bot] at h
  have himage : z.1 '' (↑(⊤ : TopologicalSpace.Closeds (Spec (.of ℂ))) :
      Set (Spec (.of ℂ))) = {z.underlying} := by
    simpa only [TopologicalSpace.Closeds.coe_top, Set.image_univ] using hrange
  rw [himage] at h
  exact h

/-- A cycle component of a projective variety is projective over `ℂ`. -/
theorem cycleComponent_projective (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    ProjectiveSpace.IsProjective (cycleComponentι V.scheme x ≫ V.structureMap) := by
  rcases V.projective with ⟨P⟩
  exact ⟨
    { ambientDimension := P.ambientDimension
      immersion := cycleComponentι V.scheme x ≫ P.immersion
      isClosedImmersion := by
        let _ := P.isClosedImmersion
        infer_instance
      immersion_toBase := by rw [Category.assoc, P.immersion_toBase] }
  ⟩

/-- A cycle component of a projective complex variety is proper over `ℂ`. -/
noncomputable instance cycleComponent_isProper
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    IsProper (cycleComponentι V.scheme x ≫ V.structureMap) :=
  (cycleComponent_projective V x).isProper

/-- A cycle component of a projective complex variety is locally of finite presentation over
`ℂ`. -/
noncomputable instance cycleComponent_locallyOfFinitePresentation
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    LocallyOfFinitePresentation (cycleComponentι V.scheme x ≫ V.structureMap) :=
  inferInstance

/-- The integral projective variety defined by one generic point of a smooth projective variety. -/
def cycleComponentVariety (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    IntegralProjectiveComplexVariety where
  scheme := cycleComponent V.scheme x
  isIntegral := inferInstance
  structureMap := cycleComponentι V.scheme x ≫ V.structureMap
  projective := cycleComponent_projective V x

/-- The reduced closure of a point in a projective complex variety is Noetherian. -/
noncomputable instance cycleComponent_isNoetherian
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    IsNoetherian (cycleComponent V.scheme x) := by
  change IsNoetherian (cycleComponentVariety V x).scheme
  infer_instance

/-- The smooth locus of an integral cycle component is a smooth complex scheme. -/
theorem cycleComponent_smoothLocus_smooth
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    Smooth
      ((cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus.ι ≫
        (cycleComponentι V.scheme x ≫ V.structureMap)) :=
  (cycleComponentι V.scheme x ≫ V.structureMap).smooth_restrict_smoothLocus

/-- Every integral cycle component has a complex point in its smooth locus. The smooth locus is
dense over the perfect field `ℂ`, and a projective complex variety has a closed point there. -/
theorem exists_cycleComponent_smooth_complexPoint
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    ∃ z : ComplexPoint (cycleComponent V.scheme x)
        (cycleComponentι V.scheme x ≫ V.structureMap),
      z.underlying ∈
        (cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus := by
  let f := cycleComponentι V.scheme x ≫ V.structureMap
  let _ : JacobsonSpace (cycleComponent V.scheme x) :=
    LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty
    f.smoothLocus.2.isLocallyClosed
  let z := (pointEquivClosedPoint f).symm ⟨y, hyClosed⟩
  refine ⟨z, ?_⟩
  have hz := (pointEquivClosedPoint f).apply_symm_apply ⟨y, hyClosed⟩
  have hz' : z.1 (IsLocalRing.closedPoint ℂ) = y := congrArg Subtype.val hz
  rw [show ComplexPoint.underlying z =
      z.1 (IsLocalRing.closedPoint ℂ) by rfl, hz']
  exact hy

/-- The complex points supported on the irreducible closed subset with generic point `x`. -/
def cycleComponentSupport (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    Set V.analyticPoint :=
  ComplexPoint.underlying ⁻¹' closure {x}

/-- The complex points over a Zariski-closed subset form an analytically closed set. -/
lemma isClosed_complexPoint_underlying_preimage
    (V : SmoothProjectiveComplexVariety)
    (Z : TopologicalSpace.Closeds V.scheme) :
    IsClosed ((@ComplexPoint.underlying V.scheme V.structureMap) ⁻¹'
      (Z : Set V.scheme)) := by
  rw [← isOpen_compl_iff]
  let U : V.scheme.Opens := ⟨(Z : Set V.scheme)ᶜ,
    isOpen_compl_iff.mpr Z.2⟩
  change @IsOpen V.analyticPoint ComplexPoint.analyticTopology
    ((@ComplexPoint.underlying V.scheme V.structureMap) ⁻¹' (Z : Set V.scheme))ᶜ
  rw [show ((@ComplexPoint.underlying V.scheme V.structureMap) ⁻¹'
      (Z : Set V.scheme))ᶜ = ComplexPoint.overOpen U by
    apply Set.ext
    intro z
    change (¬ComplexPoint.underlying z ∈ Z) ↔
      ComplexPoint.underlying z ∈ (Z : Set V.scheme)ᶜ
    rfl]
  exact ComplexPoint.isOpen_overOpen U

lemma isClosed_cycleComponentSupport (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    IsClosed (cycleComponentSupport V x) :=
  isClosed_complexPoint_underlying_preimage V
    ⟨closure {x}, isClosed_closure⟩

/-- The map on complex points induced by the canonical inclusion of a cycle component. -/
def cycleComponentMap (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    ComplexPoint (cycleComponent V.scheme x)
      (cycleComponentι V.scheme x ≫ V.structureMap) → V.analyticPoint :=
  ComplexPoint.map (cycleComponentι V.scheme x) rfl

/-- The inclusion of a cycle component on complex points, bundled as a continuous map. -/
def cycleComponentContinuousMap (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    @ContinuousMap
      (ComplexPoint (cycleComponent V.scheme x) (cycleComponentι V.scheme x ≫ V.structureMap))
      V.analyticPoint ComplexPoint.analyticTopology ComplexPoint.analyticTopology :=
  ComplexPoint.continuousMap (cycleComponentι V.scheme x) rfl

lemma range_cycleComponentMap_subset (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    Set.range (cycleComponentMap V x) ⊆ cycleComponentSupport V x := by
  rintro z ⟨w, rfl⟩
  change ComplexPoint.underlying
    (ComplexPoint.map (cycleComponentι V.scheme x) rfl w) ∈ closure {x}
  rw [ComplexPoint.underlying_map, ← range_cycleComponentι V.scheme x]
  exact ⟨w.underlying, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A complex point in the support of a component annihilates the defining ideal of that
component. -/
lemma cycleComponent_vanishingIdeal_le_complexPoint_ker
    (V : SmoothProjectiveComplexVariety) (x : V.scheme)
    (z : V.analyticPoint) (hz : z.underlying ∈ closure {x}) :
    (cycleComponentι V.scheme x).ker ≤ z.1.ker := by
  unfold cycleComponentι
  rw [Scheme.IdealSheafData.ker_subschemeι]
  change Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {x}, isClosed_closure⟩ ≤ z.1.ker
  rw [complexPoint_ker_eq_vanishingIdeal_closure z]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  exact closure_minimal (Set.singleton_subset_iff.mpr hz) isClosed_closure

/-- Lift a complex point in a component support through the reduced closed component. -/
def cycleComponentComplexPointLift
    (V : SmoothProjectiveComplexVariety) (x : V.scheme)
    (z : V.analyticPoint) (hz : z ∈ cycleComponentSupport V x) :
    ComplexPoint (cycleComponent V.scheme x)
      (cycleComponentι V.scheme x ≫ V.structureMap) :=
  have hz' : z.underlying ∈ closure {x} := hz
  ⟨IsClosedImmersion.lift (cycleComponentι V.scheme x) z.1
      (cycleComponent_vanishingIdeal_le_complexPoint_ker V x z hz'), by
    rw [← Category.assoc, IsClosedImmersion.lift_fac, z.2]⟩

@[simp]
lemma cycleComponentMap_lift
    (V : SmoothProjectiveComplexVariety) (x : V.scheme)
    (z : V.analyticPoint) (hz : z ∈ cycleComponentSupport V x) :
    cycleComponentMap V x (cycleComponentComplexPointLift V x z hz) = z := by
  apply Subtype.ext
  exact IsClosedImmersion.lift_fac _ _ _

/-- The complex points of a reduced cycle component map onto exactly its closed analytic
support. -/
lemma range_cycleComponentMap
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    Set.range (cycleComponentMap V x) = cycleComponentSupport V x := by
  apply Set.Subset.antisymm (range_cycleComponentMap_subset V x)
  intro z hz
  exact ⟨cycleComponentComplexPointLift V x z hz,
    cycleComponentMap_lift V x z hz⟩

/-- A closed immersion of a cycle component is injective on complex points. -/
lemma cycleComponentMap_injective
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    Function.Injective (cycleComponentMap V x) := by
  intro a b hab
  apply Subtype.ext
  apply (cancel_mono (cycleComponentι V.scheme x)).mp
  exact congrArg Subtype.val hab

/-- Map the complex points of a cycle component into its analytic support. -/
def cycleComponentSupportMap
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    ComplexPoint (cycleComponent V.scheme x)
        (cycleComponentι V.scheme x ≫ V.structureMap) →
      cycleComponentSupport V x :=
  fun z => ⟨cycleComponentMap V x z,
    range_cycleComponentMap_subset V x ⟨z, rfl⟩⟩

/-- Complex points of the reduced component are equivalent to the points in its analytic
support. -/
def cycleComponentPointEquivSupport
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    ComplexPoint (cycleComponent V.scheme x)
        (cycleComponentι V.scheme x ≫ V.structureMap) ≃
      cycleComponentSupport V x :=
  Equiv.ofBijective (cycleComponentSupportMap V x) ⟨
    fun _ _ h => cycleComponentMap_injective V x (congrArg Subtype.val h),
    fun z => ⟨cycleComponentComplexPointLift V x z z.2, by
      apply Subtype.ext
      exact cycleComponentMap_lift V x z z.2⟩⟩

/-- The analytic complex points in the smooth locus of a reduced cycle component. -/
def cycleComponentSmoothAnalyticLocus
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    Set (ComplexPoint (cycleComponent V.scheme x)
      (cycleComponentι V.scheme x ≫ V.structureMap)) :=
  ComplexPoint.overOpen
    (cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus

/-- The smooth locus of a cycle component is analytically open in that component. -/
lemma isOpen_cycleComponentSmoothAnalyticLocus
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    @IsOpen
      (ComplexPoint (cycleComponent V.scheme x)
        (cycleComponentι V.scheme x ≫ V.structureMap))
      ComplexPoint.analyticTopology
      (cycleComponentSmoothAnalyticLocus V x) :=
  ComplexPoint.isOpen_overOpen _

/-- The analytic smooth locus of every reduced integral cycle component is nonempty. -/
lemma cycleComponentSmoothAnalyticLocus_nonempty
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    (cycleComponentSmoothAnalyticLocus V x).Nonempty := by
  obtain ⟨z, hz⟩ := exists_cycleComponent_smooth_complexPoint V x
  exact ⟨z, hz⟩

/-- The image in the ambient analytic space of the smooth locus of a cycle component. -/
def cycleComponentSmoothSupport
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) : Set V.analyticPoint :=
  cycleComponentMap V x '' cycleComponentSmoothAnalyticLocus V x

/-- The smooth part of a component lies in its closed analytic support. -/
lemma cycleComponentSmoothSupport_subset
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    cycleComponentSmoothSupport V x ⊆ cycleComponentSupport V x := by
  rintro z ⟨w, -, rfl⟩
  exact range_cycleComponentMap_subset V x ⟨w, rfl⟩

/-- Every reduced integral cycle component has a smooth point in its analytic support. -/
lemma cycleComponentSmoothSupport_nonempty
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    (cycleComponentSmoothSupport V x).Nonempty := by
  obtain ⟨z, hz⟩ := cycleComponentSmoothAnalyticLocus_nonempty V x
  exact ⟨cycleComponentMap V x z, z, hz, rfl⟩

/-- Membership in the smooth part of a component support can be checked on the canonical lift
to the reduced component. -/
lemma mem_cycleComponentSmoothSupport_iff
    (V : SmoothProjectiveComplexVariety) (x : V.scheme)
    (z : V.analyticPoint) :
    z ∈ cycleComponentSmoothSupport V x ↔
      ∃ hz : z ∈ cycleComponentSupport V x,
        (cycleComponentComplexPointLift V x z hz).underlying ∈
          (cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    let hz : cycleComponentMap V x w ∈ cycleComponentSupport V x :=
      range_cycleComponentMap_subset V x ⟨w, rfl⟩
    refine ⟨hz, ?_⟩
    have heq : cycleComponentComplexPointLift V x (cycleComponentMap V x w) hz = w := by
      apply cycleComponentMap_injective V x
      exact cycleComponentMap_lift V x _ hz
    rw [heq]
    exact hw
  · rintro ⟨hz, hsmooth⟩
    exact ⟨cycleComponentComplexPointLift V x z hz, hsmooth,
      cycleComponentMap_lift V x z hz⟩

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
def analyticCycleSupport {R : Type*} [Zero R] (V : SmoothProjectiveComplexVariety)
    (c : AlgebraicCycle V.scheme R) : Set V.analyticPoint :=
  ComplexPoint.underlying ⁻¹' algebraicCycleSupport V.scheme c

/-- The complex points lying over the closed carrier of a principal divisor. -/
def principalDivisorCarrierSupport
    (V : SmoothProjectiveComplexVariety)
    {p : ℕ} (D : PrincipalDivisor V.scheme p) : Set V.analyticPoint :=
  (@ComplexPoint.underlying V.scheme V.structureMap) ⁻¹' Set.range D.inclusion

/-- The analytic support of a principal-divisor carrier is closed. -/
lemma isClosed_principalDivisorCarrierSupport
    (V : SmoothProjectiveComplexVariety)
    {p : ℕ} (D : PrincipalDivisor V.scheme p) :
    IsClosed (principalDivisorCarrierSupport V D) := by
  let _ := D.isClosedImmersion
  let Z : TopologicalSpace.Closeds V.scheme :=
    ⟨Set.range D.inclusion, D.inclusion.isClosedEmbedding.isClosed_range⟩
  exact isClosed_complexPoint_underlying_preimage V Z

/-- The analytic support of a pushed-forward principal divisor lies over its carrier. -/
lemma analyticCycleSupport_pushforwardCycle_subset_carrierSupport
    (V : SmoothProjectiveComplexVariety)
    {p : ℕ} (D : PrincipalDivisor V.scheme p) :
    analyticCycleSupport V D.pushforwardCycle ⊆
      principalDivisorCarrierSupport V D := by
  intro z hz
  exact D.algebraicCycleSupport_pushforwardCycle_subset_range hz

/-- The analytic support of a cycle is the union of the analytic supports of its nonzero
components. -/
lemma analyticCycleSupport_eq_iUnion {R : Type*} [Zero R]
    (V : SmoothProjectiveComplexVariety) (c : AlgebraicCycle V.scheme R) :
    analyticCycleSupport V c =
      ⋃ x ∈ c.support, cycleComponentSupport V x := by
  ext z
  simp [analyticCycleSupport, algebraicCycleSupport, cycleComponentSupport]

/-- The analytic support of an algebraic cycle on a projective variety is closed. -/
lemma isClosed_analyticCycleSupport {R : Type*} [Zero R]
    (V : SmoothProjectiveComplexVariety) (c : AlgebraicCycle V.scheme R) :
    IsClosed (analyticCycleSupport V c) := by
  rw [analyticCycleSupport_eq_iUnion]
  exact (algebraicCycle_support_finite V c).isClosed_biUnion fun x _ =>
    isClosed_cycleComponentSupport V x

lemma cycleComponentSupport_subset_analyticCycleSupport {R : Type*} [Zero R]
    (V : SmoothProjectiveComplexVariety) (c : AlgebraicCycle V.scheme R)
    (x : V.scheme) (hx : c x ≠ 0) :
    cycleComponentSupport V x ⊆ analyticCycleSupport V c := by
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
    (V : SmoothProjectiveComplexVariety) :
    analyticCycleSupport V (0 : AlgebraicCycle V.scheme R) = ∅ := by
  simp [analyticCycleSupport]

end AlgebraicGeometry
