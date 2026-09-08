/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSingularClosedFiltration
public import HodgeConjecture.Other.AlgebraicGeometry.ClosedImmersionSourceOpen
public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentClosedPointDimension

/-!
# The actual smooth-locus closed lift of an integral cycle component

The ambient open is exactly the complement of the first canonical singular-boundary
support. The smooth locus embeds closed in that open. Its constant relative dimension
is proved to be `d-p` using smooth equidimensionality and the already proved coheight
formula for a closed point of the integral component.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X)

/-- The precise algebraic open complementary to the canonical singular boundary. -/
def cycleComponentSmoothLocusAmbientOpen : X.Opens :=
  (cycleComponentSingularAmbientClosedFiltration s x 0).compl

/-- The target is the actual source-open target of the smooth locus. -/
theorem cycleComponentSmoothLocusAmbientOpen_eq_sourceOpenTarget :
    cycleComponentSmoothLocusAmbientOpen s x =
      closedImmersionSourceOpenTarget (cycleComponentι X x)
        (cycleComponentι X x ≫ s).smoothLocus := rfl

/-- The actual smooth locus, closed in the complement of its singular boundary. -/
def cycleComponentSmoothLocusClosedLift :
    (cycleComponentι X x ≫ s).smoothLocus.toScheme ⟶
      (cycleComponentSmoothLocusAmbientOpen s x).toScheme :=
  closedImmersionSourceOpenLift (cycleComponentι X x) (cycleComponentι X x ≫ s).smoothLocus

instance cycleComponentSmoothLocusClosedLift_isClosedImmersion :
    IsClosedImmersion (cycleComponentSmoothLocusClosedLift s x) := by
  dsimp [cycleComponentSmoothLocusClosedLift]
  infer_instance

@[reassoc (attr := simp)]
theorem cycleComponentSmoothLocusClosedLift_ι :
    cycleComponentSmoothLocusClosedLift s x ≫ (cycleComponentSmoothLocusAmbientOpen s x).ι =
      (cycleComponentι X x ≫ s).smoothLocus.ι ≫ cycleComponentι X x :=
  closedImmersionSourceOpenLift_ι _ _

/-- The exact image of the lift is the restriction of the full component support. -/
theorem range_cycleComponentSmoothLocusClosedLift :
    Set.range (cycleComponentSmoothLocusClosedLift s x) =
      (cycleComponentSmoothLocusAmbientOpen s x).ι ⁻¹' closure ({x} : Set X) := by
  rw [← range_cycleComponentι X x]
  exact range_closedImmersionSourceOpenLift _ _

variable {d p : ℕ} [SmoothOfRelativeDimension d s]

/-- The smooth locus has exactly the constant relative dimension of the integral
component, not just a locally chosen dimension. -/
theorem cycleComponentSmoothLocus_smoothOfRelativeDimension (hx : Order.coheight x = p) :
    SmoothOfRelativeDimension (d - p)
      ((cycleComponentι X x ≫ s).smoothLocus.ι ≫ cycleComponentι X x ≫ s) := by
  let A := (cycleComponentι X x ≫ s).smoothLocus
  let g := A.ι ≫ cycleComponentι X x ≫ s
  let : Smooth g := cycleComponent_smoothLocus_smooth s x
  let : IsIntegral A := cycleComponent_smoothLocus_isIntegral s x
  obtain ⟨m, hm⟩ := Smooth.exists_smoothOfRelativeDimension g
  let : SmoothOfRelativeDimension m g := hm
  obtain ⟨z, hzA, hzClosed⟩ := (dense_cycleComponent_smooth_closedPoints s x).nonempty
  let zA : A.toScheme := ⟨z, hzA⟩
  have hzAClosed : IsClosed ({zA} : Set A) := by
    have he : A.ι ⁻¹' ({z} : Set (cycleComponent X x)) = {zA} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hzClosed.preimage A.ι.continuous
  have hmEq : m = d - p := by
    exact_mod_cast calc
      (m : ℕ∞) = Order.coheight zA :=
        (SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
          (f := g) (d := m) zA hzAClosed).symm
      _ = Order.coheight z := (coheight_eq_of_isOpenImmersion (x := zA) A.ι).symm
      _ = d - p := cycleComponent_closedPoint_coheight_eq_sub s x z hx hzClosed
  subst m
  exact hm

/-- The ambient open retains the original smooth relative dimension. -/
instance cycleComponentSmoothLocusAmbientOpen_smoothOfRelativeDimension :
    SmoothOfRelativeDimension d ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (cycleComponentSmoothLocusAmbientOpen s x).ι s

namespace ComplexPoint

local instance cycleComponentSmoothClosedLiftAnalyticTopology :
    TopologicalSpace (ComplexPoint X s) := Point.analyticTopology

/-- The full cycle support as an actual closed analytic subset. -/
def cycleComponentAnalyticClosedSupport : Closeds (ComplexPoint X s) :=
  ⟨cycleComponentSupport s x, isClosed_cycleComponentSupport s x⟩

omit [IsIntegral X] [Smooth s] in
/-- The analytic image of the algebraic boundary complement is the exact open used by
the original ambient supported resolution. -/
theorem cycleComponentSmoothLocusAmbientOpen_analytic_image :
    Set.range (Point.map (cycleComponentSmoothLocusAmbientOpen s x).ι
      (structureMap := (cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s) rfl) =
      ((cycleComponentSingularAnalyticClosedFiltration s x 0).compl : Set (ComplexPoint X s)) := by
  rw [range_map_of_isImmersion s, Scheme.Opens.range_ι]
  rfl

/-- The complex-point image of the closed lift is precisely the restricted full support. -/
theorem cycleComponentSmoothLocusClosedLift_complexPoints_range :
    Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
      (structureMap := cycleComponentSmoothLocusClosedLift s x ≫
        (cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s) rfl) =
      Point.map (cycleComponentSmoothLocusAmbientOpen s x).ι
        (structureMap := (cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s) rfl ⁻¹'
          (cycleComponentSupport s x) := by
  rw [range_map_of_isImmersion, range_cycleComponentSmoothLocusClosedLift]
  rfl

end ComplexPoint
end AlgebraicGeometry
