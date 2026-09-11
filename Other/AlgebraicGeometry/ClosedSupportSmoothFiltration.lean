/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentSingularClosedFiltration

/-!
# The canonical smooth filtration of an arbitrary closed subset of the ambient variety

`Other/AlgebraicGeometry/CycleComponentSingularClosedFiltration.lean` sets up the finite
reduced smooth filtration of the *singular boundary of one integral cycle component*, together
with the analytic closed supports, the smooth strata and their closed lifts into the complement
of the next stage. Everything there works verbatim for an **arbitrary** closed subset
`W : Closeds X.left` of the ambient smooth projective variety, and is in fact simpler: the
filtration already lives in `X.left`, so no transport along the closed immersion of a component
is needed.

This file is that generalisation. It is the geometric half of the general-codimension vanishing
`HasCodimensionTwoSupportedVanishing`; the cohomological half is in
`Other/AlgebraicGeometry/ClosedSupportCodimensionVanishing.lean`.

Nothing here is an obligation: every declaration is proved.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (W : Closeds X.left)

attribute [local instance] isNoetherian_of_isProjective

/-! ### The algebraic filtration and its strata -/

/-- The canonical closed remainders of an arbitrary closed subset of the ambient variety. -/
abbrev closedSupportFiltration (k : ℕ) : Closeds X.left :=
  reducedSmoothClosedFiltration X.hom W k

/-- The terminal index of the canonical finite decomposition. -/
abbrev closedSupportFiltrationLength : ℕ := (reducedSmoothStratification X.hom W).length

omit [IsIntegral X.left] [Smooth X.hom] in
theorem closedSupportFiltration_length :
    closedSupportFiltration X W (closedSupportFiltrationLength X W) = ⊥ :=
  reducedSmoothClosedFiltration_length _ _

omit [IsIntegral X.left] [Smooth X.hom] in
theorem closedSupportFiltration_antitone : Antitone (closedSupportFiltration X W) :=
  reducedSmoothClosedFiltration_antitone _ _

omit [IsIntegral X.left] [Smooth X.hom] in
theorem closedSupportFiltration_le (k : ℕ) : closedSupportFiltration X W k ≤ W :=
  reducedSmoothClosedFiltration_le _ _ k

/-- The actual smooth scheme occurring between two consecutive closed remainders. -/
abbrev closedSupportStratum (k : ℕ) : Scheme :=
  reducedClosedSmoothPiece X.hom (closedSupportFiltration X W k)

/-- Its actual locally closed immersion into the ambient smooth variety. -/
def closedSupportStratumι (k : ℕ) : closedSupportStratum X W k ⟶ X.left :=
  reducedClosedSmoothPieceι X.hom (closedSupportFiltration X W k)

/-- A stratum with its induced structure map to `Spec ℂ`. -/
abbrev closedSupportStratumOver (k : ℕ) : Over (Spec (.of ℂ)) :=
  Over.mk (closedSupportStratumι X W k ≫ X.hom)

/-- The stratum immersion bundled over `Spec ℂ`. -/
def closedSupportStratumOverι (k : ℕ) : closedSupportStratumOver X W k ⟶ X :=
  Over.homMk (closedSupportStratumι X W k) rfl

instance closedSupportStratumι_isImmersion (k : ℕ) :
    IsImmersion (closedSupportStratumι X W k) := by
  change IsImmersion (reducedClosedSmoothPieceι X.hom (closedSupportFiltration X W k))
  infer_instance

instance closedSupportStratumOverι_isImmersion (k : ℕ) :
    IsImmersion (closedSupportStratumOverι X W k).left := by
  change IsImmersion (closedSupportStratumι X W k)
  infer_instance

instance closedSupportStratum_smooth (k : ℕ) :
    Smooth (closedSupportStratumι X W k ≫ X.hom) := by
  change Smooth (reducedClosedSmoothPieceι X.hom (closedSupportFiltration X W k) ≫ X.hom)
  infer_instance

instance closedSupportStratumOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (closedSupportStratumOver X W k).hom := by
  change LocallyOfFiniteType (closedSupportStratumι X W k ≫ X.hom)
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The successive difference is precisely the image of the actual smooth stratum. -/
theorem closedSupportFiltration_layer (k : ℕ) :
    Set.range (closedSupportStratumι X W k) =
      (closedSupportFiltration X W k : Set X.left) \
        (closedSupportFiltration X W (k + 1) : Set X.left) :=
  reducedSmoothClosedFiltration_layer _ _ k

/-! ### The localization open and the closed lift of a stratum -/

/-- The ambient open used by the consecutive-support localization triangle. -/
def closedSupportStratumAmbientOpen (k : ℕ) : X.left.Opens :=
  (closedSupportFiltration X W (k + 1)).compl

/-- The smooth stratum factors through the complement of the next closed remainder. -/
def closedSupportStratumClosedLift (k : ℕ) :
    closedSupportStratum X W k ⟶ closedSupportStratumAmbientOpen X W k :=
  IsOpenImmersion.lift (closedSupportStratumAmbientOpen X W k).ι
    (closedSupportStratumι X W k) (by
      rw [Scheme.Opens.range_ι]
      intro y hy
      exact ((closedSupportFiltration_layer X W k).le hy).2)

/-- The localization open with its induced structure map to `Spec ℂ`. -/
abbrev closedSupportStratumAmbientOpenOver (k : ℕ) : Over (Spec (.of ℂ)) :=
  ComplexPoint.openScheme X (closedSupportStratumAmbientOpen X W k)

instance closedSupportStratumAmbientOpenOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (closedSupportStratumAmbientOpenOver X W k).hom := by
  change LocallyOfFiniteType ((closedSupportStratumAmbientOpen X W k).ι ≫ X.hom)
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] in
@[reassoc (attr := simp)]
theorem closedSupportStratumClosedLift_ι (k : ℕ) :
    closedSupportStratumClosedLift X W k ≫ (closedSupportStratumAmbientOpen X W k).ι =
      closedSupportStratumι X W k :=
  IsOpenImmersion.lift_fac _ _ _

/-- The closed stratum lift bundled over `Spec ℂ`. -/
def closedSupportStratumClosedLiftOver (k : ℕ) :
    closedSupportStratumOver X W k ⟶ closedSupportStratumAmbientOpenOver X W k :=
  Over.homMk (closedSupportStratumClosedLift X W k) (by
    change closedSupportStratumClosedLift X W k ≫
      ((closedSupportStratumAmbientOpen X W k).ι ≫ X.hom) =
        closedSupportStratumι X W k ≫ X.hom
    rw [← Category.assoc, closedSupportStratumClosedLift_ι])

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The closed image of the lift is exactly the current support restricted to that open. -/
theorem range_closedSupportStratumClosedLift (k : ℕ) :
    Set.range (closedSupportStratumClosedLift X W k) =
      (closedSupportStratumAmbientOpen X W k).ι ⁻¹'
        (closedSupportFiltration X W k : Set X.left) := by
  have hf (w : closedSupportStratum X W k) :
      (closedSupportStratumAmbientOpen X W k).ι (closedSupportStratumClosedLift X W k w) =
        closedSupportStratumι X W k w :=
    congrArg (fun f => f w) (closedSupportStratumClosedLift_ι X W k)
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ((closedSupportFiltration_layer X W k).le ⟨w, (hf w).symm⟩).1
  · intro hy
    obtain ⟨w, hw⟩ := (closedSupportFiltration_layer X W k).ge ⟨hy, y.2⟩
    exact ⟨w, (closedSupportStratumAmbientOpen X W k).ι.isOpenEmbedding.injective
      ((hf w).trans hw)⟩

instance closedSupportStratumClosedLift_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (closedSupportStratumClosedLift X W k) := by
  have : IsPreimmersion (closedSupportStratumClosedLift X W k ≫
      (closedSupportStratumAmbientOpen X W k).ι) := by
    rw [closedSupportStratumClosedLift_ι]
    infer_instance
  let : IsPreimmersion (closedSupportStratumClosedLift X W k) :=
    .of_comp (closedSupportStratumClosedLift X W k)
      (closedSupportStratumAmbientOpen X W k).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_closedSupportStratumClosedLift]
  exact (closedSupportFiltration X W k).isClosed.preimage
    (closedSupportStratumAmbientOpen X W k).ι.continuous

instance closedSupportStratumClosedLiftOver_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (closedSupportStratumClosedLiftOver X W k).left := by
  change IsClosedImmersion (closedSupportStratumClosedLift X W k)
  infer_instance

/-- The localization open stays smooth of the ambient relative dimension. -/
instance closedSupportStratumAmbientOpen_smoothOfRelativeDimension
    (k d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    SmoothOfRelativeDimension d ((closedSupportStratumAmbientOpen X W k).ι ≫ X.hom) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (closedSupportStratumAmbientOpen X W k).ι X.hom

/-! ### The analytic supports -/

namespace ComplexPoint

local instance closedSupportFiltrationAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The analytically closed ambient supports for nested-support localization. -/
def closedSupportAnalyticFiltration (k : ℕ) : Closeds (ComplexPoint X) :=
  ⟨Point.underlying ⁻¹' (closedSupportFiltration X W k : Set X.left),
    (closedSupportFiltration X W k).isClosed.preimage (continuous_underlying_to_zariski X)⟩

omit [IsIntegral X.left] [Smooth X.hom] in
theorem closedSupportAnalyticFiltration_antitone :
    Antitone (closedSupportAnalyticFiltration X W) :=
  fun _ _ hkl _ hz => closedSupportFiltration_antitone X W hkl hz

omit [IsIntegral X.left] [Smooth X.hom] in
theorem closedSupportAnalyticFiltration_length :
    closedSupportAnalyticFiltration X W (closedSupportFiltrationLength X W) = ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹'
    (closedSupportFiltration X W (closedSupportFiltrationLength X W) : Set X.left) = ∅
  rw [closedSupportFiltration_length]
  exact Set.preimage_empty

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Each analytic successive difference is the complex-point image of its smooth stratum. -/
theorem closedSupportAnalyticFiltration_layer (k : ℕ) :
    Set.range (Point.map (closedSupportStratumOverι X W k)) =
      (closedSupportAnalyticFiltration X W k : Set (ComplexPoint X)) \
        (closedSupportAnalyticFiltration X W (k + 1) : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion X]
  change Point.underlying ⁻¹' Set.range (closedSupportStratumι X W k) = _
  rw [closedSupportFiltration_layer]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Inside the localization open, the stratum's closed-embedding image is precisely the
current analytic closed support restricted to that open. -/
theorem closedSupportStratumClosedLift_complexPoints_range (k : ℕ) :
    Set.range (Point.map (closedSupportStratumClosedLiftOver X W k)) =
      Point.map (openInclusion X (closedSupportStratumAmbientOpen X W k)) ⁻¹'
        (closedSupportAnalyticFiltration X W k : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion]
  change (Point.underlying : ComplexPoint (closedSupportStratumAmbientOpenOver X W k) →
    (closedSupportStratumAmbientOpenOver X W k).left) ⁻¹'
      Set.range (closedSupportStratumClosedLift X W k) = _
  rw [range_closedSupportStratumClosedLift]
  rfl

end ComplexPoint
end AlgebraicGeometry
