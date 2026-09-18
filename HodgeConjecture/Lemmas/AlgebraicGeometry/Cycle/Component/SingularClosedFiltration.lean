/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Ambient closed supports for singular-component localization induction

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]

/-- The exact terminal index is read from the already constructed finite decomposition. -/
abbrev closedEmbeddingSingularFiltrationLength : ℕ :=
  (closedEmbeddingSingularStratification i).length

/-- The actual smooth scheme occurring between two consecutive closed supports. -/
abbrev closedEmbeddingSingularFiltrationStratum (k : ℕ) : Scheme :=
  reducedClosedSmoothPiece (i.left ≫ X.hom)
    (closedEmbeddingSingularClosedFiltration i k)

/-- Its actual locally closed immersion into the original smooth ambient scheme. -/
def closedEmbeddingSingularFiltrationStratumι (k : ℕ) :
    closedEmbeddingSingularFiltrationStratum i k ⟶ X.left :=
  reducedClosedSmoothPieceι (i.left ≫ X.hom)
    (closedEmbeddingSingularClosedFiltration i k) ≫ i.left

/-- A singular-filtration stratum with its induced structure map to `Spec ℂ`. -/
abbrev closedEmbeddingSingularFiltrationStratumOver (k : ℕ) : Over (Spec ↧ℂ) :=
  Over.mk (closedEmbeddingSingularFiltrationStratumι i k ≫ X.hom)

/-- The stratum immersion bundled over `Spec ℂ`. -/
def closedEmbeddingSingularFiltrationStratumOverι (k : ℕ) :
    closedEmbeddingSingularFiltrationStratumOver i k ⟶ X :=
  Over.homMk (closedEmbeddingSingularFiltrationStratumι i k) rfl

instance closedEmbeddingSingularFiltrationStratumOverι_isImmersion (k : ℕ) :
    IsImmersion (closedEmbeddingSingularFiltrationStratumOverι i k).left := by
  change IsImmersion (reducedClosedSmoothPieceι (i.left ≫ X.hom)
    (closedEmbeddingSingularClosedFiltration i k) ≫ i.left)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance closedEmbeddingSingularFiltrationStratumι_isImmersion (k : ℕ) :
    IsImmersion (closedEmbeddingSingularFiltrationStratumι i k) := by
  dsimp [closedEmbeddingSingularFiltrationStratumι]
  infer_instance

instance closedEmbeddingSingularFiltrationStratum_smooth (k : ℕ) :
    Smooth (closedEmbeddingSingularFiltrationStratumι i k ≫ X.hom) := by
  change Smooth ((reducedClosedSmoothPieceι (i.left ≫ X.hom)
    (closedEmbeddingSingularClosedFiltration i k) ≫ i.left) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

instance closedEmbeddingSingularFiltrationStratumOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (closedEmbeddingSingularFiltrationStratumOver i k).hom := by
  change LocallyOfFiniteType (closedEmbeddingSingularFiltrationStratumι i k ≫ X.hom)
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- The successive ambient difference is precisely the image of the actual smooth stratum. -/
theorem closedEmbeddingSingularAmbientClosedFiltration_layer (k : ℕ) :
    Set.range (closedEmbeddingSingularFiltrationStratumι i k) =
      (closedEmbeddingSingularAmbientClosedFiltration i k : Set X.left) \
        (closedEmbeddingSingularAmbientClosedFiltration i (k + 1) : Set X.left) := by
  rw [closedEmbeddingSingularFiltrationStratumι, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, reducedSmoothClosedFiltration_layer]
  exact Set.image_sdiff (i.left).isClosedEmbedding.injective _ _

/-- The exact ambient open used by the consecutive-support localization triangle. -/
def closedEmbeddingSingularStratumAmbientOpen (k : ℕ) : X.left.Opens :=
  (closedEmbeddingSingularAmbientClosedFiltration i (k + 1)).compl

/-- The actual smooth stratum factors into the complement of the next closed support. -/
def closedEmbeddingSingularStratumClosedLift (k : ℕ) :
    closedEmbeddingSingularFiltrationStratum i k ⟶
      closedEmbeddingSingularStratumAmbientOpen i k :=
  IsOpenImmersion.lift (closedEmbeddingSingularStratumAmbientOpen i k).ι
    (closedEmbeddingSingularFiltrationStratumι i k) (by
      rw [Scheme.Opens.range_ι]
      intro y hy
      exact ((closedEmbeddingSingularAmbientClosedFiltration_layer i k).le hy).2)

/-- The localization open with its induced structure map to `Spec ℂ`. -/
abbrev closedEmbeddingSingularStratumAmbientOpenOver (k : ℕ) : Over (Spec ↧ℂ) :=
  ComplexPoint.openScheme X (closedEmbeddingSingularStratumAmbientOpen i k)

instance closedEmbeddingSingularStratumAmbientOpenOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (closedEmbeddingSingularStratumAmbientOpenOver i k).hom := by
  change LocallyOfFiniteType
    ((closedEmbeddingSingularStratumAmbientOpen i k).ι ≫ X.hom)
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
@[reassoc (attr := simp)]
theorem closedEmbeddingSingularStratumClosedLift_ι (k : ℕ) :
    closedEmbeddingSingularStratumClosedLift i k ≫
      (closedEmbeddingSingularStratumAmbientOpen i k).ι =
        closedEmbeddingSingularFiltrationStratumι i k :=
  IsOpenImmersion.lift_fac _ _ _

/-- The closed stratum lift bundled over `Spec ℂ`. -/
def closedEmbeddingSingularStratumClosedLiftOver (k : ℕ) :
    closedEmbeddingSingularFiltrationStratumOver i k ⟶
      closedEmbeddingSingularStratumAmbientOpenOver i k :=
  Over.homMk (closedEmbeddingSingularStratumClosedLift i k) (by
    change closedEmbeddingSingularStratumClosedLift i k ≫
      ((closedEmbeddingSingularStratumAmbientOpen i k).ι ≫ X.hom) =
        closedEmbeddingSingularFiltrationStratumι i k ≫ X.hom
    rw [← Category.assoc, closedEmbeddingSingularStratumClosedLift_ι])

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- Its closed image is exactly the restriction of the current support to that open. -/
theorem range_closedEmbeddingSingularStratumClosedLift (k : ℕ) :
    Set.range (closedEmbeddingSingularStratumClosedLift i k) =
      (closedEmbeddingSingularStratumAmbientOpen i k).ι ⁻¹'
        (closedEmbeddingSingularAmbientClosedFiltration i k : Set X.left) := by
  have hf (w : closedEmbeddingSingularFiltrationStratum i k) :
      (closedEmbeddingSingularStratumAmbientOpen i k).ι
        (closedEmbeddingSingularStratumClosedLift i k w) =
          closedEmbeddingSingularFiltrationStratumι i k w :=
    congrArg (fun f => f w) (closedEmbeddingSingularStratumClosedLift_ι i k)
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ((closedEmbeddingSingularAmbientClosedFiltration_layer i k).le ⟨w, (hf w).symm⟩).1
  · intro hy
    obtain ⟨w, hw⟩ := (closedEmbeddingSingularAmbientClosedFiltration_layer i k).ge ⟨hy, y.2⟩
    exact ⟨w, (closedEmbeddingSingularStratumAmbientOpen i k).ι.isOpenEmbedding.injective
      ((hf w).trans hw)⟩

/-- Each actual layer is a closed immersion in precisely the open needed by localization,
not in an unrelated auxiliary open. -/
instance closedEmbeddingSingularStratumClosedLift_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (closedEmbeddingSingularStratumClosedLift i k) := by
  have : IsPreimmersion (closedEmbeddingSingularStratumClosedLift i k ≫
      (closedEmbeddingSingularStratumAmbientOpen i k).ι) := by
    rw [closedEmbeddingSingularStratumClosedLift_ι]
    infer_instance
  let : IsPreimmersion (closedEmbeddingSingularStratumClosedLift i k) :=
    .of_comp (closedEmbeddingSingularStratumClosedLift i k)
      (closedEmbeddingSingularStratumAmbientOpen i k).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_closedEmbeddingSingularStratumClosedLift]
  exact (closedEmbeddingSingularAmbientClosedFiltration i k).isClosed.preimage
    (closedEmbeddingSingularStratumAmbientOpen i k).ι.continuous

instance closedEmbeddingSingularStratumClosedLiftOver_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (closedEmbeddingSingularStratumClosedLiftOver i k).left := by
  change IsClosedImmersion (closedEmbeddingSingularStratumClosedLift i k)
  infer_instance

/-- The actual localization open remains smooth of the original ambient dimension. -/
instance closedEmbeddingSingularStratumAmbientOpen_smoothOfRelativeDimension
    (k d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    SmoothOfRelativeDimension d ((closedEmbeddingSingularStratumAmbientOpen i k).ι ≫ X.hom) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (closedEmbeddingSingularStratumAmbientOpen i k).ι X.hom

instance closedEmbeddingSingularStratumClosedLift_smooth (k : ℕ) :
    Smooth (closedEmbeddingSingularStratumClosedLift i k ≫
      (closedEmbeddingSingularStratumAmbientOpen i k).ι ≫ X.hom) := by
  rw [← Category.assoc, closedEmbeddingSingularStratumClosedLift_ι]
  infer_instance

namespace ComplexPoint

/-- The smooth-locus immersion into the ambient variety, bundled over `Spec ℂ`. -/
def closedEmbeddingSmoothLocusOverι : closedEmbeddingSmoothLocusOver i ⟶ X :=
  Over.homMk ((i.left ≫ X.hom).smoothLocus.ι ≫ i.left) (by
    change ((i.left ≫ X.hom).smoothLocus.ι ≫ i.left) ≫ X.hom =
      (i.left ≫ X.hom).smoothLocus.ι ≫ Y.hom
    rw [Category.assoc]
    exact congrArg (fun f ↦ (i.left ≫ X.hom).smoothLocus.ι ≫ f) (Over.w i))

instance closedEmbeddingSmoothLocusOverι_isImmersion :
    IsImmersion (closedEmbeddingSmoothLocusOverι i).left := by
  change IsImmersion ((i.left ≫ X.hom).smoothLocus.ι ≫
    i.left)
  infer_instance

end ComplexPoint
end AlgebraicGeometry

end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
theorem closedEmbeddingSingularClosedFiltration_length :
    closedEmbeddingSingularClosedFiltration i
      (closedEmbeddingSingularStratification i).length = ⊥ := by
  let := closedEmbedding_isNoetherian i
  exact reducedSmoothClosedFiltration_length _ _

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
theorem closedEmbeddingSingularAmbientClosedFiltration_antitone :
    Antitone (closedEmbeddingSingularAmbientClosedFiltration i) :=
  fun _ _ hkl ↦ Set.image_mono (reducedSmoothClosedFiltration_antitone _ _ hkl)

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
theorem closedEmbeddingSingularAmbientClosedFiltration_length :
    closedEmbeddingSingularAmbientClosedFiltration i
      (closedEmbeddingSingularStratification i).length = ⊥ := by
  apply SetLike.coe_injective
  change i.left ''
    (closedEmbeddingSingularClosedFiltration i
      (closedEmbeddingSingularStratification i).length : Set _) = ∅
  rw [closedEmbeddingSingularClosedFiltration_length]
  exact Set.image_empty _

/-- Every closed remainder stays below the proved singular-boundary dimension bound. -/
theorem closedEmbeddingSingularClosedFiltration_dimension_lt
    {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p) (k : ℕ) :
    topologicalKrullDim (closedEmbeddingSingularClosedFiltration i k) < (dim X.left - p : ℕ) :=
  (IsEmbedding.inclusion (reducedSmoothClosedFiltration_le _ _ k)).isInducing.topologicalKrullDim_le.trans_lt
    (topologicalKrullDim_closedEmbedding_singularLocus_lt i hi)

/-- Every smooth layer has strictly smaller dimension than the component. -/
theorem closedEmbeddingSingularFiltrationStratum_dimension_lt
    {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p) (k : ℕ) :
    topologicalKrullDim (closedEmbeddingSingularFiltrationStratum i k) < (dim X.left - p : ℕ) :=
  (topologicalKrullDim_reducedClosedSmoothPiece_le _ le_rfl).trans_lt
    (closedEmbeddingSingularClosedFiltration_dimension_lt i hi k)

/-- The normal codimension lower bound is realized on standard-smooth affine
neighborhoods of every stratum point, including strata of nonconstant dimension. -/
theorem closedEmbeddingSingularFiltrationStratum_exists_affine_normalCodimension_ge
    {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p) (k : ℕ)
    (z : closedEmbeddingSingularFiltrationStratum i k) :
    ∃ (U : (closedEmbeddingSingularFiltrationStratum i k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < dim X.left - p ∧ p + 1 ≤ dim X.left - n ∧
        RingHom.IsStandardSmoothOfRelativeDimension n
          ((closedEmbeddingSingularFiltrationStratumι i k ≫ X.hom).appLE ⊤ U (by simp)).hom := by
  obtain ⟨U, hU, hzU, n, hn, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (closedEmbeddingSingularFiltrationStratumι i k ≫ X.hom)
      (closedEmbeddingSingularFiltrationStratum_dimension_lt i hi k) z
  exact ⟨U, hU, hzU, n, hn, by omega, hstd⟩

/-- The dimension bound supplies genuine smooth scheme morphisms of fixed local
dimension, ready for the normal-coordinate construction. -/
theorem closedEmbeddingSingularFiltrationStratum_exists_smooth_relativeDimension
    {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p) (k : ℕ)
    (z : closedEmbeddingSingularFiltrationStratum i k) :
    ∃ (U : (closedEmbeddingSingularFiltrationStratum i k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < dim X.left - p ∧ p + 1 ≤ dim X.left - n ∧
        SmoothOfRelativeDimension n (U.ι ≫ closedEmbeddingSingularFiltrationStratumι i k ≫ X.hom) := by
  obtain ⟨U, hU, hzU, n, hn, hcodim, hstd⟩ :=
    closedEmbeddingSingularFiltrationStratum_exists_affine_normalCodimension_ge i
      hi k z
  exact ⟨U, hU, hzU, n, hn, hcodim,
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth _ hU hstd⟩

namespace ComplexPoint

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
theorem closedEmbeddingSingularAnalyticClosedFiltration_antitone :
    Antitone (closedEmbeddingSingularAnalyticClosedFiltration i) :=
  fun _ _ hkl _ hz ↦ closedEmbeddingSingularAmbientClosedFiltration_antitone i hkl hz

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
theorem closedEmbeddingSingularAnalyticClosedFiltration_length :
    closedEmbeddingSingularAnalyticClosedFiltration i
      (closedEmbeddingSingularStratification i).length = ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹'
    (closedEmbeddingSingularAmbientClosedFiltration i
      (closedEmbeddingSingularStratification i).length : Set X.left) = ∅
  rw [closedEmbeddingSingularAmbientClosedFiltration_length]
  exact Set.preimage_empty

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- Each analytic successive difference is the complex-point image of its smooth
stratum, not a supplied support parametrization. -/
theorem closedEmbeddingSingularAnalyticClosedFiltration_layer (k : ℕ) :
    Set.range (Point.map (closedEmbeddingSingularFiltrationStratumOverι i k)) =
      (closedEmbeddingSingularAnalyticClosedFiltration i k : Set (ComplexPoint X)) \
        (closedEmbeddingSingularAnalyticClosedFiltration i (k + 1) : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion X]
  change Point.underlying ⁻¹' Set.range (closedEmbeddingSingularFiltrationStratumι i k) = _
  rw [closedEmbeddingSingularAmbientClosedFiltration_layer]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- Inside the exact localization open, the stratum's closed-embedding image
is precisely the current analytic closed support restricted to that open. -/
theorem closedEmbeddingSingularStratumClosedLift_complexPoints_range (k : ℕ) :
    Set.range (Point.map (closedEmbeddingSingularStratumClosedLiftOver i k)) =
      Point.map (openInclusion X (closedEmbeddingSingularStratumAmbientOpen i k)) ⁻¹'
          (closedEmbeddingSingularAnalyticClosedFiltration i k : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion]
  change (Point.underlying : ComplexPoint (closedEmbeddingSingularStratumAmbientOpenOver i k) →
    (closedEmbeddingSingularStratumAmbientOpenOver i k).left) ⁻¹'
      Set.range (closedEmbeddingSingularStratumClosedLift i k) = _
  rw [range_closedEmbeddingSingularStratumClosedLift]
  rfl

end ComplexPoint
end AlgebraicGeometry
