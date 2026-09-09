/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ReducedSmoothClosedFiltrationDimension
public import Other.AlgebraicGeometry.SmoothStratificationAnalytification
public import Other.AlgebraicGeometry.SmoothAffineRelativeDimension

/-!
# Actual ambient closed supports for singular-component localization induction

The singular boundary of an integral cycle component has its canonical finite reduced
smooth filtration. Its images are closed both algebraically and analytically in the
ambient variety, and successive differences are exactly the complex-point images of
actual smooth locally closed strata. Their local relative dimensions are strictly below
`d - p`, hence their ambient normal codimensions are at least `p + 1`.

No analytic cohomological-dimension or support-extension theorem is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X)

/-- The canonical closed remainders inside the integral component's singular boundary. -/
abbrev cycleComponentSingularClosedFiltration (k : ℕ) : Closeds (cycleComponent X x) :=
  reducedSmoothClosedFiltration (cycleComponentι X x ≫ s)
    (singularLocusClosed (cycleComponentι X x ≫ s)) k

/-- The exact terminal index is read from the already constructed finite decomposition. -/
abbrev cycleComponentSingularFiltrationLength : ℕ :=
  (cycleComponentSingularStratification s x).length

theorem cycleComponentSingularClosedFiltration_length :
    cycleComponentSingularClosedFiltration s x (cycleComponentSingularFiltrationLength s x) = ⊥ := by
  let := cycleComponent_isNoetherian s x
  exact reducedSmoothClosedFiltration_length _ _

/-- The actual smooth scheme occurring between two consecutive closed supports. -/
abbrev cycleComponentSingularFiltrationStratum (k : ℕ) : Scheme :=
  reducedClosedSmoothPiece (cycleComponentι X x ≫ s)
    (cycleComponentSingularClosedFiltration s x k)

/-- Its actual locally closed immersion into the original smooth ambient scheme. -/
def cycleComponentSingularFiltrationStratumι (k : ℕ) :
    cycleComponentSingularFiltrationStratum s x k ⟶ X :=
  reducedClosedSmoothPieceι (cycleComponentι X x ≫ s)
    (cycleComponentSingularClosedFiltration s x k) ≫ cycleComponentι X x

set_option backward.isDefEq.respectTransparency false in
instance cycleComponentSingularFiltrationStratumι_isImmersion (k : ℕ) :
    IsImmersion (cycleComponentSingularFiltrationStratumι s x k) := by
  dsimp [cycleComponentSingularFiltrationStratumι]
  infer_instance

instance cycleComponentSingularFiltrationStratum_smooth (k : ℕ) :
    Smooth (cycleComponentSingularFiltrationStratumι s x k ≫ s) := by
  change Smooth ((reducedClosedSmoothPieceι (cycleComponentι X x ≫ s)
    (cycleComponentSingularClosedFiltration s x k) ≫ cycleComponentι X x) ≫ s)
  rw [Category.assoc]
  infer_instance

/-- Every stage is a closed support in the original algebraic ambient scheme. -/
def cycleComponentSingularAmbientClosedFiltration (k : ℕ) : Closeds X :=
  ⟨cycleComponentι X x '' (cycleComponentSingularClosedFiltration s x k : Set _),
    (cycleComponentι X x).isClosedEmbedding.isClosedMap _
      (cycleComponentSingularClosedFiltration s x k).isClosed⟩

omit [IsIntegral X] [Smooth s] in
theorem cycleComponentSingularAmbientClosedFiltration_antitone :
    Antitone (cycleComponentSingularAmbientClosedFiltration s x) := by
  intro k l hkl
  exact Set.image_mono (reducedSmoothClosedFiltration_antitone _ _ hkl)

theorem cycleComponentSingularAmbientClosedFiltration_length :
    cycleComponentSingularAmbientClosedFiltration s x (cycleComponentSingularFiltrationLength s x) =
      ⊥ := by
  apply SetLike.coe_injective
  change cycleComponentι X x ''
    (cycleComponentSingularClosedFiltration s x (cycleComponentSingularFiltrationLength s x) : Set _) = ∅
  rw [cycleComponentSingularClosedFiltration_length]
  exact Set.image_empty _

omit [IsIntegral X] [Smooth s] in
/-- The successive ambient difference is precisely the image of the actual smooth stratum. -/
theorem cycleComponentSingularAmbientClosedFiltration_layer (k : ℕ) :
    Set.range (cycleComponentSingularFiltrationStratumι s x k) =
      (cycleComponentSingularAmbientClosedFiltration s x k : Set X) \
        (cycleComponentSingularAmbientClosedFiltration s x (k + 1) : Set X) := by
  rw [cycleComponentSingularFiltrationStratumι, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, reducedSmoothClosedFiltration_layer]
  exact Set.image_sdiff (cycleComponentι X x).isClosedEmbedding.injective _ _

/-- The exact ambient open used by the consecutive-support localization triangle. -/
def cycleComponentSingularStratumAmbientOpen (k : ℕ) : X.Opens :=
  (cycleComponentSingularAmbientClosedFiltration s x (k + 1)).compl

/-- The actual smooth stratum factors into the complement of the next closed support. -/
def cycleComponentSingularStratumClosedLift (k : ℕ) :
    cycleComponentSingularFiltrationStratum s x k ⟶
      cycleComponentSingularStratumAmbientOpen s x k :=
  IsOpenImmersion.lift (cycleComponentSingularStratumAmbientOpen s x k).ι
    (cycleComponentSingularFiltrationStratumι s x k) (by
      rw [Scheme.Opens.range_ι]
      intro y hy
      exact ((cycleComponentSingularAmbientClosedFiltration_layer s x k).le hy).2)

omit [IsIntegral X] [Smooth s] in
@[reassoc (attr := simp)]
theorem cycleComponentSingularStratumClosedLift_ι (k : ℕ) :
    cycleComponentSingularStratumClosedLift s x k ≫
      (cycleComponentSingularStratumAmbientOpen s x k).ι =
        cycleComponentSingularFiltrationStratumι s x k :=
  IsOpenImmersion.lift_fac _ _ _

omit [IsIntegral X] [Smooth s] in
/-- Its closed image is exactly the restriction of the current support to that open. -/
theorem range_cycleComponentSingularStratumClosedLift (k : ℕ) :
    Set.range (cycleComponentSingularStratumClosedLift s x k) =
      (cycleComponentSingularStratumAmbientOpen s x k).ι ⁻¹'
        (cycleComponentSingularAmbientClosedFiltration s x k : Set X) := by
  have hf (w : cycleComponentSingularFiltrationStratum s x k) :
      (cycleComponentSingularStratumAmbientOpen s x k).ι
        (cycleComponentSingularStratumClosedLift s x k w) =
          cycleComponentSingularFiltrationStratumι s x k w :=
    congrArg (fun f => f w) (cycleComponentSingularStratumClosedLift_ι s x k)
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ((cycleComponentSingularAmbientClosedFiltration_layer s x k).le ⟨w, (hf w).symm⟩).1
  · intro hy
    obtain ⟨w, hw⟩ := (cycleComponentSingularAmbientClosedFiltration_layer s x k).ge ⟨hy, y.2⟩
    exact ⟨w, (cycleComponentSingularStratumAmbientOpen s x k).ι.isOpenEmbedding.injective
      ((hf w).trans hw)⟩

/-- Each actual layer is a closed immersion in precisely the open needed by localization,
not in an unrelated auxiliary open. -/
instance cycleComponentSingularStratumClosedLift_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (cycleComponentSingularStratumClosedLift s x k) := by
  have : IsPreimmersion (cycleComponentSingularStratumClosedLift s x k ≫
      (cycleComponentSingularStratumAmbientOpen s x k).ι) := by
    rw [cycleComponentSingularStratumClosedLift_ι]
    infer_instance
  let : IsPreimmersion (cycleComponentSingularStratumClosedLift s x k) :=
    .of_comp (cycleComponentSingularStratumClosedLift s x k)
      (cycleComponentSingularStratumAmbientOpen s x k).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_cycleComponentSingularStratumClosedLift]
  exact (cycleComponentSingularAmbientClosedFiltration s x k).isClosed.preimage
    (cycleComponentSingularStratumAmbientOpen s x k).ι.continuous

/-- The actual localization open remains smooth of the original ambient dimension. -/
instance cycleComponentSingularStratumAmbientOpen_smoothOfRelativeDimension
    (k d : ℕ) [SmoothOfRelativeDimension d s] :
    SmoothOfRelativeDimension d ((cycleComponentSingularStratumAmbientOpen s x k).ι ≫ s) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (cycleComponentSingularStratumAmbientOpen s x k).ι s

instance cycleComponentSingularStratumClosedLift_smooth (k : ℕ) :
    Smooth (cycleComponentSingularStratumClosedLift s x k ≫
      (cycleComponentSingularStratumAmbientOpen s x k).ι ≫ s) := by
  rw [← Category.assoc, cycleComponentSingularStratumClosedLift_ι]
  infer_instance

/-- Every closed remainder stays below the proved singular-boundary dimension bound. -/
theorem cycleComponentSingularClosedFiltration_dimension_lt
    {d p : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = p) (k : ℕ) :
    topologicalKrullDim (cycleComponentSingularClosedFiltration s x k) < (d - p : ℕ) :=
  (IsEmbedding.inclusion (reducedSmoothClosedFiltration_le _ _ k)).isInducing.topologicalKrullDim_le.trans_lt
    (topologicalKrullDim_cycleComponent_singularLocus_lt s x hx)

/-- Every actual smooth layer has strictly smaller dimension than the component. -/
theorem cycleComponentSingularFiltrationStratum_dimension_lt
    {d p : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = p) (k : ℕ) :
    topologicalKrullDim (cycleComponentSingularFiltrationStratum s x k) < (d - p : ℕ) :=
  (topologicalKrullDim_reducedClosedSmoothPiece_le _ le_rfl).trans_lt
    (cycleComponentSingularClosedFiltration_dimension_lt s x hx k)

/-- The normal codimension lower bound is realized on actual standard-smooth affine
neighborhoods of every stratum point, including strata of nonconstant dimension. -/
theorem cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge
    {d p : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = p) (k : ℕ)
    (z : cycleComponentSingularFiltrationStratum s x k) :
    ∃ (U : (cycleComponentSingularFiltrationStratum s x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < d - p ∧ p + 1 ≤ d - n ∧
        RingHom.IsStandardSmoothOfRelativeDimension n
          ((cycleComponentSingularFiltrationStratumι s x k ≫ s).appLE ⊤ U (by simp)).hom := by
  obtain ⟨U, hU, hzU, n, hn, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (cycleComponentSingularFiltrationStratumι s x k ≫ s)
      (cycleComponentSingularFiltrationStratum_dimension_lt s x (d := d) hx k) z
  exact ⟨U, hU, hzU, n, hn, by omega, hstd⟩

/-- The dimension bound supplies genuine smooth scheme morphisms of fixed local
dimension, ready for the actual normal-coordinate construction. -/
theorem cycleComponentSingularFiltrationStratum_exists_smooth_relativeDimension
    {d p : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = p) (k : ℕ)
    (z : cycleComponentSingularFiltrationStratum s x k) :
    ∃ (U : (cycleComponentSingularFiltrationStratum s x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < d - p ∧ p + 1 ≤ d - n ∧
        SmoothOfRelativeDimension n (U.ι ≫ cycleComponentSingularFiltrationStratumι s x k ≫ s) := by
  obtain ⟨U, hU, hzU, n, hn, hcodim, hstd⟩ :=
    cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge s x
      (d := d) hx k z
  exact ⟨U, hU, hzU, n, hn, hcodim,
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth _ hU hstd⟩

namespace ComplexPoint

local instance cycleComponentSingularClosedFiltrationAnalyticTopology :
    TopologicalSpace (ComplexPoint X s) := Point.analyticTopology

/-- The actual analytically closed ambient supports for nested-support localization. -/
def cycleComponentSingularAnalyticClosedFiltration (k : ℕ) : Closeds (ComplexPoint X s) :=
  ⟨Point.underlying ⁻¹' (cycleComponentSingularAmbientClosedFiltration s x k : Set X),
    (cycleComponentSingularAmbientClosedFiltration s x k).isClosed.preimage
      (continuous_underlying_to_zariski s)⟩

omit [IsIntegral X] [Smooth s] in
theorem cycleComponentSingularAnalyticClosedFiltration_antitone :
    Antitone (cycleComponentSingularAnalyticClosedFiltration s x) := by
  intro k l hkl z hz
  exact cycleComponentSingularAmbientClosedFiltration_antitone s x hkl hz

theorem cycleComponentSingularAnalyticClosedFiltration_length :
    cycleComponentSingularAnalyticClosedFiltration s x (cycleComponentSingularFiltrationLength s x) =
      ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹'
    (cycleComponentSingularAmbientClosedFiltration s x (cycleComponentSingularFiltrationLength s x) :
      Set X) = ∅
  rw [cycleComponentSingularAmbientClosedFiltration_length]
  exact Set.preimage_empty

omit [IsIntegral X] [Smooth s] in
/-- Each analytic successive difference is the actual complex-point image of its smooth
stratum, not a supplied support parametrization. -/
theorem cycleComponentSingularAnalyticClosedFiltration_layer (k : ℕ) :
    Set.range (Point.map (cycleComponentSingularFiltrationStratumι s x k)
      (structureMap := cycleComponentSingularFiltrationStratumι s x k ≫ s) rfl) =
      (cycleComponentSingularAnalyticClosedFiltration s x k : Set (ComplexPoint X s)) \
        (cycleComponentSingularAnalyticClosedFiltration s x (k + 1) : Set (ComplexPoint X s)) := by
  rw [range_map_of_isImmersion s, cycleComponentSingularAmbientClosedFiltration_layer]
  rfl

omit [IsIntegral X] [Smooth s] in
/-- Inside the exact localization open, the stratum's actual closed-embedding image
is precisely the current analytic closed support restricted to that open. -/
theorem cycleComponentSingularStratumClosedLift_complexPoints_range (k : ℕ) :
    Set.range (Point.map (cycleComponentSingularStratumClosedLift s x k)
      (structureMap := cycleComponentSingularStratumClosedLift s x k ≫
        (cycleComponentSingularStratumAmbientOpen s x k).ι ≫ s) rfl) =
      Point.map (cycleComponentSingularStratumAmbientOpen s x k).ι
        (structureMap := (cycleComponentSingularStratumAmbientOpen s x k).ι ≫ s) rfl ⁻¹'
          (cycleComponentSingularAnalyticClosedFiltration s x k : Set (ComplexPoint X s)) := by
  rw [range_map_of_isImmersion, range_cycleComponentSingularStratumClosedLift]
  rfl

/-- Removing the first closed boundary support from the full cycle support gives
exactly the complex points of the actual smooth locus of the integral component. -/
theorem cycleComponentSmoothLocus_complexPoints_range_eq_support_sdiff_boundary :
    Set.range (Point.map ((cycleComponentι X x ≫ s).smoothLocus.ι ≫ cycleComponentι X x)
      (structureMap := ((cycleComponentι X x ≫ s).smoothLocus.ι ≫ cycleComponentι X x) ≫ s) rfl) =
      cycleComponentSupport s x \
        (cycleComponentSingularAnalyticClosedFiltration s x 0 : Set (ComplexPoint X s)) := by
  have he : Set.range ((cycleComponentι X x ≫ s).smoothLocus.ι ≫ cycleComponentι X x) =
      closure {x} \
        (cycleComponentSingularAmbientClosedFiltration s x 0 : Set X) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      ← range_cycleComponentι X x]
    change cycleComponentι X x '' ((cycleComponentι X x ≫ s).smoothLocus : Set _) =
      Set.range (cycleComponentι X x) \
        cycleComponentι X x '' ((cycleComponentι X x ≫ s).smoothLocus : Set _)ᶜ
    rw [Set.range_sdiff_image (cycleComponentι X x).isClosedEmbedding.injective, compl_compl]
  rw [range_map_of_isImmersion s, he]
  rfl

end ComplexPoint
end AlgebraicGeometry
