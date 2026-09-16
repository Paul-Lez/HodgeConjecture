/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The singular filtration of a cycle component

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ)) (x : X.left)

section FiniteType

variable [LocallyOfFiniteType X.hom]

/-- The smooth stratum between the `k`-th and `(k + 1)`-th stages of the singular filtration of
the cycle component at `x`. -/
abbrev cycleComponentSingularFiltrationStratum (k : ℕ) : Scheme :=
  reducedClosedSmoothPiece (X.left.pointClosureι x ≫ X.hom)
    (cycleComponentSingularFiltration X x k)

/-- The immersion of the `k`-th smooth stratum into `X.left`. -/
def cycleComponentSingularFiltrationStratumι (k : ℕ) :
    cycleComponentSingularFiltrationStratum X x k ⟶ X.left :=
  reducedClosedSmoothPieceι (X.left.pointClosureι x ≫ X.hom)
    (cycleComponentSingularFiltration X x k) ≫ X.left.pointClosureι x

/-- The `k`-th smooth stratum, over `ℂ`. -/
abbrev cycleComponentSingularFiltrationStratumOver (k : ℕ) : Over (Spec ↧ℂ) :=
  ComplexPoint.overMk X (cycleComponentSingularFiltrationStratumι X x k)

/-- The immersion of the `k`-th smooth stratum, as a morphism over `ℂ`. -/
abbrev cycleComponentSingularFiltrationStratumOverι (k : ℕ) :
    cycleComponentSingularFiltrationStratumOver X x k ⟶ X :=
  ComplexPoint.overHomMk X (cycleComponentSingularFiltrationStratumι X x k)

instance (k : ℕ) : IsImmersion (cycleComponentSingularFiltrationStratumι X x k) :=
  inferInstanceAs (IsImmersion (reducedClosedSmoothPieceι (X.left.pointClosureι x ≫ X.hom)
    (cycleComponentSingularFiltration X x k) ≫ X.left.pointClosureι x))

instance (k : ℕ) :
    Smooth (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom) := by
  change Smooth ((reducedClosedSmoothPieceι (X.left.pointClosureι x ≫ X.hom)
    (cycleComponentSingularFiltration X x k) ≫ X.left.pointClosureι x) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

/-- The `k`-th smooth stratum is the difference of consecutive stages of the ambient singular
filtration. -/
theorem cycleComponentAmbientSingularFiltration_layer (k : ℕ) :
    Set.range (cycleComponentSingularFiltrationStratumι X x k) =
      (cycleComponentAmbientSingularFiltration X x k : Set X.left) \
        (cycleComponentAmbientSingularFiltration X x (k + 1) : Set X.left) := by
  rw [cycleComponentSingularFiltrationStratumι, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, reducedSmoothClosedFiltration_layer]
  exact Set.image_sdiff (X.left.pointClosureι x).isClosedEmbedding.injective _ _

/-- The open subscheme of `X.left` in which the `k`-th smooth stratum is closed. -/
def cycleComponentSingularStratumAmbientOpen (k : ℕ) : X.left.Opens :=
  (cycleComponentAmbientSingularFiltration X x (k + 1)).compl

/-- The `k`-th smooth stratum as a closed subscheme of
`cycleComponentSingularStratumAmbientOpen X x k`. -/
def cycleComponentSingularStratumClosedLift (k : ℕ) :
    cycleComponentSingularFiltrationStratum X x k ⟶
      cycleComponentSingularStratumAmbientOpen X x k :=
  IsOpenImmersion.lift (cycleComponentSingularStratumAmbientOpen X x k).ι
    (cycleComponentSingularFiltrationStratumι X x k) (by
      rw [Scheme.Opens.range_ι]
      intro y hy
      exact ((cycleComponentAmbientSingularFiltration_layer X x k).le hy).2)

/-- The open `cycleComponentSingularStratumAmbientOpen X x k`, over `ℂ`. -/
abbrev cycleComponentSingularStratumAmbientOpenOver (k : ℕ) : Over (Spec ↧ℂ) :=
  ComplexPoint.openScheme X (cycleComponentSingularStratumAmbientOpen X x k)

@[reassoc (attr := simp)]
theorem cycleComponentSingularStratumClosedLift_ι (k : ℕ) :
    cycleComponentSingularStratumClosedLift X x k ≫
      (cycleComponentSingularStratumAmbientOpen X x k).ι =
        cycleComponentSingularFiltrationStratumι X x k :=
  IsOpenImmersion.lift_fac _ _ _

/-- The closed stratum lift, as a morphism over `ℂ`. -/
def cycleComponentSingularStratumClosedLiftOver (k : ℕ) :
    cycleComponentSingularFiltrationStratumOver X x k ⟶
      cycleComponentSingularStratumAmbientOpenOver X x k :=
  Over.homMk (cycleComponentSingularStratumClosedLift X x k) (by
    change cycleComponentSingularStratumClosedLift X x k ≫
      ((cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) =
        cycleComponentSingularFiltrationStratumι X x k ≫ X.hom
    rw [← Category.assoc, cycleComponentSingularStratumClosedLift_ι])

/-- The closed stratum lift has image the current stage of the ambient filtration. -/
theorem range_cycleComponentSingularStratumClosedLift (k : ℕ) :
    Set.range (cycleComponentSingularStratumClosedLift X x k) =
      (cycleComponentSingularStratumAmbientOpen X x k).ι ⁻¹'
        (cycleComponentAmbientSingularFiltration X x k : Set X.left) := by
  have hf (w : cycleComponentSingularFiltrationStratum X x k) :
      (cycleComponentSingularStratumAmbientOpen X x k).ι
        (cycleComponentSingularStratumClosedLift X x k w) =
          cycleComponentSingularFiltrationStratumι X x k w :=
    congrArg (fun f => f w) (cycleComponentSingularStratumClosedLift_ι X x k)
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ((cycleComponentAmbientSingularFiltration_layer X x k).le ⟨w, (hf w).symm⟩).1
  · intro hy
    obtain ⟨w, hw⟩ := (cycleComponentAmbientSingularFiltration_layer X x k).ge ⟨hy, y.2⟩
    exact ⟨w, (cycleComponentSingularStratumAmbientOpen X x k).ι.isOpenEmbedding.injective
      ((hf w).trans hw)⟩

instance (k : ℕ) :
    IsClosedImmersion (cycleComponentSingularStratumClosedLift X x k) := by
  have : IsPreimmersion (cycleComponentSingularStratumClosedLift X x k ≫
      (cycleComponentSingularStratumAmbientOpen X x k).ι) := by
    rw [cycleComponentSingularStratumClosedLift_ι]
    infer_instance
  let : IsPreimmersion (cycleComponentSingularStratumClosedLift X x k) :=
    .of_comp (cycleComponentSingularStratumClosedLift X x k)
      (cycleComponentSingularStratumAmbientOpen X x k).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_cycleComponentSingularStratumClosedLift]
  exact (cycleComponentAmbientSingularFiltration X x k).isClosed.preimage
    (cycleComponentSingularStratumAmbientOpen X x k).ι.continuous

instance (k : ℕ) :
    IsClosedImmersion (cycleComponentSingularStratumClosedLiftOver X x k).left :=
  inferInstanceAs (IsClosedImmersion (cycleComponentSingularStratumClosedLift X x k))

instance (k : ℕ) :
    Smooth (cycleComponentSingularStratumClosedLift X x k ≫
      (cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) := by
  rw [← Category.assoc, cycleComponentSingularStratumClosedLift_ι]
  infer_instance

theorem cycleComponentAmbientSingularFiltration_antitone :
    Antitone (cycleComponentAmbientSingularFiltration X x) :=
  fun _ _ hkl ↦ Set.image_mono (reducedSmoothClosedFiltration_antitone _ _ hkl)

/-- Every stage of the ambient singular filtration lies on the cycle component. -/
theorem cycleComponentAmbientSingularFiltration_le (k : ℕ) :
    cycleComponentAmbientSingularFiltration X x k ≤ Closeds.closure {x} := by
  rintro _ ⟨z, _, rfl⟩
  exact (X.left.range_pointClosureι x).le ⟨z, rfl⟩

namespace ComplexPoint

theorem cycleComponentAnalyticSingularFiltration_antitone :
    Antitone (cycleComponentAnalyticSingularFiltration X x) :=
  fun _ _ hkl _ hz ↦ cycleComponentAmbientSingularFiltration_antitone X x hkl hz

/-- Every stage of the analytic singular filtration lies in the support of the cycle
component. -/
theorem cycleComponentAnalyticSingularFiltration_le_support (k : ℕ) :
    cycleComponentAnalyticSingularFiltration X x k ≤ cycleComponentSupport X x :=
  fun _ hz ↦ cycleComponentAmbientSingularFiltration_le X x k hz

/-- The complex points of the `k`-th smooth stratum are the difference of consecutive stages of
the analytic singular filtration. -/
theorem cycleComponentAnalyticSingularFiltration_layer (k : ℕ) :
    Set.range (Point.map (cycleComponentSingularFiltrationStratumOverι X x k)) =
      (cycleComponentAnalyticSingularFiltration X x k : Set (ComplexPoint X)) \
        (cycleComponentAnalyticSingularFiltration X x (k + 1) : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion X]
  change Point.underlying ⁻¹' Set.range (cycleComponentSingularFiltrationStratumι X x k) = _
  rw [cycleComponentAmbientSingularFiltration_layer]
  rfl

/-- Inside its ambient open, the complex points of the closed stratum lift are the complex
points over the current stage of the analytic singular filtration. -/
theorem range_map_cycleComponentSingularStratumClosedLiftOver (k : ℕ) :
    Set.range (Point.map (cycleComponentSingularStratumClosedLiftOver X x k)) =
      Point.map (openInclusion X (cycleComponentSingularStratumAmbientOpen X x k)) ⁻¹'
          (cycleComponentAnalyticSingularFiltration X x k : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion]
  change (Point.underlying : ComplexPoint (cycleComponentSingularStratumAmbientOpenOver X x k) →
    (cycleComponentSingularStratumAmbientOpenOver X x k).left) ⁻¹'
      Set.range (cycleComponentSingularStratumClosedLift X x k) = _
  rw [range_cycleComponentSingularStratumClosedLift]
  rfl

end ComplexPoint

end FiniteType

section Noetherian

variable [IsNoetherian X.left] [LocallyOfFiniteType X.hom]

/-- The number of stages of the singular filtration of the cycle component at `x`. -/
abbrev cycleComponentSingularFiltrationLength : ℕ :=
  (cycleComponentSingularStratification X x).length

theorem cycleComponentSingularFiltration_length :
    cycleComponentSingularFiltration X x (cycleComponentSingularFiltrationLength X x) = ⊥ :=
  reducedSmoothClosedFiltration_length _ _

theorem cycleComponentAmbientSingularFiltration_length :
    cycleComponentAmbientSingularFiltration X x (cycleComponentSingularFiltrationLength X x) =
      ⊥ := by
  apply SetLike.coe_injective
  change X.left.pointClosureι x ''
    (cycleComponentSingularFiltration X x (cycleComponentSingularFiltrationLength X x) : Set _) =
      ∅
  rw [cycleComponentSingularFiltration_length]
  exact Set.image_empty _

theorem ComplexPoint.cycleComponentAnalyticSingularFiltration_length :
    ComplexPoint.cycleComponentAnalyticSingularFiltration X x
      (cycleComponentSingularFiltrationLength X x) = ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹'
    (cycleComponentAmbientSingularFiltration X x (cycleComponentSingularFiltrationLength X x) :
      Set X.left) = ∅
  rw [cycleComponentAmbientSingularFiltration_length]
  exact Set.preimage_empty

end Noetherian

section Dimension

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {p : ℕ}
  (hx : Order.coheight x = p)

include hx

/-- Every stage of the singular filtration has dimension below that of the component. -/
theorem cycleComponentSingularFiltration_dimension_lt (k : ℕ) :
    topologicalKrullDim (cycleComponentSingularFiltration X x k) < (dim X.left - p : ℕ) :=
  (IsEmbedding.inclusion
    (reducedSmoothClosedFiltration_le _ _ k)).isInducing.topologicalKrullDim_le.trans_lt
    (topologicalKrullDim_cycleComponent_singularLocus_lt X x hx)

/-- Every smooth stratum has dimension below that of the component. -/
theorem cycleComponentSingularFiltrationStratum_dimension_lt (k : ℕ) :
    topologicalKrullDim (cycleComponentSingularFiltrationStratum X x k) < (dim X.left - p : ℕ) :=
  (topologicalKrullDim_reducedClosedSmoothPiece_le _ le_rfl).trans_lt
    (cycleComponentSingularFiltration_dimension_lt X x hx k)

/-- Every point of a smooth stratum has a standard-smooth affine neighbourhood of relative
dimension below `dim X - p`. -/
theorem cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge (k : ℕ)
    (z : cycleComponentSingularFiltrationStratum X x k) :
    ∃ (U : (cycleComponentSingularFiltrationStratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < dim X.left - p ∧ p + 1 ≤ dim X.left - n ∧
        RingHom.IsStandardSmoothOfRelativeDimension n
          ((cycleComponentSingularFiltrationStratumι X x k ≫ X.hom).appLE ⊤ U (by simp)).hom := by
  obtain ⟨U, hU, hzU, n, hn, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)
      (cycleComponentSingularFiltrationStratum_dimension_lt X x hx k) z
  exact ⟨U, hU, hzU, n, hn, by omega, hstd⟩

/-- Every point of a smooth stratum has an affine neighbourhood smooth of relative dimension
below `dim X - p`. -/
theorem cycleComponentSingularFiltrationStratum_exists_smooth_relativeDimension (k : ℕ)
    (z : cycleComponentSingularFiltrationStratum X x k) :
    ∃ (U : (cycleComponentSingularFiltrationStratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < dim X.left - p ∧ p + 1 ≤ dim X.left - n ∧
        SmoothOfRelativeDimension n
          (U.ι ≫ cycleComponentSingularFiltrationStratumι X x k ≫ X.hom) := by
  obtain ⟨U, hU, hzU, n, hn, hcodim, hstd⟩ :=
    cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge X x hx k z
  exact ⟨U, hU, hzU, n, hn, hcodim,
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth _ hU hstd⟩

end Dimension

end AlgebraicGeometry
