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

namespace AlgebraicGeometry.CycleComponent

open ComplexPoint

variable (X : Over (Spec ↧ℂ)) (x : X.left)

section FiniteType

variable [LocallyOfFiniteType X.hom]

/-- The smooth stratum between the `k`-th and `(k + 1)`-th stages of the singular filtration of
the cycle component at `x`. -/
abbrev stratum (k : ℕ) : Scheme :=
  reducedClosedSmoothPiece (X.left.pointClosureι x ≫ X.hom)
    (singularFiltration X x k)

/-- The immersion of the `k`-th smooth stratum into `X.left`. -/
def stratumι (k : ℕ) :
    stratum X x k ⟶ X.left :=
  reducedClosedSmoothPieceι (X.left.pointClosureι x ≫ X.hom)
    (singularFiltration X x k) ≫ X.left.pointClosureι x

/-- The `k`-th smooth stratum, over `ℂ`. -/
abbrev stratumOver (k : ℕ) : Over (Spec ↧ℂ) :=
  ComplexPoint.overMk X (stratumι X x k)

/-- The immersion of the `k`-th smooth stratum, as a morphism over `ℂ`. -/
abbrev stratumOverι (k : ℕ) :
    stratumOver X x k ⟶ X :=
  ComplexPoint.overHomMk X (stratumι X x k)

instance (k : ℕ) : IsImmersion (stratumι X x k) :=
  inferInstanceAs (IsImmersion (reducedClosedSmoothPieceι (X.left.pointClosureι x ≫ X.hom)
    (singularFiltration X x k) ≫ X.left.pointClosureι x))

instance (k : ℕ) :
    Smooth (stratumι X x k ≫ X.hom) := by
  change Smooth ((reducedClosedSmoothPieceι (X.left.pointClosureι x ≫ X.hom)
    (singularFiltration X x k) ≫ X.left.pointClosureι x) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

/-- The `k`-th smooth stratum is the difference of consecutive stages of the ambient singular
filtration. -/
theorem ambientSingularFiltration_layer (k : ℕ) :
    Set.range (stratumι X x k) =
      (ambientSingularFiltration X x k : Set X.left) \
        (ambientSingularFiltration X x (k + 1) : Set X.left) := by
  rw [stratumι, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, reducedSmoothClosedFiltration_layer]
  exact Set.image_sdiff (X.left.pointClosureι x).isClosedEmbedding.injective _ _

/-- The open subscheme of `X.left` in which the `k`-th smooth stratum is closed. -/
def stratumAmbientOpen (k : ℕ) : X.left.Opens :=
  (ambientSingularFiltration X x (k + 1)).compl

/-- The `k`-th smooth stratum as a closed subscheme of
`stratumAmbientOpen X x k`. -/
def stratumClosedLift (k : ℕ) :
    stratum X x k ⟶
      stratumAmbientOpen X x k :=
  IsOpenImmersion.lift (stratumAmbientOpen X x k).ι
    (stratumι X x k) (by
      rw [Scheme.Opens.range_ι]
      intro y hy
      exact ((ambientSingularFiltration_layer X x k).le hy).2)

/-- The open `stratumAmbientOpen X x k`, over `ℂ`. -/
abbrev stratumAmbientOpenOver (k : ℕ) : Over (Spec ↧ℂ) :=
  ComplexPoint.openScheme X (stratumAmbientOpen X x k)

@[reassoc (attr := simp)]
theorem stratumClosedLift_ι (k : ℕ) :
    stratumClosedLift X x k ≫
      (stratumAmbientOpen X x k).ι =
        stratumι X x k :=
  IsOpenImmersion.lift_fac _ _ _

/-- The closed stratum lift, as a morphism over `ℂ`. -/
def stratumClosedLiftOver (k : ℕ) :
    stratumOver X x k ⟶
      stratumAmbientOpenOver X x k :=
  Over.homMk (stratumClosedLift X x k) (by
    change stratumClosedLift X x k ≫
      ((stratumAmbientOpen X x k).ι ≫ X.hom) =
        stratumι X x k ≫ X.hom
    rw [← Category.assoc, stratumClosedLift_ι])

/-- The closed stratum lift has image the current stage of the ambient filtration. -/
theorem range_stratumClosedLift (k : ℕ) :
    Set.range (stratumClosedLift X x k) =
      (stratumAmbientOpen X x k).ι ⁻¹'
        (ambientSingularFiltration X x k : Set X.left) := by
  have hf (w : stratum X x k) :
      (stratumAmbientOpen X x k).ι
        (stratumClosedLift X x k w) =
          stratumι X x k w :=
    congrArg (fun f => f w) (stratumClosedLift_ι X x k)
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ((ambientSingularFiltration_layer X x k).le ⟨w, (hf w).symm⟩).1
  · intro hy
    obtain ⟨w, hw⟩ := (ambientSingularFiltration_layer X x k).ge ⟨hy, y.2⟩
    exact ⟨w, (stratumAmbientOpen X x k).ι.isOpenEmbedding.injective
      ((hf w).trans hw)⟩

instance (k : ℕ) :
    IsClosedImmersion (stratumClosedLift X x k) := by
  have : IsPreimmersion (stratumClosedLift X x k ≫
      (stratumAmbientOpen X x k).ι) := by
    rw [stratumClosedLift_ι]
    infer_instance
  let : IsPreimmersion (stratumClosedLift X x k) :=
    .of_comp (stratumClosedLift X x k)
      (stratumAmbientOpen X x k).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_stratumClosedLift]
  exact (ambientSingularFiltration X x k).isClosed.preimage
    (stratumAmbientOpen X x k).ι.continuous

instance (k : ℕ) :
    IsClosedImmersion (stratumClosedLiftOver X x k).left :=
  inferInstanceAs (IsClosedImmersion (stratumClosedLift X x k))

instance (k : ℕ) :
    Smooth (stratumClosedLift X x k ≫
      (stratumAmbientOpen X x k).ι ≫ X.hom) := by
  rw [← Category.assoc, stratumClosedLift_ι]
  infer_instance

theorem ambientSingularFiltration_antitone :
    Antitone (ambientSingularFiltration X x) :=
  fun _ _ hkl ↦ Set.image_mono (reducedSmoothClosedFiltration_antitone _ _ hkl)

/-- Every stage of the ambient singular filtration lies on the cycle component. -/
theorem ambientSingularFiltration_le (k : ℕ) :
    ambientSingularFiltration X x k ≤ Closeds.closure {x} := by
  rintro _ ⟨z, _, rfl⟩
  exact (X.left.range_pointClosureι x).le ⟨z, rfl⟩

theorem analyticSingularFiltration_antitone :
    Antitone (analyticSingularFiltration X x) :=
  fun _ _ hkl _ hz ↦ ambientSingularFiltration_antitone X x hkl hz

/-- Every stage of the analytic singular filtration lies in the support of the cycle
component. -/
theorem analyticSingularFiltration_le_support (k : ℕ) :
    x‾ˢⁱⁿᵍ[k](ℂ) ≤ x‾(ℂ) :=
  fun _ hz ↦ ambientSingularFiltration_le X x k hz

/-- The complex points of the `k`-th smooth stratum are the difference of consecutive stages of
the analytic singular filtration. -/
theorem analyticSingularFiltration_layer (k : ℕ) :
    Set.range (Point.map (stratumOverι X x k)) =
      (x‾ˢⁱⁿᵍ[k](ℂ) : Set (ComplexPoint X)) \
        (x‾ˢⁱⁿᵍ[(k + 1)](ℂ) : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion X]
  change Point.underlying ⁻¹' Set.range (stratumι X x k) = _
  rw [ambientSingularFiltration_layer]
  rfl

/-- Inside its ambient open, the complex points of the closed stratum lift are the complex
points over the current stage of the analytic singular filtration. -/
theorem range_map_stratumClosedLiftOver (k : ℕ) :
    Set.range (Point.map (stratumClosedLiftOver X x k)) =
      Point.map (openInclusion X (stratumAmbientOpen X x k)) ⁻¹'
          (x‾ˢⁱⁿᵍ[k](ℂ) : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion]
  change (Point.underlying : ComplexPoint (stratumAmbientOpenOver X x k) →
    (stratumAmbientOpenOver X x k).left) ⁻¹'
      Set.range (stratumClosedLift X x k) = _
  rw [range_stratumClosedLift]
  rfl

end FiniteType

section Noetherian

variable [IsNoetherian X.left] [LocallyOfFiniteType X.hom]

/-- The number of stages of the singular filtration of the cycle component at `x`. -/
abbrev singularFiltrationLength : ℕ :=
  (singularStratification X x).length

theorem singularFiltration_length :
    singularFiltration X x (singularFiltrationLength X x) = ⊥ :=
  reducedSmoothClosedFiltration_length _ _

theorem ambientSingularFiltration_length :
    ambientSingularFiltration X x (singularFiltrationLength X x) =
      ⊥ := by
  apply SetLike.coe_injective
  change X.left.pointClosureι x ''
    (singularFiltration X x (singularFiltrationLength X x) : Set _) =
      ∅
  rw [singularFiltration_length]
  exact Set.image_empty _

theorem analyticSingularFiltration_length :
    x‾ˢⁱⁿᵍ[(singularFiltrationLength X x)](ℂ) = ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹'
    (ambientSingularFiltration X x (singularFiltrationLength X x) :
      Set X.left) = ∅
  rw [ambientSingularFiltration_length]
  exact Set.preimage_empty

end Noetherian

section Dimension

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {p : ℕ}
  (hx : Order.coheight x = p)

include hx

/-- Every stage of the singular filtration has dimension below that of the component. -/
theorem singularFiltration_dimension_lt (k : ℕ) :
    topologicalKrullDim (singularFiltration X x k) < (dim X.left - p : ℕ) :=
  (IsEmbedding.inclusion
    (reducedSmoothClosedFiltration_le _ _ k)).isInducing.topologicalKrullDim_le.trans_lt
    (topologicalKrullDim_singularLocus_lt X x hx)

/-- Every smooth stratum has dimension below that of the component. -/
theorem stratum_dimension_lt (k : ℕ) :
    topologicalKrullDim (stratum X x k) < (dim X.left - p : ℕ) :=
  (topologicalKrullDim_reducedClosedSmoothPiece_le _ le_rfl).trans_lt
    (singularFiltration_dimension_lt X x hx k)

/-- Every point of a smooth stratum has a standard-smooth affine neighbourhood of relative
dimension below `dim X - p`. -/
theorem stratum_exists_affine_normalCodimension_ge (k : ℕ)
    (z : stratum X x k) :
    ∃ (U : (stratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < dim X.left - p ∧ p + 1 ≤ dim X.left - n ∧
        RingHom.IsStandardSmoothOfRelativeDimension n
          ((stratumι X x k ≫ X.hom).appLE ⊤ U (by simp)).hom := by
  obtain ⟨U, hU, hzU, n, hn, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (stratumι X x k ≫ X.hom)
      (stratum_dimension_lt X x hx k) z
  exact ⟨U, hU, hzU, n, hn, by omega, hstd⟩

/-- Every point of a smooth stratum has an affine neighbourhood smooth of relative dimension
below `dim X - p`. -/
theorem stratum_exists_smooth_relativeDimension (k : ℕ)
    (z : stratum X x k) :
    ∃ (U : (stratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < dim X.left - p ∧ p + 1 ≤ dim X.left - n ∧
        SmoothOfRelativeDimension n
          (U.ι ≫ stratumι X x k ≫ X.hom) := by
  obtain ⟨U, hU, hzU, n, hn, hcodim, hstd⟩ :=
    stratum_exists_affine_normalCodimension_ge X x hx k z
  exact ⟨U, hU, hzU, n, hn, hcodim,
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth _ hU hstd⟩

end Dimension

end AlgebraicGeometry.CycleComponent
