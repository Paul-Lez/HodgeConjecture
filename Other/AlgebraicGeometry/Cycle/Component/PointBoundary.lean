/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus
public import Other.AlgebraicGeometry.Cycle.SmoothPair.PointCoclassSection
public import Other.LinearAlgebra.HodgeStructure

/-! # The singular boundary of a maximal-codimension component is empty

The already proved strict algebraic dimension drop gives a negative Krull
dimension for its singular boundary. We deduce actual emptiness, both
algebraically and analytically; the auxiliary ambient open is therefore the
whole scheme. No smoothness or emptiness of the component is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology Opposite

namespace AlgebraicGeometry.CycleComponent

open ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  (hx : Order.coheight x = dim X.left)

include hx in
/-- Every singular-filtration remainder of a maximal-codimension component is empty. -/
theorem singularFiltration_eq_bot_of_coheight_eq_dimension (k : ℕ) :
    singularFiltration X x k = ⊥ := by
  have hdim := singularFiltration_dimension_lt X x hx k
  simp only [Nat.sub_self, Nat.cast_zero] at hdim
  apply SetLike.coe_injective
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  let y' : singularFiltration X x k := ⟨y, hy⟩
  let Z : IrreducibleCloseds (singularFiltration X x k) :=
    ⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hnonneg : 0 ≤ topologicalKrullDim (singularFiltration X x k) :=
    Order.krullDim_nonneg_iff.mpr ⟨Z⟩
  exact (not_lt_of_ge hnonneg) hdim

include hx in
/-- The actual algebraic ambient singular supports vanish, not just their cohomology. -/
theorem ambientSingularFiltration_eq_bot_of_coheight_eq_dimension (k : ℕ) :
    ambientSingularFiltration X x k = ⊥ := by
  apply SetLike.coe_injective
  change X.left.pointClosureι x '' (singularFiltration X x k : Set _) = ∅
  rw [singularFiltration_eq_bot_of_coheight_eq_dimension X x hx k]
  exact Set.image_empty _

include hx in
/-- In maximal codimension, the auxiliary algebraic ambient open is the whole scheme. -/
theorem smoothAmbientOpen_eq_top_of_coheight_eq_dimension :
    smoothAmbientOpen X x = ⊤ := by
  rw [smoothAmbientOpen_eq_compl,
    ambientSingularFiltration_eq_bot_of_coheight_eq_dimension X x hx 0]
  exact Opens.ext Set.compl_empty

include hx in
/-- All analytic singular supports of a maximal-codimension component are empty. -/
theorem analyticSingularFiltration_eq_bot_of_coheight_eq_dimension (k : ℕ) :
    x‾ˢⁱⁿᵍ[k](ℂ) = ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹' (ambientSingularFiltration X x k : Set X.left) = ∅
  rw [ambientSingularFiltration_eq_bot_of_coheight_eq_dimension X x hx k]
  exact Set.preimage_empty

include hx in
/-- The exact original-ambient open used by the general component class is all of X. -/
theorem analyticSmoothAmbientOpen_eq_top_of_coheight_eq_dimension :
    x‾ˢⁱⁿᵍ(ℂ)ᶜ = ⊤ := by
  rw [analyticSmoothAmbientOpen_eq_compl,
    analyticSingularFiltration_eq_bot_of_coheight_eq_dimension X x hx 0]
  exact Opens.ext Set.compl_empty

include hx in
/-- The actual auxiliary ambient scheme-open inclusion is an isomorphism in the point case. -/
theorem smoothAmbientOpen_ι_isIso_of_coheight_eq_dimension :
    IsIso (smoothAmbientOpen X x).ι := by
  rw [smoothAmbientOpen_eq_top_of_coheight_eq_dimension X x hx]
  exact X.left.topIso.isIso_hom

include hx in
/-- Consequently the auxiliary ambient scheme retains actual projectivity in this
point case; projectivity of arbitrary auxiliary opens is not asserted. -/
theorem smoothAmbientOpen_isProjective_of_coheight_eq_dimension :
    IsProjective ((smoothAmbientOpen X x).ι ≫ X.hom) := by
  let := smoothAmbientOpen_ι_isIso_of_coheight_eq_dimension X x hx
  obtain ⟨P⟩ := (inferInstance : IsProjective X.hom).nonempty_presentation
  refine ⟨⟨{
    ambientDimension := P.ambientDimension
    immersion := (smoothAmbientOpen X x).ι ≫ P.immersion
    isClosedImmersion := ?_
    immersion_toBase := ?_ }⟩⟩
  · let := P.isClosedImmersion
    infer_instance
  · rw [Category.assoc, P.immersion_toBase]

end AlgebraicGeometry.CycleComponent
