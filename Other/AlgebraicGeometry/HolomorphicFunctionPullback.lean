/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexAnalyticMaps
public import Other.AlgebraicGeometry.HolomorphicExponential
public import Mathlib.Topology.Sheaves.Functors

/-!
# Pullback of holomorphic functions along algebraic maps

A morphism of smooth complex schemes induces a holomorphic map on complex points.  Precomposition
therefore sends holomorphic functions on an open subset of the target to holomorphic functions on
its inverse image.  This file packages that operation as a morphism from the target structure
sheaf to the direct image of the source structure sheaf, both for commutative-ring-valued and
additive-group-valued sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X Y : Over (Spec (CommRingCat.of ℂ))) (f : X ⟶ Y) (d e : ℕ)

/-- The continuous map on analytifications induced by an algebraic morphism. -/
def analyticMapContinuous : C(ComplexPoint X, ComplexPoint Y) :=
  ⟨Point.map f, Point.continuous_map f⟩

/-- The continuous map on analytifications induced by an algebraic morphism. -/
def analyticMapTopCat :
    TopCat.of (ComplexPoint X) ⟶ TopCat.of (ComplexPoint Y) :=
  TopCat.ofHom (analyticMapContinuous X Y f)

@[simp]
theorem analyticMapTopCat_apply (x : ComplexPoint X) :
    analyticMapTopCat X Y f x = Point.map f x :=
  rfl

/-- The restriction of an analytic map to the inverse image of a target open set. -/
def analyticMapOpenRestriction (U : Opens (ComplexPoint Y)) :
    U.comap (analyticMapContinuous X Y f) → U :=
  fun x => ⟨analyticMapTopCat X Y f x.1, x.2⟩

/-- Restricting the analytic map to the inverse image of an open target remains analytic as a
map into that open target.  Mathlib's corresponding public lemma is currently specialized to
`C^∞`; this is its direct local-invariant-property proof at analytic regularity. -/
theorem contMDiff_restrictPreimage_analyticMap
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom]
    (U : Opens (ComplexPoint Y)) :
    ContMDiff (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ (Fin e → ℂ)) ω
      (analyticMapOpenRestriction X Y f U) := by
  intro x
  change ChartedSpace.LiftPropWithinAt
    (ContDiffWithinAtProp (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ (Fin e → ℂ)) ω)
    _ Set.univ x
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ (Fin e → ℂ)) ω) _ Set.univ x).mp
  have h := ((contMDiff_analyticMap X Y f d e).comp contMDiff_subtype_val) x
  change ChartedSpace.LiftPropWithinAt
    (ContDiffWithinAtProp (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ (Fin e → ℂ)) ω)
    _ Set.univ x at h
  have hfun : Subtype.val ∘ analyticMapOpenRestriction X Y f U =
      Point.map f ∘ Subtype.val := by
    rfl
  rw [hfun]
  exact h

/-- Pull back holomorphic functions by precomposition with an algebraic map.  The codomain is
the pushforward sheaf, so both sides live on the target analytic space. -/
def holomorphicFunctionSheafToPushforward
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] :
    holomorphicFunctionSheaf Y e ⟶
      (TopCat.Sheaf.pushforward CommRingCat (analyticMapTopCat X Y f)).obj
        (holomorphicFunctionSheaf X d) where
  hom.app U := CommRingCat.ofHom
    { toFun := fun g =>
        ⟨g.1 ∘ analyticMapOpenRestriction X Y f (Opposite.unop U), by
          apply ContMDiff.comp (I' := modelWithCornersSelf ℂ (Fin e → ℂ)) g.2
          exact contMDiff_restrictPreimage_analyticMap X Y f d e _⟩
      map_one' := rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  hom.naturality _ _ _ := rfl

/-- The same pullback morphism after retaining only the additive groups of sections. -/
def holomorphicAdditiveFunctionSheafToPushforward
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] :
    holomorphicAdditiveFunctionSheaf Y e ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat (analyticMapTopCat X Y f)).obj
        (holomorphicAdditiveFunctionSheaf X d) where
  hom.app U := AddCommGrpCat.ofHom
    { toFun := fun g =>
        ⟨g.1 ∘ analyticMapOpenRestriction X Y f (Opposite.unop U), by
          apply ContMDiff.comp (I' := modelWithCornersSelf ℂ (Fin e → ℂ)) g.2
          exact contMDiff_restrictPreimage_analyticMap X Y f d e _⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  hom.naturality _ _ _ := rfl

end AlgebraicGeometry.ComplexPoint
