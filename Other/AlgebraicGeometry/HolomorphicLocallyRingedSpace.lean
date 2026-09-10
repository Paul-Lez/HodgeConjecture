/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RegularFunctionsHolomorphic
public import Other.Geometry.Manifold.HolomorphicLogarithm
public import Mathlib.Topology.Sheaves.Stalks

/-!
# The holomorphic locally ringed space

A germ of a holomorphic function is a unit exactly when its value at the base
point is nonzero. Consequently the holomorphic structure sheaf has local stalks.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- Evaluation at the base point, on the diagram defining a holomorphic stalk. -/
def holomorphicStalkEvaluationCocone (x : ComplexPoint X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ (holomorphicFunctionSheaf X d).presheaf) where
  pt := ↧ℂ
  ι :=
    { app U := CommRingCat.ofHom (ContMDiffMap.evalRingHom ⟨x, (unop U).property⟩)
      naturality := by
        intro U V i
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro f
        rfl }

/-- The value of a holomorphic germ at its base point. -/
def holomorphicStalkEvaluation (x : ComplexPoint X) :
    (holomorphicFunctionSheaf X d).presheaf.stalk x ⟶ ↧ℂ :=
  colimit.desc _ (holomorphicStalkEvaluationCocone X d x)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem holomorphicStalkEvaluation_germ (U : Opens (TopCat.of (ComplexPoint X)))
    (x : ComplexPoint X) (hx : x ∈ U)
    (f : (holomorphicFunctionSheaf X d).presheaf.obj (op U)) :
    holomorphicStalkEvaluation X d x
      ((holomorphicFunctionSheaf X d).presheaf.germ U x hx f) = f.1 ⟨x, hx⟩ :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (holomorphicStalkEvaluationCocone X d x) (op ⟨U, hx⟩)) f

set_option backward.isDefEq.respectTransparency false in
/-- A holomorphic germ is invertible precisely when it does not vanish at the point. -/
theorem holomorphicStalk_isUnit_iff (x : ComplexPoint X)
    (f : (holomorphicFunctionSheaf X d).presheaf.stalk x) :
    IsUnit f ↔ holomorphicStalkEvaluation X d x f ≠ 0 := by
  constructor
  · intro hf
    exact (hf.map (holomorphicStalkEvaluation X d x).hom).ne_zero
  · intro hf
    obtain ⟨U, hx, g, rfl⟩ := (holomorphicFunctionSheaf X d).presheaf.exists_germ_eq f
    have hg : g.1 ⟨x, hx⟩ ≠ 0 := by
      exact (holomorphicStalkEvaluation_germ X d U x hx g) ▸ hf
    obtain ⟨V, hVU, hxV, l, hl⟩ :=
      ContMDiffMap.exists_local_holomorphicExponential
        (I := 𝓘(ℂ, Fin d → ℂ)) g ⟨x, hx⟩ hg
    have hunit : IsUnit ((holomorphicFunctionSheaf X d).presheaf.map
        (homOfLE hVU).op g) := by
      refine ⟨(ContMDiffMap.holomorphicExponential l).toMul, ?_⟩
      apply Subtype.ext
      funext y
      exact hl y
    have hu := hunit.map ((holomorphicFunctionSheaf X d).presheaf.germ V x hxV).hom
    rwa [(holomorphicFunctionSheaf X d).presheaf.germ_res_apply
      (homOfLE hVU) x hxV g] at hu

instance holomorphicStalk_nontrivial (x : ComplexPoint X) :
    Nontrivial ((holomorphicFunctionSheaf X d).presheaf.stalk x) :=
  (holomorphicStalkEvaluation X d x).hom.domain_nontrivial

/-- The maximal ideal of a holomorphic stalk consists of germs vanishing at the point. -/
theorem holomorphicStalk_nonunits (x : ComplexPoint X) :
    nonunits ((holomorphicFunctionSheaf X d).presheaf.stalk x) =
      RingHom.ker (holomorphicStalkEvaluation X d x).hom := by
  ext f
  change (¬ IsUnit f) ↔ holomorphicStalkEvaluation X d x f = 0
  rw [holomorphicStalk_isUnit_iff, not_not]

/-- Holomorphic stalks are local rings. -/
instance holomorphicStalk_isLocalRing (x : ComplexPoint X) :
    IsLocalRing ((holomorphicFunctionSheaf X d).presheaf.stalk x) := by
  apply IsLocalRing.of_nonunits_add
  rw [holomorphicStalk_nonunits]
  exact fun f g hf hg ↦ Ideal.add_mem _ hf hg

/-- The locally ringed space of complex points with their holomorphic functions. -/
def holomorphicLocallyRingedSpace : LocallyRingedSpace where
  carrier := TopCat.of (ComplexPoint X)
  presheaf := (holomorphicFunctionSheaf X d).presheaf
  IsSheaf := (holomorphicFunctionSheaf X d).property
  isLocalRing := holomorphicStalk_isLocalRing X d

/-- The comparison with the algebraic scheme, before checking locality on stalks. -/
def analytificationToPresheafedSpace :
    (holomorphicLocallyRingedSpace X d).toPresheafedSpace ⟶ X.left.toPresheafedSpace where
  base := underlyingContinuousMap X
  c := (regularToHolomorphicSheaf X d).hom

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating an analytified algebraic germ is the original complex point's stalk map. -/
theorem analytification_stalkMap_comp_evaluation (x : ComplexPoint X) :
    (analytificationToPresheafedSpace X d).stalkMap x ≫ holomorphicStalkEvaluation X d x =
      Point.stalkHom x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [PresheafedSpace.stalkMap_germ_assoc]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change holomorphicStalkEvaluation X d x
    ((holomorphicFunctionSheaf X d).presheaf.germ (analyticOpen X U) x hx
      (regularFunctionHolomorphic X d U a)) = Point.evaluationHom U ⟨x, hx⟩ a
  rw [holomorphicStalkEvaluation_germ]
  exact (Point.evaluationHom_apply U ⟨x, hx⟩ a).symm

set_option backward.isDefEq.respectTransparency false in
/-- The natural morphism from the holomorphic locally ringed space to the algebraic scheme. -/
def analytificationToAlgebraic :
    holomorphicLocallyRingedSpace X d ⟶ X.left.toLocallyRingedSpace where
  __ := analytificationToPresheafedSpace X d
  prop x := by
    change ComplexPoint X at x
    let : IsLocalHom (Point.stalkHom x).hom := (Point.stalkData x).2.2
    refine ⟨fun a ha ↦ ?_⟩
    apply (isUnit_map_iff (Point.stalkHom x).hom a).mp
    have he := ConcreteCategory.congr_hom (analytification_stalkMap_comp_evaluation X d x) a
    exact he ▸ ha.map (holomorphicStalkEvaluation X d x).hom

end AlgebraicGeometry.ComplexPoint
