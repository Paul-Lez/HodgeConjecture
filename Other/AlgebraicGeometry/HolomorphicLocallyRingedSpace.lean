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

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ)
  [SmoothOfRelativeDimension d s]

/-- Evaluation at the base point, on the diagram defining a holomorphic stalk. -/
def holomorphicStalkEvaluationCocone (x : ComplexPoint X s) :
    Cocone ((OpenNhds.inclusion x).op ⋙ (holomorphicFunctionSheaf s d).presheaf) where
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
def holomorphicStalkEvaluation (x : ComplexPoint X s) :
    (holomorphicFunctionSheaf s d).presheaf.stalk x ⟶ ↧ℂ :=
  colimit.desc _ (holomorphicStalkEvaluationCocone s d x)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem holomorphicStalkEvaluation_germ (U : Opens (TopCat.of (ComplexPoint X s)))
    (x : ComplexPoint X s) (hx : x ∈ U)
    (f : (holomorphicFunctionSheaf s d).presheaf.obj (op U)) :
    holomorphicStalkEvaluation s d x
      ((holomorphicFunctionSheaf s d).presheaf.germ U x hx f) = f.1 ⟨x, hx⟩ :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (holomorphicStalkEvaluationCocone s d x) (op ⟨U, hx⟩)) f

set_option backward.isDefEq.respectTransparency false in
/-- A holomorphic germ is invertible precisely when it does not vanish at the point. -/
theorem holomorphicStalk_isUnit_iff (x : ComplexPoint X s)
    (f : (holomorphicFunctionSheaf s d).presheaf.stalk x) :
    IsUnit f ↔ holomorphicStalkEvaluation s d x f ≠ 0 := by
  constructor
  · intro hf
    exact (hf.map (holomorphicStalkEvaluation s d x).hom).ne_zero
  · intro hf
    let : IsManifold 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X s) := isManifold_omega s d
    obtain ⟨U, hx, g, rfl⟩ := (holomorphicFunctionSheaf s d).presheaf.exists_germ_eq f
    have hg : g.1 ⟨x, hx⟩ ≠ 0 := by
      exact (holomorphicStalkEvaluation_germ s d U x hx g) ▸ hf
    obtain ⟨V, hVU, hxV, l, hl⟩ :=
      ContMDiffMap.exists_local_holomorphicExponential
        (I := 𝓘(ℂ, Fin d → ℂ)) g ⟨x, hx⟩ hg
    have hunit : IsUnit ((holomorphicFunctionSheaf s d).presheaf.map
        (homOfLE hVU).op g) := by
      refine ⟨(ContMDiffMap.holomorphicExponential l).toMul, ?_⟩
      apply Subtype.ext
      funext y
      exact hl y
    have hu := hunit.map ((holomorphicFunctionSheaf s d).presheaf.germ V x hxV).hom
    rwa [(holomorphicFunctionSheaf s d).presheaf.germ_res_apply
      (homOfLE hVU) x hxV g] at hu

instance holomorphicStalk_nontrivial (x : ComplexPoint X s) :
    Nontrivial ((holomorphicFunctionSheaf s d).presheaf.stalk x) :=
  (holomorphicStalkEvaluation s d x).hom.domain_nontrivial

/-- The maximal ideal of a holomorphic stalk consists of germs vanishing at the point. -/
theorem holomorphicStalk_nonunits (x : ComplexPoint X s) :
    nonunits ((holomorphicFunctionSheaf s d).presheaf.stalk x) =
      RingHom.ker (holomorphicStalkEvaluation s d x).hom := by
  ext f
  change (¬ IsUnit f) ↔ holomorphicStalkEvaluation s d x f = 0
  rw [holomorphicStalk_isUnit_iff, not_not]

/-- Holomorphic stalks are local rings. -/
instance holomorphicStalk_isLocalRing (x : ComplexPoint X s) :
    IsLocalRing ((holomorphicFunctionSheaf s d).presheaf.stalk x) := by
  apply IsLocalRing.of_nonunits_add
  rw [holomorphicStalk_nonunits]
  exact fun f g hf hg ↦ Ideal.add_mem _ hf hg

/-- The locally ringed space of complex points with their holomorphic functions. -/
def holomorphicLocallyRingedSpace : LocallyRingedSpace where
  carrier := TopCat.of (ComplexPoint X s)
  presheaf := (holomorphicFunctionSheaf s d).presheaf
  IsSheaf := (holomorphicFunctionSheaf s d).property
  isLocalRing := holomorphicStalk_isLocalRing s d

/-- The comparison with the algebraic scheme, before checking locality on stalks. -/
def analytificationToPresheafedSpace :
    (holomorphicLocallyRingedSpace s d).toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := underlyingContinuousMap s
  c := (regularToHolomorphicSheaf s d).hom

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating an analytified algebraic germ is the original complex point's stalk map. -/
theorem analytification_stalkMap_comp_evaluation (x : ComplexPoint X s) :
    (analytificationToPresheafedSpace s d).stalkMap x ≫ holomorphicStalkEvaluation s d x =
      Point.stalkHom x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [PresheafedSpace.stalkMap_germ_assoc]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change holomorphicStalkEvaluation s d x
    ((holomorphicFunctionSheaf s d).presheaf.germ (analyticOpen s U) x hx
      (regularFunctionHolomorphic s d U a)) = Point.evaluationHom U ⟨x, hx⟩ a
  rw [holomorphicStalkEvaluation_germ]
  exact (Point.evaluationHom_apply U ⟨x, hx⟩ a).symm

set_option backward.isDefEq.respectTransparency false in
/-- The natural morphism from the holomorphic locally ringed space to the algebraic scheme. -/
def analytificationToAlgebraic :
    holomorphicLocallyRingedSpace s d ⟶ X.toLocallyRingedSpace where
  __ := analytificationToPresheafedSpace s d
  prop x := by
    change ComplexPoint X s at x
    let : IsLocalHom (Point.stalkHom x).hom := (Point.stalkData x).2.2
    refine ⟨fun a ha ↦ ?_⟩
    apply (isUnit_map_iff (Point.stalkHom x).hom a).mp
    have he := ConcreteCategory.congr_hom (analytification_stalkMap_comp_evaluation s d x) a
    exact he ▸ ha.map (holomorphicStalkEvaluation s d x).hom

end AlgebraicGeometry.ComplexPoint
