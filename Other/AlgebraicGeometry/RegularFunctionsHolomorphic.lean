/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexAnalyticSheaf
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
public import Mathlib.Topology.Sheaves.Functors

/-!
# Regular functions as holomorphic functions

Evaluation of algebraic regular functions defines a morphism from the algebraic
structure sheaf to the direct image of the holomorphic structure sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Topology
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open Point

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

/-- The continuous map forgetting the complex-valued point's residue-field map. -/
def underlyingContinuousMap : TopCat.of (ComplexPoint X s) ⟶ X.carrier :=
  TopCat.ofHom ⟨Point.underlying, continuous_def.mpr fun _ hU ↦
    isOpen_overOpen (⟨_, hU⟩ : X.Opens)⟩

/-- The analytic open lying over an algebraic open. -/
def analyticOpen (U : X.Opens) : Opens (ComplexPoint X s) :=
  (Opens.map (underlyingContinuousMap s)).obj U

/-- A regular function is continuous on the open where it is defined. -/
theorem continuousOn_evaluate (U : X.Opens) (a : Γ(X, U)) :
    ContinuousOn (Point.evaluate (structureMap := s) U a) (Point.overOpen U) := by
  rw [continuousOn_iff']
  intro V hV
  refine ⟨Point.overOpen U ∩ Point.evaluate U a ⁻¹' V,
    isOpen_overOpen_inter_preimage U a V hV, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  tauto

variable (d : ℕ) [SmoothOfRelativeDimension d s]

/-- Evaluation of a regular function is holomorphic at every point in its domain. -/
theorem contMDiffAt_evaluate (U : X.Opens) (a : Γ(X, U))
    (x : ComplexPoint X s) (hx : x ∈ Point.overOpen U) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (Point.evaluate U a) x := by
  let : IsManifold 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X s) := isManifold_omega s d
  have hxc : x ∈ (localChart s d x).source := mem_localChart_source s d x
  rw [contMDiffAt_iff_of_mem_source (I := 𝓘(ℂ, Fin d → ℂ)) (I' := 𝓘(ℂ))
    (x := x) (y := Point.evaluate U a x) hxc (by simp)]
  refine ⟨((continuousOn_evaluate s U a) x hx).continuousAt
    ((isOpen_overOpen U).mem_nhds hx), ?_⟩
  have hw := (localChart s d x).map_source hxc
  have hU : (localChart s d x).symm (localChart s d x x) ∈ Point.overOpen U := by
    rw [(localChart s d x).left_inv hxc]
    exact hx
  have ha := analyticAt_localChart_symm_evaluate s d x hw U a hU
  have hchart : chartAt (Fin d → ℂ) x = localChart s d x := rfl
  simpa only [extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Function.comp_apply, Function.comp_def,
    id_eq, Set.range_id, hchart, chartAt_self_eq, OpenPartialHomeomorph.refl_apply] using
    ha.contDiffAt.contDiffWithinAt

/-- A regular function, regarded as a holomorphic function on the corresponding analytic open. -/
def regularFunctionHolomorphic (U : X.Opens) (a : Γ(X, U)) :
    C^ω⟮𝓘(ℂ, Fin d → ℂ), analyticOpen s U; ℂ⟯ :=
  ⟨fun x : analyticOpen s U ↦ Point.evaluate U a (x : ComplexPoint X s), fun x ↦
    (contMDiffAt_subtype_iff (U := analyticOpen s U) (x := x)
      (f := Point.evaluate U a)).mpr
        (contMDiffAt_evaluate s d U a (x : ComplexPoint X s) x.property)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating regular functions is a ring homomorphism into holomorphic functions. -/
def regularFunctionsToHolomorphic (U : X.Opens) :
    Γ(X, U) →+* C^ω⟮𝓘(ℂ, Fin d → ℂ), analyticOpen s U; ℂ⟯ where
  toFun := regularFunctionHolomorphic s d U
  map_one' := by
    apply Subtype.ext
    funext x
    change Point.evaluate U (1 : Γ(X, U)) (x : ComplexPoint X s) = 1
    rw [← Point.evaluationHom_hom_apply U ⟨(x : ComplexPoint X s), x.property⟩]
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    funext x
    change Point.evaluate U (a * b) (x : ComplexPoint X s) =
      Point.evaluate U a (x : ComplexPoint X s) * Point.evaluate U b (x : ComplexPoint X s)
    simp only [← Point.evaluationHom_hom_apply U ⟨(x : ComplexPoint X s), x.property⟩]
    exact map_mul _ a b
  map_zero' := by
    apply Subtype.ext
    funext x
    change Point.evaluate U (0 : Γ(X, U)) (x : ComplexPoint X s) = 0
    rw [← Point.evaluationHom_hom_apply U ⟨(x : ComplexPoint X s), x.property⟩]
    exact map_zero _
  map_add' a b := by
    apply Subtype.ext
    funext x
    change Point.evaluate U (a + b) (x : ComplexPoint X s) =
      Point.evaluate U a (x : ComplexPoint X s) + Point.evaluate U b (x : ComplexPoint X s)
    simp only [← Point.evaluationHom_hom_apply U ⟨(x : ComplexPoint X s), x.property⟩]
    exact map_add _ a b

set_option backward.isDefEq.respectTransparency false in
/-- The algebraic structure sheaf maps to holomorphic functions by evaluating sections. -/
def regularToHolomorphicSheaf :
    X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat (underlyingContinuousMap s)).obj
      (holomorphicFunctionSheaf s d) where
  hom :=
    { app U := CommRingCat.ofHom (regularFunctionsToHolomorphic s d (unop U))
      naturality := by
        intro U V i
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        apply Subtype.ext
        funext x
        exact (Point.evaluate_res (leOfHom i.unop) a (x : ComplexPoint X s) x.property).symm }

end AlgebraicGeometry.ComplexPoint
