/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HolomorphicDeRham

import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicPoincare

/-!
# Regular functions as holomorphic sections

Evaluation on complex points sends regular functions to holomorphic functions in the
algebraically constructed analytic atlas. This comparison respects scalar multiplication,
restriction, and the algebraic de Rham differential.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- The analytic open lying above a scheme open. -/
def regularAnalyticOpen (U : X.left.Opens) : Opens (TopCat.of (ComplexPoint X)) :=
  ⟨Point.overOpen U, Point.isOpen_overOpen U⟩

/-- The scalar map on a regular section ring induced by the structure morphism. -/
def regularSectionScalar (U : X.left.Opens) : ℂ →+* Γ(X.left, U) :=
  ((Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appTop ≫
    X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom

/-- The scalar structure used by the regular-to-holomorphic comparison. -/
@[instance_reducible]
def regularSectionAlgebra (U : X.left.Opens) : Algebra ℂ Γ(X.left, U) :=
  (regularSectionScalar X U).toAlgebra

attribute [local instance] regularSectionAlgebra

theorem evaluationHom_top (z : ComplexPoint X) :
    Point.evaluationHom (X := X) ⊤ ⟨z, trivial⟩ =
      z.left.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom := by
  change X.left.presheaf.germ ⊤ _ _ ≫ Scheme.stalkClosedPointTo z.left = _
  rw [Scheme.germ_stalkClosedPointTo]
  simp [Scheme.Hom.appTop]

/-- Evaluation respects the actual complex scalar map on regular sections. -/
theorem evaluate_regularSectionScalar (U : X.left.Opens) (c : ℂ)
    (z : ComplexPoint X) (hz : z ∈ Point.overOpen U) :
    Point.evaluate U (regularSectionScalar X U c) z = c := by
  change Point.evaluate U (X.left.presheaf.map (homOfLE le_top).op
    (X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c))) z = c
  rw [← Point.evaluate_res le_top _ z hz]
  rw [← Point.evaluationHom_apply (X := X) ⊤ ⟨z, trivial⟩,
    evaluationHom_top]
  change ((Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appTop ≫ z.left.appTop ≫
    (Scheme.ΓSpecIso ↧ℂ).hom) c = c
  rw [← Scheme.Hom.comp_appTop_assoc, Over.w]
  simp

/-- Evaluation of a regular section is holomorphic near each point of its domain. -/
theorem contMDiffAt_evaluate [SmoothOfRelativeDimension d X.hom]
    (U : X.left.Opens) (s : Γ(X.left, U))
    (z : ComplexPoint X) (hz : z ∈ Point.overOpen U) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (Point.evaluate U s) z := by
  rw [contMDiffAt_iff_source]
  have hzsource := mem_localChart_source X d z
  have h := analyticAt_localChart_symm_evaluate X d z
    ((localChart X d z).map_source hzsource) U s (by
      rw [(localChart X d z).left_inv hzsource]
      exact hz)
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def, Set.range_id, contMDiffWithinAt_univ,
    id_eq, chartAt_eq_localChart]
    using h.contDiffAt.contMDiffAt

/-- A regular section, evaluated as an actual holomorphic function. -/
def regularHolomorphicFunction [SmoothOfRelativeDimension d X.hom]
    (U : X.left.Opens) (s : Γ(X.left, U)) :
    OpenHolomorphicFunctions X d (.op (regularAnalyticOpen X U)) := by
  change C^ω⟮𝓘(ℂ, Fin d → ℂ), regularAnalyticOpen X U; ℂ⟯
  refine ⟨fun z => Point.evaluate U s z.1, fun z => ?_⟩
  exact (contMDiffAt_subtype_iff (I := 𝓘(ℂ, Fin d → ℂ)) (I' := 𝓘(ℂ))
    (U := regularAnalyticOpen X U) (f := Point.evaluate U s)).mpr
      (contMDiffAt_evaluate X d U s z.1 z.2)

/-- Evaluation of regular functions as a homomorphism of rings. -/
def regularToHolomorphicRingHom [SmoothOfRelativeDimension d X.hom]
    (U : X.left.Opens) :
    Γ(X.left, U) →+* OpenHolomorphicFunctions X d (.op (regularAnalyticOpen X U)) where
  toFun := regularHolomorphicFunction X d U
  map_one' := by
    apply ContMDiffMap.ext
    intro z
    change Point.evaluate U 1 z.1 = 1
    simp [Point.evaluate, show z.1.underlying ∈ U from z.2]
  map_mul' a b := by
    apply ContMDiffMap.ext
    intro z
    change Point.evaluate U (a * b) z.1 = Point.evaluate U a z.1 * Point.evaluate U b z.1
    simp [Point.evaluate, show z.1.underlying ∈ U from z.2]
  map_zero' := by
    apply ContMDiffMap.ext
    intro z
    change Point.evaluate U 0 z.1 = 0
    simp [Point.evaluate, show z.1.underlying ∈ U from z.2]
  map_add' a b := by
    apply ContMDiffMap.ext
    intro z
    change Point.evaluate U (a + b) z.1 = Point.evaluate U a z.1 + Point.evaluate U b z.1
    simp [Point.evaluate, show z.1.underlying ∈ U from z.2]

/-- Regular functions map complex-algebraically to the actual holomorphic functions. -/
def regularToHolomorphicAlgHom [SmoothOfRelativeDimension d X.hom]
    (U : X.left.Opens) :
    Γ(X.left, U) →ₐ[ℂ] OpenHolomorphicFunctions X d (.op (regularAnalyticOpen X U)) where
  __ := regularToHolomorphicRingHom X d U
  commutes' c := by
    apply ContMDiffMap.ext
    intro z
    exact evaluate_regularSectionScalar X U c z.1 z.2

/-- Restriction of regular sections preserves the complex scalar structures. -/
def regularSectionRestriction {U V : X.left.Opens} (h : V ≤ U) :
    Γ(X.left, U) →ₐ[ℂ] Γ(X.left, V) where
  toRingHom := (X.left.presheaf.map (homOfLE h).op).hom
  commutes' c := by
    change (((Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appTop ≫
      X.left.presheaf.map (homOfLE le_top).op) ≫
        X.left.presheaf.map (homOfLE h).op) c =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appTop ≫
        X.left.presheaf.map (homOfLE le_top).op) c
    simp only [Category.assoc, ← Functor.map_comp]
    rfl

/-- An inclusion of scheme opens induces an inclusion of the corresponding analytic opens. -/
def regularAnalyticRestriction {U V : X.left.Opens} (h : V ≤ U) :
    regularAnalyticOpen X V ⟶ regularAnalyticOpen X U :=
  homOfLE (fun _ hz => h hz)

/-- Evaluation of regular sections commutes with restriction as holomorphic functions. -/
theorem regularToHolomorphic_restrict [SmoothOfRelativeDimension d X.hom]
    {U V : X.left.Opens} (h : V ≤ U) (s : Γ(X.left, U)) :
    holomorphicRestrictionAlgHom X d (regularAnalyticRestriction X h).op
        (regularToHolomorphicAlgHom X d U s) =
      regularToHolomorphicAlgHom X d V (regularSectionRestriction X h s) := by
  apply ContMDiffMap.ext
  intro z
  exact Point.evaluate_res h s z.1 z.2

/-- The naturality square for the regular-to-holomorphic algebra homomorphism. -/
theorem regularToHolomorphicAlgHom_naturality [SmoothOfRelativeDimension d X.hom]
    {U V : X.left.Opens} (h : V ≤ U) :
    (holomorphicRestrictionAlgHom X d (regularAnalyticRestriction X h).op).comp
        (regularToHolomorphicAlgHom X d U) =
      (regularToHolomorphicAlgHom X d V).comp (regularSectionRestriction X h) := by
  ext s
  exact regularToHolomorphic_restrict X d h s

/-- Algebraic de Rham forms on regular sections map to the actual holomorphic-form quotient. -/
def regularFormToHolomorphicForm [SmoothOfRelativeDimension d X.hom]
    (U : X.left.Opens) (p : ℕ) :
    Algebra.DeRham.Form ℂ Γ(X.left, U) p →ₗ[ℂ]
      HolomorphicForm X d (.op (regularAnalyticOpen X U)) p :=
  (algebraicFormToHolomorphicForm X d (.op (regularAnalyticOpen X U)) p).comp
    (Algebra.DeRham.map ℂ (regularToHolomorphicAlgHom X d U) p)

/-- The regular-to-holomorphic form comparison commutes with exterior differentiation. -/
theorem regularFormToHolomorphicForm_differential [SmoothOfRelativeDimension d X.hom]
    (U : X.left.Opens) (p : ℕ) (a : Algebra.DeRham.Form ℂ Γ(X.left, U) p) :
    regularFormToHolomorphicForm X d U (p + 1) (Algebra.DeRham.differential ℂ _ p a) =
      holomorphicFormDifferential X d (.op (regularAnalyticOpen X U)) p
        (regularFormToHolomorphicForm X d U p a) := by
  simp only [regularFormToHolomorphicForm, LinearMap.comp_apply,
    holomorphicFormDifferential_algebraicFormToHolomorphicForm,
    Algebra.DeRham.map_differential]

/-- The regular-to-holomorphic form comparison commutes with restriction. -/
theorem regularFormToHolomorphicForm_restrict [SmoothOfRelativeDimension d X.hom]
    {U V : X.left.Opens} (h : V ≤ U) (p : ℕ)
    (a : Algebra.DeRham.Form ℂ Γ(X.left, U) p) :
    holomorphicFormRestriction X d (regularAnalyticRestriction X h).op p
        (regularFormToHolomorphicForm X d U p a) =
      regularFormToHolomorphicForm X d V p
        (Algebra.DeRham.map ℂ (regularSectionRestriction X h) p a) := by
  simp only [regularFormToHolomorphicForm, LinearMap.comp_apply,
    holomorphicFormRestriction_algebraicFormToHolomorphicForm]
  congr 1
  rw [← LinearMap.comp_apply, ← Algebra.DeRham.map_comp,
    regularToHolomorphicAlgHom_naturality, Algebra.DeRham.map_comp,
    LinearMap.comp_apply]

end AlgebraicGeometry.ComplexPoint
