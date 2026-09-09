/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticDifferentialOverlap
public import Other.AlgebraicGeometry.RegularHolomorphicForms
public import Other.Algebra.DeRham.Kaehler
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The regular elliptic differential as a global holomorphic sheaf section

The actual regular forms are evaluated on complex points and glued in the holomorphic
de Rham sheaf using their proved compatibility on the two algebraic charts.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance curveOver_smooth : SmoothOfRelativeDimension 1 (Over.mk curveToBase).hom :=
  inferInstanceAs (SmoothOfRelativeDimension 1 curveToBase)

/-- The analytic open lying over a regular open of the elliptic curve. -/
abbrev curveAnalyticOpen (U : curve.Opens) := regularAnalyticOpen (Over.mk curveToBase) U

/-- Interpret regular Kähler differentials as actual holomorphic forms. -/
def curveDifferentialToHolomorphic (U : curve.Opens) :
    KaehlerDifferential ℂ Γ(curve, U) →ₗ[ℂ]
      HolomorphicForm (Over.mk curveToBase) 1 (.op (curveAnalyticOpen U)) 1 :=
  (regularFormToHolomorphicForm (Over.mk curveToBase) 1 U 1).comp
    (Algebra.DeRham.kaehlerToForm ℂ Γ(curve, U))

/-- Evaluation of the regular one-forms commutes with restriction. -/
theorem curveDifferentialToHolomorphic_restrict {U V : curve.Opens} (h : V ≤ U)
    (w : KaehlerDifferential ℂ Γ(curve, U)) :
    holomorphicFormRestriction (Over.mk curveToBase) 1
        (regularAnalyticRestriction (Over.mk curveToBase) h).op 1
        (curveDifferentialToHolomorphic U w) =
      curveDifferentialToHolomorphic V (curveDifferentialRestriction h w) := by
  let := (curveSectionRestriction h).toRingHom.toAlgebra
  let : IsScalarTower ℂ Γ(curve, U) Γ(curve, V) :=
    IsScalarTower.of_algebraMap_eq' (curveSectionRestriction h).comp_algebraMap.symm
  have hr := regularFormToHolomorphicForm_restrict (Over.mk curveToBase) 1 h 1
    (Algebra.DeRham.kaehlerToForm ℂ Γ(curve, U) w)
  have hk := Algebra.DeRham.kaehlerToForm_map ℂ Γ(curve, U) Γ(curve, V) w
  exact hr.trans (congrArg (regularFormToHolomorphicForm (Over.mk curveToBase) 1 V 1) hk.symm)

/-- The analytic images agree on every open coming from the algebraic overlap. -/
theorem curveHolomorphicDifferential_overlap_on (V : curve.Opens)
    (hZ : V ≤ chart 2) (hY : V ≤ chart 1) :
    holomorphicFormRestriction (Over.mk curveToBase) 1
        (regularAnalyticRestriction (Over.mk curveToBase) hZ).op 1
        (curveDifferentialToHolomorphic (chart 2) curveZDifferential) =
      holomorphicFormRestriction (Over.mk curveToBase) 1
        (regularAnalyticRestriction (Over.mk curveToBase) hY).op 1
        (curveDifferentialToHolomorphic (chart 1) curveYDifferential) := by
  rw [curveDifferentialToHolomorphic_restrict, curveDifferentialToHolomorphic_restrict,
    curveDifferential_overlap_on V hZ hY]

/-- The actual sheaf of holomorphic one-forms on the explicit elliptic curve. -/
abbrev curveHolomorphicOneFormSheaf := holomorphicDeRhamSheaf (Over.mk curveToBase) 1 1

/-- A regular differential regarded as a section of the actual holomorphic de Rham sheaf. -/
def curveDifferentialToHolomorphicSheaf (U : curve.Opens)
    (w : KaehlerDifferential ℂ Γ(curve, U)) :
    curveHolomorphicOneFormSheaf.obj.obj (.op (curveAnalyticOpen U)) :=
  (toSheafify (Opens.grothendieckTopology _)
      (holomorphicDeRhamPresheaf (Over.mk curveToBase) 1 1)).app
    (.op (curveAnalyticOpen U)) (curveDifferentialToHolomorphic U w)

/-- The sheafified regular-to-holomorphic comparison respects restriction. -/
theorem curveDifferentialToHolomorphicSheaf_restrict {U V : curve.Opens} (h : V ≤ U)
    (w : KaehlerDifferential ℂ Γ(curve, U)) :
    curveHolomorphicOneFormSheaf.obj.map
        (regularAnalyticRestriction (Over.mk curveToBase) h).op
        (curveDifferentialToHolomorphicSheaf U w) =
      curveDifferentialToHolomorphicSheaf V (curveDifferentialRestriction h w) := by
  let η := toSheafify (Opens.grothendieckTopology _)
    (holomorphicDeRhamPresheaf (Over.mk curveToBase) 1 1)
  have hn := congrArg (fun g => g (curveDifferentialToHolomorphic U w))
    (η.naturality (regularAnalyticRestriction (Over.mk curveToBase) h).op)
  exact hn.symm.trans (congrArg (η.app (.op (curveAnalyticOpen V)))
    (curveDifferentialToHolomorphic_restrict h w))

/-- The local holomorphic sheaf sections satisfy the actual gluing condition. -/
theorem curveHolomorphicSheafDifferential_overlap_on (V : curve.Opens)
    (hZ : V ≤ chart 2) (hY : V ≤ chart 1) :
    curveHolomorphicOneFormSheaf.obj.map
        (regularAnalyticRestriction (Over.mk curveToBase) hZ).op
        (curveDifferentialToHolomorphicSheaf (chart 2) curveZDifferential) =
      curveHolomorphicOneFormSheaf.obj.map
        (regularAnalyticRestriction (Over.mk curveToBase) hY).op
        (curveDifferentialToHolomorphicSheaf (chart 1) curveYDifferential) := by
  rw [curveDifferentialToHolomorphicSheaf_restrict,
    curveDifferentialToHolomorphicSheaf_restrict, curveDifferential_overlap_on V hZ hY]

/-- The two analytic coordinate opens cover all complex points of the curve. -/
theorem curveAnalyticOpen_cover :
    curveAnalyticOpen (chart 2) ⊔ curveAnalyticOpen (chart 1) = ⊤ := by
  apply top_unique
  intro z _
  have hz : z.underlying ∈ chart 1 ⊔ chart 2 := by rw [chart_one_sup_chart_two]; trivial
  exact hz.elim Or.inr Or.inl

/-- A global holomorphic sheaf section exists with the two explicit regular chart formulas. -/
theorem exists_curveGlobalHolomorphicDifferential :
    ∃ s : curveHolomorphicOneFormSheaf.obj.obj (.op ⊤),
      curveHolomorphicOneFormSheaf.obj.map (homOfLE
          (show curveAnalyticOpen (chart 2) ≤ ⊤ from le_top)).op s =
        curveDifferentialToHolomorphicSheaf (chart 2) curveZDifferential ∧
      curveHolomorphicOneFormSheaf.obj.map (homOfLE
          (show curveAnalyticOpen (chart 1) ≤ ⊤ from le_top)).op s =
        curveDifferentialToHolomorphicSheaf (chart 1) curveYDifferential := by
  let U : Fin 2 → Opens (TopCat.of (ComplexPoint (Over.mk curveToBase))) :=
    ![curveAnalyticOpen (chart 2), curveAnalyticOpen (chart 1)]
  let sf : ∀ i : Fin 2, curveHolomorphicOneFormSheaf.obj.obj (.op (U i)) :=
    Fin.cases (curveDifferentialToHolomorphicSheaf (chart 2) curveZDifferential)
      (Fin.cases (curveDifferentialToHolomorphicSheaf (chart 1) curveYDifferential)
        (fun i => i.elim0))
  have hcompat : TopCat.Presheaf.IsCompatible curveHolomorphicOneFormSheaf.obj U sf := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact curveHolomorphicSheafDifferential_overlap_on (chart 2 ⊓ chart 1)
        inf_le_left inf_le_right
    · exact (curveHolomorphicSheafDifferential_overlap_on (chart 1 ⊓ chart 2)
        inf_le_right inf_le_left).symm
    · rfl
  have hcover : (⊤ : Opens (TopCat.of (ComplexPoint (Over.mk curveToBase)))) ≤ iSup U := by
    rw [← curveAnalyticOpen_cover]
    exact sup_le (le_iSup U 0) (le_iSup U 1)
  obtain ⟨s, hs, _⟩ := curveHolomorphicOneFormSheaf.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) hcover sf hcompat
  exact ⟨s, hs 0, hs 1⟩

/-- The global holomorphic one-form obtained by gluing the two explicit invariant forms. -/
def curveGlobalHolomorphicDifferential : curveHolomorphicOneFormSheaf.obj.obj (.op ⊤) :=
  exists_curveGlobalHolomorphicDifferential.choose

theorem curveGlobalHolomorphicDifferential_restrict_z :
    curveHolomorphicOneFormSheaf.obj.map (homOfLE
        (show curveAnalyticOpen (chart 2) ≤ ⊤ from le_top)).op curveGlobalHolomorphicDifferential =
      curveDifferentialToHolomorphicSheaf (chart 2) curveZDifferential :=
  exists_curveGlobalHolomorphicDifferential.choose_spec.1

theorem curveGlobalHolomorphicDifferential_restrict_y :
    curveHolomorphicOneFormSheaf.obj.map (homOfLE
        (show curveAnalyticOpen (chart 1) ≤ ⊤ from le_top)).op curveGlobalHolomorphicDifferential =
      curveDifferentialToHolomorphicSheaf (chart 1) curveYDifferential :=
  exists_curveGlobalHolomorphicDifferential.choose_spec.2

end AlgebraicGeometry.ExplicitEllipticCandidate
