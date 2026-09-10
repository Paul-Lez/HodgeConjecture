/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicOneFormLocalDivision
public import Other.AlgebraicGeometry.ExplicitEllipticDifferentialNowhereVanishing
public import Other.AlgebraicGeometry.ProjectiveAnalytification
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Geometry.Manifold.Complex

/-!
# Local rank one for holomorphic differentials on the explicit elliptic curve

The explicit invariant differential has already been shown to be nonzero at every complex point.
Here we combine that result with local division of analytic one-forms and the local surjectivity of
sheafification.  Every section of the actual sheaf of holomorphic one-forms is locally a unique
holomorphic-function multiple of the invariant differential.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (X : Over (Spec (CommRingCat.of ℂ)))
  [SmoothOfRelativeDimension 1 X.hom]

/-- Every section of the sheafification of holomorphic one-forms has a presheaf representative
near each point. -/
theorem exists_local_holomorphicOneForm_representation
    (U : Opens (TopCat.of (ComplexPoint X)))
    (s : (holomorphicDeRhamSheaf X 1 1).obj.obj (.op U))
    (x : ComplexPoint X) (hxU : x ∈ U) :
    ∃ (V : Opens (TopCat.of (ComplexPoint X))) (hV : V ≤ U)
      (alpha : HolomorphicForm X 1 (.op V) 1),
      x ∈ V ∧
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X 1 1)).app (.op V) alpha =
        (holomorphicDeRhamSheaf X 1 1).obj.map (homOfLE hV).op s := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  let P := holomorphicDeRhamPresheaf X 1 1
  let eta := toSheafify J P
  have hloc : TopCat.Presheaf.IsLocallySurjective eta :=
    (inferInstance : CategoryTheory.Presheaf.IsLocallySurjective J eta)
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hloc
  obtain ⟨V, hV, ⟨alpha, halpha⟩, hxV⟩ := hloc U s x hxU
  exact ⟨V, hV, alpha, hxV, halpha⟩

/-- Sheafification of a holomorphic one-form commutes with restriction. -/
theorem holomorphicDeRham_toSheafify_restrict
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (w : HolomorphicForm X 1 U 1) :
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X 1 1)).app V
        (holomorphicFormRestriction X 1 i 1 w) =
      (sheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X 1 1)).map i
        ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X 1 1)).app U w) := by
  let eta := toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicDeRhamPresheaf X 1 1)
  change eta.app V ((holomorphicDeRhamPresheaf X 1 1).map i w) =
    (sheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X 1 1)).map i (eta.app U w)
  have h := congrArg (fun f => f w) (eta.naturality i)
  simpa only [ConcreteCategory.comp_apply] using h

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev curveAnalyticVariety : Over (Spec (CommRingCat.of ℂ)) := Over.mk curveToBase

local instance curveAnalytic_smooth : SmoothOfRelativeDimension 1 curveAnalyticVariety.hom :=
  curveOver_smooth

local instance curveAnalytic_projective : IsProjective curveAnalyticVariety.hom :=
  inferInstanceAs (IsProjective curveToBase)

/-- The invariant differential remains nonzero after restriction inside the `Z` chart. -/
theorem curveZDifferential_restriction_evaluation_ne_zero
    [hcurve : SmoothOfRelativeDimension 1 curveAnalyticVariety.hom]
    (U : Opens (TopCat.of (ComplexPoint curveAnalyticVariety)))
    (hU : U ≤ curveAnalyticOpen (chart 2))
    (x : ComplexPoint curveAnalyticVariety) (hxU : x ∈ U) :
    (@holomorphicFormEvaluation curveAnalyticVariety 1 hcurve (.op U) x 1
        (@localChart curveAnalyticVariety 1 hcurve x x)
        (@localChart_center_mem_chartSectionDomain curveAnalyticVariety hcurve (.op U) x hxU)
        (@holomorphicFormRestriction curveAnalyticVariety 1 hcurve _ _ (homOfLE hU).op 1
          (curveDifferentialToHolomorphic (chart 2) curveZDifferential))) ≠ 0 := by
  rw [holomorphicFormEvaluation_restriction]
  exact curveZDifferential_evaluation_ne_zero x (hU hxU)

/-- The invariant differential remains nonzero after restriction inside the chart containing
infinity. -/
theorem curveYDifferential_restriction_evaluation_ne_zero
    [hcurve : SmoothOfRelativeDimension 1 curveAnalyticVariety.hom]
    (U : Opens (TopCat.of (ComplexPoint curveAnalyticVariety)))
    (hU : U ≤ curveAnalyticOpen (chart 1))
    (x : ComplexPoint curveAnalyticVariety) (hxU : x ∈ U) :
    (@holomorphicFormEvaluation curveAnalyticVariety 1 hcurve (.op U) x 1
        (@localChart curveAnalyticVariety 1 hcurve x x)
        (@localChart_center_mem_chartSectionDomain curveAnalyticVariety hcurve (.op U) x hxU)
        (@holomorphicFormRestriction curveAnalyticVariety 1 hcurve _ _ (homOfLE hU).op 1
          (curveDifferentialToHolomorphic (chart 1) curveYDifferential))) ≠ 0 := by
  rw [holomorphicFormEvaluation_restriction]
  exact curveYDifferential_evaluation_ne_zero x (hU hxU)

abbrev curveHolomorphicOneFormPresheaf :=
  holomorphicDeRhamPresheaf (Over.mk curveToBase) 1 1

abbrev curveHolomorphicOneFormPresheafSheafification :=
  curveHolomorphicOneFormSheaf.obj

abbrev curveHolomorphicOneFormSheafificationUnit :=
  toSheafify (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint (Over.mk curveToBase))))
    curveHolomorphicOneFormPresheaf

/-- Local coefficient data for a global form at a point of the `Z` chart. -/
theorem exists_local_curveOneForm_coefficient_z
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤))
    (x : ComplexPoint curveAnalyticVariety)
    (hxC : x ∈ curveAnalyticOpen (chart 2)) :
    ∃ (W : Opens (TopCat.of (ComplexPoint curveAnalyticVariety)))
      (hWC : W ≤ curveAnalyticOpen (chart 2))
      (q : OpenHolomorphicFunctions curveAnalyticVariety 1 (.op W)),
      x ∈ W ∧
      curveHolomorphicOneFormSheafificationUnit.app (.op W)
          (holomorphicFormFunctionMul curveAnalyticVariety 1 (.op W) 1 q
            (holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hWC).op 1
              (curveDifferentialToHolomorphic (chart 2) curveZDifferential))) =
        curveHolomorphicOneFormPresheafSheafification.map (homOfLE (show W ≤ ⊤ from le_top)).op s ∧
      curveHolomorphicOneFormSheafificationUnit.app (.op W)
          (holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hWC).op 1
            (curveDifferentialToHolomorphic (chart 2) curveZDifferential)) =
        curveHolomorphicOneFormPresheafSheafification.map (homOfLE (show W ≤ ⊤ from le_top)).op
          curveGlobalHolomorphicDifferential ∧
      ∀ (z : ComplexPoint curveAnalyticVariety) (hz : z ∈ W),
        holomorphicFormEvaluation curveAnalyticVariety 1 (.op W) z 1
          (localChart curveAnalyticVariety 1 z z)
          (localChart_center_mem_chartSectionDomain curveAnalyticVariety (.op W) z hz)
          (holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hWC).op 1
            (curveDifferentialToHolomorphic (chart 2) curveZDifferential)) ≠ 0 := by
  let C := curveAnalyticOpen (chart 2)
  let topC : Opposite.op (⊤ : Opens (TopCat.of (ComplexPoint curveAnalyticVariety))) ⟶
      Opposite.op C :=
    (homOfLE le_top).op
  let sC := curveHolomorphicOneFormPresheafSheafification.map topC s
  obtain ⟨V, hVC, alpha, hxV, halpha⟩ :=
    exists_local_holomorphicOneForm_representation curveAnalyticVariety C sC x hxC
  let betaV : HolomorphicForm curveAnalyticVariety 1 (.op V) 1 :=
    holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hVC).op 1
      (curveDifferentialToHolomorphic (chart 2) curveZDifferential)
  have hbetaV : holomorphicFormEvaluation curveAnalyticVariety 1 (.op V) x 1
      (localChart curveAnalyticVariety 1 x x)
      (localChart_center_mem_chartSectionDomain curveAnalyticVariety (.op V) x hxV) betaV ≠ 0 :=
    curveZDifferential_restriction_evaluation_ne_zero V hVC x hxV
  obtain ⟨Wop, k, q, hxW, heq⟩ :=
    exists_local_holomorphicOneForm_eq_functionMul_of_ne_zero
      curveAnalyticVariety (.op V) x hxV alpha betaV hbetaV
  let W := Opposite.unop Wop
  have hWV : W ≤ V := leOfHom k.unop
  have hWC : W ≤ C := hWV.trans hVC
  have hcomp : (homOfLE hVC).op ≫ k = (homOfLE hWC).op := Subsingleton.elim _ _
  have hbeta : holomorphicFormRestriction curveAnalyticVariety 1 k 1 betaV =
      holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hWC).op 1
        (curveDifferentialToHolomorphic (chart 2) curveZDifferential) := by
    change holomorphicFormRestriction curveAnalyticVariety 1 k 1
        (holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hVC).op 1
          (curveDifferentialToHolomorphic (chart 2) curveZDifferential)) = _
    rw [← LinearMap.comp_apply, ← holomorphicFormRestriction_comp, hcomp]
  rw [hbeta] at heq
  refine ⟨W, hWC, q, hxW, ?_, ?_, ?_⟩
  · rw [← heq]
    rw [holomorphicDeRham_toSheafify_restrict]
    rw [halpha]
    change curveHolomorphicOneFormPresheafSheafification.map k
        (curveHolomorphicOneFormPresheafSheafification.map (homOfLE hVC).op
          (curveHolomorphicOneFormPresheafSheafification.map topC s)) = _
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 2
  · rw [holomorphicDeRham_toSheafify_restrict]
    have hz := curveGlobalHolomorphicDifferential_restrict_z
    have hz' : curveHolomorphicOneFormPresheafSheafification.map topC curveGlobalHolomorphicDifferential =
        curveHolomorphicOneFormSheafificationUnit.app (.op C)
          (curveDifferentialToHolomorphic (chart 2) curveZDifferential) := by
      simpa only [curveAnalyticVariety, curveHolomorphicOneFormPresheafSheafification, curveHolomorphicOneFormSheafificationUnit,
        curveDifferentialToHolomorphicSheaf] using hz
    change curveHolomorphicOneFormPresheafSheafification.map (homOfLE hWC).op
        (curveHolomorphicOneFormSheafificationUnit.app (.op C)
          (curveDifferentialToHolomorphic (chart 2) curveZDifferential)) = _
    rw [← hz']
    change curveHolomorphicOneFormPresheafSheafification.map (homOfLE hWC).op
        (curveHolomorphicOneFormPresheafSheafification.map topC curveGlobalHolomorphicDifferential) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  · intro z hz
    exact curveZDifferential_restriction_evaluation_ne_zero W hWC z hz

/-- Local coefficient data for a global form at a point of the chart containing infinity. -/
theorem exists_local_curveOneForm_coefficient_y
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤))
    (x : ComplexPoint curveAnalyticVariety)
    (hxC : x ∈ curveAnalyticOpen (chart 1)) :
    ∃ (W : Opens (TopCat.of (ComplexPoint curveAnalyticVariety)))
      (hWC : W ≤ curveAnalyticOpen (chart 1))
      (q : OpenHolomorphicFunctions curveAnalyticVariety 1 (.op W)),
      x ∈ W ∧
      curveHolomorphicOneFormSheafificationUnit.app (.op W)
          (holomorphicFormFunctionMul curveAnalyticVariety 1 (.op W) 1 q
            (holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hWC).op 1
              (curveDifferentialToHolomorphic (chart 1) curveYDifferential))) =
        curveHolomorphicOneFormPresheafSheafification.map (homOfLE (show W ≤ ⊤ from le_top)).op s ∧
      curveHolomorphicOneFormSheafificationUnit.app (.op W)
          (holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hWC).op 1
            (curveDifferentialToHolomorphic (chart 1) curveYDifferential)) =
        curveHolomorphicOneFormPresheafSheafification.map (homOfLE (show W ≤ ⊤ from le_top)).op
          curveGlobalHolomorphicDifferential ∧
      ∀ (z : ComplexPoint curveAnalyticVariety) (hz : z ∈ W),
        holomorphicFormEvaluation curveAnalyticVariety 1 (.op W) z 1
          (localChart curveAnalyticVariety 1 z z)
          (localChart_center_mem_chartSectionDomain curveAnalyticVariety (.op W) z hz)
          (holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hWC).op 1
            (curveDifferentialToHolomorphic (chart 1) curveYDifferential)) ≠ 0 := by
  let C := curveAnalyticOpen (chart 1)
  let topC : Opposite.op (⊤ : Opens (TopCat.of (ComplexPoint curveAnalyticVariety))) ⟶
      Opposite.op C :=
    (homOfLE le_top).op
  let sC := curveHolomorphicOneFormPresheafSheafification.map topC s
  obtain ⟨V, hVC, alpha, hxV, halpha⟩ :=
    exists_local_holomorphicOneForm_representation curveAnalyticVariety C sC x hxC
  let betaV : HolomorphicForm curveAnalyticVariety 1 (.op V) 1 :=
    holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hVC).op 1
      (curveDifferentialToHolomorphic (chart 1) curveYDifferential)
  have hbetaV : holomorphicFormEvaluation curveAnalyticVariety 1 (.op V) x 1
      (localChart curveAnalyticVariety 1 x x)
      (localChart_center_mem_chartSectionDomain curveAnalyticVariety (.op V) x hxV) betaV ≠ 0 :=
    curveYDifferential_restriction_evaluation_ne_zero V hVC x hxV
  obtain ⟨Wop, k, q, hxW, heq⟩ :=
    exists_local_holomorphicOneForm_eq_functionMul_of_ne_zero
      curveAnalyticVariety (.op V) x hxV alpha betaV hbetaV
  let W := Opposite.unop Wop
  have hWV : W ≤ V := leOfHom k.unop
  have hWC : W ≤ C := hWV.trans hVC
  have hcomp : (homOfLE hVC).op ≫ k = (homOfLE hWC).op := Subsingleton.elim _ _
  have hbeta : holomorphicFormRestriction curveAnalyticVariety 1 k 1 betaV =
      holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hWC).op 1
        (curveDifferentialToHolomorphic (chart 1) curveYDifferential) := by
    change holomorphicFormRestriction curveAnalyticVariety 1 k 1
        (holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hVC).op 1
          (curveDifferentialToHolomorphic (chart 1) curveYDifferential)) = _
    rw [← LinearMap.comp_apply, ← holomorphicFormRestriction_comp, hcomp]
  rw [hbeta] at heq
  refine ⟨W, hWC, q, hxW, ?_, ?_, ?_⟩
  · rw [← heq]
    rw [holomorphicDeRham_toSheafify_restrict]
    rw [halpha]
    change curveHolomorphicOneFormPresheafSheafification.map k
        (curveHolomorphicOneFormPresheafSheafification.map (homOfLE hVC).op
          (curveHolomorphicOneFormPresheafSheafification.map topC s)) = _
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 2
  · rw [holomorphicDeRham_toSheafify_restrict]
    have hy := curveGlobalHolomorphicDifferential_restrict_y
    have hy' : curveHolomorphicOneFormPresheafSheafification.map topC curveGlobalHolomorphicDifferential =
        curveHolomorphicOneFormSheafificationUnit.app (.op C)
          (curveDifferentialToHolomorphic (chart 1) curveYDifferential) := by
      simpa only [curveAnalyticVariety, curveHolomorphicOneFormPresheafSheafification, curveHolomorphicOneFormSheafificationUnit,
        curveDifferentialToHolomorphicSheaf] using hy
    change curveHolomorphicOneFormPresheafSheafification.map (homOfLE hWC).op
        (curveHolomorphicOneFormSheafificationUnit.app (.op C)
          (curveDifferentialToHolomorphic (chart 1) curveYDifferential)) = _
    rw [← hy']
    change curveHolomorphicOneFormPresheafSheafification.map (homOfLE hWC).op
        (curveHolomorphicOneFormPresheafSheafification.map topC curveGlobalHolomorphicDifferential) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  · intro z hz
    exact curveYDifferential_restriction_evaluation_ne_zero W hWC z hz

/-- Every sheafified global holomorphic one-form is locally a function multiple of the explicit
invariant differential. -/
theorem curveGlobalOneForm_locally_functionMul
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤))
    (x : ComplexPoint curveAnalyticVariety) :
    ∃ (W : Opens (TopCat.of (ComplexPoint curveAnalyticVariety)))
      (q : OpenHolomorphicFunctions curveAnalyticVariety 1 (.op W))
      (beta : HolomorphicForm curveAnalyticVariety 1 (.op W) 1),
      x ∈ W ∧
      curveHolomorphicOneFormSheafificationUnit.app (.op W)
          (holomorphicFormFunctionMul curveAnalyticVariety 1 (.op W) 1 q beta) =
        curveHolomorphicOneFormPresheafSheafification.map (homOfLE (show W ≤ ⊤ from le_top)).op s ∧
      curveHolomorphicOneFormSheafificationUnit.app (.op W) beta =
        curveHolomorphicOneFormPresheafSheafification.map (homOfLE (show W ≤ ⊤ from le_top)).op
          curveGlobalHolomorphicDifferential ∧
      ∀ (z : ComplexPoint curveAnalyticVariety) (hz : z ∈ W),
        holomorphicFormEvaluation curveAnalyticVariety 1 (.op W) z 1
          (localChart curveAnalyticVariety 1 z z)
          (localChart_center_mem_chartSectionDomain curveAnalyticVariety (.op W) z hz) beta ≠ 0 := by
  have hx : x.underlying ∈ chart 1 ⊔ chart 2 := by
    rw [chart_one_sup_chart_two]
    trivial
  rcases hx with hxY | hxZ
  · obtain ⟨W, hW, q, hxW, hs, homega, hne⟩ :=
      exists_local_curveOneForm_coefficient_y s x hxY
    exact ⟨W, q,
      holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hW).op 1
        (curveDifferentialToHolomorphic (chart 1) curveYDifferential),
      hxW, hs, homega, hne⟩
  · obtain ⟨W, hW, q, hxW, hs, homega, hne⟩ :=
      exists_local_curveOneForm_coefficient_z s x hxZ
    exact ⟨W, q,
      holomorphicFormRestriction curveAnalyticVariety 1 (homOfLE hW).op 1
        (curveDifferentialToHolomorphic (chart 2) curveZDifferential),
      hxW, hs, homega, hne⟩

/-- Chosen local coefficient data for a global holomorphic one-form. -/
structure CurveOneFormLocalCoefficient
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤))
    (x : ComplexPoint curveAnalyticVariety) where
  U : Opens (TopCat.of (ComplexPoint curveAnalyticVariety))
  q : OpenHolomorphicFunctions curveAnalyticVariety 1 (.op U)
  beta : HolomorphicForm curveAnalyticVariety 1 (.op U) 1
  mem : x ∈ U
  form_eq :
    curveHolomorphicOneFormSheafificationUnit.app (.op U)
        (holomorphicFormFunctionMul curveAnalyticVariety 1 (.op U) 1 q beta) =
      curveHolomorphicOneFormPresheafSheafification.map
        (homOfLE (show U ≤ ⊤ from le_top)).op s
  generator_eq :
    curveHolomorphicOneFormSheafificationUnit.app (.op U) beta =
      curveHolomorphicOneFormPresheafSheafification.map
        (homOfLE (show U ≤ ⊤ from le_top)).op curveGlobalHolomorphicDifferential
  generator_ne : ∀ (z : ComplexPoint curveAnalyticVariety) (hz : z ∈ U),
    holomorphicFormEvaluation curveAnalyticVariety 1 (.op U) z 1
      (localChart curveAnalyticVariety 1 z z)
      (localChart_center_mem_chartSectionDomain curveAnalyticVariety (.op U) z hz) beta ≠ 0

/-- Noncomputably choose the local coefficient data supplied at each point. -/
def curveOneFormLocalCoefficient
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤))
    (x : ComplexPoint curveAnalyticVariety) : CurveOneFormLocalCoefficient s x :=
  Classical.choice (show Nonempty (CurveOneFormLocalCoefficient s x) by
    obtain ⟨U, q, beta, hxU, hs, homega, hne⟩ :=
      curveGlobalOneForm_locally_functionMul s x
    exact ⟨⟨U, q, beta, hxU, hs, homega, hne⟩⟩)

/-- The locally defined coefficients of a global holomorphic one-form agree on pairwise
intersections.  The proof uses the injectivity of sheafification and cancellation by the
nowhere-vanishing invariant differential. -/
theorem curveOneFormLocalCoefficient_compatible
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤))
    (x y : ComplexPoint curveAnalyticVariety) :
    (holomorphicFunctionSheaf curveAnalyticVariety 1).presheaf.map
        (homOfLE inf_le_left :
          (curveOneFormLocalCoefficient s x).U ⊓ (curveOneFormLocalCoefficient s y).U ⟶
            (curveOneFormLocalCoefficient s x).U).op
        (curveOneFormLocalCoefficient s x).q =
      (holomorphicFunctionSheaf curveAnalyticVariety 1).presheaf.map
        (homOfLE inf_le_right :
          (curveOneFormLocalCoefficient s x).U ⊓ (curveOneFormLocalCoefficient s y).U ⟶
            (curveOneFormLocalCoefficient s y).U).op
        (curveOneFormLocalCoefficient s y).q := by
  let dx := curveOneFormLocalCoefficient s x
  let dy := curveOneFormLocalCoefficient s y
  let I := dx.U ⊓ dy.U
  let ix : Opposite.op dx.U ⟶ Opposite.op I := (homOfLE inf_le_left).op
  let iy : Opposite.op dy.U ⟶ Opposite.op I := (homOfLE inf_le_right).op
  let bx := holomorphicFormRestriction curveAnalyticVariety 1 ix 1 dx.beta
  let byForm := holomorphicFormRestriction curveAnalyticVariety 1 iy 1 dy.beta
  have hb : bx = byForm := by
    apply holomorphicDeRham_toSheafify_injective curveAnalyticVariety 1 I 1
    rw [holomorphicDeRham_toSheafify_restrict,
      holomorphicDeRham_toSheafify_restrict]
    rw [dx.generator_eq, dy.generator_eq]
    change curveHolomorphicOneFormPresheafSheafification.map ix
        (curveHolomorphicOneFormPresheafSheafification.map
          (homOfLE (show dx.U ≤ ⊤ from le_top)).op
          curveGlobalHolomorphicDifferential) =
      curveHolomorphicOneFormPresheafSheafification.map iy
        (curveHolomorphicOneFormPresheafSheafification.map
          (homOfLE (show dy.U ≤ ⊤ from le_top)).op
          curveGlobalHolomorphicDifferential)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 2
  let qx := holomorphicRestrictionAlgHom curveAnalyticVariety 1 ix dx.q
  let qy := holomorphicRestrictionAlgHom curveAnalyticVariety 1 iy dy.q
  have hm0 :
      holomorphicFormRestriction curveAnalyticVariety 1 ix 1
          (holomorphicFormFunctionMul curveAnalyticVariety 1 (.op dx.U) 1 dx.q dx.beta) =
        holomorphicFormRestriction curveAnalyticVariety 1 iy 1
          (holomorphicFormFunctionMul curveAnalyticVariety 1 (.op dy.U) 1 dy.q dy.beta) := by
    apply holomorphicDeRham_toSheafify_injective curveAnalyticVariety 1 I 1
    rw [holomorphicDeRham_toSheafify_restrict,
      holomorphicDeRham_toSheafify_restrict]
    rw [dx.form_eq, dy.form_eq]
    change curveHolomorphicOneFormPresheafSheafification.map ix
        (curveHolomorphicOneFormPresheafSheafification.map
          (homOfLE (show dx.U ≤ ⊤ from le_top)).op s) =
      curveHolomorphicOneFormPresheafSheafification.map iy
        (curveHolomorphicOneFormPresheafSheafification.map
          (homOfLE (show dy.U ≤ ⊤ from le_top)).op s)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 2
  have hm : holomorphicFormFunctionMul curveAnalyticVariety 1 (.op I) 1 qx bx =
      holomorphicFormFunctionMul curveAnalyticVariety 1 (.op I) 1 qy byForm := by
    rw [← holomorphicFormRestriction_functionMul,
      ← holomorphicFormRestriction_functionMul]
    exact hm0
  rw [← hb] at hm
  have hbx : ∀ (z : ComplexPoint curveAnalyticVariety) (hz : z ∈ I),
      holomorphicFormEvaluation curveAnalyticVariety 1 (.op I) z 1
        (localChart curveAnalyticVariety 1 z z)
        (localChart_center_mem_chartSectionDomain curveAnalyticVariety (.op I) z hz) bx ≠ 0 := by
    intro z hz
    rw [holomorphicFormEvaluation_restriction]
    exact dx.generator_ne z hz.1
  exact holomorphicFormFunctionMul_injective_of_pointwise_ne_zero
    curveAnalyticVariety (.op I) bx hbx hm

/-- The compatible local coefficients glue to a global holomorphic function. -/
theorem exists_curveOneFormGlobalCoefficient
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤)) :
    ∃ q : OpenHolomorphicFunctions curveAnalyticVariety 1 (.op ⊤),
      ∀ x : ComplexPoint curveAnalyticVariety,
        (holomorphicFunctionSheaf curveAnalyticVariety 1).presheaf.map
          (homOfLE (show (curveOneFormLocalCoefficient s x).U ≤ ⊤ from le_top)).op q =
            (curveOneFormLocalCoefficient s x).q := by
  let U : ComplexPoint curveAnalyticVariety →
      Opens (TopCat.of (ComplexPoint curveAnalyticVariety)) :=
    fun x => (curveOneFormLocalCoefficient s x).U
  let sf : ∀ x, (holomorphicFunctionSheaf curveAnalyticVariety 1).presheaf.obj (.op (U x)) :=
    fun x => (curveOneFormLocalCoefficient s x).q
  have hcompat : TopCat.Presheaf.IsCompatible
      (holomorphicFunctionSheaf curveAnalyticVariety 1).presheaf U sf := by
    intro x y
    exact curveOneFormLocalCoefficient_compatible s x y
  have hcover : (⊤ : Opens (TopCat.of (ComplexPoint curveAnalyticVariety))) ≤ iSup U := by
    intro x _
    exact (le_iSup U x) (curveOneFormLocalCoefficient s x).mem
  obtain ⟨q, hq, _⟩ := (holomorphicFunctionSheaf curveAnalyticVariety 1).existsUnique_gluing'
    U ⊤ (fun _ => homOfLE le_top) hcover sf hcompat
  exact ⟨q, hq⟩

/-- The global holomorphic coefficient of a global one-form. -/
def curveOneFormGlobalCoefficient
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤)) :
    OpenHolomorphicFunctions curveAnalyticVariety 1 (.op ⊤) :=
  (exists_curveOneFormGlobalCoefficient s).choose

theorem curveOneFormGlobalCoefficient_restrict
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤))
    (x : ComplexPoint curveAnalyticVariety) :
    (holomorphicFunctionSheaf curveAnalyticVariety 1).presheaf.map
        (homOfLE (show (curveOneFormLocalCoefficient s x).U ≤ ⊤ from le_top)).op
        (curveOneFormGlobalCoefficient s) =
      (curveOneFormLocalCoefficient s x).q :=
  (exists_curveOneFormGlobalCoefficient s).choose_spec x

/-- On a connected analytification, the global coefficient of every holomorphic one-form is a
single complex constant. -/
theorem exists_curveOneFormGlobalCoefficient_eq_algebraMap
    [ConnectedSpace (ComplexPoint curveAnalyticVariety)]
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤)) :
    ∃ c : ℂ, curveOneFormGlobalCoefficient s =
      algebraMap ℂ (OpenHolomorphicFunctions curveAnalyticVariety 1 (.op ⊤)) c := by
  letI : IsManifold (modelWithCornersSelf ℂ (Fin 1 → ℂ)) ω
      (ComplexPoint curveAnalyticVariety) := isManifold_omega curveAnalyticVariety 1
  letI : ConnectedSpace
      {x : ComplexPoint curveAnalyticVariety // x ∈ (⊤ : Opens _)} :=
    (Homeomorph.Set.univ (ComplexPoint curveAnalyticVariety)).connectedSpace_iff.mpr
      inferInstance
  letI : CompactSpace
      {x : ComplexPoint curveAnalyticVariety // x ∈ (⊤ : Opens _)} :=
    isCompact_iff_compactSpace.mp isCompact_univ
  let q := curveOneFormGlobalCoefficient s
  have hlocal : IsLocallyConstant q.1 :=
    ((holomorphicFunctionSheaf_section_analytic curveAnalyticVariety 1 q).mdifferentiable
      (by simp)).isLocallyConstant
  obtain ⟨c, hc⟩ := hlocal.exists_eq_const
  refine ⟨c, Subtype.ext ?_⟩
  change q.1 = Function.const _ c
  exact hc

/-- Scalar multiplication on the actual sheafified sheaf of holomorphic one-forms. -/
abbrev curveHolomorphicOneFormScalarSheafMap (c : ℂ) :=
  (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint curveAnalyticVariety)))
      AddCommGrpCat).map
    (scalarHolomorphicDeRhamPresheaf curveAnalyticVariety 1 1 c)

/-- The scalar multiple of the explicit global invariant differential. -/
def curveGlobalHolomorphicDifferential_smul (c : ℂ) :
    curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤) :=
  (curveHolomorphicOneFormScalarSheafMap c).hom.app (.op ⊤)
    curveGlobalHolomorphicDifferential

/-- Scalar multiplication commutes with the sheafification unit on one-forms. -/
theorem curveHolomorphicOneFormScalar_toSheafify (c : ℂ)
    (U : (Opens (TopCat.of (ComplexPoint curveAnalyticVariety)))ᵒᵖ)
    (beta : HolomorphicForm curveAnalyticVariety 1 U 1) :
    (curveHolomorphicOneFormScalarSheafMap c).hom.app U
        (curveHolomorphicOneFormSheafificationUnit.app U beta) =
      curveHolomorphicOneFormSheafificationUnit.app U (c • beta) := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint curveAnalyticVariety))
  let P := holomorphicDeRhamPresheaf curveAnalyticVariety 1 1
  let a := scalarHolomorphicDeRhamPresheaf curveAnalyticVariety 1 1 c
  change ((toSheafify J P ≫ sheafifyMap J a).app U) beta =
    ((a ≫ toSheafify J P).app U) beta
  rw [toSheafify_naturality]

/-- Restriction of a scalar multiple of the global invariant differential. -/
theorem curveGlobalHolomorphicDifferential_smul_restrict (c : ℂ)
    (U : Opens (TopCat.of (ComplexPoint curveAnalyticVariety))) :
    curveHolomorphicOneFormPresheafSheafification.map
        (homOfLE (show U ≤ ⊤ from le_top)).op
        (curveGlobalHolomorphicDifferential_smul c) =
      (curveHolomorphicOneFormScalarSheafMap c).hom.app (.op U)
        (curveHolomorphicOneFormPresheafSheafification.map
          (homOfLE (show U ≤ ⊤ from le_top)).op
          curveGlobalHolomorphicDifferential) := by
  exact (NatTrans.naturality_apply (curveHolomorphicOneFormScalarSheafMap c).hom
    (homOfLE (show U ≤ ⊤ from le_top)).op curveGlobalHolomorphicDifferential).symm

/-- On a connected analytification, every global holomorphic one-form is a complex scalar
multiple of the explicit invariant differential. -/
theorem exists_curveGlobalOneForm_eq_smul
    [ConnectedSpace (ComplexPoint curveAnalyticVariety)]
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤)) :
    ∃ c : ℂ, s = curveGlobalHolomorphicDifferential_smul c := by
  obtain ⟨c, hc⟩ := exists_curveOneFormGlobalCoefficient_eq_algebraMap s
  refine ⟨c, ?_⟩
  let U : ComplexPoint curveAnalyticVariety →
      Opens (TopCat.of (ComplexPoint curveAnalyticVariety)) :=
    fun x => (curveOneFormLocalCoefficient s x).U
  have hcover : (⊤ : Opens (TopCat.of (ComplexPoint curveAnalyticVariety))) ≤ iSup U := by
    intro x _
    exact (le_iSup U x) (curveOneFormLocalCoefficient s x).mem
  apply curveHolomorphicOneFormSheaf.eq_of_locally_eq' U ⊤
    (fun _ => homOfLE le_top) hcover
  intro x
  let dx := curveOneFormLocalCoefficient s x
  let i : Opposite.op (⊤ : Opens (TopCat.of (ComplexPoint curveAnalyticVariety))) ⟶
      Opposite.op dx.U := (homOfLE le_top).op
  have hqtop := curveOneFormGlobalCoefficient_restrict s x
  rw [hc] at hqtop
  have hqx : dx.q =
      algebraMap ℂ (OpenHolomorphicFunctions curveAnalyticVariety 1 (.op dx.U)) c := by
    change holomorphicRestrictionAlgHom curveAnalyticVariety 1 i
        (algebraMap ℂ (OpenHolomorphicFunctions curveAnalyticVariety 1 (.op ⊤)) c) =
      dx.q at hqtop
    rw [(holomorphicRestrictionAlgHom curveAnalyticVariety 1 i).commutes c] at hqtop
    exact hqtop.symm
  calc
    curveHolomorphicOneFormPresheafSheafification.map i s =
        curveHolomorphicOneFormSheafificationUnit.app (.op dx.U)
          (holomorphicFormFunctionMul curveAnalyticVariety 1 (.op dx.U) 1 dx.q dx.beta) :=
      dx.form_eq.symm
    _ = curveHolomorphicOneFormSheafificationUnit.app (.op dx.U) (c • dx.beta) := by
      rw [hqx, holomorphicFormFunctionMul_algebraMap]
    _ = (curveHolomorphicOneFormScalarSheafMap c).hom.app (.op dx.U)
        (curveHolomorphicOneFormSheafificationUnit.app (.op dx.U) dx.beta) :=
      (curveHolomorphicOneFormScalar_toSheafify c (.op dx.U) dx.beta).symm
    _ = (curveHolomorphicOneFormScalarSheafMap c).hom.app (.op dx.U)
        (curveHolomorphicOneFormPresheafSheafification.map i
          curveGlobalHolomorphicDifferential) := by rw [dx.generator_eq]
    _ = curveHolomorphicOneFormPresheafSheafification.map i
        (curveGlobalHolomorphicDifferential_smul c) :=
      (curveGlobalHolomorphicDifferential_smul_restrict c dx.U).symm

/-- Scalar multiplication of the invariant differential is injective. -/
theorem curveGlobalHolomorphicDifferential_smul_injective :
    Function.Injective curveGlobalHolomorphicDifferential_smul := by
  intro c d hcd
  let x : ComplexPoint curveAnalyticVariety := infinity
  let dx := curveOneFormLocalCoefficient curveGlobalHolomorphicDifferential x
  let i : Opposite.op (⊤ : Opens (TopCat.of (ComplexPoint curveAnalyticVariety))) ⟶
      Opposite.op dx.U := (homOfLE le_top).op
  have hlocal := congrArg
    (fun w : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤) =>
      curveHolomorphicOneFormPresheafSheafification.map i w) hcd
  rw [curveGlobalHolomorphicDifferential_smul_restrict,
    curveGlobalHolomorphicDifferential_smul_restrict] at hlocal
  rw [← dx.generator_eq, curveHolomorphicOneFormScalar_toSheafify,
    curveHolomorphicOneFormScalar_toSheafify] at hlocal
  have hforms : c • dx.beta = d • dx.beta :=
    (holomorphicDeRham_toSheafify_injective curveAnalyticVariety 1 dx.U 1) hlocal
  have hbeta : dx.beta ≠ 0 := by
    intro hzero
    have hn := dx.generator_ne x dx.mem
    rw [hzero, map_zero] at hn
    exact hn rfl
  exact smul_left_injective ℂ hbeta hforms

/-- On a connected analytification, every global holomorphic one-form is a unique complex scalar
multiple of the explicit invariant differential. -/
theorem existsUnique_curveGlobalOneForm_eq_smul
    [ConnectedSpace (ComplexPoint curveAnalyticVariety)]
    (s : curveHolomorphicOneFormPresheafSheafification.obj (.op ⊤)) :
    ∃! c : ℂ, s = curveGlobalHolomorphicDifferential_smul c := by
  obtain ⟨c, hc⟩ := exists_curveGlobalOneForm_eq_smul s
  refine ⟨c, hc, ?_⟩
  intro d hd
  apply curveGlobalHolomorphicDifferential_smul_injective
  exact hd.symm.trans hc

end AlgebraicGeometry.ExplicitEllipticCandidate
