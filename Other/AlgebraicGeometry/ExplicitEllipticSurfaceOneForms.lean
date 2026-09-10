/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceDifferential
public import Other.AlgebraicGeometry.HolomorphicFormSheafification
public import Other.AlgebraicGeometry.ExplicitEllipticCotangentTrivialization
public import Other.Algebra.DeRham.KaehlerWedgeAlternating

/-!
# The two pulled elliptic one-forms on the explicit surface

The algebraic pullbacks of the invariant elliptic differential already exist on every product
chart.  This file evaluates and glues them separately, producing the two global holomorphic
one-forms whose local wedge is the previously constructed global two-form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] regularSectionAlgebra

/-- The explicit surface, with its structure morphism typed over `Spec ℂ`. -/
abbrev surfaceOverComplex : Over (Spec (CommRingCat.of ℂ)) :=
  Over.mk surfaceToBase

local instance surfaceOneFormSectionAlgebra (V : surface.Opens) :
    Algebra ℂ Γ(surface, V) :=
  regularSectionAlgebra (Over.mk surfaceToBase) V

/-- Every algebraic two-form on either affine elliptic chart vanishes. -/
theorem indexedCurveTwoForm_eq_zero (i : Fin 2)
    (η : Algebra.DeRham.Form ℂ Γ(curve, chart (differentialChartIndex i)) 2) :
    η = 0 := by
  fin_cases i
  · apply Algebra.DeRham.complex_twoForm_eq_zero_of_cotangent_generator
      Γ(curve, chart 2) curveZDifferential
    intro w
    let a := curveZCotangentLinearEquiv.symm w
    refine ⟨a, ?_⟩
    change curveZCotangentLinearEquiv a = w
    exact curveZCotangentLinearEquiv.apply_symm_apply w
  · apply Algebra.DeRham.complex_twoForm_eq_zero_of_cotangent_generator
      Γ(curve, chart 1) curveYDifferential
    intro w
    let a := curveYCotangentLinearEquiv.symm w
    refine ⟨a, ?_⟩
    rw [← curveYCotangentLinearEquiv_apply]
    exact curveYCotangentLinearEquiv.apply_symm_apply w

/-- On a product chart, the invariant differential pulled back from the selected factor. -/
def surfaceLocalPulledOneFormOn (factor : Fin 2) (ij : Fin 2 × Fin 2)
    (V : surface.Opens) (h : V ≤ surfaceDifferentialOpen ij) :
    Algebra.DeRham.Form ℂ Γ(surface, V) 1 :=
  Fin.cases
    (Algebra.DeRham.kaehlerToForm ℂ Γ(surface, V)
      (surfacePulledCurveDifferential
        (pullback.fst curveToBase curveToBase) rfl ij.1 V (h.trans inf_le_left)))
    (Fin.cases
      (Algebra.DeRham.kaehlerToForm ℂ Γ(surface, V)
        (surfacePulledCurveDifferential
          (pullback.snd curveToBase curveToBase) pullback.condition.symm
            ij.2 V (h.trans inf_le_right)))
      (fun i ↦ i.elim0)) factor

/-- The local pulled one-form does not depend on the chosen product-chart formula. -/
theorem surfaceLocalPulledOneFormOn_eq (factor : Fin 2) (ij kl : Fin 2 × Fin 2)
    (V : surface.Opens) (hij : V ≤ surfaceDifferentialOpen ij)
    (hkl : V ≤ surfaceDifferentialOpen kl) :
    surfaceLocalPulledOneFormOn factor ij V hij =
      surfaceLocalPulledOneFormOn factor kl V hkl := by
  fin_cases factor
  · exact congrArg (Algebra.DeRham.kaehlerToForm ℂ Γ(surface, V))
      (surfacePulledCurveDifferential_eq
        (pullback.fst curveToBase curveToBase) rfl ij.1 kl.1 V
          (hij.trans inf_le_left) (hkl.trans inf_le_left))
  · exact congrArg (Algebra.DeRham.kaehlerToForm ℂ Γ(surface, V))
      (surfacePulledCurveDifferential_eq
        (pullback.snd curveToBase curveToBase) pullback.condition.symm ij.2 kl.2 V
          (hij.trans inf_le_right) (hkl.trans inf_le_right))

/-- The local pulled one-forms commute with restriction to a smaller algebraic open. -/
theorem surfaceLocalPulledOneFormOn_restrict (factor : Fin 2) (ij : Fin 2 × Fin 2)
    {V W : surface.Opens} (hV : V ≤ surfaceDifferentialOpen ij) (hWV : W ≤ V) :
    Algebra.DeRham.map ℂ (regularSectionRestriction (Over.mk surfaceToBase) hWV) 1
        (surfaceLocalPulledOneFormOn factor ij V hV) =
      surfaceLocalPulledOneFormOn factor ij W (hWV.trans hV) := by
  let : Algebra Γ(surface, V) Γ(surface, W) :=
    (regularSectionRestriction (Over.mk surfaceToBase) hWV).toRingHom.toAlgebra
  let : IsScalarTower ℂ Γ(surface, V) Γ(surface, W) :=
    IsScalarTower.of_algebraMap_eq'
      (regularSectionRestriction (Over.mk surfaceToBase) hWV).comp_algebraMap.symm
  fin_cases factor
  · have hk := Algebra.DeRham.kaehlerToForm_map
      ℂ Γ(surface, V) Γ(surface, W)
      (surfacePulledCurveDifferential
        (pullback.fst curveToBase curveToBase) rfl ij.1 V (hV.trans inf_le_left))
    have hf := surfaceDifferentialPullback_restrict
      (pullback.fst curveToBase curveToBase) rfl _ (hV.trans inf_le_left) hWV
      (indexedCurveDifferential ij.1)
    exact hk.symm.trans (congrArg
      (Algebra.DeRham.kaehlerToForm ℂ Γ(surface, W)) hf)
  · have hk := Algebra.DeRham.kaehlerToForm_map
      ℂ Γ(surface, V) Γ(surface, W)
      (surfacePulledCurveDifferential
        (pullback.snd curveToBase curveToBase) pullback.condition.symm
          ij.2 V (hV.trans inf_le_right))
    have hf := surfaceDifferentialPullback_restrict
      (pullback.snd curveToBase curveToBase) pullback.condition.symm _
        (hV.trans inf_le_right) hWV (indexedCurveDifferential ij.2)
    exact hk.symm.trans (congrArg
      (Algebra.DeRham.kaehlerToForm ℂ Γ(surface, W)) hf)

/-- Every local projection pullback of the invariant differential is algebraically closed. -/
theorem surfaceLocalPulledOneFormOn_differential (factor : Fin 2)
    (ij : Fin 2 × Fin 2) (V : surface.Opens)
    (hV : V ≤ surfaceDifferentialOpen ij) :
    Algebra.DeRham.differential ℂ Γ(surface, V) 1
      (surfaceLocalPulledOneFormOn factor ij V hV) = 0 := by
  fin_cases factor
  · change Algebra.DeRham.differential ℂ Γ(surface, V) 1
      (surfaceLocalPulledOneFormOn (0 : Fin 2) ij V hV) = 0
    let f := pullback.fst curveToBase curveToBase
    let U := chart (differentialChartIndex ij.1)
    let h := hV.trans inf_le_left
    let φ := surfaceSectionPullback f rfl U V h
    let : Algebra Γ(curve, U) Γ(surface, V) := φ.toRingHom.toAlgebra
    let : IsScalarTower ℂ Γ(curve, U) Γ(surface, V) :=
      IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
    have hk := Algebra.DeRham.kaehlerToForm_map
      ℂ Γ(curve, U) Γ(surface, V) (indexedCurveDifferential ij.1)
    have hform : surfaceLocalPulledOneFormOn (0 : Fin 2) ij V hV =
        Algebra.DeRham.map ℂ
          (IsScalarTower.toAlgHom ℂ Γ(curve, U) Γ(surface, V)) 1
          (Algebra.DeRham.kaehlerToForm ℂ Γ(curve, U)
            (indexedCurveDifferential ij.1)) := by
      change Algebra.DeRham.kaehlerToForm ℂ Γ(surface, V)
          ((KaehlerDifferential.map ℂ ℂ Γ(curve, U) Γ(surface, V))
            (indexedCurveDifferential ij.1)) = _
      exact hk
    rw [hform, ← Algebra.DeRham.map_differential]
    have hz := indexedCurveTwoForm_eq_zero ij.1
      (Algebra.DeRham.differential ℂ Γ(curve, U) 1
        (Algebra.DeRham.kaehlerToForm ℂ Γ(curve, U)
          (indexedCurveDifferential ij.1)))
    rw [hz, map_zero]
  · change Algebra.DeRham.differential ℂ Γ(surface, V) 1
      (surfaceLocalPulledOneFormOn (1 : Fin 2) ij V hV) = 0
    let f := pullback.snd curveToBase curveToBase
    let U := chart (differentialChartIndex ij.2)
    let h := hV.trans inf_le_right
    let φ := surfaceSectionPullback f pullback.condition.symm U V h
    let : Algebra Γ(curve, U) Γ(surface, V) := φ.toRingHom.toAlgebra
    let : IsScalarTower ℂ Γ(curve, U) Γ(surface, V) :=
      IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
    have hk := Algebra.DeRham.kaehlerToForm_map
      ℂ Γ(curve, U) Γ(surface, V) (indexedCurveDifferential ij.2)
    have hform : surfaceLocalPulledOneFormOn (1 : Fin 2) ij V hV =
        Algebra.DeRham.map ℂ
          (IsScalarTower.toAlgHom ℂ Γ(curve, U) Γ(surface, V)) 1
          (Algebra.DeRham.kaehlerToForm ℂ Γ(curve, U)
            (indexedCurveDifferential ij.2)) := by
      change Algebra.DeRham.kaehlerToForm ℂ Γ(surface, V)
          ((KaehlerDifferential.map ℂ ℂ Γ(curve, U) Γ(surface, V))
            (indexedCurveDifferential ij.2)) = _
      exact hk
    rw [hform, ← Algebra.DeRham.map_differential]
    have hz := indexedCurveTwoForm_eq_zero ij.2
      (Algebra.DeRham.differential ℂ Γ(curve, U) 1
        (Algebra.DeRham.kaehlerToForm ℂ Γ(curve, U)
          (indexedCurveDifferential ij.2)))
    rw [hz, map_zero]
/-- The two selected local one-forms wedge to the local surface two-form. -/
theorem surfaceLocalPulledOneForms_wedge (ij : Fin 2 × Fin 2)
    (V : surface.Opens) (h : V ≤ surfaceDifferentialOpen ij) :
    Algebra.DeRham.kaehlerWedge ℂ Γ(surface, V)
        (surfacePulledCurveDifferential
          (pullback.fst curveToBase curveToBase) rfl ij.1 V (h.trans inf_le_left))
        (surfacePulledCurveDifferential
          (pullback.snd curveToBase curveToBase) pullback.condition.symm
            ij.2 V (h.trans inf_le_right)) =
      surfaceLocalTwoFormOn ij V h :=
  rfl

/-- Evaluate a selected algebraic pullback as an actual holomorphic one-form. -/
def surfaceLocalHolomorphicPulledOneFormOn (factor : Fin 2) (ij : Fin 2 × Fin 2)
    (V : surface.Opens) (h : V ≤ surfaceDifferentialOpen ij) :
    HolomorphicForm (Over.mk surfaceToBase) 2 (.op (surfaceAnalyticOpen V)) 1 :=
  regularFormToHolomorphicForm (Over.mk surfaceToBase) 2 V 1
    (surfaceLocalPulledOneFormOn factor ij V h)

/-- The actual local holomorphic pullbacks commute with restriction. -/
theorem surfaceLocalHolomorphicPulledOneFormOn_restrict
    (factor : Fin 2) (ij : Fin 2 × Fin 2) {V W : surface.Opens}
    (hV : V ≤ surfaceDifferentialOpen ij) (hWV : W ≤ V) :
    holomorphicFormRestriction (Over.mk surfaceToBase) 2
        (regularAnalyticRestriction (Over.mk surfaceToBase) hWV).op 1
        (surfaceLocalHolomorphicPulledOneFormOn factor ij V hV) =
      surfaceLocalHolomorphicPulledOneFormOn factor ij W (hWV.trans hV) := by
  have hr := regularFormToHolomorphicForm_restrict
    (Over.mk surfaceToBase) 2 hWV 1
      (surfaceLocalPulledOneFormOn factor ij V hV)
  exact hr.trans (congrArg
    (regularFormToHolomorphicForm (Over.mk surfaceToBase) 2 W 1)
    (surfaceLocalPulledOneFormOn_restrict factor ij hV hWV))

/-- The actual local holomorphic pullback is independent of the product chart. -/
theorem surfaceLocalHolomorphicPulledOneFormOn_eq
    (factor : Fin 2) (ij kl : Fin 2 × Fin 2) (V : surface.Opens)
    (hij : V ≤ surfaceDifferentialOpen ij) (hkl : V ≤ surfaceDifferentialOpen kl) :
    surfaceLocalHolomorphicPulledOneFormOn factor ij V hij =
      surfaceLocalHolomorphicPulledOneFormOn factor kl V hkl :=
  congrArg (regularFormToHolomorphicForm (Over.mk surfaceToBase) 2 V 1)
    (surfaceLocalPulledOneFormOn_eq factor ij kl V hij hkl)

/-- Every local holomorphic pullback of the invariant differential is closed. -/
theorem surfaceLocalHolomorphicPulledOneFormOn_differential
    (factor : Fin 2) (ij : Fin 2 × Fin 2) (V : surface.Opens)
    (hV : V ≤ surfaceDifferentialOpen ij) :
    holomorphicFormDifferential (Over.mk surfaceToBase) 2
        (.op (surfaceAnalyticOpen V)) 1
        (surfaceLocalHolomorphicPulledOneFormOn factor ij V hV) = 0 := by
  unfold surfaceLocalHolomorphicPulledOneFormOn
  rw [← regularFormToHolomorphicForm_differential
    (Over.mk surfaceToBase) 2 V 1
      (surfaceLocalPulledOneFormOn factor ij V hV)]
  change regularFormToHolomorphicForm (Over.mk surfaceToBase) 2 V 2
      (Algebra.DeRham.differential ℂ Γ(surface, V) 1
        (surfaceLocalPulledOneFormOn factor ij V hV)) = 0
  rw [surfaceLocalPulledOneFormOn_differential, map_zero]

abbrev surfaceHolomorphicOneFormSheaf :=
  holomorphicDeRhamSheaf (Over.mk surfaceToBase) 2 1

/-- A local projection pullback as a section of the actual one-form sheaf. -/
def surfaceLocalSheafPulledOneFormOn (factor : Fin 2) (ij : Fin 2 × Fin 2)
    (V : surface.Opens) (h : V ≤ surfaceDifferentialOpen ij) :
    surfaceHolomorphicOneFormSheaf.obj.obj (.op (surfaceAnalyticOpen V)) :=
  (toSheafify (Opens.grothendieckTopology _)
      (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 1)).app
    (.op (surfaceAnalyticOpen V))
      (surfaceLocalHolomorphicPulledOneFormOn factor ij V h)

/-- Every local sheaf section obtained by projection pullback is closed. -/
theorem surfaceLocalSheafPulledOneFormOn_differential
    (factor : Fin 2) (ij : Fin 2 × Fin 2) (V : surface.Opens)
    (hV : V ≤ surfaceDifferentialOpen ij) :
    (holomorphicDeRhamSheafDifferential (Over.mk surfaceToBase) 2 1).hom.app
        (.op (surfaceAnalyticOpen V))
        (surfaceLocalSheafPulledOneFormOn factor ij V hV) = 0 := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint (Over.mk surfaceToBase)))
  change ((toSheafify J (holomorphicDeRhamPresheaf
      (Over.mk surfaceToBase) 2 1) ≫
      sheafifyMap J (holomorphicDeRhamDifferential
        (Over.mk surfaceToBase) 2 1)).app (.op (surfaceAnalyticOpen V)))
      (surfaceLocalHolomorphicPulledOneFormOn factor ij V hV) = 0
  rw [← toSheafify_naturality]
  have hz := surfaceLocalHolomorphicPulledOneFormOn_differential
    factor ij V hV
  rw [NatTrans.comp_app]
  change (toSheafify J (holomorphicDeRhamPresheaf
      (Over.mk surfaceToBase) 2 2)).app (.op (surfaceAnalyticOpen V))
      ((holomorphicDeRhamDifferential (Over.mk surfaceToBase) 2 1).app
        (.op (surfaceAnalyticOpen V))
        (surfaceLocalHolomorphicPulledOneFormOn factor ij V hV)) = 0
  change (toSheafify J (holomorphicDeRhamPresheaf
      surfaceOverComplex 2 2)).app (.op (regularAnalyticOpen surfaceOverComplex V))
      (holomorphicFormDifferential surfaceOverComplex 2
        (.op (regularAnalyticOpen surfaceOverComplex V)) 1
        (surfaceLocalHolomorphicPulledOneFormOn factor ij V hV)) = 0
  rw [hz]
  exact map_zero (ConcreteCategory.hom
    ((toSheafify J (holomorphicDeRhamPresheaf
      (Over.mk surfaceToBase) 2 2)).app (.op (surfaceAnalyticOpen V))))

/-- The sheaf sections representing the local pullbacks commute with restriction. -/
theorem surfaceLocalSheafPulledOneFormOn_restrict
    (factor : Fin 2) (ij : Fin 2 × Fin 2) {V W : surface.Opens}
    (hV : V ≤ surfaceDifferentialOpen ij) (hWV : W ≤ V) :
    surfaceHolomorphicOneFormSheaf.obj.map
        (regularAnalyticRestriction (Over.mk surfaceToBase) hWV).op
        (surfaceLocalSheafPulledOneFormOn factor ij V hV) =
      surfaceLocalSheafPulledOneFormOn factor ij W (hWV.trans hV) := by
  let η := toSheafify (Opens.grothendieckTopology _)
    (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 1)
  have hn := congrArg
    (fun g ↦ g (surfaceLocalHolomorphicPulledOneFormOn factor ij V hV))
    (η.naturality (regularAnalyticRestriction (Over.mk surfaceToBase) hWV).op)
  exact hn.symm.trans (congrArg (η.app (.op (surfaceAnalyticOpen W)))
    (surfaceLocalHolomorphicPulledOneFormOn_restrict factor ij hV hWV))

/-- Local sheaf pullbacks computed in two product charts agree on every common open. -/
theorem surfaceLocalSheafPulledOneFormOn_eq
    (factor : Fin 2) (ij kl : Fin 2 × Fin 2) (V : surface.Opens)
    (hij : V ≤ surfaceDifferentialOpen ij) (hkl : V ≤ surfaceDifferentialOpen kl) :
    surfaceLocalSheafPulledOneFormOn factor ij V hij =
      surfaceLocalSheafPulledOneFormOn factor kl V hkl :=
  congrArg ((toSheafify (Opens.grothendieckTopology _)
    (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 1)).app
      (.op (surfaceAnalyticOpen V)))
    (surfaceLocalHolomorphicPulledOneFormOn_eq factor ij kl V hij hkl)

/-- Each factor's local projection pullbacks glue to a global holomorphic one-form. -/
theorem exists_surfaceGlobalHolomorphicPulledOneForm (factor : Fin 2) :
    ∃ s : surfaceHolomorphicOneFormSheaf.obj.obj (.op ⊤),
      ∀ ij : Fin 2 × Fin 2,
        surfaceHolomorphicOneFormSheaf.obj.map (homOfLE
            (show surfaceAnalyticOpen (surfaceDifferentialOpen ij) ≤ ⊤ from le_top)).op s =
          surfaceLocalSheafPulledOneFormOn factor ij
            (surfaceDifferentialOpen ij) le_rfl := by
  let U (ij : Fin 2 × Fin 2) := surfaceAnalyticOpen (surfaceDifferentialOpen ij)
  let sf (ij : Fin 2 × Fin 2) :=
    surfaceLocalSheafPulledOneFormOn factor ij (surfaceDifferentialOpen ij) le_rfl
  have hc : TopCat.Presheaf.IsCompatible surfaceHolomorphicOneFormSheaf.obj U sf := by
    intro ij kl
    have h₁ := surfaceLocalSheafPulledOneFormOn_restrict factor ij le_rfl
      (show surfaceDifferentialOpen ij ⊓ surfaceDifferentialOpen kl ≤
        surfaceDifferentialOpen ij from inf_le_left)
    have h₂ := surfaceLocalSheafPulledOneFormOn_restrict factor kl le_rfl
      (show surfaceDifferentialOpen ij ⊓ surfaceDifferentialOpen kl ≤
        surfaceDifferentialOpen kl from inf_le_right)
    exact h₁.trans ((surfaceLocalSheafPulledOneFormOn_eq factor ij kl
      (surfaceDifferentialOpen ij ⊓ surfaceDifferentialOpen kl)
      inf_le_left inf_le_right).trans h₂.symm)
  obtain ⟨s, hs, _⟩ := surfaceHolomorphicOneFormSheaf.existsUnique_gluing' U ⊤
    (fun _ ↦ homOfLE le_top) surfaceDifferentialOpen_analytic_cover.ge sf hc
  exact ⟨s, hs⟩

/-- The global holomorphic one-form pulled back from the selected elliptic factor. -/
def surfaceGlobalHolomorphicPulledOneForm (factor : Fin 2) :
    surfaceHolomorphicOneFormSheaf.obj.obj (.op ⊤) :=
  (exists_surfaceGlobalHolomorphicPulledOneForm factor).choose

/-- The global pulled one-form has the prescribed formula on every product chart. -/
theorem surfaceGlobalHolomorphicPulledOneForm_restrict
    (factor : Fin 2) (ij : Fin 2 × Fin 2) :
    surfaceHolomorphicOneFormSheaf.obj.map (homOfLE
        (show surfaceAnalyticOpen (surfaceDifferentialOpen ij) ≤ ⊤ from le_top)).op
        (surfaceGlobalHolomorphicPulledOneForm factor) =
      surfaceLocalSheafPulledOneFormOn factor ij
        (surfaceDifferentialOpen ij) le_rfl :=
  (exists_surfaceGlobalHolomorphicPulledOneForm factor).choose_spec ij

/-- Each global one-form pulled back from a factor is closed in the holomorphic de Rham
complex. -/
theorem surfaceGlobalHolomorphicPulledOneForm_differential (factor : Fin 2) :
    (holomorphicDeRhamSheafDifferential (Over.mk surfaceToBase) 2 1).hom.app (.op ⊤)
        (surfaceGlobalHolomorphicPulledOneForm factor) = 0 := by
  let U (ij : Fin 2 × Fin 2) :=
    surfaceAnalyticOpen (surfaceDifferentialOpen ij)
  let D := holomorphicDeRhamSheafDifferential (Over.mk surfaceToBase) 2 1
  let t := D.hom.app (.op ⊤)
    (surfaceGlobalHolomorphicPulledOneForm factor)
  have ht : ∀ ij : Fin 2 × Fin 2,
      surfaceHolomorphicTwoFormSheaf.obj.map
        (show U ij ⟶ ⊤ from homOfLE le_top).op t = 0 := by
    intro ij
    let i : U ij ⟶ (⊤ : Opens (TopCat.of (ComplexPoint (Over.mk surfaceToBase)))) :=
      homOfLE le_top
    have hn := congrArg
      (fun f ↦ f (surfaceGlobalHolomorphicPulledOneForm factor))
      (D.hom.naturality i.op)
    calc
      surfaceHolomorphicTwoFormSheaf.obj.map i.op t =
          D.hom.app (.op (U ij))
            (surfaceHolomorphicOneFormSheaf.obj.map i.op
              (surfaceGlobalHolomorphicPulledOneForm factor)) := by
        simpa only [D, t, ConcreteCategory.comp_apply] using hn.symm
      _ = D.hom.app (.op (U ij))
          (surfaceLocalSheafPulledOneFormOn factor ij
            (surfaceDifferentialOpen ij) le_rfl) := by
        rw [surfaceGlobalHolomorphicPulledOneForm_restrict]
      _ = 0 := surfaceLocalSheafPulledOneFormOn_differential
        factor ij (surfaceDifferentialOpen ij) le_rfl
  have hc : TopCat.Presheaf.IsCompatible surfaceHolomorphicTwoFormSheaf.obj U
      (fun _ ↦ 0) := by
    intro ij kl
    simp
  obtain ⟨q, hq, huniq⟩ := surfaceHolomorphicTwoFormSheaf.existsUnique_gluing'
    U ⊤ (fun _ ↦ homOfLE le_top) surfaceDifferentialOpen_analytic_cover.ge
      (fun _ ↦ 0) hc
  have hzero : ∀ ij : Fin 2 × Fin 2,
      surfaceHolomorphicTwoFormSheaf.obj.map
        (show U ij ⟶ ⊤ from homOfLE le_top).op
        (0 : surfaceHolomorphicTwoFormSheaf.obj.obj (.op ⊤)) = 0 := by
    intro ij
    exact map_zero _
  change t = 0
  exact (huniq t ht).trans (huniq 0 hzero).symm

/-- The global one-form pulled back along the first projection. -/
abbrev surfaceFstGlobalHolomorphicOneForm :=
  surfaceGlobalHolomorphicPulledOneForm (0 : Fin 2)

/-- The global one-form pulled back along the second projection. -/
abbrev surfaceSndGlobalHolomorphicOneForm :=
  surfaceGlobalHolomorphicPulledOneForm (1 : Fin 2)

end AlgebraicGeometry.ExplicitEllipticCandidate
