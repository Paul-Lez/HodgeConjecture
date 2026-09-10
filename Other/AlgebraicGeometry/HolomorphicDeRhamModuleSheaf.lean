/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicFormFunctionMultiplication
public import Other.AlgebraicGeometry.HolomorphicExponential
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Holomorphic differential forms as modules over holomorphic functions

The additive holomorphic de Rham sheaves used by the derived-category
development arise by sheafifying presheaves which are naturally modules over
the holomorphic-function sheaf.  This file retains that module structure and
identifies its underlying additive sheaf with the existing one.  In
particular, a global holomorphic form gives an honest morphism from the
structure sheaf by multiplication.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (X : Over (Spec (.of ℂ))) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

attribute [local instance] regularSectionAlgebra

local instance holomorphicDeRhamModuleRegularSectionAlgebra
    (U : X.left.Opens) : Algebra ℂ Γ(X.left, U) :=
  regularSectionAlgebra X U

/-- Holomorphic forms are determined by all of their coordinate evaluations. -/
theorem holomorphicForm_ext_evaluation
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    {w z : HolomorphicForm X d U p}
    (h : ∀ (x : ComplexPoint X) (y : Fin d → ℂ)
      (hy : y ∈ chartSectionDomain X d U x),
      holomorphicFormEvaluation X d U x p y hy w =
        holomorphicFormEvaluation X d U x p y hy z) :
    w = z := by
  obtain ⟨a, rfl⟩ :=
    Submodule.mkQ_surjective (holomorphicFormRelations X d U p) w
  obtain ⟨b, rfl⟩ :=
    Submodule.mkQ_surjective (holomorphicFormRelations X d U p) z
  apply (Submodule.Quotient.eq (holomorphicFormRelations X d U p)).2
  rw [holomorphicFormRelations_eq_chartEvaluationKernel]
  apply (mem_chartEvaluationKernel_iff X d U p (a - b)).2
  intro x y hy
  rw [map_sub]
  exact sub_eq_zero.mpr (h x y hy)

/-- Multiplication by the zero function is zero. -/
theorem holomorphicFormFunctionMul_zero
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (w : HolomorphicForm X d U p) :
    holomorphicFormFunctionMul X d U p 0 w = 0 := by
  apply holomorphicForm_ext_evaluation X d U p
  intro x y hy
  rw [holomorphicFormEvaluation_functionMul]
  rw [chartSection_apply_of_mem X d U x _ hy]
  change (0 : ℂ) • (holomorphicFormEvaluation X d U x p y hy) w = 0
  apply ContinuousAlternatingMap.ext
  intro v
  simp

/-- Function addition distributes over multiplication of a form. -/
theorem holomorphicFormFunctionMul_add
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (a b : OpenHolomorphicFunctions X d U)
    (w : HolomorphicForm X d U p) :
    holomorphicFormFunctionMul X d U p (a + b) w =
      holomorphicFormFunctionMul X d U p a w +
        holomorphicFormFunctionMul X d U p b w := by
  apply holomorphicForm_ext_evaluation X d U p
  intro x y hy
  rw [holomorphicFormEvaluation_functionMul, map_add,
    holomorphicFormEvaluation_functionMul,
    holomorphicFormEvaluation_functionMul]
  change chartSection X d U x (a + b) y • _ =
    chartSection X d U x a y • _ + chartSection X d U x b y • _
  rw [show chartSection X d U x (a + b) y =
      chartSection X d U x a y + chartSection X d U x b y by
    rw [chartSection_apply_of_mem X d U x _ hy,
      chartSection_apply_of_mem X d U x _ hy,
      chartSection_apply_of_mem X d U x _ hy]
    rfl]
  exact add_smul
    (chartSection X d U x a y : ℂ)
    (chartSection X d U x b y : ℂ)
    ((holomorphicFormEvaluation X d U x p y hy) w)

/-- Multiplication by the unit function is the identity. -/
theorem holomorphicFormFunctionMul_one
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (w : HolomorphicForm X d U p) :
    holomorphicFormFunctionMul X d U p 1 w = w := by
  simpa using
    holomorphicFormFunctionMul_algebraMap X d U p 1 w

/-- Multiplication of function coefficients is associative on forms. -/
theorem holomorphicFormFunctionMul_mul
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (a b : OpenHolomorphicFunctions X d U)
    (w : HolomorphicForm X d U p) :
    holomorphicFormFunctionMul X d U p (a * b) w =
      holomorphicFormFunctionMul X d U p a
        (holomorphicFormFunctionMul X d U p b w) := by
  apply holomorphicForm_ext_evaluation X d U p
  intro x y hy
  rw [holomorphicFormEvaluation_functionMul,
    holomorphicFormEvaluation_functionMul,
    holomorphicFormEvaluation_functionMul]
  change chartSection X d U x (a * b) y • _ =
    chartSection X d U x a y • chartSection X d U x b y • _
  rw [show chartSection X d U x (a * b) y =
      chartSection X d U x a y * chartSection X d U x b y by
    rw [chartSection_apply_of_mem X d U x _ hy,
      chartSection_apply_of_mem X d U x _ hy,
      chartSection_apply_of_mem X d U x _ hy]
    rfl,
    mul_smul]

/-- Multiplication by the product of two regular functions on a regular
Kähler wedge agrees with multiplying the two Kähler factors separately.
This is the representative-level compatibility used for logarithmic product
classes. -/
theorem holomorphicFormFunctionMul_regular_kaehlerWedge
    (U : X.left.Opens) (a b : Γ(X.left, U))
    (w z : KaehlerDifferential ℂ Γ(X.left, U)) :
    holomorphicFormFunctionMul X d (.op (regularAnalyticOpen X U)) 2
        (regularToHolomorphicAlgHom X d U (a * b))
        (regularFormToHolomorphicForm X d U 2
          (Algebra.DeRham.kaehlerWedge ℂ Γ(X.left, U) w z)) =
      regularFormToHolomorphicForm X d U 2
        (Algebra.DeRham.kaehlerWedge ℂ Γ(X.left, U) (a • w) (b • z)) := by
  obtain ⟨v, rfl⟩ :=
    KaehlerDifferential.linearCombination_surjective ℂ Γ(X.left, U) w
  obtain ⟨u, rfl⟩ :=
    KaehlerDifferential.linearCombination_surjective ℂ Γ(X.left, U) z
  induction v using Finsupp.induction with
  | zero => simp [Algebra.DeRham.kaehlerWedge]
  | single_add e c v he hc ih =>
    simp only [map_add, Finsupp.linearCombination_single, smul_add,
      LinearMap.add_apply]
    rw [ih]
    congr 1
    clear ih
    induction u using Finsupp.induction with
    | zero => simp [Algebra.DeRham.kaehlerWedge]
    | single_add g f u hg hf ih' =>
      simp only [map_add, Finsupp.linearCombination_single, smul_add]
      rw [ih']
      congr 1
      clear ih'
      rw [smul_smul, smul_smul,
        Algebra.DeRham.kaehlerWedge_smul_D_smul_D,
        Algebra.DeRham.kaehlerWedge_smul_D_smul_D]
      simp only [regularFormToHolomorphicForm, LinearMap.comp_apply,
        Algebra.DeRham.map_mk]
      change holomorphicFormFunctionMul X d
          (.op (regularAnalyticOpen X U)) 2
          (regularToHolomorphicAlgHom X d U (a * b))
          ((holomorphicFormRelations X d
            (.op (regularAnalyticOpen X U)) 2).mkQ
              (Finsupp.single
                (regularToHolomorphicAlgHom X d U (c * f),
                  fun i => regularToHolomorphicAlgHom X d U (![e, g] i)) 1)) = _
      rw [holomorphicFormFunctionMul_mk]
      apply congrArg
      rw [rawHolomorphicFormFunctionMul_single]
      congr 2
      simp only [map_mul]
      ring

/-- The natural module of holomorphic forms over holomorphic functions. -/
noncomputable instance holomorphicFormModule
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Module (OpenHolomorphicFunctions X d U) (HolomorphicForm X d U p) := by
  letI : SMul (OpenHolomorphicFunctions X d U)
      (HolomorphicForm X d U p) :=
    ⟨fun a w => holomorphicFormFunctionMul X d U p a w⟩
  exact Module.ofMinimalAxioms
    (fun a w z => (holomorphicFormFunctionMul X d U p a).map_add w z)
    (holomorphicFormFunctionMul_add X d U p)
    (holomorphicFormFunctionMul_mul X d U p)
    (holomorphicFormFunctionMul_one X d U p)

/-- The sheaf of holomorphic functions, regarded as a sheaf of rings. -/
def holomorphicRingSheaf :
    TopCat.Sheaf RingCat (TopCat.of (ComplexPoint X)) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (forget₂ CommRingCat RingCat)).obj (holomorphicFunctionSheaf X d)

/-- The additive sheaf underlying the free rank-one module over the holomorphic
function sheaf is the usual additive holomorphic-function sheaf. -/
def holomorphicRingSheafUnitToAdditiveIso :
    (SheafOfModules.toSheaf (holomorphicRingSheaf X d)).obj
        (SheafOfModules.unit (holomorphicRingSheaf X d)) ≅
      holomorphicAdditiveFunctionSheaf X d :=
  Iso.refl _

/-- A section on the top open determines a compatible section over every open
by restriction. -/
def moduleSectionsOfTop
    {M : SheafOfModules (holomorphicRingSheaf X d)}
    (s : M.val.obj (.op ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
    (by
      intro U V f
      change (M.val.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op ≫
        M.val.presheaf.map f) s =
          M.val.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op s
      rw [← M.val.presheaf.map_comp]
      congr 2)

@[simp]
theorem moduleSectionsOfTop_eval_top
    {M : SheafOfModules (holomorphicRingSheaf X d)}
    (s : M.val.obj (.op ⊤)) :
    (moduleSectionsOfTop X d s).val (.op ⊤) = s := by
  change M.val.map (𝟙 (.op ⊤)) s = s
  simp

/-- Holomorphic `p`-forms as a presheaf of modules over holomorphic functions. -/
def holomorphicDeRhamOPresheaf (p : ℕ) :
    PresheafOfModules (holomorphicRingSheaf X d).obj :=
  letI : ∀ U,
      Module ((holomorphicRingSheaf X d).obj.obj U)
        ((holomorphicDeRhamPresheaf X d p).obj U) :=
    fun U => holomorphicFormModule X d U p
  PresheafOfModules.ofPresheaf
    (holomorphicDeRhamPresheaf X d p)
    (fun {U V} f a w =>
      holomorphicFormRestriction_functionMul
        (X := X) (d := d) (U := U) (V := V) f p a w)

/-- The sheafification of holomorphic `p`-forms retaining its structure-sheaf module action. -/
def holomorphicDeRhamOSheaf (p : ℕ) :
    SheafOfModules (holomorphicRingSheaf X d) :=
  (PresheafOfModules.sheafification
    (𝟙 (holomorphicRingSheaf X d).obj)).obj
      (holomorphicDeRhamOPresheaf X d p)

/-- Forgetting the structure-sheaf module action recovers the existing additive de Rham sheaf. -/
def holomorphicDeRhamOSheafToAdditiveIso (p : ℕ) :
    (SheafOfModules.toSheaf (holomorphicRingSheaf X d)).obj
        (holomorphicDeRhamOSheaf X d p) ≅
      holomorphicDeRhamSheaf X d p := by
  exact (PresheafOfModules.sheafificationCompToSheaf
    (𝟙 (holomorphicRingSheaf X d).obj)).app
      (holomorphicDeRhamOPresheaf X d p)

/-- Multiplication by a global holomorphic `p`-form, as a morphism from the
additive structure sheaf to the additive sheaf of `p`-forms. -/
def holomorphicTopFormMultiplicationSheaf (p : ℕ)
    (s : (holomorphicDeRhamSheaf X d p).obj.obj (.op ⊤)) :
    holomorphicAdditiveFunctionSheaf X d ⟶ holomorphicDeRhamSheaf X d p :=
  (holomorphicRingSheafUnitToAdditiveIso X d).inv ≫
    (SheafOfModules.toSheaf (holomorphicRingSheaf X d)).map
      ((holomorphicDeRhamOSheaf X d p).unitHomEquiv.symm
        (moduleSectionsOfTop X d
          ((holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app (.op ⊤) s))) ≫
    (holomorphicDeRhamOSheafToAdditiveIso X d p).hom

/-- Objectwise, the global-form multiplication morphism is the module action
on the sheaf of holomorphic forms after transporting through the canonical
underlying-additive-sheaf isomorphism. -/
theorem holomorphicTopFormMultiplicationSheaf_app
    (p : ℕ) (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (s : (holomorphicDeRhamSheaf X d p).obj.obj (.op ⊤))
    (a : OpenHolomorphicFunctions X d U) :
    (holomorphicTopFormMultiplicationSheaf X d p s).hom.app U a =
      (holomorphicDeRhamOSheafToAdditiveIso X d p).hom.hom.app U
        ((show (holomorphicRingSheaf X d).obj.obj U from a) •
          (show ↑((holomorphicDeRhamOSheaf X d p).val.obj U) from
            (holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app U
              ((holomorphicDeRhamSheaf X d p).obj.map
                (homOfLE (le_top : U.unop ≤ ⊤)).op s))) := by
  simp only [holomorphicTopFormMultiplicationSheaf]
  change (((holomorphicDeRhamOSheaf X d p).unitHomEquiv.symm
    (moduleSectionsOfTop X d
      ((holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app (.op ⊤) s))).val.app U) a = _
  change (show (holomorphicRingSheaf X d).obj.obj U from a) •
    (show ↑((holomorphicDeRhamOSheaf X d p).val.obj U) from
      (moduleSectionsOfTop X d
        ((holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app (.op ⊤) s)).val U) = _
  dsimp only [moduleSectionsOfTop, PresheafOfModules.sectionsMk]
  rw [← ConcreteCategory.comp_apply,
    (holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.naturality]
  rfl

/-- If the restriction of the global form has a presheaf representative `w`,
then multiplying a local function `a` by that global form is represented by
the literal function multiple `a * w` before sheafification. -/
theorem holomorphicTopFormMultiplicationSheaf_app_toSheafify
    (p : ℕ) (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (s : (holomorphicDeRhamSheaf X d p).obj.obj (.op ⊤))
    (a : OpenHolomorphicFunctions X d U)
    (w : HolomorphicForm X d U p)
    (hs : (holomorphicDeRhamSheaf X d p).obj.map
              (homOfLE (le_top : U.unop ≤ ⊤)).op s =
            (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
              (holomorphicDeRhamPresheaf X d p)).app U w) :
    (holomorphicTopFormMultiplicationSheaf X d p s).hom.app U a =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app U
          (holomorphicFormFunctionMul X d U p a w) := by
  rw [holomorphicTopFormMultiplicationSheaf_app X d p U s a]
  rw [hs]
  dsimp [holomorphicDeRhamOSheafToAdditiveIso,
    PresheafOfModules.sheafificationCompToSheaf]
  change (show (holomorphicRingSheaf X d).obj.obj U from a) •
      (show ↑((holomorphicDeRhamOSheaf X d p).val.obj U) from
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app U w) =
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)).app U
        (holomorphicFormFunctionMul X d U p a w)
  let hφinj : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)) :=
    ((Opens.grothendieckTopology (TopCat.of (ComplexPoint X))).W_toSheafify
      (holomorphicDeRhamPresheaf X d p)).isLocallyInjective
  let hφsurj : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)) :=
    ((Opens.grothendieckTopology (TopCat.of (ComplexPoint X))).W_toSheafify
      (holomorphicDeRhamPresheaf X d p)).isLocallySurjective
  have h :=
    @PresheafOfModules.Sheafify.map_smul_eq
      (Opens (TopCat.of (ComplexPoint X))) _
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicRingSheaf X d).obj
      (holomorphicRingSheaf X d)
      (𝟙 (holomorphicRingSheaf X d).obj)
      (inferInstance) (inferInstance)
      (holomorphicDeRhamOPresheaf X d p)
      (holomorphicDeRhamSheaf X d p)
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p))
      hφinj hφsurj
      U
      (show (holomorphicRingSheaf X d).obj.obj U from a)
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app U w)
      U (𝟙 U) a (by simp) w (by
        exact ((holomorphicDeRhamSheaf X d p).obj.map_id_apply U _).symm)
  exact ((holomorphicDeRhamSheaf X d p).obj.map_id_apply U _).symm.trans h

end AlgebraicGeometry.ComplexPoint
