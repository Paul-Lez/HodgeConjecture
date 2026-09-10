/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicFunctionPullback
public import Other.AlgebraicGeometry.HolomorphicFormSheafification
public import Other.Algebra.Homology.MapExtend
public import Other.AlgebraicTopology.SheafCohomologyWithSupport
public import Other.AlgebraicTopology.SingularChainSheafPushforward

/-!
# Pullback on the holomorphic de Rham complex

An algebraic morphism between smooth complex schemes induces pullback of holomorphic differential
forms. The analytic chain rule shows that raw pullback preserves the coordinate-evaluation
relations, so it descends through the quotient and sheafification to a morphism into direct image.
-/

@[expose] public noncomputable section

open CategoryTheory Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (d e : ℕ)
variable [SmoothOfRelativeDimension d X.hom]
  [SmoothOfRelativeDimension e Y.hom]

def holomorphicFunctionPullbackAlgHom
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) :
    OpenHolomorphicFunctions Y e U →ₐ[ℂ]
      OpenHolomorphicFunctions X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) where
  toFun g := ⟨g.1 ∘ analyticMapOpenRestriction X Y f U.unop, by
    apply ContMDiff.comp (I' := modelWithCornersSelf ℂ (Fin e → ℂ)) g.2
    exact contMDiff_restrictPreimage_analyticMap X Y f d e _⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def rawHolomorphicFormPullback
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p →ₗ[ℂ]
      Algebra.DeRham.RawForm ℂ
        (OpenHolomorphicFunctions X d
          (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop))) p :=
  Algebra.DeRham.rawMap ℂ
    (holomorphicFunctionPullbackAlgHom X Y f d e U) p

def holomorphicPullbackChartMapAt
    (z : ComplexPoint X) (y : Fin d → ℂ) :
    (Fin d → ℂ) → (Fin e → ℂ) :=
  let x := (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y
  let fx := Point.map f x
  fun v ↦
    (extChartAt (modelWithCornersSelf ℂ (Fin e → ℂ)) fx)
      (Point.map f
        ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm v))

lemma holomorphicPullbackChartMapAt_apply_self
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).target) :
    holomorphicPullbackChartMapAt X Y f d e z y y =
      (extChartAt (modelWithCornersSelf ℂ (Fin e → ℂ))
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)))
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) := rfl

lemma holomorphicPullback_chartSection_eventuallyEq
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (g : OpenHolomorphicFunctions Y e U)
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z) :
    chartSection X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z
        (holomorphicFunctionPullbackAlgHom X Y f d e U g) =ᶠ[𝓝 y]
      fun v ↦ chartSection Y e U
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) g
        (holomorphicPullbackChartMapAt X Y f d e z y v) := by
  let eX := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
  let x : ComplexPoint X := eX.symm y
  let fx : ComplexPoint Y := Point.map f x
  let eY := extChartAt (modelWithCornersSelf ℂ (Fin e → ℂ)) fx
  have hyX : y ∈ eX.target := hy.1
  have hxU : Point.map f x ∈ U.unop := hy.2
  have hfxY : fx ∈ eY.source := mem_extChartAt_source fx
  have hcont : ContinuousAt (fun v ↦ Point.map f (eX.symm v)) y :=
    (Point.continuous_map f).continuousAt.comp
      (continuousAt_extChartAt_symm'' hyX)
  have htarget : ∀ᶠ v in 𝓝 y, Point.map f (eX.symm v) ∈ eY.source :=
    hcont ((isOpen_extChartAt_source fx).mem_nhds hfxY)
  have hdomain : ∀ᶠ v in 𝓝 y,
      v ∈ chartSectionDomain X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z :=
    (isOpen_chartSectionDomain X d _ z).mem_nhds hy
  filter_upwards [htarget, hdomain] with v hvY hvX
  rw [chartSection_apply_of_mem X d _ z _ hvX]
  change g.1 ⟨Point.map f (eX.symm v), _⟩ =
    chartSection Y e U fx g (eY (Point.map f (eX.symm v)))
  have hmapY : eY (Point.map f (eX.symm v)) ∈
      chartSectionDomain Y e U fx := by
    refine ⟨eY.map_source hvY, ?_⟩
    change eY.symm (eY (Point.map f (eX.symm v))) ∈ U.unop
    rw [eY.left_inv hvY]
    exact hvX.2
  rw [chartSection_apply_of_mem Y e U fx g hmapY]
  change g.1 ⟨Point.map f (eX.symm v), _⟩ =
    g.1 ⟨eY.symm (eY (Point.map f (eX.symm v))), _⟩
  apply congrArg g.1
  apply Subtype.ext
  exact (eY.left_inv hvY).symm

lemma holomorphicPullbackChartMapAt_differentiableAt
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).target) :
    DifferentiableAt ℂ (holomorphicPullbackChartMapAt X Y f d e z y) y := by
  let IX := modelWithCornersSelf ℂ (Fin d → ℂ)
  let IY := modelWithCornersSelf ℂ (Fin e → ℂ)
  let eX := extChartAt IX z
  let x := eX.symm y
  let fx := Point.map f x
  let eY := extChartAt IY fx
  letI : IsManifold IX ω (ComplexPoint X) := isManifold_omega X d
  letI : IsManifold IY ω (ComplexPoint Y) := isManifold_omega Y e
  have hsymm : ContMDiffAt IX IX ω eX.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target z hy).contMDiffAt
      ((isOpen_extChartAt_target z).mem_nhds hy)
  have hmap : ContMDiffAt IX IY ω (Point.map f ∘ eX.symm) y :=
    (contMDiff_analyticMap X Y f d e).contMDiffAt.comp y hsymm
  have hfxY : fx ∈ eY.source := mem_extChartAt_source fx
  have hchartAt : ContMDiffAt IY IY ω eY fx :=
    contMDiffAt_extChartAt
  have hchart : ContMDiffAt IX IY ω
      (eY ∘ Point.map f ∘ eX.symm) y :=
    hchartAt.comp y hmap
  exact hchart.contDiffAt.differentiableAt (by simp)

lemma holomorphicPullback_chartSectionDifferential
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (g : OpenHolomorphicFunctions Y e U)
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z) :
    chartSectionDifferential X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z
        (holomorphicFunctionPullbackAlgHom X Y f d e U g) y =
      (chartSectionDifferential Y e U
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) g
        (holomorphicPullbackChartMapAt X Y f d e z y y)).comp
          (fderiv ℂ (holomorphicPullbackChartMapAt X Y f d e z y) y) := by
  let eX := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
  let x : ComplexPoint X := eX.symm y
  let fx : ComplexPoint Y := Point.map f x
  let eY := extChartAt (modelWithCornersSelf ℂ (Fin e → ℂ)) fx
  have hfxY : fx ∈ eY.source := mem_extChartAt_source fx
  have hyTarget : eY fx ∈ chartSectionDomain Y e U fx := by
    refine ⟨eY.map_source hfxY, ?_⟩
    change eY.symm (eY fx) ∈ U.unop
    rw [eY.left_inv hfxY]
    exact hy.2
  have hsourceN : chartSectionDomain X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z ∈ 𝓝 y :=
    (isOpen_chartSectionDomain X d _ z).mem_nhds hy
  have htargetN : chartSectionDomain Y e U fx ∈ 𝓝 (eY fx) :=
    (isOpen_chartSectionDomain Y e U fx).mem_nhds hyTarget
  have heq := holomorphicPullback_chartSection_eventuallyEq X Y f d e U g z hy
  have hself : holomorphicPullbackChartMapAt X Y f d e z y y = eY fx := rfl
  rw [hself]
  unfold chartSectionDifferential
  rw [fderivWithin_of_mem_nhds hsourceN,
    fderivWithin_of_mem_nhds htargetN]
  rw [heq.fderiv_eq]
  have hg : DifferentiableAt ℂ (chartSection Y e U fx g) (eY fx) :=
    ((chartSection_contDiffWithinAt Y e U fx g hyTarget).differentiableWithinAt
      (by simp)).differentiableAt htargetN
  have hf : DifferentiableAt ℂ (holomorphicPullbackChartMapAt X Y f d e z y) y :=
    holomorphicPullbackChartMapAt_differentiableAt X Y f d e z hy.1
  change fderiv ℂ
      (chartSection Y e U fx g ∘ holomorphicPullbackChartMapAt X Y f d e z y) y = _
  rw [fderiv_comp y hg hf]
  rw [hself]

lemma holomorphicPullback_chartGeneratorEvaluation
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (p : ℕ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions Y e U) p)
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z) :
    chartGeneratorEvaluation X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z p
        (Algebra.DeRham.generatorMap ℂ
          (holomorphicFunctionPullbackAlgHom X Y f d e U) p g) y =
      (chartGeneratorEvaluation Y e U
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) p g
        (holomorphicPullbackChartMapAt X Y f d e z y y)).compContinuousLinearMap
          (fderiv ℂ (holomorphicPullbackChartMapAt X Y f d e z y) y) := by
  have hcoeff := holomorphicPullback_chartSection_eventuallyEq X Y f d e U g.1 z hy
  have hcoeffAt := hcoeff.self_of_nhds
  simp only [Algebra.DeRham.generatorMap, chartGeneratorEvaluation]
  rw [hcoeffAt]
  have hdiff : ∀ i : Fin p,
      chartSectionDifferential X d
          (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z
          (holomorphicFunctionPullbackAlgHom X Y f d e U (g.2 i)) y =
        (chartSectionDifferential Y e U
          (Point.map f
            ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y))
          (g.2 i) (holomorphicPullbackChartMapAt X Y f d e z y y)).comp
            (fderiv ℂ (holomorphicPullbackChartMapAt X Y f d e z y) y) :=
    fun i ↦ holomorphicPullback_chartSectionDifferential X Y f d e U (g.2 i) z hy
  simp_rw [hdiff]
  rw [wedgeCovectors_compContinuousLinearMap]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma holomorphicPullback_chartRawEvaluation
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (p : ℕ)
    (a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p)
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z) :
    chartRawEvaluation X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z p
        (rawHolomorphicFormPullback X Y f d e U p a) y =
      (chartRawEvaluation Y e U
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) p a
        (holomorphicPullbackChartMapAt X Y f d e z y y)).compContinuousLinearMap
          (fderiv ℂ (holomorphicPullbackChartMapAt X Y f d e z y) y) := by
  classical
  unfold rawHolomorphicFormPullback
  induction a using Finsupp.induction with
  | zero =>
      simp only [map_zero, Pi.zero_apply]
      refine ContinuousAlternatingMap.ext fun v ↦ ?_
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  | single_add g c a hg hc ih =>
      rw [map_add, map_add, map_add]
      rw [Algebra.DeRham.rawMap_single]
      rw [chartRawEvaluation_single, chartRawEvaluation_single]
      rw [Pi.add_apply, Pi.add_apply]
      simp only [Pi.smul_apply]
      rw [ih]
      rw [holomorphicPullback_chartGeneratorEvaluation X Y f d e U p g z hy]
      refine ContinuousAlternatingMap.ext fun v ↦ ?_
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma rawHolomorphicFormPullback_mem_relations
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (p : ℕ)
    {a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p}
    (ha : a ∈ holomorphicFormRelations Y e U p) :
    rawHolomorphicFormPullback X Y f d e U p a ∈
      holomorphicFormRelations X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p := by
  rw [holomorphicFormRelations_eq_chartEvaluationKernel] at ha ⊢
  apply (mem_chartEvaluationKernel_iff X d
    (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p _).2
  intro z y hy
  rw [holomorphicPullback_chartRawEvaluation X Y f d e U p a z hy]
  let eX := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
  let x : ComplexPoint X := eX.symm y
  let fx : ComplexPoint Y := Point.map f x
  let eY := extChartAt (modelWithCornersSelf ℂ (Fin e → ℂ)) fx
  have hfxY : fx ∈ eY.source := mem_extChartAt_source fx
  have htarget : holomorphicPullbackChartMapAt X Y f d e z y y ∈
      chartSectionDomain Y e U fx := by
    refine ⟨eY.map_source hfxY, ?_⟩
    change eY.symm (eY fx) ∈ U.unop
    rw [eY.left_inv hfxY]
    exact hy.2
  have heval :=
    (mem_chartEvaluationKernel_iff Y e U p a).1 ha fx
      (holomorphicPullbackChartMapAt X Y f d e z y y) htarget
  rw [heval]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- Pullback of holomorphic differential forms along an algebraic morphism. -/
def holomorphicFormPullback
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ) :
    HolomorphicForm Y e U p →ₗ[ℂ]
      HolomorphicForm X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p :=
  (holomorphicFormRelations Y e U p).liftQ
    ((holomorphicFormRelations X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p).mkQ.comp
        (rawHolomorphicFormPullback X Y f d e U p)) (by
      intro a ha
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact rawHolomorphicFormPullback_mem_relations X Y f d e U p ha)

@[simp]
lemma holomorphicFormPullback_mkQ
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ)
    (a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p) :
    holomorphicFormPullback X Y f d e U p
        ((holomorphicFormRelations Y e U p).mkQ a) =
      (holomorphicFormRelations X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p).mkQ
        (rawHolomorphicFormPullback X Y f d e U p a) :=
  rfl

@[simp]
lemma holomorphicFormPullback_algebraicFormToHolomorphicForm
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ)
    (a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions Y e U) p) :
    holomorphicFormPullback X Y f d e U p
        (algebraicFormToHolomorphicForm Y e U p a) =
      algebraicFormToHolomorphicForm X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p
        (Algebra.DeRham.map ℂ
          (holomorphicFunctionPullbackAlgHom X Y f d e U) p a) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions Y e U) p) a
  rfl

@[simp]
lemma holomorphicFormPullback_ofConstant
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (c : ℂ) :
    holomorphicFormPullback X Y f d e U 0
        (holomorphicFormOfConstant Y e U c) =
      holomorphicFormOfConstant X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) c := by
  rw [holomorphicFormOfConstant, holomorphicFormOfConstant, LinearMap.comp_apply,
    holomorphicFormPullback_algebraicFormToHolomorphicForm,
    Algebra.DeRham.map_ofConstant]
  rfl

lemma holomorphicFormPullback_differential
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ)
    (a : HolomorphicForm Y e U p) :
    holomorphicFormPullback X Y f d e U (p + 1)
        (holomorphicFormDifferential Y e U p a) =
      holomorphicFormDifferential X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p
        (holomorphicFormPullback X Y f d e U p a) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations Y e U p) a
  change Submodule.Quotient.mk
      (rawHolomorphicFormPullback X Y f d e U (p + 1)
        (Algebra.DeRham.rawDifferential ℂ
          (OpenHolomorphicFunctions Y e U) p a)) =
    Submodule.Quotient.mk
      (Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d
          (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop))) p
        (rawHolomorphicFormPullback X Y f d e U p a))
  exact congrArg Submodule.Quotient.mk
    (Algebra.DeRham.rawMap_rawDifferential ℂ
      (holomorphicFunctionPullbackAlgHom X Y f d e U) p a)

lemma holomorphicFunctionPullbackAlgHom_restriction
    {U V : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ} (i : U ⟶ V) :
    (holomorphicFunctionPullbackAlgHom X Y f d e V).comp
        (holomorphicRestrictionAlgHom Y e i) =
      (holomorphicRestrictionAlgHom X d
          ((Opens.map (analyticMapTopCat X Y f)).op.map i)).comp
        (holomorphicFunctionPullbackAlgHom X Y f d e U) := by
  ext g x
  rfl

lemma rawHolomorphicFormPullback_restriction
    {U V : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ} (i : U ⟶ V)
    (p : ℕ)
    (a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p) :
    rawHolomorphicFormPullback X Y f d e V p
        (rawRestriction Y e i p a) =
      rawRestriction X d ((Opens.map (analyticMapTopCat X Y f)).op.map i) p
        (rawHolomorphicFormPullback X Y f d e U p a) := by
  unfold rawHolomorphicFormPullback rawRestriction
  have h := congrArg (fun g ↦ Algebra.DeRham.rawMap ℂ g p)
    (holomorphicFunctionPullbackAlgHom_restriction X Y f d e i)
  simpa only [Algebra.DeRham.rawMap_comp, LinearMap.comp_apply] using
    congrArg (fun L ↦ L a) h

lemma holomorphicFormPullback_restriction
    {U V : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ} (i : U ⟶ V)
    (p : ℕ) (a : HolomorphicForm Y e U p) :
    holomorphicFormPullback X Y f d e V p
        (holomorphicFormRestriction Y e i p a) =
      holomorphicFormRestriction X d
          ((Opens.map (analyticMapTopCat X Y f)).op.map i) p
        (holomorphicFormPullback X Y f d e U p a) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations Y e U p) a
  change Submodule.Quotient.mk
      (rawHolomorphicFormPullback X Y f d e V p
        (rawRestriction Y e i p a)) =
    Submodule.Quotient.mk
      (rawRestriction X d
        ((Opens.map (analyticMapTopCat X Y f)).op.map i) p
        (rawHolomorphicFormPullback X Y f d e U p a))
  rw [rawHolomorphicFormPullback_restriction X Y f d e i p a]

/-- Pullback of holomorphic forms as a morphism of presheaves on the target. -/
def holomorphicFormPullbackPresheaf (p : ℕ) :
    holomorphicDeRhamPresheaf Y e p ⟶
      (Opens.map (analyticMapTopCat X Y f)).op ⋙
        holomorphicDeRhamPresheaf X d p where
  app U := AddCommGrpCat.ofHom
    (holomorphicFormPullback X Y f d e U p).toAddMonoidHom
  naturality U V i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    exact holomorphicFormPullback_restriction X Y f d e i p a

lemma holomorphicFormPullbackPresheaf_differential (p : ℕ) :
    holomorphicDeRhamDifferential Y e p ≫
        holomorphicFormPullbackPresheaf X Y f d e (p + 1) =
      holomorphicFormPullbackPresheaf X Y f d e p ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (holomorphicDeRhamDifferential X d p) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact holomorphicFormPullback_differential X Y f d e U p a

/-- The presheaf-level pullback followed by sheafification on the source. -/
noncomputable def holomorphicFormPullbackToPushforwardPresheaf (p : ℕ) :
    holomorphicDeRhamPresheaf Y e p ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).obj
          (holomorphicDeRhamSheaf X d p)).obj :=
  holomorphicFormPullbackPresheaf X Y f d e p ≫
    Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
      (toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p))

/-- Pullback of holomorphic forms as a map to the direct image sheaf. -/
noncomputable def holomorphicFormPullbackSheaf (p : ℕ) :
    holomorphicDeRhamSheaf Y e p ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).obj
          (holomorphicDeRhamSheaf X d p) :=
  ⟨sheafifyLift
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
    (holomorphicFormPullbackToPushforwardPresheaf X Y f d e p)
    (((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X Y f)).obj
        (holomorphicDeRhamSheaf X d p)).property)⟩

lemma toSheafify_comp_holomorphicFormPullbackSheaf (p : ℕ) :
    toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
        (holomorphicDeRhamPresheaf Y e p) ≫
      (holomorphicFormPullbackSheaf X Y f d e p).hom =
        holomorphicFormPullbackToPushforwardPresheaf X Y f d e p :=
  toSheafify_sheafifyLift
    (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
    (holomorphicFormPullbackToPushforwardPresheaf X Y f d e p)
    (((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X Y f)).obj
        (holomorphicDeRhamSheaf X d p)).property)

set_option backward.isDefEq.respectTransparency false in
lemma holomorphicFormPullbackToPushforwardPresheaf_differential (p : ℕ) :
    holomorphicDeRhamDifferential Y e p ≫
        holomorphicFormPullbackToPushforwardPresheaf X Y f d e (p + 1) =
      holomorphicFormPullbackToPushforwardPresheaf X Y f d e p ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (holomorphicDeRhamSheafDifferential X d p)).hom := by
  unfold holomorphicFormPullbackToPushforwardPresheaf
  change holomorphicDeRhamDifferential Y e p ≫
      holomorphicFormPullbackPresheaf X Y f d e (p + 1) ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
            (holomorphicDeRhamPresheaf X d (p + 1))) =
    holomorphicFormPullbackPresheaf X Y f d e p ≫
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        (toSheafify
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)) ≫
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        ((holomorphicDeRhamSheafDifferential X d p).hom)
  calc
    _ = (holomorphicDeRhamDifferential Y e p ≫
          holomorphicFormPullbackPresheaf X Y f d e (p + 1)) ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
            (holomorphicDeRhamPresheaf X d (p + 1))) :=
      (Category.assoc _ _ _).symm
    _ = (holomorphicFormPullbackPresheaf X Y f d e p ≫
          Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
            (holomorphicDeRhamDifferential X d p)) ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
            (holomorphicDeRhamPresheaf X d (p + 1))) := by
      rw [holomorphicFormPullbackPresheaf_differential]
    _ = holomorphicFormPullbackPresheaf X Y f d e p ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (holomorphicDeRhamDifferential X d p ≫
            toSheafify
              (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
              (holomorphicDeRhamPresheaf X d (p + 1))) := by
      rw [Category.assoc, Functor.whiskerLeft_comp]
    _ = holomorphicFormPullbackPresheaf X Y f d e p ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (toSheafify
              (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
              (holomorphicDeRhamPresheaf X d p) ≫
            (holomorphicDeRhamSheafDifferential X d p).hom) := by
      rw [toSheafify_naturality]
      rfl
    _ = _ := by rw [Functor.whiskerLeft_comp]

/-- Pullback commutes with the sheafified de Rham differential. -/
lemma holomorphicFormPullbackSheaf_differential (p : ℕ) :
    holomorphicDeRhamSheafDifferential Y e p ≫
        holomorphicFormPullbackSheaf X Y f d e (p + 1) =
      holomorphicFormPullbackSheaf X Y f d e p ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (holomorphicDeRhamSheafDifferential X d p) := by
  apply Sheaf.hom_ext
  let η := holomorphicDeRhamDifferential Y e p ≫
    holomorphicFormPullbackToPushforwardPresheaf X Y f d e (p + 1)
  apply (sheafifyLift_unique
    (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint Y))) η
    (((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X Y f)).obj
        (holomorphicDeRhamSheaf X d (p + 1))).property) _ ?_).trans
  · apply (sheafifyLift_unique
      (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint Y))) η
      (((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).obj
          (holomorphicDeRhamSheaf X d (p + 1))).property) _ ?_).symm
    unfold η
    change toSheafify
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
          (holomorphicDeRhamPresheaf Y e p) ≫
        (holomorphicFormPullbackSheaf X Y f d e p).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (holomorphicDeRhamSheafDifferential X d p)).hom = _
    calc
      _ = (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
            (holomorphicDeRhamPresheaf Y e p) ≫
            (holomorphicFormPullbackSheaf X Y f d e p).hom) ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat
            (analyticMapTopCat X Y f)).map
              (holomorphicDeRhamSheafDifferential X d p)).hom :=
        (Category.assoc _ _ _).symm
      _ = holomorphicFormPullbackToPushforwardPresheaf X Y f d e p ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat
            (analyticMapTopCat X Y f)).map
              (holomorphicDeRhamSheafDifferential X d p)).hom := by
        rw [toSheafify_comp_holomorphicFormPullbackSheaf]
      _ = _ :=
        (holomorphicFormPullbackToPushforwardPresheaf_differential
          X Y f d e p).symm
  · unfold η
    change toSheafify
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
          (holomorphicDeRhamPresheaf Y e p) ≫
        (holomorphicDeRhamSheafDifferential Y e p).hom ≫
        (holomorphicFormPullbackSheaf X Y f d e (p + 1)).hom = _
    calc
      _ = (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
            (holomorphicDeRhamPresheaf Y e p) ≫
            (holomorphicDeRhamSheafDifferential Y e p).hom) ≫
          (holomorphicFormPullbackSheaf X Y f d e (p + 1)).hom :=
        (Category.assoc _ _ _).symm
      _ = (holomorphicDeRhamDifferential Y e p ≫
            toSheafify
              (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
              (holomorphicDeRhamPresheaf Y e (p + 1))) ≫
          (holomorphicFormPullbackSheaf X Y f d e (p + 1)).hom := by
        rw [toSheafify_naturality]
        rfl
      _ = holomorphicDeRhamDifferential Y e p ≫
          (toSheafify
              (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
              (holomorphicDeRhamPresheaf Y e (p + 1)) ≫
            (holomorphicFormPullbackSheaf X Y f d e (p + 1)).hom) :=
        Category.assoc _ _ _
      _ = _ := by
        rw [toSheafify_comp_holomorphicFormPullbackSheaf]

/-- Pullback on the entire holomorphic de Rham complex, valued in direct image. -/
noncomputable def holomorphicDeRhamPullbackComplex :
    holomorphicDeRhamComplex Y e ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (holomorphicDeRhamComplex X d) where
  f p := holomorphicFormPullbackSheaf X Y f d e p
  comm' p q hpq := by
    obtain rfl := hpq
    rw [holomorphicDeRhamComplex_d, Functor.mapHomologicalComplex_obj_d,
      holomorphicDeRhamComplex_d]
    exact (holomorphicFormPullbackSheaf_differential X Y f d e p).symm

/-- Pullback on the integer-indexed holomorphic de Rham complex. -/
def holomorphicDeRhamPullbackComplexInt
    [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] :
    holomorphicDeRhamComplexInt Y ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (holomorphicDeRhamComplexInt X) :=
  HomologicalComplex.extendMap
      (holomorphicDeRhamPullbackComplex X Y f (dim X.left) (dim Y.left))
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.pushforward AddCommGrpCat (analyticMapTopCat X Y f))
      (holomorphicDeRhamComplex X (dim X.left))
      ComplexShape.embeddingUpNat).inv

/-- Pullback of zero-forms sends a constant to the same constant, at presheaf level. -/
theorem constantsToHolomorphicDeRhamZero_naturality :
    constantsToHolomorphicDeRhamZero Y e ≫
        holomorphicFormPullbackPresheaf X Y f d e 0 =
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        (constantsToHolomorphicDeRhamZero X d) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  exact holomorphicFormPullback_ofConstant X Y f d e U c

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The constant-to-de Rham comparison is natural under holomorphic pullback. -/
theorem constantsToHolomorphicDeRhamZeroSheaf_naturality :
    constantsToHolomorphicDeRhamZeroSheaf Y e ≫
        holomorphicFormPullbackSheaf X Y f d e 0 =
      TopCat.Sheaf.constantRestriction (analyticMapTopCat X Y f)
          (AddCommGrpCat.of ℂ) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (constantsToHolomorphicDeRhamZeroSheaf X d) := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext
  · exact (((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X Y f)).obj
        (holomorphicDeRhamSheaf X d 0)).property)
  change toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
        (constantComplexAddCommGrpPresheaf Y) ≫
      (constantsToHolomorphicDeRhamZeroSheaf Y e).hom ≫
      (holomorphicFormPullbackSheaf X Y f d e 0).hom =
    toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
        (constantComplexAddCommGrpPresheaf Y) ≫
      (TopCat.Sheaf.constantRestriction (analyticMapTopCat X Y f)
        (AddCommGrpCat.of ℂ)).hom ≫
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        ((constantsToHolomorphicDeRhamZeroSheaf X d).hom)
  dsimp only [constantsToHolomorphicDeRhamZeroSheaf]
  dsimp only [constantComplexAddCommGrpPresheaf]
  rw [← Category.assoc, ← toSheafify_naturality,
    Category.assoc, toSheafify_comp_holomorphicFormPullbackSheaf]
  have hconst := congrArg (fun k ↦ k ≫
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        (((presheafToSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          AddCommGrpCat).map
            (constantsToHolomorphicDeRhamZero X d)).hom))
    (TopCat.Sheaf.toSheafify_constantRestriction
      (analyticMapTopCat X Y f) (AddCommGrpCat.of ℂ))
  conv_rhs => rw [← Category.assoc]
  rw [hconst]
  unfold holomorphicFormPullbackToPushforwardPresheaf
  rw [← Category.assoc,
    constantsToHolomorphicDeRhamZero_naturality X Y f d e]
  rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp]
  rw [toSheafify_naturality]
  rfl

/-- Restriction of the complex constant sheaf, as a morphism of complexes
concentrated in degree zero. -/
def complexConstantRestrictionComplex :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y)))).obj
        (constantComplexSheaf Y) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        ((CochainComplex.single₀
          (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
          (constantComplexSheaf X)) :=
  (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y)))).map
      (TopCat.Sheaf.constantRestriction (analyticMapTopCat X Y f)
        (AddCommGrpCat.of ℂ)) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat (analyticMapTopCat X Y f))
      (ComplexShape.up ℕ) 0).inv.app (constantComplexSheaf X)

/-- Restriction of the complex constant sheaf on integer-indexed complexes. -/
def complexConstantRestrictionComplexInt :
    constantComplexSheafComplexInt Y ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (constantComplexSheafComplexInt X) :=
  HomologicalComplex.extendMap
      (complexConstantRestrictionComplex X Y f)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.pushforward AddCommGrpCat (analyticMapTopCat X Y f))
      ((CochainComplex.single₀
        (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexSheaf X))
      ComplexShape.embeddingUpNat).inv

/-- The constant-to-de Rham comparison commutes with holomorphic pullback as
a morphism of natural-degree complexes. -/
theorem constantsToHolomorphicDeRhamComplex_naturality :
    constantsToHolomorphicDeRhamComplex Y e ≫
        holomorphicDeRhamPullbackComplex X Y f d e =
      complexConstantRestrictionComplex X Y f ≫
        (((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map
          (constantsToHolomorphicDeRhamComplex X d)) := by
  apply HomologicalComplex.hom_ext
  intro p
  rcases p with _ | p
  · change constantsToHolomorphicDeRhamZeroSheaf Y e ≫
        holomorphicFormPullbackSheaf X Y f d e 0 =
      TopCat.Sheaf.constantRestriction (analyticMapTopCat X Y f)
          (AddCommGrpCat.of ℂ) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (constantsToHolomorphicDeRhamZeroSheaf X d)
    exact constantsToHolomorphicDeRhamZeroSheaf_naturality X Y f d e
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 (constantComplexSheaf Y) (p + 1)
      (Nat.succ_ne_zero p)).eq_of_src

/-- The constant-to-de Rham comparison commutes with holomorphic pullback on
the integer-indexed complexes used by public hypercohomology. -/
theorem constantsToHolomorphicDeRhamComplexInt_naturality
    [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] :
    constantsToHolomorphicDeRhamComplexInt Y ≫
        holomorphicDeRhamPullbackComplexInt X Y f =
      complexConstantRestrictionComplexInt X Y f ≫
        (((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (constantsToHolomorphicDeRhamComplexInt X)) := by
  let F := TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticMapTopCat X Y f)
  let L := holomorphicDeRhamComplex X (dim X.left)
  let E := ComplexShape.embeddingUpNat
  apply (cancel_mono
    (HomologicalComplex.mapExtendCanonicalIso F L E).hom).1
  dsimp only [complexConstantRestrictionComplexInt,
    holomorphicDeRhamPullbackComplexInt,
    constantsToHolomorphicDeRhamComplexInt,
    constantComplexSheafComplexInt,
    holomorphicDeRhamComplexInt]
  simp only [F, L, E, Category.assoc]
  rw [HomologicalComplex.mapExtendCanonicalIso_naturality]
  simp only [Category.comp_id, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  rw [← HomologicalComplex.extendMap_comp,
    constantsToHolomorphicDeRhamComplex_naturality]
  rw [HomologicalComplex.extendMap_comp]

end AlgebraicGeometry.ComplexPoint
