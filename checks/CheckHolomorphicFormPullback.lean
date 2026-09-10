import Other.AlgebraicGeometry.HolomorphicFunctionPullback
import Other.AlgebraicGeometry.HolomorphicFormSheafification

@[expose] noncomputable section

open CategoryTheory Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (d e : ℕ)
variable [SmoothOfRelativeDimension d X.hom]
  [SmoothOfRelativeDimension e Y.hom]

def checkHolomorphicFunctionPullbackAlgHom
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

def checkRawHolomorphicFormPullback
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p →ₗ[ℂ]
      Algebra.DeRham.RawForm ℂ
        (OpenHolomorphicFunctions X d
          (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop))) p :=
  Algebra.DeRham.rawMap ℂ
    (checkHolomorphicFunctionPullbackAlgHom X Y f d e U) p

def checkChartMapAt
    (z : ComplexPoint X) (y : Fin d → ℂ) :
    (Fin d → ℂ) → (Fin e → ℂ) :=
  let x := (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y
  let fx := Point.map f x
  fun v ↦
    (extChartAt (modelWithCornersSelf ℂ (Fin e → ℂ)) fx)
      (Point.map f
        ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm v))

lemma checkChartMapAt_apply_self
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).target) :
    checkChartMapAt X Y f d e z y y =
      (extChartAt (modelWithCornersSelf ℂ (Fin e → ℂ))
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)))
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) := rfl

lemma check_chartSection_pullback_eventuallyEq
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (g : OpenHolomorphicFunctions Y e U)
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z) :
    chartSection X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z
        (checkHolomorphicFunctionPullbackAlgHom X Y f d e U g) =ᶠ[𝓝 y]
      fun v ↦ chartSection Y e U
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) g
        (checkChartMapAt X Y f d e z y v) := by
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

lemma checkChartMapAt_differentiableAt
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).target) :
    DifferentiableAt ℂ (checkChartMapAt X Y f d e z y) y := by
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

lemma check_chartSectionDifferential_pullback
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (g : OpenHolomorphicFunctions Y e U)
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z) :
    chartSectionDifferential X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z
        (checkHolomorphicFunctionPullbackAlgHom X Y f d e U g) y =
      (chartSectionDifferential Y e U
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) g
        (checkChartMapAt X Y f d e z y y)).comp
          (fderiv ℂ (checkChartMapAt X Y f d e z y) y) := by
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
  have heq := check_chartSection_pullback_eventuallyEq X Y f d e U g z hy
  have hself : checkChartMapAt X Y f d e z y y = eY fx := rfl
  rw [hself]
  unfold chartSectionDifferential
  rw [fderivWithin_of_mem_nhds hsourceN,
    fderivWithin_of_mem_nhds htargetN]
  rw [heq.fderiv_eq]
  have hg : DifferentiableAt ℂ (chartSection Y e U fx g) (eY fx) :=
    ((chartSection_contDiffWithinAt Y e U fx g hyTarget).differentiableWithinAt
      (by simp)).differentiableAt htargetN
  have hf : DifferentiableAt ℂ (checkChartMapAt X Y f d e z y) y :=
    checkChartMapAt_differentiableAt X Y f d e z hy.1
  change fderiv ℂ
      (chartSection Y e U fx g ∘ checkChartMapAt X Y f d e z y) y = _
  rw [fderiv_comp y hg hf]
  rw [hself]

lemma check_chartGeneratorEvaluation_pullback
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (p : ℕ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions Y e U) p)
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z) :
    chartGeneratorEvaluation X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z p
        (Algebra.DeRham.generatorMap ℂ
          (checkHolomorphicFunctionPullbackAlgHom X Y f d e U) p g) y =
      (chartGeneratorEvaluation Y e U
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) p g
        (checkChartMapAt X Y f d e z y y)).compContinuousLinearMap
          (fderiv ℂ (checkChartMapAt X Y f d e z y) y) := by
  have hcoeff := check_chartSection_pullback_eventuallyEq X Y f d e U g.1 z hy
  have hcoeffAt := hcoeff.self_of_nhds
  simp only [Algebra.DeRham.generatorMap, chartGeneratorEvaluation]
  rw [hcoeffAt]
  have hdiff : ∀ i : Fin p,
      chartSectionDifferential X d
          (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z
          (checkHolomorphicFunctionPullbackAlgHom X Y f d e U (g.2 i)) y =
        (chartSectionDifferential Y e U
          (Point.map f
            ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y))
          (g.2 i) (checkChartMapAt X Y f d e z y y)).comp
            (fderiv ℂ (checkChartMapAt X Y f d e z y) y) :=
    fun i ↦ check_chartSectionDifferential_pullback X Y f d e U (g.2 i) z hy
  simp_rw [hdiff]
  rw [wedgeCovectors_compContinuousLinearMap]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma check_chartRawEvaluation_pullback
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (p : ℕ)
    (a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p)
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z) :
    chartRawEvaluation X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) z p
        (checkRawHolomorphicFormPullback X Y f d e U p a) y =
      (chartRawEvaluation Y e U
        (Point.map f
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) p a
        (checkChartMapAt X Y f d e z y y)).compContinuousLinearMap
          (fderiv ℂ (checkChartMapAt X Y f d e z y) y) := by
  classical
  unfold checkRawHolomorphicFormPullback
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
      rw [check_chartGeneratorEvaluation_pullback X Y f d e U p g z hy]
      refine ContinuousAlternatingMap.ext fun v ↦ ?_
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma checkRawHolomorphicFormPullback_mem_relations
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ)
    (p : ℕ)
    {a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p}
    (ha : a ∈ holomorphicFormRelations Y e U p) :
    checkRawHolomorphicFormPullback X Y f d e U p a ∈
      holomorphicFormRelations X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p := by
  rw [holomorphicFormRelations_eq_chartEvaluationKernel] at ha ⊢
  apply (mem_chartEvaluationKernel_iff X d
    (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p _).2
  intro z y hy
  rw [check_chartRawEvaluation_pullback X Y f d e U p a z hy]
  let eX := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
  let x : ComplexPoint X := eX.symm y
  let fx : ComplexPoint Y := Point.map f x
  let eY := extChartAt (modelWithCornersSelf ℂ (Fin e → ℂ)) fx
  have hfxY : fx ∈ eY.source := mem_extChartAt_source fx
  have htarget : checkChartMapAt X Y f d e z y y ∈
      chartSectionDomain Y e U fx := by
    refine ⟨eY.map_source hfxY, ?_⟩
    change eY.symm (eY fx) ∈ U.unop
    rw [eY.left_inv hfxY]
    exact hy.2
  have heval :=
    (mem_chartEvaluationKernel_iff Y e U p a).1 ha fx
      (checkChartMapAt X Y f d e z y y) htarget
  rw [heval]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- Pullback of holomorphic differential forms along an algebraic morphism. -/
def checkHolomorphicFormPullback
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ) :
    HolomorphicForm Y e U p →ₗ[ℂ]
      HolomorphicForm X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p :=
  (holomorphicFormRelations Y e U p).liftQ
    ((holomorphicFormRelations X d
      (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p).mkQ.comp
        (checkRawHolomorphicFormPullback X Y f d e U p)) (by
      intro a ha
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact checkRawHolomorphicFormPullback_mem_relations X Y f d e U p ha)

@[simp]
lemma checkHolomorphicFormPullback_mkQ
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ)
    (a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p) :
    checkHolomorphicFormPullback X Y f d e U p
        ((holomorphicFormRelations Y e U p).mkQ a) =
      (holomorphicFormRelations X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p).mkQ
        (checkRawHolomorphicFormPullback X Y f d e U p a) :=
  rfl

@[simp]
lemma checkHolomorphicFormPullback_algebraicFormToHolomorphicForm
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ)
    (a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions Y e U) p) :
    checkHolomorphicFormPullback X Y f d e U p
        (algebraicFormToHolomorphicForm Y e U p a) =
      algebraicFormToHolomorphicForm X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p
        (Algebra.DeRham.map ℂ
          (checkHolomorphicFunctionPullbackAlgHom X Y f d e U) p a) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions Y e U) p) a
  rfl

@[simp]
lemma checkHolomorphicFormPullback_ofConstant
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (c : ℂ) :
    checkHolomorphicFormPullback X Y f d e U 0
        (holomorphicFormOfConstant Y e U c) =
      holomorphicFormOfConstant X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) c := by
  rw [holomorphicFormOfConstant, holomorphicFormOfConstant, LinearMap.comp_apply,
    checkHolomorphicFormPullback_algebraicFormToHolomorphicForm,
    Algebra.DeRham.map_ofConstant]
  rfl

lemma checkHolomorphicFormPullback_differential
    (U : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ) (p : ℕ)
    (a : HolomorphicForm Y e U p) :
    checkHolomorphicFormPullback X Y f d e U (p + 1)
        (holomorphicFormDifferential Y e U p a) =
      holomorphicFormDifferential X d
        (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop)) p
        (checkHolomorphicFormPullback X Y f d e U p a) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations Y e U p) a
  change Submodule.Quotient.mk
      (checkRawHolomorphicFormPullback X Y f d e U (p + 1)
        (Algebra.DeRham.rawDifferential ℂ
          (OpenHolomorphicFunctions Y e U) p a)) =
    Submodule.Quotient.mk
      (Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d
          (.op ((Opens.map (analyticMapTopCat X Y f)).obj U.unop))) p
        (checkRawHolomorphicFormPullback X Y f d e U p a))
  exact congrArg Submodule.Quotient.mk
    (Algebra.DeRham.rawMap_rawDifferential ℂ
      (checkHolomorphicFunctionPullbackAlgHom X Y f d e U) p a)

lemma checkHolomorphicFunctionPullbackAlgHom_restriction
    {U V : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ} (i : U ⟶ V) :
    (checkHolomorphicFunctionPullbackAlgHom X Y f d e V).comp
        (holomorphicRestrictionAlgHom Y e i) =
      (holomorphicRestrictionAlgHom X d
          ((Opens.map (analyticMapTopCat X Y f)).op.map i)).comp
        (checkHolomorphicFunctionPullbackAlgHom X Y f d e U) := by
  ext g x
  rfl

lemma checkRawHolomorphicFormPullback_restriction
    {U V : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ} (i : U ⟶ V)
    (p : ℕ)
    (a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions Y e U) p) :
    checkRawHolomorphicFormPullback X Y f d e V p
        (rawRestriction Y e i p a) =
      rawRestriction X d ((Opens.map (analyticMapTopCat X Y f)).op.map i) p
        (checkRawHolomorphicFormPullback X Y f d e U p a) := by
  unfold checkRawHolomorphicFormPullback rawRestriction
  have h := congrArg (fun g ↦ Algebra.DeRham.rawMap ℂ g p)
    (checkHolomorphicFunctionPullbackAlgHom_restriction X Y f d e i)
  simpa only [Algebra.DeRham.rawMap_comp, LinearMap.comp_apply] using
    congrArg (fun L ↦ L a) h

lemma checkHolomorphicFormPullback_restriction
    {U V : (Opens (TopCat.of (ComplexPoint Y)))ᵒᵖ} (i : U ⟶ V)
    (p : ℕ) (a : HolomorphicForm Y e U p) :
    checkHolomorphicFormPullback X Y f d e V p
        (holomorphicFormRestriction Y e i p a) =
      holomorphicFormRestriction X d
          ((Opens.map (analyticMapTopCat X Y f)).op.map i) p
        (checkHolomorphicFormPullback X Y f d e U p a) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations Y e U p) a
  change Submodule.Quotient.mk
      (checkRawHolomorphicFormPullback X Y f d e V p
        (rawRestriction Y e i p a)) =
    Submodule.Quotient.mk
      (rawRestriction X d
        ((Opens.map (analyticMapTopCat X Y f)).op.map i) p
        (checkRawHolomorphicFormPullback X Y f d e U p a))
  rw [checkRawHolomorphicFormPullback_restriction X Y f d e i p a]

/-- Pullback of holomorphic forms as a morphism of presheaves on the target. -/
def checkHolomorphicFormPullbackPresheaf (p : ℕ) :
    holomorphicDeRhamPresheaf Y e p ⟶
      (Opens.map (analyticMapTopCat X Y f)).op ⋙
        holomorphicDeRhamPresheaf X d p where
  app U := AddCommGrpCat.ofHom
    (checkHolomorphicFormPullback X Y f d e U p).toAddMonoidHom
  naturality U V i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    exact checkHolomorphicFormPullback_restriction X Y f d e i p a

lemma checkHolomorphicFormPullbackPresheaf_differential (p : ℕ) :
    holomorphicDeRhamDifferential Y e p ≫
        checkHolomorphicFormPullbackPresheaf X Y f d e (p + 1) =
      checkHolomorphicFormPullbackPresheaf X Y f d e p ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (holomorphicDeRhamDifferential X d p) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact checkHolomorphicFormPullback_differential X Y f d e U p a

/-- The presheaf-level pullback followed by sheafification on the source. -/
noncomputable def checkHolomorphicFormPullbackToPushforwardPresheaf (p : ℕ) :
    holomorphicDeRhamPresheaf Y e p ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).obj
          (holomorphicDeRhamSheaf X d p)).obj :=
  checkHolomorphicFormPullbackPresheaf X Y f d e p ≫
    Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
      (toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p))

/-- Pullback of holomorphic forms as a map to the direct image sheaf. -/
noncomputable def checkHolomorphicFormPullbackSheaf (p : ℕ) :
    holomorphicDeRhamSheaf Y e p ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).obj
          (holomorphicDeRhamSheaf X d p) :=
  ⟨sheafifyLift
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
    (checkHolomorphicFormPullbackToPushforwardPresheaf X Y f d e p)
    (((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X Y f)).obj
        (holomorphicDeRhamSheaf X d p)).property)⟩

lemma check_toSheafify_comp_holomorphicFormPullbackSheaf (p : ℕ) :
    toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
        (holomorphicDeRhamPresheaf Y e p) ≫
      (checkHolomorphicFormPullbackSheaf X Y f d e p).hom =
        checkHolomorphicFormPullbackToPushforwardPresheaf X Y f d e p :=
  toSheafify_sheafifyLift
    (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
    (checkHolomorphicFormPullbackToPushforwardPresheaf X Y f d e p)
    (((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X Y f)).obj
        (holomorphicDeRhamSheaf X d p)).property)

set_option backward.isDefEq.respectTransparency false in
lemma checkHolomorphicFormPullbackToPushforwardPresheaf_differential (p : ℕ) :
    holomorphicDeRhamDifferential Y e p ≫
        checkHolomorphicFormPullbackToPushforwardPresheaf X Y f d e (p + 1) =
      checkHolomorphicFormPullbackToPushforwardPresheaf X Y f d e p ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (holomorphicDeRhamSheafDifferential X d p)).hom := by
  unfold checkHolomorphicFormPullbackToPushforwardPresheaf
  change holomorphicDeRhamDifferential Y e p ≫
      checkHolomorphicFormPullbackPresheaf X Y f d e (p + 1) ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
            (holomorphicDeRhamPresheaf X d (p + 1))) =
    checkHolomorphicFormPullbackPresheaf X Y f d e p ≫
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        (toSheafify
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)) ≫
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        ((holomorphicDeRhamSheafDifferential X d p).hom)
  calc
    _ = (holomorphicDeRhamDifferential Y e p ≫
          checkHolomorphicFormPullbackPresheaf X Y f d e (p + 1)) ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
            (holomorphicDeRhamPresheaf X d (p + 1))) :=
      (Category.assoc _ _ _).symm
    _ = (checkHolomorphicFormPullbackPresheaf X Y f d e p ≫
          Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
            (holomorphicDeRhamDifferential X d p)) ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
            (holomorphicDeRhamPresheaf X d (p + 1))) := by
      rw [checkHolomorphicFormPullbackPresheaf_differential]
    _ = checkHolomorphicFormPullbackPresheaf X Y f d e p ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (holomorphicDeRhamDifferential X d p ≫
            toSheafify
              (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
              (holomorphicDeRhamPresheaf X d (p + 1))) := by
      rw [Category.assoc, Functor.whiskerLeft_comp]
    _ = checkHolomorphicFormPullbackPresheaf X Y f d e p ≫
        Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
          (toSheafify
              (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
              (holomorphicDeRhamPresheaf X d p) ≫
            (holomorphicDeRhamSheafDifferential X d p).hom) := by
      rw [toSheafify_naturality]
      rfl
    _ = _ := by rw [Functor.whiskerLeft_comp]

/-- Pullback commutes with the sheafified de Rham differential. -/
lemma checkHolomorphicFormPullbackSheaf_differential (p : ℕ) :
    holomorphicDeRhamSheafDifferential Y e p ≫
        checkHolomorphicFormPullbackSheaf X Y f d e (p + 1) =
      checkHolomorphicFormPullbackSheaf X Y f d e p ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (holomorphicDeRhamSheafDifferential X d p) := by
  apply Sheaf.hom_ext
  let η := holomorphicDeRhamDifferential Y e p ≫
    checkHolomorphicFormPullbackToPushforwardPresheaf X Y f d e (p + 1)
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
        (checkHolomorphicFormPullbackSheaf X Y f d e p).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (holomorphicDeRhamSheafDifferential X d p)).hom = _
    calc
      _ = (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
            (holomorphicDeRhamPresheaf Y e p) ≫
            (checkHolomorphicFormPullbackSheaf X Y f d e p).hom) ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat
            (analyticMapTopCat X Y f)).map
              (holomorphicDeRhamSheafDifferential X d p)).hom :=
        (Category.assoc _ _ _).symm
      _ = checkHolomorphicFormPullbackToPushforwardPresheaf X Y f d e p ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat
            (analyticMapTopCat X Y f)).map
              (holomorphicDeRhamSheafDifferential X d p)).hom := by
        rw [check_toSheafify_comp_holomorphicFormPullbackSheaf]
      _ = _ :=
        (checkHolomorphicFormPullbackToPushforwardPresheaf_differential
          X Y f d e p).symm
  · unfold η
    change toSheafify
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
          (holomorphicDeRhamPresheaf Y e p) ≫
        (holomorphicDeRhamSheafDifferential Y e p).hom ≫
        (checkHolomorphicFormPullbackSheaf X Y f d e (p + 1)).hom = _
    calc
      _ = (toSheafify
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
            (holomorphicDeRhamPresheaf Y e p) ≫
            (holomorphicDeRhamSheafDifferential Y e p).hom) ≫
          (checkHolomorphicFormPullbackSheaf X Y f d e (p + 1)).hom :=
        (Category.assoc _ _ _).symm
      _ = (holomorphicDeRhamDifferential Y e p ≫
            toSheafify
              (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
              (holomorphicDeRhamPresheaf Y e (p + 1))) ≫
          (checkHolomorphicFormPullbackSheaf X Y f d e (p + 1)).hom := by
        rw [toSheafify_naturality]
        rfl
      _ = holomorphicDeRhamDifferential Y e p ≫
          (toSheafify
              (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
              (holomorphicDeRhamPresheaf Y e (p + 1)) ≫
            (checkHolomorphicFormPullbackSheaf X Y f d e (p + 1)).hom) :=
        Category.assoc _ _ _
      _ = _ := by
        rw [check_toSheafify_comp_holomorphicFormPullbackSheaf]

/-- Pullback on the entire holomorphic de Rham complex, valued in direct image. -/
noncomputable def checkHolomorphicDeRhamPullbackComplex :
    holomorphicDeRhamComplex Y e ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (holomorphicDeRhamComplex X d) where
  f p := checkHolomorphicFormPullbackSheaf X Y f d e p
  comm' p q hpq := by
    obtain rfl := hpq
    rw [holomorphicDeRhamComplex_d, Functor.mapHomologicalComplex_obj_d,
      holomorphicDeRhamComplex_d]
    exact (checkHolomorphicFormPullbackSheaf_differential X Y f d e p).symm

end AlgebraicGeometry.ComplexPoint
