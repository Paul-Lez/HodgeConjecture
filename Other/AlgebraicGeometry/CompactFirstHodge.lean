/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExponentialConnectingComparison
public import Other.AlgebraicGeometry.FirstHodgeObstruction
public import Other.AlgebraicGeometry.HolomorphicFormSheafification
public import Other.AlgebraicGeometry.BettiGlobalSectionsComparison
public import Mathlib.Geometry.Manifold.Complex

/-!
# Compact holomorphic functions and the first Hodge filtration

On a compact smooth complex variety, every global holomorphic function is locally constant,
so its exterior derivative vanishes. This gives an explicit degree-zero lift from holomorphic-
function hypercohomology to the holomorphic de Rham complex. The first Hodge filtration long
exact sequence then makes F^1 H^1 → H^1_dR injective.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Topology Filter
open scoped ContDiff Manifold
open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance compactFirstHodgeDerived : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

theorem chartSectionDifferential_eq_zero
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : OpenHolomorphicFunctions X d (.op ⊤))
    (z : ComplexPoint X) (y : Fin d → ℂ)
    (hy : y ∈ chartSectionDomain X d (.op ⊤) z) :
    chartSectionDifferential X d (.op ⊤) z f y = 0 := by
  letI : IsManifold (modelWithCornersSelf ℂ (Fin d → ℂ)) ω
      (ComplexPoint X) := isManifold_omega X d
  letI : CompactSpace
      {x : ComplexPoint X // x ∈ (⊤ : Opens (ComplexPoint X))} :=
    isCompact_iff_compactSpace.mp isCompact_univ
  let S := chartSectionDomain X d (.op ⊤) z
  let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
  have hfinv : Continuous (fun w : S ↦ e.symm w.1) := by
    apply ContinuousOn.restrict
    exact (contMDiffOn_extChartAt_symm
      (I := modelWithCornersSelf ℂ (Fin d → ℂ)) (n := ω) z).continuousOn.mono
        Set.inter_subset_left
  let g : S → {x : ComplexPoint X // x ∈ (⊤ : Opens (ComplexPoint X))} :=
    fun w ↦ ⟨e.symm w.1, trivial⟩
  have hg : Continuous g := hfinv.subtype_mk (fun _ ↦ trivial)
  have hfLocal : IsLocallyConstant f.1 :=
    ((holomorphicFunctionSheaf_section_analytic X d f).mdifferentiable (by simp)).isLocallyConstant
  have hchartLocal : IsLocallyConstant
      (fun w : S ↦ chartSection X d (.op ⊤) z f w.1) := by
    have hcomp := hfLocal.comp_continuous hg
    convert hcomp using 1
    funext w
    rw [chartSection_apply_of_mem X d (.op ⊤) z f w.2]
    rfl
  have hevSub := hchartLocal.eventually_eq ⟨y, hy⟩
  have hev :
      Filter.EventuallyEq (nhdsWithin y S)
        (fun w ↦ chartSection X d (.op ⊤) z f w)
        (fun _ ↦ chartSection X d (.op ⊤) z f y) := by
    change ∀ᶠ w in nhdsWithin y S,
      chartSection X d (.op ⊤) z f w = chartSection X d (.op ⊤) z f y
    simpa using (eventually_nhds_subtype_iff S ⟨y, hy⟩
      (fun w ↦ chartSection X d (.op ⊤) z f w =
        chartSection X d (.op ⊤) z f y)).mp hevSub
  rw [chartSectionDifferential]
  rw [hev.fderivWithin_eq rfl]
  exact congrFun (fderivWithin_const (s := S) (chartSection X d (.op ⊤) z f y)) y

theorem holomorphicFormDifferential_function_eq_zero
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : OpenHolomorphicFunctions X d (.op ⊤)) :
    holomorphicFormDifferential X d (.op ⊤) 0
      (holomorphicFormOfFunction X d (.op ⊤) f) = 0 := by
  change Submodule.Quotient.mk
    (Algebra.DeRham.rawDifferential ℂ (OpenHolomorphicFunctions X d (.op ⊤)) 0
      (Finsupp.single (f, Fin.elim0) 1)) = 0
  rw [Submodule.Quotient.mk_eq_zero,
    holomorphicFormRelations_eq_chartEvaluationKernel]
  apply (mem_chartEvaluationKernel_iff X d (.op ⊤) 1 _).2
  intro z y hy
  rw [Algebra.DeRham.rawDifferential_single, chartRawEvaluation_single]
  simp only [one_smul, chartGeneratorEvaluation, Algebra.DeRham.nextGenerator]
  have hv :
      (fun i : Fin 1 ↦ chartSectionDifferential X d (.op ⊤) z
        (Fin.cases f Fin.elim0 i) y) =
      (fun _ ↦ chartSectionDifferential X d (.op ⊤) z f y) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv]
  rw [chartSectionDifferential_eq_zero X d f z y hy]
  rw [show wedgeCovectors (Fin d → ℂ) 1
      (fun _ ↦ (0 : (Fin d → ℂ) →L[ℂ] ℂ)) = 0 by
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    simp [wedgeCovectors, ContinuousAlternatingMap.alternatizeUncurryFin_apply]]
  exact smul_zero (M := ℂ)
    (A := (Fin d → ℂ) [⋀^Fin 1]→L[ℂ] ℂ)
    (chartSection X d (.op ⊤) z 1 y)

theorem holomorphicDeRhamSheafDifferential_function_eq_zero
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : OpenHolomorphicFunctions X d (.op ⊤)) :
    (holomorphicDeRhamSheafDifferential X d 0).hom.app (.op ⊤)
      ((holomorphicFunctionToZeroFormSheaf X d).hom.app (.op ⊤) f) = 0 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  change ((toSheafify J (holomorphicDeRhamPresheaf X d 0) ≫
      sheafifyMap J (holomorphicDeRhamDifferential X d 0)).app (.op ⊤))
        ((holomorphicFunctionToZeroFormPresheaf X d).app (.op ⊤) f) = 0
  rw [← toSheafify_naturality]
  have hz :
      (holomorphicDeRhamDifferential X d 0).app (.op ⊤)
        ((holomorphicFunctionToZeroFormPresheaf X d).app (.op ⊤) f) = 0 :=
    holomorphicFormDifferential_function_eq_zero X d f
  rw [NatTrans.comp_app]
  change (toSheafify J (holomorphicDeRhamPresheaf X d 1)).app (.op ⊤)
    ((holomorphicDeRhamDifferential X d 0).app (.op ⊤)
      ((holomorphicFunctionToZeroFormPresheaf X d).app (.op ⊤) f)) = 0
  rw [hz]
  exact map_zero (ConcreteCategory.hom
    ((toSheafify J (holomorphicDeRhamPresheaf X d 1)).app (.op ⊤)))

theorem constantToHolomorphicFunction_comp_differential_eq_zero
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : constantIntegerSheaf X ⟶ holomorphicAdditiveFunctionSheaf X d) :
    f ≫ holomorphicFunctionToZeroFormSheaf X d ≫
      holomorphicDeRhamSheafDifferential X d 0 = 0 := by
  letI : AddCommGroup
      (constantIntegerSheaf X ⟶ holomorphicDeRhamSheaf X d 1) :=
    (inferInstance : Preadditive (AnalyticAdditiveSheaf X)).homGroup _ _
  letI : AddCommGroup
      ((constantSheaf
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ) ⟶ holomorphicDeRhamSheaf X d 1) :=
    (inferInstance : Preadditive (AnalyticAdditiveSheaf X)).homGroup _ _
  apply (TopCat.Sheaf.integerConstantHomEquivGlobalSections
    (holomorphicDeRhamSheaf X d 1)).injective
  let q : holomorphicAdditiveFunctionSheaf X d ⟶
      holomorphicDeRhamSheaf X d 1 :=
    holomorphicFunctionToZeroFormSheaf X d ≫
    holomorphicDeRhamSheafDifferential X d 0
  calc
    TopCat.Sheaf.integerConstantHomEquivGlobalSections
        (holomorphicDeRhamSheaf X d 1)
        (f ≫ holomorphicFunctionToZeroFormSheaf X d ≫
          holomorphicDeRhamSheafDifferential X d 0) =
      TopCat.Sheaf.integerConstantHomEquivGlobalSections
        (holomorphicDeRhamSheaf X d 1) (f ≫ q) := by
          rfl
    _ = q.hom.app (.op ⊤)
        (TopCat.Sheaf.integerConstantHomEquivGlobalSections
          (holomorphicAdditiveFunctionSheaf X d) f) :=
      TopCat.Sheaf.integerConstantHomEquivGlobalSections_naturality q f
    _ = 0 := by
      change (holomorphicDeRhamSheafDifferential X d 0).hom.app (.op ⊤)
        ((holomorphicFunctionToZeroFormSheaf X d).hom.app (.op ⊤)
          (TopCat.Sheaf.integerConstantHomEquivGlobalSections
            (holomorphicAdditiveFunctionSheaf X d) f)) = 0
      exact holomorphicDeRhamSheafDifferential_function_eq_zero X d _
    _ = TopCat.Sheaf.integerConstantHomEquivGlobalSections
        (holomorphicDeRhamSheaf X d 1)
        (0 : constantIntegerSheaf X ⟶ holomorphicDeRhamSheaf X d 1) :=
      by
        let e := TopCat.Sheaf.integerConstantHomEquivGlobalSections
          (holomorphicDeRhamSheaf X d 1)
        have hsection : e.symm 0 =
            (0 : constantIntegerSheaf X ⟶ holomorphicDeRhamSheaf X d 1) :=
          (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections
            (holomorphicDeRhamSheaf X d 1)).symm.map_zero
        have hzero : e
            (0 : constantIntegerSheaf X ⟶ holomorphicDeRhamSheaf X d 1) = 0 := by
          apply e.symm.injective
          exact (e.symm_apply_apply 0).trans hsection.symm
        exact hzero.symm

theorem constantToExtendedZeroForm_closed
    [IsIntegral X.left] [Smooth X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : constantIntegerSheaf X ⟶
      holomorphicAdditiveFunctionSheaf X (dim X.left)) :
    (f ≫ holomorphicFunctionToZeroFormSheaf X (dim X.left) ≫
      ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
        ComplexShape.embeddingUpNat (i := 0) rfl).inv) ≫
      (holomorphicDeRhamComplexInt X).d 0 1 = 0 := by
  unfold holomorphicDeRhamComplexInt
  rw [HomologicalComplex.extend_d_eq
    (holomorphicDeRhamComplex X (dim X.left))
      ComplexShape.embeddingUpNat (i' := 0) (j' := 1)
      (i := 0) (j := 1) rfl rfl]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  rw [holomorphicDeRhamComplex_d]
  have h := constantToHolomorphicFunction_comp_differential_eq_zero
    X (dim X.left) f
  simpa only [Category.assoc, zero_comp] using congrArg
    (fun q ↦ q ≫ ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
      ComplexShape.embeddingUpNat (i := 1) rfl).inv) h

theorem constantToDeRhamZero_closed
    [IsIntegral X.left] [Smooth X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : constantIntegerSheaf X ⟶
      holomorphicAdditiveFunctionSheaf X (dim X.left)) :
    (f ≫ (deRhamDegreeZeroIsoFunctions X).inv) ≫
      (holomorphicDeRhamComplexInt X).d 0 1 = 0 := by
  change (f ≫ exponentialComparisonZero X) ≫
    (holomorphicDeRhamComplexInt X).d 0 1 = 0
  change (f ≫ holomorphicFunctionToZeroFormSheaf X (dim X.left) ≫
    ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).inv) ≫
      (holomorphicDeRhamComplexInt X).d 0 1 = 0
  exact constantToExtendedZeroForm_closed X f

/-- A compact global holomorphic function, viewed as a closed degree-zero de Rham map. -/
def compactFunctionToDeRhamSingle
    [IsIntegral X.left] [Smooth X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : constantIntegerSheaf X ⟶
      holomorphicAdditiveFunctionSheaf X (dim X.left)) :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (constantIntegerSheaf X) ⟶ holomorphicDeRhamComplexInt X :=
  HomologicalComplex.mkHomFromSingle
    (f ≫ (deRhamDegreeZeroIsoFunctions X).inv) (by
      intro k hk
      have hk' : k = 1 := by
        simpa [ComplexShape.up_Rel] using hk.symm
      subst k
      exact constantToDeRhamZero_closed X f)

/-- The closed lift, with the repository's actual integer constant complex as source. -/
def compactFunctionToDeRham
    [IsIntegral X.left] [Smooth X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : constantIntegerSheaf X ⟶
      holomorphicAdditiveFunctionSheaf X (dim X.left)) :
    constantIntegerSheafComplexInt X ⟶ holomorphicDeRhamComplexInt X :=
  (constantIntegerComplexIsoSingle X).hom ≫
    compactFunctionToDeRhamSingle X f

theorem compactFunctionToDeRham_comp_projection
    [IsIntegral X.left] [Smooth X.hom]
    [CompactSpace (ComplexPoint X)]
    (f : constantIntegerSheaf X ⟶
      holomorphicAdditiveFunctionSheaf X (dim X.left)) :
    compactFunctionToDeRham X f ≫ deRhamToHolomorphicFunctions X =
      (constantIntegerComplexIsoSingle X).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f := by
  unfold compactFunctionToDeRham
  have hinner : compactFunctionToDeRhamSingle X f ≫
      deRhamToHolomorphicFunctions X =
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, compactFunctionToDeRhamSingle,
      HomologicalComplex.mkHomFromSingle_f, deRhamToHolomorphicFunctions,
      CochainComplex.toDegreeZero_f_zero]
    erw [HomologicalComplex.single_map_f_self]
    erw [HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [Category.assoc, hinner]

theorem hypercohomologyMap_mk₀
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (f : constantIntegerSheafComplexInt X ⟶ K) (g : K ⟶ L) :
    hypercohomologyMap X g 0
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl f) =
      Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl (f ≫ g) := by
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  simp [hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk₀, ShiftedHom.mk₀_comp_mk₀,
    ← Functor.map_comp]

theorem sheafExtHypercohomologyEquiv_mk₀
    (F : AnalyticAdditiveSheaf X)
    (f : constantIntegerSheaf X ⟶ F) :
    sheafExtHypercohomologyEquiv X F 0 0 (Abelian.Ext.mk₀ f) =
      Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        ((constantIntegerComplexIsoSingle X).hom ≫
          (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f) := by
  rw [sheafExtHypercohomologyEquiv_zeroDegree]
  unfold Abelian.Ext.mk₀
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  simp [Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.mk₀_comp_mk₀, ← Functor.map_comp]

theorem deRhamToHolomorphicFunctions_surjective
    [IsIntegral X.left] [Smooth X.hom]
    [CompactSpace (ComplexPoint X)] :
    Function.Surjective
      (hypercohomologyMap X (deRhamToHolomorphicFunctions X) 0) := by
  intro α
  let e := sheafExtHypercohomologyEquiv X
    (holomorphicAdditiveFunctionSheaf X (dim X.left)) 0 0
  let ξ := e.symm α
  let f := Abelian.Ext.homEquiv₀ ξ
  refine ⟨Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
    (compactFunctionToDeRham X f), ?_⟩
  rw [hypercohomologyMap_mk₀]
  rw [compactFunctionToDeRham_comp_projection]
  rw [← sheafExtHypercohomologyEquiv_mk₀]
  change e (Abelian.Ext.mk₀ f) = α
  rw [show Abelian.Ext.mk₀ f = ξ from Abelian.Ext.mk₀_homEquiv₀_apply ξ]
  exact e.apply_symm_apply α

theorem injective_of_surjective_prev
    (S : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ)) (hS : S.ShortExact)
    (n : ℤ) (hsurj : Function.Surjective (hypercohomologyMap X S.g n)) :
    Function.Injective (hypercohomologyMap X S.f (n + 1)) := by
  intro a b hab
  apply sub_eq_zero.mp
  let x := a - b
  have hx : hypercohomologyMap X S.f (n + 1) x = 0 := by
    dsimp [x]
    rw [map_sub, hab, sub_self]
  let e (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (m : ℤ) :
      Hypercohomology X K m ≃ ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) m :=
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
  let F := preadditiveCoyoneda.obj
    (Opposite.op (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X)))
  let T := DerivedCategory.triangleOfSES hS
  have hexact := F.homologySequence_exact₁ T
    (DerivedCategory.triangleOfSES_distinguished hS) n (n + 1) (by omega)
  rw [ShortComplex.ab_exact_iff_function_exact] at hexact
  have hx' : e S.X₁ (n + 1) x ≫
      (DerivedCategory.Q.map S.f)⟦n + 1⟧' = 0 := by
    have h := congrArg (e S.X₂ (n + 1)) hx
    simpa [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero, ShiftedHom.comp_mk₀] using h
  obtain ⟨c, hc⟩ := (hexact (e S.X₁ (n + 1) x)).mp hx'
  obtain ⟨y, hy⟩ := hsurj ((e S.X₃ n).symm c)
  have hcmap : e S.X₂ n y ≫ (DerivedCategory.Q.map S.g)⟦n⟧' = c := by
    have hmap : e S.X₂ n y ≫ (DerivedCategory.Q.map S.g)⟦n⟧' =
        e S.X₃ n (hypercohomologyMap X S.g n y) := by
      simp [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
        ShiftedHom.comp_mk₀]
    exact hmap.trans ((congrArg (e S.X₃ n) hy).trans
      ((e S.X₃ n).apply_symm_apply c))
  have hdelta : F.homologySequenceδ T n (n + 1) (by omega) c = 0 := by
    rw [← hcmap]
    have hz := F.comp_homologySequenceδ T
      (DerivedCategory.triangleOfSES_distinguished hS) n (n + 1) (by omega)
    have hz' := congrArg ConcreteCategory.hom hz
    exact DFunLike.congr_fun hz' (e S.X₂ n y)
  have hc' : e S.X₁ (n + 1) x = 0 := by
    rw [← hc]
    exact hdelta
  have hezero : e S.X₁ (n + 1) 0 = 0 := by
    change (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q) 0 = 0
    exact hypercohomologyEquiv_zero X S.X₁ (n + 1)
  have hex : x = 0 := (e S.X₁ (n + 1)).injective (hc'.trans hezero.symm)
  exact hex

theorem firstHodgeFilteredToDeRham_injective
    [IsIntegral X.left] [Smooth X.hom]
    [CompactSpace (ComplexPoint X)] :
    Function.Injective (filteredToDeRhamCohomology X 1 1) := by
  change Function.Injective
    (hypercohomologyMap X (firstHodgeFiltrationSequence X).f (0 + 1))
  exact injective_of_surjective_prev X (firstHodgeFiltrationSequence X)
    (firstHodgeFiltrationSequence_shortExact X) 0
    (deRhamToHolomorphicFunctions_surjective X)

end AlgebraicGeometry.ComplexPoint
