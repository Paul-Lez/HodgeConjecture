/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingGenericChartAssembly
public import Other.Analysis.Complex.NormalDerivative
public import Other.Analysis.Complex.NormalDivisionChart

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Order AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingGenericChartConditionalTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}
variable (c : Scheme.CartierData X.left) (x : X.left) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

namespace FlatteningChartWithCoclass

variable {x d} {q : ComplexPoint X}

set_option maxHeartbeats 1000000 in
theorem exists_genericWindingChartData_of_fderiv_ne_zero
    (F : FlatteningChartWithCoclass X x d q)
    (i : c.ι) (localForm : c.LocalForm i x)
    (hV : F.flattened ≤ analyticOpen X localForm.opens)
    (coord : (holomorphicUnitSheaf X d).obj.obj
      (op (F.flattened ⊓ (cycleComponentAnalyticClosedSupport X x).compl)))
    (hcoord : ((Additive.toMul coord).val :
        (holomorphicRingSheaf X d).obj.obj
          (op (F.flattened ⊓ (cycleComponentAnalyticClosedSupport X x).compl))) =
      (holomorphicRingSheaf X d).obj.map
        (homOfLE (inf_le_left.trans hV)).op
        (analyticFunction X d localForm.opens localForm.equation))
    {f : ComplexPoint X → ℂ}
    (hf : AnalyticOnNhd ℂ (fun v ↦ f (F.chart.symm v)) F.chart.target)
    (hzero : ∀ v ∈ F.chart.target, v.2 = 0 → f (F.chart.symm v) = 0)
    (hfd : fderiv ℂ (fun v ↦ f (F.chart.symm v)) (F.chart q) ≠ 0)
    (hEval : ∀ w : ChernWinding.puncturedSpace
        ((F.flattened : Set (ComplexPoint X))) (cycleComponentSupport X x),
        windingUnitFunction X d F.flattened
          (cycleComponentAnalyticClosedSupport X x) coord w =
        f (ChernWinding.flattenedPuncturedInclusion
          (S := cycleComponentSupport X x) (Fin (d - 1) → ℂ) F.chart q F.mem_source w)) :
    Nonempty (GenericWindingChartData X c x d q) := by
  obtain ⟨U, hUn, hUopen, hUsub, e', hq', he'sub, he'source, he'apply, he'U, u, hu, hfactor⟩ :=
    Complex.exists_restricted_normalDivision_chart F.chart F.mem_source F.center hf hzero
      (by
        have hpoint : ((F.chart q).1, 0) = F.chart q := Prod.ext rfl F.center.symm
        have htupletarget : ((F.chart q).1, 0) ∈ F.chart.target := by
          rw [hpoint]
          exact F.chart.map_source F.mem_source
        have hn := Complex.normal_deriv_ne_zero_of_fderiv_ne_zero F.chart.open_target
          hzero hf htupletarget (by
            rw [hpoint]
            exact hfd)
        rw [hpoint] at hn
        exact hn)
  let Vsmall : Opens (ComplexPoint X) :=
    F.flattened ⊓ ⟨F.chart.source ∩ F.chart ⁻¹' U,
      F.chart.isOpen_inter_preimage hUopen⟩
  have hqU : F.chart q ∈ U := mem_of_mem_nhds hUn
  have hqsmall : q ∈ Vsmall := by
    exact ⟨mem_flattenedSupportNeighborhood _ _ _ _ _, F.mem_source, hqU⟩
  let Fsmall := F.restrict Vsmall hqsmall
  have hWsmall : Fsmall.flattened ≤ F.flattened := by
    exact F.flattened_restrictChart_le Vsmall hqsmall
  have hVsmall : Vsmall ≤ analyticOpen X localForm.opens :=
    (inf_le_left : Vsmall ≤ F.flattened).trans hV
  have hFsmall_analytic : Fsmall.flattened ≤ analyticOpen X localForm.opens :=
    hWsmall.trans hV
  have hFsmall_source : (Fsmall.chart.source : Set (ComplexPoint X)) ⊆ e'.source := by
    intro y hy
    have hyV : y ∈ Vsmall := F.restrict_chart_source_subset Vsmall hqsmall hy
    have hyChart : y ∈ F.chart.source := hyV.2.1
    have hyA : y ∈ e'.source := by
      rw [he'source]
      exact ⟨hyChart, hyV.2.2⟩
    exact hyA
  let hP : Fsmall.flattened ⊓ (cycleComponentAnalyticClosedSupport X x).compl ≤
      F.flattened ⊓ (cycleComponentAnalyticClosedSupport X x).compl :=
    inf_le_inf hWsmall le_rfl
  let coordSmall := (holomorphicUnitSheaf X d).obj.map (homOfLE hP).op coord
  have hcoordSmall : ((Additive.toMul coordSmall).val :
      (holomorphicRingSheaf X d).obj.obj
        (op (Fsmall.flattened ⊓ (cycleComponentAnalyticClosedSupport X x).compl))) =
      (holomorphicRingSheaf X d).obj.map
        (homOfLE (inf_le_left.trans hFsmall_analytic)).op
        (analyticFunction X d localForm.opens localForm.equation) := by
    change (holomorphicRingSheaf X d).obj.map (homOfLE hP).op
        ((Additive.toMul coord).val) = _
    rw [hcoord, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 1
  have hflat_source : (Fsmall.flattened : Set (ComplexPoint X)) ⊆ e'.source := by
    intro y hy
    exact hFsmall_source (flattenedSupportNeighborhood_subset_source _ _ _ _ _ hy)
  let inclusion : C((Fsmall.flattened : Set (ComplexPoint X)), e'.source) :=
    ⟨fun y ↦ ⟨(y : ComplexPoint X), hflat_source y.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let normalUnit : C((Fsmall.flattened : Set (ComplexPoint X)), ℂ) := u.comp inclusion
  have normalUnit_ne_zero : ∀ y, normalUnit y ≠ 0 := by
    intro y
    exact hu _
  have hfactorSmall : ∀ w : ChernWinding.puncturedSpace
      ((Fsmall.flattened : Set (ComplexPoint X))) (cycleComponentSupport X x),
        windingUnitFunction X d Fsmall.flattened
          (cycleComponentAnalyticClosedSupport X x) coordSmall w =
        normalUnit (ChernWinding.flattenedPuncturedInclusion
          (S := cycleComponentSupport X x) (Fin (d - 1) → ℂ) Fsmall.chart q
            Fsmall.mem_source w) *
          ChernWinding.complexLineCoordinate
            ((ChernWinding.flattenedNormalProjection (Fin (d - 1) → ℂ)
              Fsmall.chart (cycleComponentSupport X x) Fsmall.flattens q Fsmall.mem_source).left w) := by
    intro w
    let w0 : ChernWinding.puncturedSpace
        ((F.flattened : Set (ComplexPoint X))) (cycleComponentSupport X x) :=
      ⟨⟨(w.1.1 : ComplexPoint X), hWsmall w.1.2⟩, w.2⟩
    have hunit : windingUnitFunction X d Fsmall.flattened
        (cycleComponentAnalyticClosedSupport X x) coordSmall w =
        windingUnitFunction X d F.flattened
          (cycleComponentAnalyticClosedSupport X x) coord w0 := by
      change (unitOf coordSmall).val _ = (unitOf coord).val _
      rw [unitOf_sres_val hP coord]
      rfl
    have heval := hEval w0
    have hwsource : (w.1.1 : ComplexPoint X) ∈ e'.source := hflat_source w.1.2
    have hfac := hfactor ⟨(w.1.1 : ComplexPoint X), hwsource⟩
    have heq : e' (w.1.1 : ComplexPoint X) = Fsmall.chart (w.1.1 : ComplexPoint X) := by
      calc
        e' (w.1.1 : ComplexPoint X) = F.chart (w.1.1 : ComplexPoint X) :=
          he'apply _ hwsource
        _ = Fsmall.chart (w.1.1 : ComplexPoint X) := by rfl
    rw [hunit, heval]
    change f (w.1.1 : ComplexPoint X) = _ at hfac
    rw [heq] at hfac
    change f (w.1.1 : ComplexPoint X) = _
    rw [hfac]
    rw [mul_comm]
    have hnu : normalUnit (ChernWinding.flattenedPuncturedInclusion
        (S := cycleComponentSupport X x) (Fin (d - 1) → ℂ) Fsmall.chart q
          Fsmall.mem_source w) = u ⟨(w.1.1 : ComplexPoint X), hwsource⟩ := by
      change u (inclusion ⟨(w.1.1 : ComplexPoint X), w.1.2⟩) = _
      congr 1
    have hline : ChernWinding.complexLineCoordinate
        ((ChernWinding.flattenedNormalProjection (Fin (d - 1) → ℂ)
          Fsmall.chart (cycleComponentSupport X x) Fsmall.flattens q Fsmall.mem_source).left w) =
        (Fsmall.chart (w.1.1 : ComplexPoint X)).2 0 := by
      rfl
    rw [hnu, hline]
  exact ⟨toGenericWindingChartData c F Vsmall hqsmall i localForm hVsmall
    (by simpa [Fsmall, restrictedFlattened] using coordSmall)
    (by simpa [Fsmall, restrictedFlattened] using hcoordSmall)
    (by simpa [Fsmall, restrictedFlattened] using normalUnit)
    (by simpa [Fsmall, restrictedFlattened] using normalUnit_ne_zero)
    (by simpa [Fsmall, restrictedFlattened] using hfactorSmall)⟩

end FlatteningChartWithCoclass

end AlgebraicGeometry.ComplexPoint
