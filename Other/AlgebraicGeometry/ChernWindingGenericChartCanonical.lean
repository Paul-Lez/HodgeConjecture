/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingGenericChartConditional
public import Other.AlgebraicGeometry.CartierWindingChartUnit
public import Other.AlgebraicGeometry.ClosedImmersion.HolomorphicChartsAnalytic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothClosedLift

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology Opposite Order AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace AlgebraicGeometry.ComplexPoint

attribute [local instance] isNoetherian_of_isProjective

def castNormalChart {M : Type} [TopologicalSpace M] {k c c' : ℕ}
    (h : c = c')
    (e : OpenPartialHomeomorph M ((Fin k → ℂ) × (Fin c → ℂ))) :
    OpenPartialHomeomorph M ((Fin k → ℂ) × (Fin c' → ℂ)) :=
  Eq.mp (congrArg (fun n ↦ OpenPartialHomeomorph M
    ((Fin k → ℂ) × (Fin n → ℂ))) h) e

theorem castNormalChart_source {M : Type} [TopologicalSpace M] {k c c' : ℕ}
    (h : c = c')
    (e : OpenPartialHomeomorph M ((Fin k → ℂ) × (Fin c → ℂ))) :
    (castNormalChart h e).source = e.source := by
  subst c'
  rfl

theorem castNormalChart_openEmbeddingTransport
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [Nonempty M]
    {k c c' : ℕ} (f : M → N) (hf : IsOpenEmbedding f)
    (h : c = c') (e : OpenPartialHomeomorph M ((Fin k → ℂ) × (Fin c → ℂ))) :
    castNormalChart h (openEmbeddingTransportChart f hf (Fin k → ℂ) c e) =
      openEmbeddingTransportChart f hf (Fin k → ℂ) c'
        (castNormalChart h e) := by
  subst c'
  rfl

theorem analyticOnNhd_castNormalChart_restrict
    {M : Type} [TopologicalSpace M] {k c c' : ℕ}
    (h : c = c') (e : OpenPartialHomeomorph M ((Fin k → ℂ) × (Fin c → ℂ)))
    (A : Set M) (hA : IsOpen A) {f : M → ℂ}
    (hf : AnalyticOnNhd ℂ (fun v ↦ f ((e.restrOpen A hA).symm v))
      (e.restrOpen A hA).target) :
    AnalyticOnNhd ℂ
      (fun v ↦ f (((castNormalChart h e).restrOpen A hA).symm v))
      ((castNormalChart h e).restrOpen A hA).target := by
  subst c'
  exact hf

theorem fderiv_ne_zero_castNormalChart
    {M : Type} [TopologicalSpace M] {k c c' : ℕ}
    (h : c = c') (e : OpenPartialHomeomorph M ((Fin k → ℂ) × (Fin c → ℂ)))
    (p : M) {f : M → ℂ}
    (hf : fderiv ℂ (fun v ↦ f (e.symm v)) (e p) ≠ 0) :
    fderiv ℂ (fun v ↦ f ((castNormalChart h e).symm v))
      ((castNormalChart h e) p) ≠ 0 := by
  subst c'
  exact hf

theorem analyticOnNhd_openEmbeddingTransportChart_restrict_evaluate
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens)
    (Y : Over (Spec ↧ℂ)) (j : Y ⟶ ComplexPoint.openScheme X U)
    (m d : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [SmoothOfRelativeDimension d (ComplexPoint.openScheme X U).hom]
    [IsClosedImmersion j.left] (z : ComplexPoint Y)
    [Nonempty (ComplexPoint (ComplexPoint.openScheme X U))]
    (V : X.left.Opens) (s : Γ(X.left, V))
    (A : Set (ComplexPoint X)) (hA : IsOpen A)
    (hAV : A ⊆ Point.overOpen V) :
    AnalyticOnNhd ℂ
      (fun v ↦ Point.evaluate V s
        (((openEmbeddingTransportChart
          (Point.map (ComplexPoint.openInclusion X U))
          (isOpenEmbedding_map_open X U) (Fin m → ℂ) (d - m)
          (closedImmersionHolomorphicFlatteningChart
            (ComplexPoint.openScheme X U) Y j m d z)).restrOpen A hA).symm v))
      ((openEmbeddingTransportChart
        (Point.map (ComplexPoint.openInclusion X U))
        (isOpenEmbedding_map_open X U) (Fin m → ℂ) (d - m)
        (closedImmersionHolomorphicFlatteningChart
          (ComplexPoint.openScheme X U) Y j m d z)).restrOpen A hA).target := by
  let M := ComplexPoint.openScheme X U
  let e := closedImmersionHolomorphicFlatteningChart M Y j m d z
  let f := Point.map (ComplexPoint.openInclusion X U)
  let hf := isOpenEmbedding_map_open X U
  let r := ComplexPoint.openInclusion X U
  let t := openEmbeddingTransportChart f hf (Fin m → ℂ) (d - m) e
  let eA := t.restrOpen A hA
  intro v hv
  have hvT : v ∈ t.target := by
    change v ∈ t.target ∩ _ at hv
    exact hv.1
  have hvA : eA.symm v ∈ eA.source := eA.map_target hv
  have hyA : eA.symm v ∈ A := by
    rw [OpenPartialHomeomorph.restrOpen_source] at hvA
    exact hvA.2
  have hvE : v ∈ e.target := by
    change v ∈ e.target ∩ _ at hvT
    exact hvT.1
  have hyE : e.symm v ∈ e.source := e.symm.map_source hvE
  have hyMap : f (e.symm v) = eA.symm v := by
    have ht : t.symm v = f (e.symm v) := by
      change (e.symm.trans (hf.toOpenPartialHomeomorph f)) v = _
      rw [OpenPartialHomeomorph.trans_apply]
      rfl
    rw [← ht]
    change t.symm v = _
    rfl
  have hV : e.symm v ∈ Point.overOpen (r.left ⁻¹ᵁ V) := by
    rw [← Point.mem_overOpen_map_iff r (e.symm v) V]
    change f (e.symm v) ∈ Point.overOpen V
    rw [hyMap]
    exact hAV hyA
  have hV' : e.symm (e (e.symm v)) ∈ Point.overOpen (r.left ⁻¹ᵁ V) := by
    rw [e.left_inv hyE]
    exact hV
  have hat' := analyticAt_closedImmersionHolomorphicFlatteningChart_evaluate
    M Y j m d z (r.left ⁻¹ᵁ V) (r.left.app V s) (e.symm v) hyE hV'
  have hat : AnalyticAt ℂ
      (fun w ↦ Point.evaluate (r.left ⁻¹ᵁ V) (r.left.app V s) (e.symm w)) v := by
    change AnalyticAt ℂ
      (fun w ↦ Point.evaluate (r.left ⁻¹ᵁ V) (r.left.app V s) (e.symm w))
      (e (e.symm v)) at hat'
    simpa only [e.right_inv hvE] using hat'
  have heq : (fun w ↦ Point.evaluate V s (eA.symm w)) =ᶠ[𝓝 v]
      (fun w ↦ Point.evaluate (r.left ⁻¹ᵁ V) (r.left.app V s) (e.symm w)) := by
    filter_upwards [eA.open_target.mem_nhds hv] with w hw
    have hwT : w ∈ t.target := by
      change w ∈ t.target ∩ _ at hw
      exact hw.1
    have hwE : w ∈ e.target := by
      change w ∈ e.target ∩ _ at hwT
      exact hwT.1
    have hweq : t.symm w = f (e.symm w) := by
      change (e.symm.trans (hf.toOpenPartialHomeomorph f)) w = _
      rw [OpenPartialHomeomorph.trans_apply]
      rfl
    change Point.evaluate V s (t.symm w) = _
    rw [hweq]
    exact Point.evaluate_map r V s (e.symm w)
  exact hat.congr heq.symm



set_option maxHeartbeats 1000000 in
/-- A canonical transported flattening chart can be restricted to an arbitrary analytic
neighbourhood while retaining the holomorphic provenance needed by the normal-division step. -/
theorem exists_genericWindingChartData_of_component_canonical
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c : Scheme.CartierData X.left) (x : X.left)
    (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (i : c.ι) (localForm : c.LocalForm i x)
    (z : ComplexPoint (cycleComponentSmoothLocusOver X x))
    (q : ComplexPoint X)
    (hq : q = Point.map (ComplexPoint.openInclusion X
      (cycleComponentSmoothLocusAmbientOpen X x))
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z))
    (N : Opens (ComplexPoint X)) (hqN : q ∈ N)
    (hN : N ≤ analyticOpen X localForm.opens)
    (hambient :
      let M := cycleComponentSmoothLocusAmbientOpenOver X x
      let r := ComplexPoint.openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)
      let j := cycleComponentSmoothLocusClosedLiftOver X x
      fderiv ℂ (fun w ↦ Point.evaluate (r.left ⁻¹ᵁ localForm.opens)
          (r.left.app localForm.opens localForm.equation)
          ((localChart M (dim X.left) (Point.map j z)).symm w))
        (localChart M (dim X.left) (Point.map j z) (Point.map j z)) ≠ 0) :
    ∃ G : GenericWindingChartData X c x (dim X.left) q,
      G.toChart.carrier ≤ N := by
  subst q
  let M := cycleComponentSmoothLocusAmbientOpenOver X x
  let r := ComplexPoint.openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)
  let j := cycleComponentSmoothLocusClosedLiftOver X x
  let D := dim X.left
  let q0 := (cycleComponentSmoothClosedLiftAmbientMap X x) (Point.map j z)
  have hcod0 : dim X.left - (dim X.left - 1) = 1 :=
    cycleComponentSmoothClosedLift_codimension X x hx
  have hcod : D - (D - 1) = 1 := by simpa [D] using hcod0
  let : SmoothOfRelativeDimension (D - 1) (cycleComponentSmoothLocusOver X x).hom :=
    cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have hambient' : fderiv ℂ (fun w ↦ Point.evaluate (r.left ⁻¹ᵁ localForm.opens)
      (r.left.app localForm.opens localForm.equation)
      ((localChart M D (Point.map j z)).symm w))
      (localChart M D (Point.map j z) (Point.map j z)) ≠ 0 := by
    simpa [M, r, j] using hambient
  let e0 := closedImmersionHolomorphicFlatteningChart M
    (cycleComponentSmoothLocusOver X x) j (D - 1) D z
  let e : OpenPartialHomeomorph (ComplexPoint M)
      ((Fin (D - 1) → ℂ) × (Fin 1 → ℂ)) := castNormalChart hcod e0
  let : Nonempty (ComplexPoint M) := ⟨Point.map j z⟩
  let f := cycleComponentSmoothClosedLiftAmbientMap X x
  let hf := cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x
  let t0 := openEmbeddingTransportChart f hf (Fin (D - 1) → ℂ) (D - (D - 1)) e0
  have hmem0 : q0 ∈ t0.source := by
    apply mem_openEmbeddingTransportChart_source f hf (Fin (D - 1) → ℂ)
      (D - (D - 1)) e0
    exact closedImmersionHolomorphicFlatteningChart_mem_source
      M (cycleComponentSmoothLocusOver X x) j (D - 1) D z
  let T0 : TransportedFlatteningChart M (cycleComponentSmoothLocusOver X x) j
      (D - 1) f hf (cycleComponentSupport X x)
      (cycleComponentSmoothClosedLiftAmbientMap_support X x)
      (cycleComponentSmoothSupportAmbientOpen X x)
      (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x) q0 (D - (D - 1))
      (smoothClosedSupportCoclassSection M (cycleComponentSmoothLocusOver X x)
        j (D - 1) D) := {
    chart := t0
    mem_source := hmem0
    flattens := openEmbeddingTransportChart_mem_support_iff f hf
      (Fin (D - 1) → ℂ) (D - (D - 1)) e0 _ (cycleComponentSupport X x)
      (cycleComponentSmoothClosedLiftAmbientMap_support X x)
      (closedImmersionHolomorphicFlatteningChart_mem_range_iff
        M (cycleComponentSmoothLocusOver X x) j (D - 1) D z)
    center := by
      rw [openEmbeddingTransportChart_apply]
      exact congrArg Prod.snd
        (closedImmersionHolomorphicFlatteningChart_center
          M (cycleComponentSmoothLocusOver X x) j (D - 1) D z)
    le := flattenedSupportNeighborhood_openEmbeddingTransportChart_le f hf
      (Fin (D - 1) → ℂ) (D - (D - 1)) e0 (cycleComponentSmoothSupportAmbientOpen X x)
      (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x) q0 hmem0
    coclass_restrict := supportRelativeCohomologySectionOnOpen_restrict_flattened f hf
      (cycleComponentSupport X x) _
      (cycleComponentSmoothClosedLiftAmbientMap_support X x)
      (Fin (D - 1) → ℂ) (D - (D - 1)) e0
      (closedImmersionHolomorphicFlatteningChart_mem_range_iff
        M (cycleComponentSmoothLocusOver X x) j (D - 1) D z)
      (cycleComponentSmoothSupportAmbientOpen X x)
      (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
      (smoothClosedSupportCoclassSection M (cycleComponentSmoothLocusOver X x)
        j (D - 1) D)
      (smoothClosedSupportCoclassSection_restrict_chart
        M (cycleComponentSmoothLocusOver X x) j (D - 1) D z) _ hmem0 }
  let Section (cc : ℕ) :=
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint M))
      (Set.range (Point.map j)) (2 * cc)).obj.obj (op ⊤)
  let R (cc : ℕ) :=
    Σ s : Section cc,
      TransportedFlatteningChart M (cycleComponentSmoothLocusOver X x) j
        (D - 1) f hf (cycleComponentSupport X x)
        (cycleComponentSmoothClosedLiftAmbientMap_support X x)
        (cycleComponentSmoothSupportAmbientOpen X x)
        (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x) q0 cc s
  let p0 : R (D - (D - 1)) :=
    ⟨smoothClosedSupportCoclassSection M (cycleComponentSmoothLocusOver X x)
      j (D - 1) D, T0⟩
  have hcast_chart : ∀ {cc cc' : ℕ} (hcc : cc = cc') (pp : R cc),
      (Eq.mp (congrArg R hcc) pp).2.chart =
        castNormalChart hcc pp.2.chart := by
    intro cc cc' hcc pp
    subst cc'
    rfl
  have hcast_section : ∀ {cc cc' : ℕ} (hcc : cc = cc') (pp : R cc),
      (Eq.mp (congrArg R hcc) pp).1 =
        Eq.mp (congrArg (fun cc => (Section cc : Type)) hcc) pp.1 := by
    intro cc cc' hcc pp
    subst cc'
    rfl
  let p1 : R 1 := Eq.mp (congrArg R hcod) p0
  let T := p1.2
  let t := openEmbeddingTransportChart f hf (Fin (D - 1) → ℂ) 1 e
  have hmem : q0 ∈ t.source := by
    have he_source : e.source = e0.source := castNormalChart_source hcod e0
    have hs : t.source = t0.source := by
      rw [openEmbeddingTransportChart_source, openEmbeddingTransportChart_source,
        he_source]
    rw [hs]
    exact hmem0
  have hTchart : T.chart = t := by
    have h := hcast_chart hcod p0
    calc
      T.chart = castNormalChart hcod t0 := by simpa [T, p1] using h
      _ = t := by
        rw [castNormalChart_openEmbeddingTransport]

  let F0 : FlatteningChartWithCoclass X x D q0 := {
    chart := T.chart
    mem_source := by
      simpa [q0, f] using T.mem_source
    flattens := by simpa [q0, r, j, cycleComponentSmoothClosedLiftAmbientMap] using T.flattens
    center := by simpa [q0, f] using T.center
    le := T.le
    coclass_restrict := fun _ => by
      have hp1 : p1.1 = hcod ▸
          (show Section (D - (D - 1)) from
            smoothClosedSupportCoclassSection M (cycleComponentSmoothLocusOver X x) j
              (D - 1) D) := by
        rw [hcast_section hcod p0]
        dsimp [p0, Section]
        let sm : Section (D - (D - 1)) :=
          smoothClosedSupportCoclassSection M (cycleComponentSmoothLocusOver X x) j
            (D - 1) D
        have hrec : HEq (hcod ▸ sm) sm :=
          eqRec_heq (φ := fun cc => (Section cc : Type)) hcod sm
        have hcast : HEq
            (cast (congrArg (fun cc => (Section cc : Type)) hcod) sm) sm :=
          cast_heq _ _
        simpa [sm] using eq_of_heq (hcast.trans hrec.symm)
      have hsection :
          (hcod ▸ (show Section (D - (D - 1)) from
            smoothClosedSupportCoclassSection M
              (cycleComponentSmoothLocusOver X x) j (D - 1) D)) =
            cycleComponentSmoothClosedLiftCoclassSection X x hx := by
        have hcod' : hcod = cycleComponentSmoothClosedLift_codimension X x hx := by
            apply Subsingleton.elim
        rw [hcod']
        rfl
      unfold cycleComponentSmoothSupportCoclassSection
      rw [← hsection, ← hp1]
      simpa [cycleComponentSmoothSupportCoclassSection,
        cycleComponentSmoothClosedLiftCoclassSection] using T.coclass_restrict }
  let V : Opens (ComplexPoint X) :=
    N ⊓ analyticOpen X localForm.opens ⊓ F0.flattened
  have hqV : q0 ∈ V := by
    exact ⟨⟨hqN, hN hqN⟩, mem_flattenedSupportNeighborhood _ _ _ _ _⟩
  let F := F0.restrict V hqV
  have hV : V ≤ analyticOpen X localForm.opens :=
    (inf_le_left : V ≤ N ⊓ analyticOpen X localForm.opens).trans inf_le_right
  have hF : F.flattened ≤ analyticOpen X localForm.opens := by
    exact (F0.restrict_flattened_le V hqV).trans hV
  let A : Set (ComplexPoint X) := (V ⊓ F0.flattened : Opens (ComplexPoint X))
  have hA : IsOpen A := (V ⊓ F0.flattened).isOpen
  have hAV : A ⊆ Point.overOpen localForm.opens := by
    intro y hy
    have hyV : y ∈ V := hy.1
    have hyOpen : y ∈ analyticOpen X localForm.opens := hV hyV
    change Point.underlying y ∈ localForm.opens
    exact hyOpen
  have hFchart : F.chart = t.restrOpen A hA := by
    change F0.restrictChart V = t.restrOpen A hA
    change T.chart.restrOpen (V ⊓ F0.flattened : Set (ComplexPoint X)) _ = _
    rw [hTchart]
    rfl
  have hfan : AnalyticOnNhd ℂ
      (fun v ↦ Point.evaluate localForm.opens localForm.equation (F.chart.symm v))
      F.chart.target := by
    have han := analyticOnNhd_openEmbeddingTransportChart_restrict_evaluate X
      (cycleComponentSmoothLocusAmbientOpen X x)
      (cycleComponentSmoothLocusOver X x) j (D - 1) D z
      localForm.opens localForm.equation A hA hAV
    rw [hFchart]
    have han0 : AnalyticOnNhd ℂ
        (fun v ↦ Point.evaluate localForm.opens localForm.equation
          ((t0.restrOpen A hA).symm v)) (t0.restrOpen A hA).target := han
    have hcast := analyticOnNhd_castNormalChart_restrict hcod t0 A hA han0
    simpa only [t0, t, e, castNormalChart_openEmbeddingTransport] using hcast
  have hzero : ∀ v ∈ F.chart.target,
      v.2 = 0 → Point.evaluate localForm.opens localForm.equation
        (F.chart.symm v) = 0 := by
    intro v hv hv0
    have hy : F.chart.symm v ∈ F.chart.source := F.chart.map_target hv
    have hyA : F.chart.symm v ∈ A := by
      change (F0.restrictChart V).symm v ∈ (F0.restrictChart V).source at hy
      rw [F0.restrictChart_source] at hy
      exact hy.2
    have hyV : F.chart.symm v ∈ V := hyA.1
    have hyOpen : F.chart.symm v ∈ Point.overOpen localForm.opens := by
      change Point.underlying (F.chart.symm v) ∈ localForm.opens
      exact hV hyV
    have hyS : F.chart.symm v ∈ cycleComponentSupport X x := by
      apply (F.flattens (F.chart.symm v) (F.chart.map_target hv)).mpr
      simpa only [F.chart.right_inv hv] using hv0
    have hyClosure : Point.underlying (F.chart.symm v) ∈ closure ({x} : Set X.left) := hyS
    have hnot : Point.underlying (F.chart.symm v) ∉
        X.left.basicOpen localForm.equation :=
      localForm.notMem_basicOpen _ hyClosure
    have hnotne : ¬ Point.evaluate localForm.opens localForm.equation
        (F.chart.symm v) ≠ 0 := by
      intro hne
      apply hnot
      exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
        localForm.equation (F.chart.symm v) hyOpen).mpr hne
    exact not_not.mp hnotne

  have hbasic : F.flattened ⊓ (cycleComponentAnalyticClosedSupport X x).compl ≤
      analyticOpen X (X.left.basicOpen localForm.equation) := by
    intro y hy
    have hyU : Point.underlying y ∈ localForm.opens := hF hy.1
    by_contra hyb
    apply hy.2
    change Point.underlying y ∈ closure ({x} : Set X.left)
    exact localForm.mem_closure_of_notMem_basicOpen _ hyU hyb
  let coord : (holomorphicUnitSheaf X D).obj.obj
      (op (F.flattened ⊓ (cycleComponentAnalyticClosedSupport X x).compl)) :=
    (holomorphicUnitSheaf X D).obj.map (homOfLE hbasic).op
      (analyticUnitHom (X := X) (d := D) (X.left.basicOpen localForm.equation)
        (Additive.ofMul localForm.equationUnit))
  have hcoord : ((Additive.toMul coord).val :
      (holomorphicRingSheaf X D).obj.obj
      (op (F.flattened ⊓ (cycleComponentAnalyticClosedSupport X x).compl))) =
      (holomorphicRingSheaf X D).obj.map
        (homOfLE (inf_le_left.trans hF)).op
        (analyticFunction X D localForm.opens localForm.equation) := by
    change (holomorphicRingSheaf X D).obj.map (homOfLE hbasic).op
        (analyticFunction X D (X.left.basicOpen localForm.equation)
          localForm.equationUnit) = _
    rw [localForm.equationUnit_val, analyticFunction_res]
    rfl
  have hEval : ∀ w : ChernWinding.puncturedSpace
      ((F.flattened : Set (ComplexPoint X))) (cycleComponentSupport X x),
      windingUnitFunction X D F.flattened
        (cycleComponentAnalyticClosedSupport X x) coord w =
      Point.evaluate localForm.opens localForm.equation
        (ChernWinding.flattenedPuncturedInclusion
          (S := cycleComponentSupport X x) (Fin (D - 1) → ℂ) F.chart q0
            F.mem_source w) := by
    intro w
    change (unitOf coord).val (windingPuncturedMap X F.flattened
      (cycleComponentAnalyticClosedSupport X x) w) = _
    rw [show coord = (holomorphicUnitSheaf X D).obj.map (homOfLE hbasic).op
        (analyticUnitHom (X := X) (d := D)
          (X.left.basicOpen localForm.equation)
          (Additive.ofMul localForm.equationUnit)) from rfl]
    rw [unitOf_sres_val]
    let y : ComplexPoint X :=
      (ChernWinding.flattenedPuncturedInclusion
        (S := cycleComponentSupport X x) (Fin (D - 1) → ℂ) F.chart q0
          F.mem_source w)
    have hy : y ∈ F.flattened ⊓
        (cycleComponentAnalyticClosedSupport X x).compl := by
      have hyflat : y ∈ F.flattened := by
        change y ∈ (flattenedSupportNeighborhood (Fin (D - 1) → ℂ) 1
          F.chart q0 F.mem_source : Set (ComplexPoint X))
        exact (ChernWinding.flattenedPuncturedInclusion
          (S := cycleComponentSupport X x) (Fin (D - 1) → ℂ) F.chart q0
            F.mem_source w).property
      have hyS : y ∈ (cycleComponentSupport X x).compl := by
        change (w.1.1 : ComplexPoint X) ∉ cycleComponentSupport X x
        exact w.2
      exact ⟨hyflat, hyS⟩
    let y' : (analyticOpen X (X.left.basicOpen localForm.equation) :
        Set (ComplexPoint X)) := ⟨y, hbasic hy⟩
    change (unitSection (unitOf (analyticUnitHom (X := X) (d := D)
        (X.left.basicOpen localForm.equation)
        (Additive.ofMul localForm.equationUnit)))).val y' = _
    rw [analyticUnitHom_val]
    rw [localForm.equationUnit_val, analyticFunction_res]
    rfl

  have hy0source : Point.map j z ∈ e0.source := by
    exact closedImmersionHolomorphicFlatteningChart_mem_source
      M (cycleComponentSmoothLocusOver X x) j (D - 1) D z
  have hy0V : Point.map j z ∈ Point.overOpen (r.left ⁻¹ᵁ localForm.opens) := by
    rw [← Point.mem_overOpen_map_iff r (Point.map j z) localForm.opens]
    change q0 ∈ Point.overOpen localForm.opens
    change Point.underlying q0 ∈ localForm.opens
    exact hN hqN
  have hV0 : e0.symm (e0 (Point.map j z)) ∈
      Point.overOpen (r.left ⁻¹ᵁ localForm.opens) := by
    rw [e0.left_inv hy0source]
    exact hy0V
  have hcanonical := fderiv_closedImmersionHolomorphicFlatteningChart_evaluate_ne_zero
    M (cycleComponentSmoothLocusOver X x) j (D - 1) D z
    (r.left ⁻¹ᵁ localForm.opens) (r.left.app localForm.opens localForm.equation)
    (Point.map j z) hy0source hV0 hambient'
  have hqchart : F.chart q0 = e (Point.map j z) := by
    rw [hFchart]
    change t q0 = _
    rw [openEmbeddingTransportChart_apply]
  have heqderiv :
      (fun v ↦ Point.evaluate localForm.opens localForm.equation
        (F.chart.symm v)) =ᶠ[𝓝 (e (Point.map j z))]
      (fun v ↦ Point.evaluate (r.left ⁻¹ᵁ localForm.opens)
        (r.left.app localForm.opens localForm.equation) (e.symm v)) := by
    rw [hFchart]
    have htarget : e (Point.map j z) ∈ F.chart.target := by
      rw [← hqchart]
      exact F.chart.map_source F.mem_source
    have htarget' : e (Point.map j z) ∈ (t.restrOpen A hA).target := by
      simpa [hFchart] using htarget
    filter_upwards [(t.restrOpen A hA).open_target.mem_nhds htarget'] with v hv
    change v ∈ t.target ∩ _ at hv
    have hvT : v ∈ t.target := hv.1
    have hvE : v ∈ e.target := by
      change v ∈ e.target ∩ _ at hvT
      exact hvT.1
    have htv : t.symm v = f (e.symm v) := by
      change (e.symm.trans (hf.toOpenPartialHomeomorph f)) v = _
      rw [OpenPartialHomeomorph.trans_apply]
      rfl
    change Point.evaluate localForm.opens localForm.equation (t.symm v) = _
    rw [htv]
    exact Point.evaluate_map r localForm.opens localForm.equation (e.symm v)
  have hfd : fderiv ℂ
      (fun v ↦ Point.evaluate localForm.opens localForm.equation (F.chart.symm v))
      (F.chart q0) ≠ 0 := by
    have hfd' : fderiv ℂ
        (fun v ↦ Point.evaluate localForm.opens localForm.equation (F.chart.symm v))
        (e (Point.map j z)) ≠ 0 := by
      rw [heqderiv.fderiv_eq]
      exact fderiv_ne_zero_castNormalChart hcod e0 (Point.map j z) hcanonical
    simpa only [hqchart] using hfd'

  obtain ⟨G, hG⟩ := F.exists_genericWindingChartData_of_fderiv_ne_zero
    (c := c) i localForm hF coord hcoord hfan hzero hfd hEval
  refine ⟨G, hG.trans ?_⟩
  exact (F0.restrict_flattened_le V hqV).trans
    (inf_le_left.trans inf_le_left)

end AlgebraicGeometry.ComplexPoint
