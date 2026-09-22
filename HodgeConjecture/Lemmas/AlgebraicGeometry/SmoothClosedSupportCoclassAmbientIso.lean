/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentSmoothSupportCoclassSection
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAnalyticMaps

/-!
# Ambient-isomorphism naturality of normalized smooth-support coclasses

The normal-chart coclass is natural under an algebraic ambient isomorphism whose map on
complex points is presented as an open embedding.  The proof compares actual holomorphic
normal charts, then their literal neighborhood-support pairs, and finally glues by sheaf germs.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter TopologicalSpace AlgebraicGeometry
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (A X Y : Over (Spec (.of ℂ)))
  (f : A ⟶ X) (i : Y ⟶ A) (m d : ℕ)
  [SmoothOfRelativeDimension d A.hom]
  [SmoothOfRelativeDimension d X.hom]
  [SmoothOfRelativeDimension m Y.hom]
  [IsClosedImmersion i.left]
  [IsClosedImmersion (i ≫ f).left]
  [IsIso f]
  (hf : IsOpenEmbedding (Point.map f))
  (z : ComplexPoint Y)

noncomputable def ambientOpenNormalTransition :
    OpenPartialHomeomorph ((Fin m → ℂ) × (Fin (d - m) → ℂ))
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) := by
  letI : Nonempty (ComplexPoint A) := ⟨Point.map i z⟩
  exact (closedImmersionHolomorphicFlatteningChart A Y i m d z).symm.trans
    ((hf.toOpenPartialHomeomorph (Point.map f)).trans
      (closedImmersionHolomorphicFlatteningChart X Y (i ≫ f) m d z))

theorem analyticAt_ambientOpenNormalTransition
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (ambientOpenNormalTransition A X Y f i m d hf z).source) :
    AnalyticAt ℂ (ambientOpenNormalTransition A X Y f i m d hf z) v := by
  letI : Nonempty (ComplexPoint A) := ⟨Point.map i z⟩
  let e := closedImmersionHolomorphicFlatteningChart A Y i m d z
  let e' := closedImmersionHolomorphicFlatteningChart X Y (i ≫ f) m d z
  let F := hf.toOpenPartialHomeomorph (Point.map f)
  let C := localChart A d (Point.map i z)
  let C' := localChart X d (Point.map (i ≫ f) z)
  let N := closedImmersionNormalCoordinateChange A Y i m d z
  let N' := closedImmersionNormalCoordinateChange X Y (i ≫ f) m d z
  change v ∈ (e.symm.trans (F.trans e')).source at hv
  let y := e.symm v
  have hyv : y ∈ e.source := e.map_target hv.1
  have hyF : y ∈ F.source := hv.2.1
  have hyv' : Point.map f y ∈ e'.source := by
    have h := hv.2.2
    change F (e.symm v) ∈ e'.source at h
    simpa only [y, F, IsOpenEmbedding.toOpenPartialHomeomorph_apply] using h
  have hyC : y ∈ C.source := hyv.1.1
  have hyC' : Point.map f y ∈ C'.source := hyv'.1.1
  have hNv : N.symm (e y) = C y := by
    change N.symm (N (C y)) = C y
    exact N.left_inv hyv.1.2.1
  rw [e.right_inv hv.1] at hNv
  have hN : AnalyticAt ℂ N.symm (e y) := by
    exact ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff N (C y)).mp
      hyv.1.2).2.2
  rw [e.right_inv hv.1] at hN
  have hN' : AnalyticAt ℂ N' (C' (Point.map f y)) := by
    exact ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff
      N' (C' (Point.map f y))).mp hyv'.1.2).2.1
  have hCC : AnalyticAt ℂ (fun w ↦ C' (Point.map f (C.symm w))) (C y) := by
    apply analyticAt_localChart_symm_map A X f d d (Point.map i z)
    · exact C.map_source hyC
    · rw [C.left_inv hyC]
      simpa only [C', AlgebraicGeometry.Point.map_comp_apply] using hyC'
  have hCC' : AnalyticAt ℂ (fun w ↦ C' (Point.map f (C.symm w))) (N.symm v) := hNv ▸ hCC
  have hmiddle := hCC'.comp hN
  have himage : C' (Point.map f (C.symm (N.symm v))) = C' (Point.map f y) := by
    rw [hNv, C.left_inv hyC]
  have hlast : AnalyticAt ℂ N' (C' (Point.map f (C.symm (N.symm v)))) := himage ▸ hN'
  exact hlast.comp
    (f := fun w ↦ C' (Point.map f (C.symm (N.symm w)))) (x := v) hmiddle

theorem analyticAt_ambientOpenNormalTransition_symm
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (ambientOpenNormalTransition A X Y f i m d hf z).source) :
    AnalyticAt ℂ (ambientOpenNormalTransition A X Y f i m d hf z).symm
      (ambientOpenNormalTransition A X Y f i m d hf z v) := by
  letI : Nonempty (ComplexPoint A) := ⟨Point.map i z⟩
  let e := closedImmersionHolomorphicFlatteningChart A Y i m d z
  let e' := closedImmersionHolomorphicFlatteningChart X Y (i ≫ f) m d z
  let F := hf.toOpenPartialHomeomorph (Point.map f)
  let C := localChart A d (Point.map i z)
  let C' := localChart X d (Point.map (i ≫ f) z)
  let N := closedImmersionNormalCoordinateChange A Y i m d z
  let N' := closedImmersionNormalCoordinateChange X Y (i ≫ f) m d z
  let T := ambientOpenNormalTransition A X Y f i m d hf z
  change v ∈ (e.symm.trans (F.trans e')).source at hv
  let y := e.symm v
  have hyv : y ∈ e.source := e.map_target hv.1
  have hyv' : Point.map f y ∈ e'.source := by
    have h := hv.2.2
    change F (e.symm v) ∈ e'.source at h
    simpa only [y, F, IsOpenEmbedding.toOpenPartialHomeomorph_apply] using h
  have hyC : y ∈ C.source := hyv.1.1
  have hyC' : Point.map f y ∈ C'.source := hyv'.1.1
  have hTv : T v = e' (Point.map f y) := by
    rfl
  have hN'v : N'.symm (T v) = C' (Point.map f y) := by
    rw [hTv]
    change N'.symm (N' (C' (Point.map f y))) = C' (Point.map f y)
    exact N'.left_inv hyv'.1.2.1
  have hNinv' : AnalyticAt ℂ N'.symm (T v) := by
    rw [hTv]
    exact ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff
      N' (C' (Point.map f y))).mp hyv'.1.2).2.2
  have hcenter : Point.map (inv f) (Point.map (i ≫ f) z) = Point.map i z := by
    rw [AlgebraicGeometry.Point.map_comp_apply,
      ← AlgebraicGeometry.Point.map_comp_apply, IsIso.hom_inv_id,
      AlgebraicGeometry.Point.map_id]
  have hinv : Point.map (inv f) (Point.map f y) = y := by
    rw [← AlgebraicGeometry.Point.map_comp_apply, IsIso.hom_inv_id,
      AlgebraicGeometry.Point.map_id]
  have hCC : AnalyticAt ℂ
      (fun w ↦ C (Point.map (inv f) (C'.symm w))) (C' (Point.map f y)) := by
    have h := analyticAt_localChart_symm_map X A (inv f) d d
      (Point.map (i ≫ f) z) (C'.map_source hyC')
      (show Point.map (inv f) (C'.symm (C' (Point.map f y))) ∈
        (localChart A d (Point.map (inv f) (Point.map (i ≫ f) z))).source by
          rw [C'.left_inv hyC', hcenter, hinv]
          exact hyC)
    simpa only [C, C', hcenter] using h
  have hCC' : AnalyticAt ℂ
      (fun w ↦ C (Point.map (inv f) (C'.symm w))) (N'.symm (T v)) := hN'v ▸ hCC
  have hmiddle := hCC'.comp hNinv'
  have hN : AnalyticAt ℂ N (C y) := by
    exact ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff N (C y)).mp
      hyv.1.2).2.1
  have himage : C (Point.map (inv f) (C'.symm (N'.symm (T v)))) = C y := by
    rw [hN'v, C'.left_inv hyC', hinv]
  have hlast : AnalyticAt ℂ N
      (C (Point.map (inv f) (C'.symm (N'.symm (T v))))) := himage ▸ hN
  have ha := hlast.comp
    (f := fun w ↦ C (Point.map (inv f) (C'.symm (N'.symm w))))
    (x := T v) hmiddle
  apply ha.congr
  filter_upwards [T.open_target.mem_nhds (T.map_source (by
    change v ∈ (e.symm.trans (F.trans e')).source
    exact hv))] with w hw
  change w ∈ (e.symm.trans (F.trans e')).target at hw
  have hxF : e'.symm w ∈ F.target := hw.1.2
  have hxRange : e'.symm w ∈ Set.range (Point.map f) := by
    simpa only [F, IsOpenEmbedding.toOpenPartialHomeomorph_target] using hxF
  have hFinv : F.symm (e'.symm w) = Point.map (inv f) (e'.symm w) := by
    apply hf.injective
    rw [hf.toOpenPartialHomeomorph_right_inv (Point.map f) hxRange]
    rw [← AlgebraicGeometry.Point.map_comp_apply, IsIso.inv_hom_id,
      AlgebraicGeometry.Point.map_id]
  have he' : e'.symm w = C'.symm (N'.symm w) := rfl
  change N (C (Point.map (inv f) (C'.symm (N'.symm w)))) =
    N (C (F.symm (C'.symm (N'.symm w))))
  rw [← he', hFinv]

theorem ambientOpenNormalTransition_preserves_support
    (hB : Point.map f ⁻¹' Set.range (Point.map (i ≫ f)) = Set.range (Point.map i))
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (ambientOpenNormalTransition A X Y f i m d hf z).source) :
    ((ambientOpenNormalTransition A X Y f i m d hf z v).2 = 0 ↔ v.2 = 0) := by
  letI : Nonempty (ComplexPoint A) := ⟨Point.map i z⟩
  let e := closedImmersionHolomorphicFlatteningChart A Y i m d z
  let e' := closedImmersionHolomorphicFlatteningChart X Y (i ≫ f) m d z
  let F := hf.toOpenPartialHomeomorph (Point.map f)
  change v ∈ (e.symm.trans (F.trans e')).source at hv
  let y := e.symm v
  have hyv : y ∈ e.source := e.map_target hv.1
  have hyv' : Point.map f y ∈ e'.source := by
    have h := hv.2.2
    change F (e.symm v) ∈ e'.source at h
    simpa only [y, F, IsOpenEmbedding.toOpenPartialHomeomorph_apply] using h
  have he : e y = v := e.right_inv hv.1
  have he' : ambientOpenNormalTransition A X Y f i m d hf z v =
      e' (Point.map f y) := rfl
  rw [he',
    ← closedImmersionHolomorphicFlatteningChart_mem_range_iff
      X Y (i ≫ f) m d z (Point.map f y) hyv',
    show Point.map f y ∈ Set.range (Point.map (i ≫ f)) ↔
        y ∈ Set.range (Point.map i) by
      change y ∈ Point.map f ⁻¹' Set.range (Point.map (i ≫ f)) ↔ _
      rw [hB],
    closedImmersionHolomorphicFlatteningChart_mem_range_iff
      A Y i m d z y hyv,
    he]

noncomputable def ambientPullbackFlatteningChart [Nonempty (ComplexPoint A)] :
    OpenPartialHomeomorph (ComplexPoint A)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (hf.toOpenPartialHomeomorph (Point.map f)).trans
    (closedImmersionHolomorphicFlatteningChart X Y (i ≫ f) m d z)

theorem ambientPullbackFlatteningChart_mem_range_iff
    [Nonempty (ComplexPoint A)]
    (hB : Point.map f ⁻¹' Set.range (Point.map (i ≫ f)) = Set.range (Point.map i))
    (y : ComplexPoint A) (hy : y ∈ (ambientPullbackFlatteningChart A X Y f i m d hf z).source) :
    y ∈ Set.range (Point.map i) ↔
      ((ambientPullbackFlatteningChart A X Y f i m d hf z) y).2 = 0 := by
  rw [← hB]
  exact closedImmersionHolomorphicFlatteningChart_mem_range_iff
    X Y (i ≫ f) m d z (Point.map f y) hy.2

theorem ambientPullbackFlatteningChart_image_subset
    [Nonempty (ComplexPoint A)]
    (V : Opens (ComplexPoint A))
    (hV : (V : Set _) ⊆ (ambientPullbackFlatteningChart A X Y f i m d hf z).source) :
    Point.map f '' (V : Set _) ⊆
      (closedImmersionHolomorphicFlatteningChart X Y (i ≫ f) m d z).source := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (hV hy).2

set_option maxHeartbeats 800000 in
theorem supportRelativeCohomologyPresheafOpenIso_inv_app_pulledChartCoclass
    [Nonempty (ComplexPoint A)]
    (hB : Point.map f ⁻¹' Set.range (Point.map (i ≫ f)) = Set.range (Point.map i))
    (V : Opens (ComplexPoint A))
    (hV : (V : Set _) ⊆
      (ambientPullbackFlatteningChart A X Y f i m d hf z).source) :
    (supportRelativeCohomologyPresheafOpenIso
      (TopCat.ofHom (Point.continuousMap f)) hf
      (Set.range (Point.map (i ≫ f))) (Set.range (Point.map i)) hB
      (2 * (d - m))).inv.app (Opposite.op V)
      (chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
        (ambientPullbackFlatteningChart A X Y f i m d hf z)
        (Set.range (Point.map i))
        (ambientPullbackFlatteningChart_mem_range_iff A X Y f i m d hf z hB)
        V hV) =
      smoothClosedSupportChartCoclass X Y (i ≫ f) m d z
        (Point.map f '' (V : Set _))
        (ambientPullbackFlatteningChart_image_subset A X Y f i m d hf z V hV) := by
  change relativeCohomologyMap ℚ (2 * (d - m))
      (neighborhoodSupportPairImageIso (Point.map f) hf.isEmbedding
        (V : Set _) (Set.range (Point.map i)) (Set.range (Point.map (i ≫ f))) _).inv
      (chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
        (ambientPullbackFlatteningChart A X Y f i m d hf z)
        (Set.range (Point.map i)) _ V hV) = _
  unfold smoothClosedSupportChartCoclass chartNormalProjectionCoclass
  let E := neighborhoodSupportPairImageIso (Point.map f) hf.isEmbedding
    (V : Set _) (Set.range (Point.map i)) (Set.range (Point.map (i ≫ f)))
      (fun y _ ↦ by rw [← hB]; rfl)
  let P := E.inv
  let Q := chartNormalProjectionPair (Fin m → ℂ) (d - m)
    (ambientPullbackFlatteningChart A X Y f i m d hf z)
    (Set.range (Point.map i))
      (ambientPullbackFlatteningChart_mem_range_iff A X Y f i m d hf z hB) V hV
  let Q' := chartNormalProjectionPair (Fin m → ℂ) (d - m)
    (closedImmersionHolomorphicFlatteningChart X Y (i ≫ f) m d z)
    (Set.range (Point.map (i ≫ f)))
      (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y (i ≫ f) m d z)
      (Point.map f '' (V : Set _))
      (ambientPullbackFlatteningChart_image_subset A X Y f i m d hf z V hV)
  have hQ : Q = E.hom ≫ Q' := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  have hPQ : P ≫ Q = Q' := by
    rw [hQ, ← Category.assoc, E.inv_hom_id, Category.id_comp]
  change (relativeCohomologyMap ℚ (2 * (d - m)) P)
      ((relativeCohomologyMap ℚ (2 * (d - m)) Q) _) =
    (relativeCohomologyMap ℚ (2 * (d - m)) Q') _
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hPQ]

set_option maxHeartbeats 800000 in
theorem exists_open_smoothClosedSupportChartCoclass_eq_ambientOpenTransport
    [Nonempty (ComplexPoint A)]
    (hB : Point.map f ⁻¹' Set.range (Point.map (i ≫ f)) = Set.range (Point.map i)) :
    ∃ (W : Opens (ComplexPoint A))
      (hW : (W : Set _) ⊆
        (closedImmersionHolomorphicFlatteningChart A Y i m d z).source)
      (hW' : (W : Set _) ⊆
        (ambientPullbackFlatteningChart A X Y f i m d hf z).source),
      Point.map i z ∈ W ∧
      (supportRelativeCohomologyPresheafOpenIso
        (TopCat.ofHom (Point.continuousMap f)) hf
        (Set.range (Point.map (i ≫ f))) (Set.range (Point.map i)) hB
        (2 * (d - m))).inv.app (Opposite.op W)
        (smoothClosedSupportChartCoclass A Y i m d z W hW) =
      smoothClosedSupportChartCoclass X Y (i ≫ f) m d z
        (Point.map f '' (W : Set _))
        (ambientPullbackFlatteningChart_image_subset A X Y f i m d hf z W hW') := by
  letI : Nonempty (ComplexPoint A) := ⟨Point.map i z⟩
  let e := closedImmersionHolomorphicFlatteningChart A Y i m d z
  let e' := ambientPullbackFlatteningChart A X Y f i m d hf z
  have hz : Point.map i z ∈ e.source :=
    mem_smoothClosedSupportChartOpen A Y i m d z
  have hzf : Point.map f (Point.map i z) ∈
      (closedImmersionHolomorphicFlatteningChart X Y (i ≫ f) m d z).source := by
    rw [← AlgebraicGeometry.Point.map_comp_apply]
    exact mem_smoothClosedSupportChartOpen X Y (i ≫ f) m d z
  have hz' : Point.map i z ∈ e'.source := ⟨Set.mem_univ _, hzf⟩
  have ht : e (Point.map i z) ∈
      (ambientOpenNormalTransition A X Y f i m d hf z).source := by
    refine ⟨e.map_source hz, ?_⟩
    change e.symm (e (Point.map i z)) ∈ e'.source
    rwa [e.left_inv hz]
  obtain ⟨W, hW, hW', hzW, heq⟩ :=
    exists_open_chartNormalProjectionCoclass_eq (d - m) e e'
      (Set.range (Point.map i))
      (closedImmersionHolomorphicFlatteningChart_mem_range_iff A Y i m d z)
      (ambientPullbackFlatteningChart_mem_range_iff A X Y f i m d hf z hB)
      (Point.map i z) hz
      ((closedImmersionHolomorphicFlatteningChart_mem_range_iff
        A Y i m d z (Point.map i z) hz).mp ⟨z, rfl⟩)
      hz'
      (analyticAt_ambientOpenNormalTransition A X Y f i m d hf z (e (Point.map i z)) ht)
      (analyticAt_ambientOpenNormalTransition_symm A X Y f i m d hf z
        (e (Point.map i z)) ht)
  refine ⟨W, hW, hW', hzW, ?_⟩
  have heq' := congrArg
    ((supportRelativeCohomologyPresheafOpenIso
      (TopCat.ofHom (Point.continuousMap f)) hf
      (Set.range (Point.map (i ≫ f))) (Set.range (Point.map i)) hB
      (2 * (d - m))).inv.app (Opposite.op W)) heq
  rw [supportRelativeCohomologyPresheafOpenIso_inv_app_pulledChartCoclass
    A X Y f i m d hf z hB W hW'] at heq'
  exact heq'

set_option maxHeartbeats 800000 in
theorem smoothClosedSupportCoclassSection_restrict_chart_subset
    (W : Opens (ComplexPoint A))
    (hW : W ≤ smoothClosedSupportChartOpen A Y i m d z) :
    (smoothClosedSupportCoclassSheaf A Y i m d).obj.map
      (homOfLE (show W ≤ ⊤ from le_top)).op
      (smoothClosedSupportCoclassSection A Y i m d) =
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint A))
      (Set.range (Point.map i)) (2 * (d - m))).app (Opposite.op W)
      (smoothClosedSupportChartCoclass A Y i m d z W hW) := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf A Y i m d)
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  change (smoothClosedSupportCoclassSheaf A Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection A Y i m d) = _
  rw [smoothClosedSupportCoclassSection_germ_eq_chart A Y i m d z x (hW hx)]
  unfold smoothClosedSupportChartCoclassGerm
  change supportRelativeCohomologyGerm (TopCat.of (ComplexPoint A))
      (Set.range (Point.map i)) (2 * (d - m))
      (smoothClosedSupportChartOpen A Y i m d z) x (hW hx)
      (smoothClosedSupportChartCoclass A Y i m d z
        (smoothClosedSupportChartOpen A Y i m d z) (le_refl _)) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint A))
      (Set.range (Point.map i)) (2 * (d - m)) W x hx
      (smoothClosedSupportChartCoclass A Y i m d z W hW)
  rw [← smoothClosedSupportChartCoclass_restrict A Y i m d z hW (le_refl _)]
  exact (supportRelativeCohomologyGerm_restrict
    (TopCat.of (ComplexPoint A)) (Set.range (Point.map i)) (2 * (d - m))
    hW x hx _).symm

theorem smoothClosedSupportCoclassSection_restrict_eq_zero_of_disjoint
    (W : Opens (ComplexPoint A))
    (hW : ∀ x ∈ W, x ∉ Set.range (Point.map i)) :
    (smoothClosedSupportCoclassSheaf A Y i m d).obj.map
      (homOfLE (show W ≤ ⊤ from le_top)).op
      (smoothClosedSupportCoclassSection A Y i m d) = 0 := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf A Y i m d)
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply, map_zero]
  change (smoothClosedSupportCoclassSheaf A Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection A Y i m d) = 0
  exact smoothClosedSupportCoclassSection_germ_eq_zero A Y i m d x (hW x hx)

noncomputable def ambientAlgebraicMapOpenFunctor :
    CategoryTheory.Functor (Opens (ComplexPoint A)) (Opens (ComplexPoint X)) :=
  @Topology.IsOpenEmbedding.functor
    (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint X))
    (TopCat.ofHom (Point.continuousMap f)) hf

set_option maxHeartbeats 1600000 in
theorem smoothClosedSupportCoclassSection_ambientIso
    [Nonempty (ComplexPoint A)]
    (hB : Point.map f ⁻¹' Set.range (Point.map (i ≫ f)) = Set.range (Point.map i))
    (hTop : (ambientAlgebraicMapOpenFunctor A X f hf).obj (⊤ : Opens (ComplexPoint A)) =
      (⊤ : Opens (ComplexPoint X))) :
    supportRelativeCohomologySectionOnOpen
        (TopCat.ofHom (Point.continuousMap f)) hf
        (Set.range (Point.map (i ≫ f))) (Set.range (Point.map i)) hB
        (2 * (d - m)) ⊤ hTop
        (smoothClosedSupportCoclassSection A Y i m d) =
      smoothClosedSupportCoclassSection X Y (i ≫ f) m d := by
  let s := supportRelativeCohomologySectionOnOpen
    (TopCat.ofHom (Point.continuousMap f)) hf
    (Set.range (Point.map (i ≫ f))) (Set.range (Point.map i)) hB
    (2 * (d - m)) ⊤ hTop
    (smoothClosedSupportCoclassSection A Y i m d)
  apply smoothClosedSupportCoclassSection_unique_of_normalization X Y (i ≫ f) m d s
  · intro z'
    letI : Nonempty (ComplexPoint A) := ⟨Point.map i z'⟩
    obtain ⟨W, hW, hW', hzW, heq⟩ :=
      exists_open_smoothClosedSupportChartCoclass_eq_ambientOpenTransport
        A X Y f i m d hf z' hB
    have hxW : Point.map (i ≫ f) z' ∈
        (ambientAlgebraicMapOpenFunctor A X f hf).obj W := by
      refine ⟨Point.map i z', hzW, ?_⟩
      rfl
    have himage : ((ambientAlgebraicMapOpenFunctor A X f hf).obj W :
        Set (ComplexPoint X)) ⊆
        (smoothClosedSupportChartOpen X Y (i ≫ f) m d z' : Set _) :=
      ambientPullbackFlatteningChart_image_subset A X Y f i m d hf z' W hW'
    have haux := smoothClosedSupportCoclassSection_restrict_chart_subset
      A Y i m d z' W hW
    have hsres := supportRelativeCohomologySectionOnOpen_restrict
      (TopCat.ofHom (Point.continuousMap f)) hf
      (Set.range (Point.map (i ≫ f))) (Set.range (Point.map i)) hB
      (2 * (d - m)) ⊤ hTop
      (smoothClosedSupportCoclassSection A Y i m d) W le_top
    rw [haux] at hsres
    have hunit := supportRelativeCohomologySheafOpenIso_unit_apply
      (TopCat.ofHom (Point.continuousMap f)) hf
      (Set.range (Point.map (i ≫ f))) (Set.range (Point.map i)) hB
      (2 * (d - m)) W
      (smoothClosedSupportChartCoclass A Y i m d z' W hW)
    rw [hunit] at hsres
    rw [heq] at hsres
    have hsres' :
        (supportRelativeCohomologySheaf (TopCat.of (Point ℂ X))
          (Set.range (Point.map (i ≫ f))) (2 * (d - m))).obj.map
          (homOfLE (show (ambientAlgebraicMapOpenFunctor A X f hf).obj W ≤
            (⊤ : Opens (ComplexPoint X)) from le_top)).op s =
        (supportRelativeCohomologyToSheaf (TopCat.of (Point ℂ X))
          (Set.range (Point.map (i ≫ f))) (2 * (d - m))).app
          (Opposite.op ((ambientAlgebraicMapOpenFunctor A X f hf).obj W))
          (smoothClosedSupportChartCoclass X Y (i ≫ f) m d z'
            ((ambientAlgebraicMapOpenFunctor A X f hf).obj W) himage) := by
      dsimp only [s, ambientAlgebraicMapOpenFunctor]
      convert hsres using 1 <;> rfl
    change (smoothClosedSupportCoclassSheaf X Y (i ≫ f) m d).presheaf.germ ⊤
        (Point.map (i ≫ f) z') _ s = _
    rw [← (smoothClosedSupportCoclassSheaf X Y (i ≫ f) m d).presheaf.germ_res_apply
      (homOfLE (show (ambientAlgebraicMapOpenFunctor A X f hf).obj W ≤
        (⊤ : Opens (ComplexPoint X)) from le_top))
      (Point.map (i ≫ f) z') hxW s]
    change (supportRelativeCohomologySheaf (TopCat.of (Point ℂ X))
        (Set.range (Point.map (i ≫ f))) (2 * (d - m))).presheaf.germ
      ((ambientAlgebraicMapOpenFunctor A X f hf).obj W)
      (Point.map (i ≫ f) z') hxW
      ((supportRelativeCohomologySheaf (TopCat.of (Point ℂ X))
        (Set.range (Point.map (i ≫ f))) (2 * (d - m))).obj.map
        (homOfLE (show (ambientAlgebraicMapOpenFunctor A X f hf).obj W ≤
          (⊤ : Opens (ComplexPoint X)) from le_top)).op s) = _
    rw [hsres']
    unfold smoothClosedSupportChartCoclassGerm
    change supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (Set.range (Point.map (i ≫ f))) (2 * (d - m))
        ((ambientAlgebraicMapOpenFunctor A X f hf).obj W)
        (Point.map (i ≫ f) z') hxW
        (smoothClosedSupportChartCoclass X Y (i ≫ f) m d z'
          ((ambientAlgebraicMapOpenFunctor A X f hf).obj W) himage) = _
    rw [← smoothClosedSupportChartCoclass_restrict X Y (i ≫ f) m d z'
      himage (le_refl _)]
    exact supportRelativeCohomologyGerm_restrict
      (TopCat.of (ComplexPoint X)) (Set.range (Point.map (i ≫ f)))
      (2 * (d - m)) himage (Point.map (i ≫ f) z') hxW _
  · intro x hxS
    let y : ComplexPoint A := Point.map (inv f) x
    have hfy : Point.map f y = x := by
      rw [← AlgebraicGeometry.Point.map_comp_apply, IsIso.inv_hom_id,
        AlgebraicGeometry.Point.map_id]
    have hyB : y ∉ Set.range (Point.map i) := by
      intro hy
      apply hxS
      have : Point.map f y ∈ Set.range (Point.map (i ≫ f)) := by
        change y ∈ Point.map f ⁻¹' Set.range (Point.map (i ≫ f))
        rwa [hB]
      rwa [hfy] at this
    let U : Opens (ComplexPoint A) :=
      ⟨(Set.range (Point.map i))ᶜ,
        (isClosed_range_map_of_closedImmersion i).isOpen_compl⟩
    have hyU : y ∈ U := hyB
    have hxU : x ∈ (ambientAlgebraicMapOpenFunctor A X f hf).obj U :=
      ⟨y, hyU, hfy⟩
    have haux := smoothClosedSupportCoclassSection_restrict_eq_zero_of_disjoint
      A Y i m d U (fun _ hu ↦ hu)
    have hsres := supportRelativeCohomologySectionOnOpen_restrict
      (TopCat.ofHom (Point.continuousMap f)) hf
      (Set.range (Point.map (i ≫ f))) (Set.range (Point.map i)) hB
      (2 * (d - m)) ⊤ hTop
      (smoothClosedSupportCoclassSection A Y i m d) U le_top
    rw [haux, map_zero] at hsres
    have hsres' :
        (supportRelativeCohomologySheaf (TopCat.of (Point ℂ X))
          (Set.range (Point.map (i ≫ f))) (2 * (d - m))).obj.map
          (homOfLE (show (ambientAlgebraicMapOpenFunctor A X f hf).obj U ≤
            (⊤ : Opens (ComplexPoint X)) from le_top)).op s = 0 := by
      dsimp only [s, ambientAlgebraicMapOpenFunctor]
      convert hsres using 1 <;> rfl
    change (smoothClosedSupportCoclassSheaf X Y (i ≫ f) m d).presheaf.germ
      ⊤ x _ s = 0
    rw [← (smoothClosedSupportCoclassSheaf X Y (i ≫ f) m d).presheaf.germ_res_apply
      (homOfLE (show (ambientAlgebraicMapOpenFunctor A X f hf).obj U ≤
        (⊤ : Opens (ComplexPoint X)) from le_top))
      x hxU s]
    change (supportRelativeCohomologySheaf (TopCat.of (Point ℂ X))
        (Set.range (Point.map (i ≫ f))) (2 * (d - m))).presheaf.germ
      ((ambientAlgebraicMapOpenFunctor A X f hf).obj U) x hxU
      ((supportRelativeCohomologySheaf (TopCat.of (Point ℂ X))
        (Set.range (Point.map (i ≫ f))) (2 * (d - m))).obj.map
        (homOfLE (show (ambientAlgebraicMapOpenFunctor A X f hf).obj U ≤
          (⊤ : Opens (ComplexPoint X)) from le_top)).op s) = 0
    rw [hsres', map_zero]

end AlgebraicGeometry.ComplexPoint
