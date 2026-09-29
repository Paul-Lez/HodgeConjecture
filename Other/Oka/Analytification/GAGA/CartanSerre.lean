/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.CohomologyModule
public import Other.Oka.AnalyticSpace.LocalFreeResolution
public import Other.Oka.Analytification.GAGA.RationalBox
public import Other.Oka.Topology.Sheaves.SectionModelCech

/-!
# Cartan–Serre finiteness in degree one on `ℙⁿ_an`

For every coherent sheaf of modules `M` on `ℙⁿ_an`, the cohomology `H¹(ℙⁿ_an, M)` is a
finite-dimensional `ℂ`-vector space
(`ComplexAnalytic.projectiveSpaceAn.finiteDimensional_H_one`).

## Proof

1. *Models.* Every point has a neighbourhood `N` with generators and generated relations of `M`
   valid on every open inside `N` on which `𝒪` is acyclic (local free resolutions and dimension
   shifting, `ComplexAnalytic.exists_generatorData`); finitely many such `N` cover `ℙⁿ_an`. The
   images of rational boxes under the standard charts lying in one of these `N` form a countable
   basis `Q` of the topology, and `M(Q) ≃ 𝒪(box)^I / ker` is a Fréchet space
   (`ComplexAnalytic.GeneratorData.ModelSpace`). Restrictions between them are continuous, and
   compact between nested boxes of the same chart (Montel). This is a
   `TopCat.Sheaf.SectionModel` of `M` (`ComplexAnalytic.projectiveSpaceAn.sectionModel`).
2. *Covers.* By compactness there are finite covers `U`, `V` by such boxes with `V i` of compact
   closure in `U i`. `M` is acyclic on all of them (Theorem B), so both compute `H¹` by Čech
   cocycles (`TopCat.Sheaf.cechToH`), compatibly with refinement.
3. *Schwartz.* `TopCat.Sheaf.SectionModel.finiteDimensional_of_cech`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology Set

namespace ComplexAnalytic

namespace projectiveSpaceAn

noncomputable section

variable {n : ℕ} (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
  [M.IsCoherent]

/-- Every point of `ℙⁿ_an` lies in the domain of some generator data of a coherent `M`. -/
lemma exists_generatorData_mem (x : projectiveSpaceAn.{u} n) :
    ∃ D : GeneratorData M, x ∈ D.N := by
  obtain ⟨U, hx, h⟩ := exists_hasFreeResolutionLE_projectiveSpaceAn n M x
  obtain ⟨D, hD⟩ := exists_generatorData M U h
  exact ⟨D, hD ▸ hx⟩

/-- A choice of generator data around each point. -/
def genData (x : projectiveSpaceAn.{u} n) : GeneratorData M :=
  (exists_generatorData_mem M x).choose

lemma mem_genData (x : projectiveSpaceAn.{u} n) : x ∈ (genData M x).N :=
  (exists_generatorData_mem M x).choose_spec

lemma exists_finset_genData :
    ∃ t : Finset (projectiveSpaceAn.{u} n), ∀ x, ∃ y ∈ t, x ∈ (genData M y).N := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : projectiveSpaceAn.{u} n ↦ ((genData M x).N : Set (projectiveSpaceAn.{u} n)))
    (fun x ↦ (genData M x).N.isOpen) (fun x _ ↦ mem_iUnion.2 ⟨x, mem_genData M x⟩)
  exact ⟨t, fun x ↦ by simpa using ht (mem_univ x)⟩

/-- Finitely many points whose generator data cover `ℙⁿ_an`. -/
def genPts : Finset (projectiveSpaceAn.{u} n) := (exists_finset_genData M).choose

lemma exists_mem_genPts (x : projectiveSpaceAn.{u} n) :
    ∃ y ∈ genPts M, x ∈ (genData M y).N :=
  (exists_finset_genData M).choose_spec x

/-- The index type of the model opens: a chart, one of the chosen generator data, and a rational
box whose image under the chart lies in the domain of the generator data. -/
def Idx : Type u :=
  {q : Fin (n + 1) × genPts M × (ULift.{u} (Fin n) → ℚ × ℚ) × (ULift.{u} (Fin n) → ℚ × ℚ) //
    chartOpen (projectiveSpaceAnChart.{u} q.1) (Complex.ratBox q.2.2.1 q.2.2.2) ≤
      (genData M q.2.1.1).N}

instance : Countable (Idx M) := by
  unfold Idx
  infer_instance

variable {M}

/-- The chart of a model index. -/
abbrev Idx.chart (q : Idx M) : AnalyticSpace.complexAffineSpace.{u} n ⟶ projectiveSpaceAn.{u} n :=
  projectiveSpaceAnChart.{u} q.1.1

/-- The box of a model index. -/
abbrev Idx.box (q : Idx M) : Opens (ULift.{u} (Fin n) → ℂ) := Complex.ratBox q.1.2.2.1 q.1.2.2.2

/-- The generator data of a model index. -/
abbrev Idx.data (q : Idx M) : GeneratorData M := genData M q.1.2.1.1

/-- The model open of a model index: the image of its box under its chart. -/
abbrev Idx.opens (q : Idx M) : Opens (projectiveSpaceAn.{u} n).toPresheafedSpace :=
  chartOpen q.chart q.box

lemma Idx.acyclic (q : Idx M) : StructureAcyclic q.opens :=
  structureAcyclic_chartOpen_ratBox _ _ _

variable (M) in
/-- The model space of a model index. -/
abbrev Model (q : Idx M) : Type u := q.data.ModelSpace q.chart q.2 q.acyclic

/-- The image of the closure of a box under a chart contains the closure of the image. -/
lemma closure_chartOpen_subset {c : Fin (n + 1)} {B B' : Opens (ULift.{u} (Fin n) → ℂ)}
    (hc : IsCompact (closure (B' : Set (ULift.{u} (Fin n) → ℂ))))
    (hcl : closure (B' : Set (ULift.{u} (Fin n) → ℂ)) ⊆ B) :
    closure (chartOpen (projectiveSpaceAnChart.{u} c) B' : Set (projectiveSpaceAn.{u} n)) ⊆
      chartOpen (projectiveSpaceAnChart.{u} c) B := by
  have hK := hc.image (projectiveSpaceAnChart.{u} c).toLRSHom.base.hom.continuous
  refine (closure_minimal (image_mono subset_closure) hK.isClosed).trans ?_
  exact image_mono hcl

variable (M) in
/-- **Model opens form a basis with compact shrinkings**: every point `x` of an open `W` lies in the
image `Q'` of a rational box `B'` under a chart, with `B'` of compact closure inside a rational
box `B` whose image `Q ⊆ W` lies in the domain of one of the chosen generator data. -/
theorem exists_pair (W : Opens (projectiveSpaceAn.{u} n).toPresheafedSpace)
    {x : projectiveSpaceAn.{u} n} (hx : x ∈ W) :
    ∃ (c : Fin (n + 1)) (k : genPts M) (a b a' b' : ULift.{u} (Fin n) → ℚ × ℚ)
      (_ : chartOpen (projectiveSpaceAnChart.{u} c) (Complex.ratBox a b) ≤ (genData M k.1).N)
      (_ : chartOpen (projectiveSpaceAnChart.{u} c) (Complex.ratBox a' b') ≤ (genData M k.1).N),
      x ∈ chartOpen (projectiveSpaceAnChart.{u} c) (Complex.ratBox a' b') ∧
      chartOpen (projectiveSpaceAnChart.{u} c) (Complex.ratBox a b) ≤ W ∧
      Complex.ratBox a' b' ≤ Complex.ratBox a b ∧
      IsCompact (closure (Complex.ratBox a' b' : Set (ULift.{u} (Fin n) → ℂ))) ∧
      closure (Complex.ratBox a' b' : Set (ULift.{u} (Fin n) → ℂ)) ⊆ Complex.ratBox a b ∧
      closure (chartOpen (projectiveSpaceAnChart.{u} c) (Complex.ratBox a' b') :
        Set (projectiveSpaceAn.{u} n)) ⊆ chartOpen (projectiveSpaceAnChart.{u} c)
          (Complex.ratBox a b) := by
  obtain ⟨k, hk, hxk⟩ := exists_mem_genPts M x
  obtain ⟨c, z, rfl⟩ := exists_mem_range_chart x
  let O : Set (ULift.{u} (Fin n) → ℂ) := (projectiveSpaceAnChart.{u} c).toLRSHom.base ⁻¹'
    ((W : Set (projectiveSpaceAn.{u} n)) ∩ (genData M k).N)
  have hO : IsOpen O := (W.isOpen.inter (genData M k).N.isOpen).preimage
    (projectiveSpaceAnChart.{u} c).toLRSHom.base.hom.continuous
  obtain ⟨a, b, a', b', hz, hc, hcl, hsub⟩ := Complex.exists_ratBox_subset hO ⟨hx, hxk⟩
  have hB' : Complex.ratBox a' b' ≤ Complex.ratBox a b := subset_closure.trans hcl
  have hq : chartOpen (projectiveSpaceAnChart.{u} c) (Complex.ratBox a b) ≤ (genData M k).N := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hsub hw).2
  refine ⟨c, ⟨k, hk⟩, a, b, a', b', hq, (chartOpen_mono hB').trans hq, ⟨z, hz, rfl⟩, ?_, hB',
    hc, hcl, closure_chartOpen_subset hc hcl⟩
  rintro _ ⟨w, hw, rfl⟩
  exact (hsub hw).1

variable (M) in
/-- The endomorphism "multiplication by the constant `c`" of the underlying abelian sheaf. -/
abbrev smulHom (c : ℂ) : M.toAb ⟶ M.toAb :=
  (LocallyRingedSpace.modulesToAb _).map
    (LocallyRingedSpace.modulesSMul M ((projectiveSpaceAn.{u} n).algebraMap c))

variable (M) in
/-- **The Fréchet section model of a coherent sheaf on `ℙⁿ_an`**: model opens are the images of
rational boxes under the standard charts inside the domain of one of the chosen generator data,
with model spaces `𝒪(box)^I / ker`. -/
def sectionModel : TopCat.Sheaf.SectionModel M.toAb (Model M) where
  Q q := q.opens
  ε q := q.data.ε q.chart q.2 q.acyclic
  smulHom := smulHom M
  ε_smul q c x := q.data.ε_smul q.chart q.2 q.acyclic c x
  continuous_res q q' h := q.data.continuous_modelRes q'.data q'.2 q'.acyclic h
  exists_mem_le W x hx := by
    obtain ⟨c, k, a, b, a', b', hq, hq', hx', hqW, -, -, -, hcl⟩ := exists_pair M W hx
    exact ⟨⟨(c, k, a', b'), hq'⟩, hx', fun y hy ↦ hqW (hcl (subset_closure hy))⟩

variable (M) in
/-- **Compact restrictions**: every point of every open `W` lies in a model open `Q q'` with
`Q q' ≤ Q q ≤ W` and compact restriction `M(Q q) → M(Q q')` (Montel). -/
theorem exists_isCompactOperator_resL (W : Opens (projectiveSpaceAn.{u} n).toPresheafedSpace)
    (x : projectiveSpaceAn.{u} n) (hx : x ∈ W) :
    ∃ (q q' : Idx M) (h : (sectionModel M).Q q' ≤ (sectionModel M).Q q),
      x ∈ (sectionModel M).Q q' ∧ (sectionModel M).Q q ≤ W ∧
        IsCompactOperator ((sectionModel M).resL q q' h) := by
  obtain ⟨c, k, a, b, a', b', hq, hq', hx', hqW, hB', hc, hcl, -⟩ := exists_pair M W hx
  exact ⟨⟨(c, k, a, b), hq⟩, ⟨(c, k, a', b'), hq'⟩, chartOpen_mono hB', hx', hqW,
    (genData M k.1).isCompactOperator_modelRes _ hq (structureAcyclic_chartOpen_ratBox _ _ _) hB'
      hc hcl hq' (structureAcyclic_chartOpen_ratBox _ _ _)⟩

variable (M) in
/-- **Finite covers by model opens with relatively compact shrinkings.** -/
theorem exists_covers : ∃ (ι : Type u) (_ : Finite ι) (qU qV : ι → Idx M),
    (∀ i, (qV i).opens ≤ (qU i).opens) ∧ (⨆ i, (qV i).opens = ⊤) ∧
      ∀ i, closure ((qV i).opens : Set (projectiveSpaceAn.{u} n)) ⊆ (qU i).opens := by
  choose c k a b a' b' hq hq' hx _hW hB' _hc _hcl' hcl using fun x : projectiveSpaceAn.{u} n ↦
    exists_pair M ⊤ (x := x) trivial
  let qU : projectiveSpaceAn.{u} n → Idx M := fun x ↦ ⟨(c x, k x, a x, b x), hq x⟩
  let qV : projectiveSpaceAn.{u} n → Idx M := fun x ↦ ⟨(c x, k x, a' x, b' x), hq' x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ ((qV x).opens : Set (projectiveSpaceAn.{u} n))) (fun x ↦ (qV x).opens.isOpen)
    (fun x _ ↦ mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨t, inferInstance, fun i ↦ qU i.1, fun i ↦ qV i.1, fun i ↦ chartOpen_mono (hB' i.1),
    ?_, fun i ↦ hcl i.1⟩
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨x, hxt, hy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  exact Opens.mem_iSup.2 ⟨⟨x, hxt⟩, hy⟩

/-- `M` is acyclic in degree one on model opens (Theorem B). -/
lemma H_one_eq_zero (q : Idx M)
    (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen q.opens).obj M.toAb) 1) : x = 0 :=
  @Subsingleton.elim _ (q.data.acyclic q.opens q.2 q.acyclic 1 one_pos) x 0

variable (M) in
open TopCat.Presheaf TopCat.Sheaf in
/-- **Cartan–Serre finiteness in degree one on `ℙⁿ_an`**: for a coherent sheaf of modules `M` on
`ℙⁿ_an`, `H¹(ℙⁿ_an, M)` is a finite-dimensional `ℂ`-vector space. -/
theorem finiteDimensional_H_one : FiniteDimensional ℂ (LocallyRingedSpace.H M 1) := by
  obtain ⟨ι, _, qU, qV, hVU, hVcov, hcl⟩ := exists_covers M
  let U := fun i ↦ (qU i).opens
  let V := fun i ↦ (qV i).opens
  have hVU' : ∀ i, V i ≤ U i := hVU
  have hV : ⨆ i, V i = ⊤ := hVcov
  have hU : ⨆ i, U i = ⊤ := eq_top_iff.2 (hV.ge.trans (iSup_mono hVU'))
  -- the comparison map on cocycles of `V`
  let κ : (cechD V M.toAb.obj 1).ker →+ LocallyRingedSpace.H M 1 :=
    { toFun z := cechToH hV M.toAb z.1 z.2
      map_zero' := (cechToH_eq_zero_iff hV M.toAb _).2 ⟨0, map_zero _⟩
      map_add' z z' := (cechToH_congr hV M.toAb rfl _ _).trans
        (cechToH_add hV M.toAb z.2 z'.2) }
  refine (sectionModel M).finiteDimensional_of_cech (exists_isCompactOperator_resL M)
    (U := U) (V := V) hVU' (fun i ↦ isClosed_closure.isCompact) hcl ?_ κ ?_ ?_ ?_
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := cechToH_surjective hU M.toAb (fun i ↦ H_one_eq_zero (qU i))
      (cechToH hV M.toAb w hw)
    have hr := cechToH_cechRefine hU hV hVU' M.toAb hz
    set r := cechRefine U (τ := id) hVU' M.toAb.obj 1 z with hrdef
    have hr' : cechD V M.toAb.obj 1 r = 0 := by rw [hrdef, cechD_cechRefine, hz, map_zero]
    have hdiff : cechD V M.toAb.obj 1 (w - r) = 0 := by rw [map_sub, hw, hr', sub_zero]
    have hsum : κ ⟨w - r, hdiff⟩ + κ ⟨r, hr'⟩ = κ ⟨w, hw⟩ := by
      rw [← map_add]
      congr 1
      exact Subtype.ext (sub_add_cancel _ _)
    have hκr : κ ⟨r, hr'⟩ = κ ⟨w, hw⟩ := hr.trans hzw
    rw [hκr] at hsum
    obtain ⟨b, hb⟩ := (cechToH_eq_zero_iff hV M.toAb hdiff).1 (add_eq_right.1 hsum)
    exact ⟨z, b, hz, by rw [hb]; exact (add_sub_cancel _ _).symm⟩
  · intro x
    obtain ⟨z, hz, rfl⟩ := cechToH_surjective hV M.toAb (fun i ↦ H_one_eq_zero (qV i)) x
    exact ⟨⟨z, hz⟩, rfl⟩
  · intro b
    exact cechToH_cechD hV M.toAb b
  · intro c z
    exact cechToH_map hV (smulHom M c) z.2

end

end projectiveSpaceAn

end ComplexAnalytic

end
