/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.TheoremBProduct

/-!
# Projective space over a polynomial ring and its analytification

Let `A = ℂ[y₀, …, y_{m-1}]` (`ComplexAnalytic.RelBase m`) and `P = ℙₒ(N; A)`, a scheme locally of
finite type over `ℂ` (`ComplexAnalytic.relProjectiveSpace m N`) with a morphism to
`𝔸ᵐ = Spec A`. The chart `i` of `P`, composed with `A[Y₀, …, Y_{N-1}] ≅ ℂ[x₀, …, x_{N+m-1}]`
(`Yₖ ↦ xₖ`, `yⱼ ↦ x_{N+j}`), is a chart `𝔸^{N+m} ⟶ P` over `ℂ`
(`ComplexAnalytic.relProjectiveSpaceChart i`), and its analytification is an open immersion
`ℂ^{N+m} ⟶ P^an` (`ComplexAnalytic.relProjectiveSpaceAnChart i`) with image `π⁻¹(U i)`.

A point `w ∈ ℂ^{N+m}` has chart coordinates `z = zPart w ∈ ℂᴺ` and base coordinates
`y = yPart w ∈ ℂᵐ`, and `π` sends its image to the point of the chart `i` of `P` given by the
evaluation of `A[Y]` at `z` over the evaluation `A → ℂ` at `y`
(`ComplexAnalytic.relProjectiveSpaceAn.π_chart`). Hence `π` is injective, and for `v ∈ ℂᴺ⁺¹ ∖ 0`
and `y ∈ ℂᵐ` the point `pointOfVec v y` (the chart `i` at the dehomogenisation of `v` at `i`,
any `i` with `vᵢ ≠ 0`) is well defined; every point of `P^an` is of this form.

The analytification of `P ⟶ 𝔸ᵐ`, read through `(𝔸ᵐ)^an ≅ ℂᵐ`, is
`ComplexAnalytic.relProjectiveSpaceAnBase`; on points it sends `pointOfVec v y` to `y`
(`ComplexAnalytic.relProjectiveSpaceAn.baseY_pointOfVec`). For an open `U ⊆ ℂᵐ`, `tube U` is its
preimage in `P^an`, and for `i ∈ I` the chart `i` maps the locus of the `w` with `yPart w ∈ U`
and nonvanishing homogeneous coordinates `j ∈ I` (`chartPiece U I i`) onto `tube U ⊓ opensUI I`
(`ComplexAnalytic.relProjectiveSpaceAn.image_chart_tubeUI`); over an open box it is a mixed
domain `B × (ℂ^×)^P × ℂ^{N - P}` (`chartPiece_eq_mixedSet`), on which Theorem B holds
(`ComplexAnalytic.relProjectiveSpaceAn.subsingleton_H_tube_inf_opensUI`).
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology MvPolynomial

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable (m N : ℕ)

/-- The polynomial ring `ℂ[y₀, …, y_{m-1}]`, the base ring of the relative projective space. -/
abbrev RelBase : Type u := MvPolynomial (Fin m) (ULift.{u} ℂ)

instance : LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (C : ULift.{u} ℂ →+* RelBase.{u} m))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- **Projective `N`-space over `ℂ[y₀, …, y_{m-1}]`**, as a scheme locally of finite type over
`ℂ`. -/
def relProjectiveSpace : SchemeLFTℂ.{u} :=
  ⟨Over.mk (ProjectiveSpace.toSpec N (RelBase.{u} m) ≫
      Spec.map (CommRingCat.ofHom (C : ULift.{u} ℂ →+* RelBase.{u} m))),
    by
      haveI : LocallyOfFiniteType (ProjectiveSpace.toSpec N (RelBase.{u} m)) :=
        IsProper.toLocallyOfFiniteType
      change LocallyOfFiniteType (ProjectiveSpace.toSpec N (RelBase.{u} m) ≫
        Spec.map (CommRingCat.ofHom (C : ULift.{u} ℂ →+* RelBase.{u} m)))
      exact locallyOfFiniteType_comp _ _⟩

@[simp]
lemma relProjectiveSpace_obj_left : (relProjectiveSpace.{u} m N).obj.left = ℙₒ(N; RelBase.{u} m) :=
  rfl

/-- The structure morphism `ℙₒ(N; A) ⟶ 𝔸ᵐ = Spec A` over `ℂ`. -/
def relProjectiveSpaceToAffine : relProjectiveSpace.{u} m N ⟶ affineSpace.{u} m :=
  ObjectProperty.homMk (Over.homMk (ProjectiveSpace.toSpec N (RelBase.{u} m)) rfl)

/-- The ring isomorphism `A[Y₀, …, Y_{N-1}] ≅ ℂ[x₀, …, x_{N+m-1}]`, `Yₖ ↦ xₖ`, `yⱼ ↦ x_{N+j}`. -/
def relChartRingEquiv :
    MvPolynomial (Fin N) (RelBase.{u} m) ≃+* MvPolynomial (Fin (N + m)) (ULift.{u} ℂ) :=
  (sumAlgEquiv (ULift.{u} ℂ) (Fin N) (Fin m)).symm.toRingEquiv.trans
    (renameEquiv (ULift.{u} ℂ) finSumFinEquiv).toRingEquiv

variable {m N}

@[simp]
lemma relChartRingEquiv_X (k : Fin N) :
    relChartRingEquiv.{u} m N (X k) = X (Fin.castAdd m k) := by
  simp [relChartRingEquiv]

@[simp]
lemma relChartRingEquiv_C_X (j : Fin m) :
    relChartRingEquiv.{u} m N (C (X j)) = X (Fin.natAdd N j) := by
  simp [relChartRingEquiv]

@[simp]
lemma relChartRingEquiv_C_C (c : ULift.{u} ℂ) :
    relChartRingEquiv.{u} m N (C (C c)) = C c := by
  simp [relChartRingEquiv]

lemma relChart_toSpec (i : Fin (N + 1)) :
    Spec.map (CommRingCat.ofHom (relChartRingEquiv.{u} m N).toRingHom) ≫
      ProjectiveSpace.chart i ≫ ProjectiveSpace.toSpec N (RelBase.{u} m) ≫
        Spec.map (CommRingCat.ofHom (C : ULift.{u} ℂ →+* RelBase.{u} m)) =
      Spec.map (CommRingCat.ofHom (C : ULift.{u} ℂ →+* MvPolynomial (Fin (N + m)) _)) := by
  rw [ProjectiveSpace.chart_toSpec_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext c
  simp

/-- The **standard chart** `i` of `ℙₒ(N; A)`, `𝔸^{N+m} ⟶ ℙₒ(N; A)` over `ℂ`. -/
def relProjectiveSpaceChart (i : Fin (N + 1)) :
    affineSpace.{u} (N + m) ⟶ relProjectiveSpace.{u} m N :=
  ObjectProperty.homMk (Over.homMk
    (Spec.map (CommRingCat.ofHom (relChartRingEquiv.{u} m N).toRingHom) ≫
      ProjectiveSpace.chart i) (by
      rw [Category.assoc]; exact relChart_toSpec i))

@[simp]
lemma relProjectiveSpaceChart_hom_left (i : Fin (N + 1)) :
    (relProjectiveSpaceChart.{u} (m := m) i).hom.left =
      Spec.map (CommRingCat.ofHom (relChartRingEquiv.{u} m N).toRingHom) ≫
        ProjectiveSpace.chart i :=
  rfl

instance isIso_SpecMap_relChartRingEquiv :
    IsIso (Spec.map (CommRingCat.ofHom (relChartRingEquiv.{u} m N).toRingHom)) :=
  inferInstanceAs (IsIso (Scheme.Spec.mapIso (relChartRingEquiv.{u} m N).toCommRingCatIso.op).hom)

instance (i : Fin (N + 1)) :
    AlgebraicGeometry.IsOpenImmersion (relProjectiveSpaceChart.{u} (m := m) i).hom.left := by
  rw [relProjectiveSpaceChart_hom_left]
  haveI h1 : AlgebraicGeometry.IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (relChartRingEquiv.{u} m N).toRingHom)) := inferInstance
  haveI h2 : AlgebraicGeometry.IsOpenImmersion (ProjectiveSpace.chart (R := RelBase.{u} m) i) :=
    inferInstance
  exact @AlgebraicGeometry.IsOpenImmersion.comp _ _ _ _ _ h1 h2

variable (m N) in
/-- **The analytification `P^an` of `ℙₒ(N; ℂ[y₀, …, y_{m-1}])`.** -/
abbrev relProjectiveSpaceAn : AnalyticSpace.{u} :=
  analytification.obj (relProjectiveSpace.{u} m N)

/-- **The analytic chart `i`**, `ℂ^{N+m} ⟶ P^an`. -/
def relProjectiveSpaceAnChart (i : Fin (N + 1)) :
    AnalyticSpace.complexAffineSpace.{u} (N + m) ⟶ relProjectiveSpaceAn.{u} m N :=
  (analytificationAffineSpaceIso.{u} (N + m)).inv ≫
    analytification.map (relProjectiveSpaceChart i)

variable (m N) in
/-- The analytification of `P ⟶ 𝔸ᵐ`, read through `(𝔸ᵐ)^an ≅ ℂᵐ`. -/
def relProjectiveSpaceAnBase :
    relProjectiveSpaceAn.{u} m N ⟶ AnalyticSpace.complexAffineSpace.{u} m :=
  analytification.map (relProjectiveSpaceToAffine m N) ≫ (analytificationAffineSpaceIso.{u} m).hom

namespace relProjectiveSpaceAn

open ProjectiveSpace projectiveSpaceAn

instance isOpenImmersion_chart (i : Fin (N + 1)) :
    LocallyRingedSpace.IsOpenImmersion (relProjectiveSpaceAnChart.{u} (m := m) i).toLRSHom := by
  haveI : IsIso (analytificationAffineSpaceIso.{u} (N + m)).inv.toLRSHom :=
    (forgetToLocallyRingedSpace.mapIso (analytificationAffineSpaceIso.{u} (N + m))).isIso_inv
  exact LocallyRingedSpace.IsOpenImmersion.comp
    (analytificationAffineSpaceIso.{u} (N + m)).inv.toLRSHom
    (analytification.map (relProjectiveSpaceChart.{u} (m := m) i)).toLRSHom

/-- The chart `i` of `P^an`, as a morphism of locally ringed spaces. -/
abbrev chartLRS (i : Fin (N + 1)) :
    (AnalyticSpace.complexAffineSpace.{u} (N + m)).toLocallyRingedSpace ⟶
      (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace :=
  (relProjectiveSpaceAnChart.{u} i).toLRSHom

variable (m N) in
/-- The comparison morphism `P^an ⟶ P` on points. -/
abbrev π : relProjectiveSpaceAn.{u} m N → ℙₒ(N; RelBase.{u} m) :=
  (analytificationπ (relProjectiveSpace.{u} m N)).left.base

/-- The charts are open embeddings. -/
theorem isOpenEmbedding_chart (i : Fin (N + 1)) :
    IsOpenEmbedding (chartLRS.{u} (m := m) i).base :=
  PresheafedSpace.IsOpenImmersion.base_open (f := (chartLRS.{u} (m := m) i).toHom)

theorem chart_injective (i : Fin (N + 1)) : Function.Injective (chartLRS.{u} (m := m) i).base :=
  (isOpenEmbedding_chart i).injective

/-- **The image of the analytic chart `i` is the preimage of `U i = D₊(Xᵢ)`.** -/
theorem range_chart (i : Fin (N + 1)) :
    Set.range (chartLRS.{u} (m := m) i).base =
      π m N ⁻¹' (U N (RelBase.{u} m) i : Set ℙₒ(N; RelBase.{u} m)) := by
  have hs := (AnalyticSpace.bijective_base_of_isIso
    (analytificationAffineSpaceIso.{u} (N + m)).inv).2.range_eq
  change Set.range ((analytification.map (relProjectiveSpaceChart.{u} (m := m) i)).toLRSHom.base ∘
    (analytificationAffineSpaceIso.{u} (N + m)).inv.toLRSHom.base) = _
  rw [Set.range_comp, hs, Set.image_univ, range_analytification_map]
  ext y
  change π m N y ∈ Set.range (Spec.map (CommRingCat.ofHom (relChartRingEquiv.{u} m N).toRingHom) ≫
    ProjectiveSpace.chart i).base ↔ _
  change π m N y ∈ (Spec.map (CommRingCat.ofHom (relChartRingEquiv.{u} m N).toRingHom) ≫
    ProjectiveSpace.chart i).opensRange ↔ _
  rw [Scheme.Hom.opensRange_comp_of_isIso, ProjectiveSpace.opensRange_chart]
  rfl

/-- The chart coordinates `z ∈ ℂᴺ` of a point of `ℂ^{N+m}`. -/
def zPart (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) : Fin N → ℂ :=
  fun k ↦ (w : ULift.{u} (Fin (N + m)) → ℂ) ⟨Fin.castAdd m k⟩

/-- The base coordinates `y ∈ ℂᵐ` of a point of `ℂ^{N+m}`. -/
def yPart (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) : Fin m → ℂ :=
  fun j ↦ (w : ULift.{u} (Fin (N + m)) → ℂ) ⟨Fin.natAdd N j⟩

/-- The point of `ℂ^{N+m}` with chart coordinates `z` and base coordinates `y`. -/
def joinPt (z : Fin N → ℂ) (y : Fin m → ℂ) : AnalyticSpace.complexAffineSpace.{u} (N + m) :=
  show ULift.{u} (Fin (N + m)) → ℂ from fun k ↦ Fin.append z y k.down

@[simp]
lemma zPart_joinPt (z : Fin N → ℂ) (y : Fin m → ℂ) : zPart.{u} (joinPt.{u} z y) = z := by
  funext k
  simp [zPart, joinPt]

@[simp]
lemma yPart_joinPt (z : Fin N → ℂ) (y : Fin m → ℂ) : yPart.{u} (joinPt.{u} z y) = y := by
  funext k
  simp [yPart, joinPt]

@[simp]
lemma joinPt_zPart_yPart (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    joinPt.{u} (zPart w) (yPart w) = w := by
  change (fun k : ULift.{u} (Fin (N + m)) ↦ Fin.append (zPart w) (yPart w) k.down) =
    (w : ULift.{u} (Fin (N + m)) → ℂ)
  funext ⟨k⟩
  induction k using Fin.addCases with
  | left k => simp [zPart]
  | right j => simp [yPart]

/-- Evaluation `A → ℂ` of `ℂ[y₀, …, y_{m-1}]` at `y`. -/
abbrev evalBase (y : Fin m → ℂ) : RelBase.{u} m →+* ℂ :=
  eval₂Hom φ.{u} y

lemma evalBase_surjective (y : Fin m → ℂ) : Function.Surjective (evalBase.{u} y) :=
  fun c ↦ ⟨C (ULift.up c), by simp; rfl⟩

lemma eval₂Hom_comp_relChartRingEquiv (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    (eval₂Hom φ.{u} (toFin w)).comp (relChartRingEquiv.{u} m N).toRingHom =
      eval₂Hom (evalBase.{u} (yPart w)) (zPart w) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun k ↦ ?_)
  · rw [RingHom.comp_apply, eval₂Hom_C]
    change eval₂Hom φ.{u} (toFin w) (relChartRingEquiv.{u} m N (C a)) = evalBase (yPart w) a
    induction a using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add] at hp hq ⊢; rw [hp, hq]
    | mul_X p j hp =>
      simp only [map_mul] at hp ⊢
      rw [hp, relChartRingEquiv_C_X]
      simp [toFin, yPart]
  · simp [toFin, zPart]

/-- **The comparison morphism on the chart `i`**: `π(ψᵢ w)` is the chart `i` at the evaluation
at `zPart w` over the evaluation `A → ℂ` at `yPart w`. -/
theorem π_chart (i : Fin (N + 1)) (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    π m N ((chartLRS.{u} i).base w) =
      (ProjectiveSpace.chart (R := RelBase.{u} m) i).base
        (evalPoint (evalBase.{u} (yPart w)) (zPart w)) := by
  have h : toOverSpec.map (relProjectiveSpaceAnChart.{u} (m := m) i) ≫
      analytificationπ (relProjectiveSpace.{u} m N) =
      complexAffineSpaceπ.{u} (N + m) ≫
        schemeToOverSpec.map (relProjectiveSpaceChart.{u} (m := m) i).hom := by
    rw [relProjectiveSpaceAnChart, Functor.map_comp, Category.assoc, analytificationπ_naturality,
      analytificationAffineSpaceIso_inv_comp_assoc]
  have := congrArg (fun f ↦ f.left.base w) h
  refine this.trans ?_
  change (ProjectiveSpace.chart i).base ((Spec.map (CommRingCat.ofHom
    (relChartRingEquiv.{u} m N).toRingHom)).base ((complexAffineSpaceπ.{u} (N + m)).left.base w))
      = _
  rw [complexAffineSpaceπ_base]
  congr 1
  refine PrimeSpectrum.ext ?_
  change Ideal.comap _ (RingHom.ker _) = RingHom.ker _
  rw [RingHom.comap_ker]
  exact congrArg RingHom.ker (eval₂Hom_comp_relChartRingEquiv w)

/-- The images of the charts cover `P^an`. -/
theorem exists_mem_range_chart (x : relProjectiveSpaceAn.{u} m N) :
    ∃ i, x ∈ Set.range (chartLRS.{u} i).base := by
  have hx : π m N x ∈ (⊤ : (ℙₒ(N; RelBase.{u} m)).Opens) := trivial
  rw [← ProjectiveSpace.iSup_U, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, by rw [range_chart]; exact hi⟩

/-- **The comparison morphism `P^an ⟶ P` is injective on points.** -/
theorem π_injective : Function.Injective (π.{u} m N) := by
  intro x y h
  obtain ⟨i, z, rfl⟩ := exists_mem_range_chart x
  have hy : y ∈ Set.range (chartLRS.{u} i).base := by
    rw [range_chart, Set.mem_preimage, ← h, ← Set.mem_preimage, ← range_chart]
    exact ⟨z, rfl⟩
  obtain ⟨w, rfl⟩ := hy
  rw [π_chart, π_chart] at h
  have h' := (ProjectiveSpace.chart (R := RelBase.{u} m) i).isOpenEmbedding.injective h
  have hy : yPart z = yPart w := by
    funext j
    have h2 : C (X j) - C (C (ULift.up (yPart w j))) ∈
        (show PrimeSpectrum (MvPolynomial (Fin N) (RelBase.{u} m)) from
          evalPoint (evalBase.{u} (yPart z)) (zPart z)).asIdeal := by
      rw [h', mem_evalPoint_asIdeal_iff]
      simp only [eval₂_sub, eval₂_C, eval₂Hom_X', eval₂Hom_C, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe]
      exact sub_self _
    rw [mem_evalPoint_asIdeal_iff] at h2
    simp only [eval₂_sub, eval₂_C, eval₂Hom_X', eval₂Hom_C, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe] at h2
    exact sub_eq_zero.1 h2
  rw [hy] at h'
  have hz := evalPoint_injective _ (evalBase_surjective _) h'
  rw [← joinPt_zPart_yPart z, ← joinPt_zPart_yPart w, hz, hy]

/-! ### Homogeneous coordinates -/

/-- **Chart transitions in coordinates**: for `vᵢ ≠ 0` and `vⱼ ≠ 0`, the chart `i` at the
dehomogenisation of `v` at `i` and the chart `j` at its dehomogenisation at `j` (over the same
base point `y`) are the same point. -/
theorem chart_dehomogenizeVec_eq (i j : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0)
    (hj : v j ≠ 0) (y : Fin m → ℂ) :
    (chartLRS.{u} i).base (joinPt (dehomogenizeVec i v) y) =
      (chartLRS.{u} j).base (joinPt (dehomogenizeVec j v) y) := by
  apply π_injective
  rw [π_chart, π_chart, zPart_joinPt, yPart_joinPt, zPart_joinPt, yPart_joinPt]
  exact ProjectiveSpace.chart_base_evalPoint_eq (evalBase.{u} y) i j v hi hj

/-- **The image of a point of the chart `i` lies in the chart `j` iff its `j`-th homogeneous
coordinate is nonzero.** -/
theorem chart_dehomogenizeVec_mem_range_iff (i j : Fin (N + 1)) (v : Fin (N + 1) → ℂ)
    (hi : v i ≠ 0) (y : Fin m → ℂ) :
    (chartLRS.{u} i).base (joinPt (dehomogenizeVec i v) y) ∈ Set.range (chartLRS.{u} j).base ↔
      v j ≠ 0 := by
  rw [range_chart, Set.mem_preimage, π_chart, zPart_joinPt, yPart_joinPt]
  exact ProjectiveSpace.chart_base_evalPoint_mem_U_iff (evalBase.{u} y) i j v hi

/-- **The point of `P^an` with homogeneous coordinates `v ≠ 0` over `y ∈ ℂᵐ`**: the chart `i` at
the dehomogenisation of `v` at some `i` with `vᵢ ≠ 0` (independent of `i`, `pointOfVec_eq`). -/
def pointOfVec (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) :
    relProjectiveSpaceAn.{u} m N :=
  (chartLRS.{u} (Function.ne_iff.1 hv).choose).base
    (joinPt (dehomogenizeVec (Function.ne_iff.1 hv).choose v) y)

theorem pointOfVec_eq (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) (i : Fin (N + 1))
    (hi : v i ≠ 0) :
    pointOfVec.{u} v hv y = (chartLRS.{u} i).base (joinPt (dehomogenizeVec i v) y) :=
  chart_dehomogenizeVec_eq _ _ v (Function.ne_iff.1 hv).choose_spec hi y

theorem mem_range_chart_pointOfVec_iff (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ)
    (j : Fin (N + 1)) :
    pointOfVec.{u} v hv y ∈ Set.range (chartLRS.{u} j).base ↔ v j ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  rw [pointOfVec_eq _ _ _ i hi]
  exact chart_dehomogenizeVec_mem_range_iff i j v hi y

/-- The homogeneous coordinates `(zPart w with 1 inserted at i)` of a point `w` of the chart
`i`. -/
def homogCoord (i : Fin (N + 1)) (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    Fin (N + 1) → ℂ :=
  Fin.insertNth i 1 (zPart w)

@[simp]
lemma homogCoord_self (i : Fin (N + 1)) (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    homogCoord i w i = 1 := by
  simp [homogCoord]

lemma homogCoord_ne_zero (i : Fin (N + 1)) (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    homogCoord i w ≠ 0 :=
  Function.ne_iff.2 ⟨i, by simp⟩

@[simp]
lemma dehomogenizeVec_homogCoord (i : Fin (N + 1))
    (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    dehomogenizeVec i (homogCoord i w) = zPart w :=
  ProjectiveSpace.dehomogenizeVec_insertNth i _

/-- The chart `i` at `w` is the point with homogeneous coordinates `homogCoord i w` over
`yPart w`. -/
theorem chart_eq_pointOfVec (i : Fin (N + 1)) (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    (chartLRS.{u} i).base w =
      pointOfVec.{u} (homogCoord i w) (homogCoord_ne_zero i w) (yPart w) := by
  rw [pointOfVec_eq _ _ _ i (by simp), dehomogenizeVec_homogCoord, joinPt_zPart_yPart]

theorem pointOfVec_surjective (x : relProjectiveSpaceAn.{u} m N) :
    ∃ (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ), pointOfVec.{u} v hv y = x := by
  obtain ⟨i, w, rfl⟩ := exists_mem_range_chart x
  exact ⟨_, _, _, (chart_eq_pointOfVec i w).symm⟩

theorem pointOfVec_smul (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) {c : ℂ}
    (hc : c ≠ 0) : pointOfVec.{u} (c • v) (smul_ne_zero hc hv) y = pointOfVec.{u} v hv y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  rw [pointOfVec_eq _ _ _ i hi, pointOfVec_eq _ _ _ i
    (by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero hc hi),
    ProjectiveSpace.dehomogenizeVec_smul i v hc]

/-! ### The base point -/

/-- The base coordinates `y ∈ ℂᵐ` of a point of `P^an`: the image under `P^an ⟶ ℂᵐ`. -/
def baseY (x : relProjectiveSpaceAn.{u} m N) : Fin m → ℂ :=
  toFin ((relProjectiveSpaceAnBase.{u} m N).toLRSHom.base x)

lemma continuous_baseY : Continuous (baseY.{u} (m := m) (N := N)) :=
  (continuous_pi fun k ↦ continuous_apply (ULift.up k)).comp
    (relProjectiveSpaceAnBase.{u} m N).toLRSHom.base.hom.continuous

lemma relProjectiveSpaceAnBase_comp :
    toOverSpec.map (relProjectiveSpaceAnBase.{u} m N) ≫ complexAffineSpaceπ.{u} m =
      analytificationπ (relProjectiveSpace.{u} m N) ≫
        schemeToOverSpec.map (relProjectiveSpaceToAffine.{u} m N).hom := by
  rw [relProjectiveSpaceAnBase, Functor.map_comp, Category.assoc,
    analytificationAffineSpaceIso_hom_comp, analytificationπ_naturality]

/-- **The base coordinates of a point of the chart `i` are its coordinates `yPart`.** -/
theorem baseY_chart (i : Fin (N + 1)) (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    baseY.{u} ((chartLRS.{u} i).base w) = yPart w := by
  have h := congrArg (fun f ↦ f.left.base ((chartLRS.{u} i).base w))
    (relProjectiveSpaceAnBase_comp.{u} (m := m) (N := N))
  change (complexAffineSpaceπ.{u} m).left.base _ =
    (ProjectiveSpace.toSpec N (RelBase.{u} m)).base (π m N ((chartLRS.{u} i).base w)) at h
  rw [π_chart, ← Scheme.Hom.comp_apply, ProjectiveSpace.chart_toSpec] at h
  have h2 : (complexAffineSpaceπ.{u} m).left.base
      ((relProjectiveSpaceAnBase.{u} m N).toLRSHom.base ((chartLRS.{u} i).base w)) =
      (complexAffineSpaceπ.{u} m).left.base (ofFin (yPart w)) := by
    refine h.trans (PrimeSpectrum.ext ?_)
    rw [complexAffineSpaceπ_base, toFin_ofFin]
    change Ideal.comap _ (RingHom.ker _) = RingHom.ker _
    rw [RingHom.comap_ker]
    congr 1
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun j ↦ ?_) <;> simp
  exact congrArg toFin (complexAffineSpaceπ_base_injective m h2)

theorem baseY_pointOfVec (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) :
    baseY.{u} (pointOfVec.{u} v hv y) = y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  rw [pointOfVec_eq _ _ _ i hi, baseY_chart, yPart_joinPt]

/-! ### Opens -/

/-- **The preimage `U × ℙᴺ` of an open `U ⊆ ℂᵐ` in `P^an`.** -/
def tube (U : Opens (Fin m → ℂ)) : (relProjectiveSpaceAn.{u} m N).Opens :=
  ⟨baseY ⁻¹' U, U.isOpen.preimage continuous_baseY⟩

@[simp]
lemma mem_tube {U : Opens (Fin m → ℂ)} {x : relProjectiveSpaceAn.{u} m N} :
    x ∈ tube.{u} U ↔ baseY x ∈ U :=
  Iff.rfl

/-- The open `π⁻¹(UI I) = ⋂_{j ∈ I} (image of the chart j)` of `P^an`. -/
def opensUI (I : Finset (Fin (N + 1))) : (relProjectiveSpaceAn.{u} m N).Opens :=
  (Opens.map (analytificationπ (relProjectiveSpace.{u} m N)).left.base).obj
    (ProjectiveSpace.UI N (RelBase.{u} m) I)

/-- The image of the chart `i` of `P^an`, an open. -/
def chartOpens (i : Fin (N + 1)) : (relProjectiveSpaceAn.{u} m N).Opens :=
  ⟨Set.range (chartLRS.{u} i).base, (isOpenEmbedding_chart i).isOpen_range⟩

lemma mem_opensUI_iff {I : Finset (Fin (N + 1))} {x : relProjectiveSpaceAn.{u} m N} :
    x ∈ opensUI.{u} I ↔ ∀ j ∈ I, x ∈ Set.range (chartLRS.{u} j).base := by
  change π m N x ∈ ProjectiveSpace.UI N (RelBase.{u} m) I ↔ _
  rw [ProjectiveSpace.UI_eq_iInf]
  simp only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter, range_chart, Set.mem_preimage]
  refine forall_congr' fun j ↦ ?_
  by_cases hj : j ∈ I
  · simp [hj]
  · simp [hj]

/-- `π⁻¹(UI I)` is the intersection of the chart images `j ∈ I`. -/
lemma iInf_chartOpens (I : Finset (Fin (N + 1))) :
    ⨅ i ∈ I, chartOpens.{u} (m := m) (N := N) i = opensUI I := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_opensUI_iff]
  simp only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  refine forall_congr' fun j ↦ ?_
  by_cases hj : j ∈ I
  · simp [hj, chartOpens]
  · simp [hj]

/-- The chart images cover `P^an`. -/
lemma iSup_chartOpens : ⨆ i, chartOpens.{u} (m := m) (N := N) i = ⊤ :=
  eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 (exists_mem_range_chart x)

/-- **The chart `i ∈ I` maps `{w | yPart w ∈ U, (homogCoord i w)ⱼ ≠ 0 for j ∈ I}` onto
`tube U ⊓ opensUI I`.** -/
theorem image_chart_tubeUI (U : Opens (Fin m → ℂ)) {I : Finset (Fin (N + 1))}
    {i : Fin (N + 1)} (hi : i ∈ I) :
    (chartLRS.{u} i).base '' {w | yPart w ∈ U ∧ ∀ j ∈ I, homogCoord i w j ≠ 0} =
      ((tube.{u} (N := N) U ⊓ opensUI I : (relProjectiveSpaceAn.{u} m N).Opens) :
        Set (relProjectiveSpaceAn.{u} m N)) := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Opens.coe_inf, Set.mem_inter_iff,
    SetLike.mem_coe, mem_tube, mem_opensUI_iff]
  constructor
  · rintro ⟨w, ⟨hU, hw⟩, rfl⟩
    refine ⟨by rw [baseY_chart]; exact hU, fun j hj ↦ ?_⟩
    rw [chart_eq_pointOfVec, mem_range_chart_pointOfVec_iff]
    exact hw j hj
  · rintro ⟨hU, hx⟩
    obtain ⟨w, rfl⟩ := hx i hi
    refine ⟨w, ⟨by rwa [baseY_chart] at hU, fun j hj ↦ ?_⟩, rfl⟩
    have := hx j hj
    rwa [chart_eq_pointOfVec, mem_range_chart_pointOfVec_iff] at this

/-! ### Theorem B on the chart pieces over a box -/

/-- An open box, as an open of `ℂᵐ`. -/
def boxOpens (a b : Fin m → ℂ) : Opens (Fin m → ℂ) :=
  ⟨Complex.openBox a b, by
    have : Complex.openBox a b = ⋂ j ∈ (Set.univ : Set (Fin m)),
        (fun w : Fin m → ℂ ↦ w j) ⁻¹' (Set.Ioo (a j).re (b j).re ×ℂ Set.Ioo (a j).im (b j).im) := by
      ext w; simp [Complex.openBox]
    rw [this]
    exact Set.finite_univ.isOpen_biInter fun j _ ↦ (isOpen_Ioo.reProdIm isOpen_Ioo).preimage
      (continuous_apply j)⟩

@[simp]
lemma coe_boxOpens (a b : Fin m → ℂ) :
    (boxOpens a b : Set (Fin m → ℂ)) = Complex.openBox a b :=
  rfl

lemma continuous_yPart : Continuous (yPart.{u} (N := N) (m := m)) :=
  continuous_pi fun _ ↦ continuous_apply _

lemma continuous_homogCoord (i j : Fin (N + 1)) :
    Continuous fun w : AnalyticSpace.complexAffineSpace.{u} (N + m) ↦ homogCoord i w j :=
  (continuous_apply j).comp (Continuous.finInsertNth i continuous_const
    (continuous_pi fun _ ↦ continuous_apply _))

/-- The locus `{w | yPart w ∈ U, (homogCoord i w)ⱼ ≠ 0 for j ∈ I}` of `ℂ^{N+m}`, an open. -/
def chartPiece (U : Opens (Fin m → ℂ)) (I : Finset (Fin (N + 1))) (i : Fin (N + 1)) :
    Opens (AnalyticSpace.complexAffineSpace.{u} (N + m)).toLocallyRingedSpace.toPresheafedSpace :=
  ⟨{w | yPart w ∈ U ∧ ∀ j ∈ I, homogCoord i w j ≠ 0}, by
    have : {w : AnalyticSpace.complexAffineSpace.{u} (N + m) |
        yPart w ∈ U ∧ ∀ j ∈ I, homogCoord i w j ≠ 0} =
        yPart ⁻¹' U ∩ ⋂ j ∈ (I : Set (Fin (N + 1))), {w | homogCoord i w j ≠ 0} := by
      ext w
      simp
    rw [this]
    exact (U.isOpen.preimage continuous_yPart).inter (I.finite_toSet.isOpen_biInter fun j _ ↦
      isOpen_ne_fun (continuous_homogCoord i j) continuous_const)⟩

/-- **Over a box, the chart pieces are mixed domains**: `B × (ℂ^×)^P × ℂ^{N - P}` with
`P = {l | i.succAbove l ∈ I}`, in the coordinates `ULift (Fin (N + m))` of `ℂ^{N+m}`. -/
lemma chartPiece_eq_mixedSet (a b : Fin m → ℂ) {U : Opens (Fin m → ℂ)}
    (hU : (U : Set (Fin m → ℂ)) = Complex.openBox a b) (I : Finset (Fin (N + 1)))
    (i : Fin (N + 1)) :
    ((chartPiece.{u} U I i : Set (AnalyticSpace.complexAffineSpace.{u} (N + m))) :
        Set (ULift.{u} (Fin (N + m)) → ℂ)) =
      Complex.mixedSet {k : ULift.{u} (Fin (N + m)) | N ≤ (k.down : ℕ)}
        {k | ∃ l : Fin N, k.down = Fin.castAdd m l ∧ i.succAbove l ∈ I}
        (fun k ↦ Fin.append (0 : Fin N → ℂ) a k.down)
        (fun k ↦ Fin.append (0 : Fin N → ℂ) b k.down) := by
  ext w
  change (yPart.{u} (N := N) (m := m) w ∈ U ∧ ∀ j ∈ I, homogCoord.{u} i w j ≠ 0) ↔ _
  rw [← SetLike.mem_coe, hU]
  simp only [Complex.openBox, Complex.mixedSet, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy, hz⟩ ⟨k⟩
    induction k using Fin.addCases with
    | left l =>
      refine ⟨fun h ↦ absurd h (by simp), ?_⟩
      rintro ⟨l', hl', hI⟩
      rw [Fin.castAdd_inj.1 hl'] at *
      have := hz _ hI
      simpa [homogCoord, zPart] using this
    | right j =>
      refine ⟨fun _ ↦ by simpa [yPart] using hy j, ?_⟩
      rintro ⟨l', hl', -⟩
      exact absurd hl' (by simp [Fin.ext_iff]; omega)
  · intro h
    refine ⟨fun j ↦ by simpa [yPart] using (h ⟨Fin.natAdd N j⟩).1 (by simp), fun j hj ↦ ?_⟩
    obtain rfl | ⟨l, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
    · simp
    · simpa [homogCoord, zPart] using (h ⟨Fin.castAdd m l⟩).2 ⟨l, rfl, hj⟩

/-- **Theorem B on the chart pieces over a box**: `Hᵠ(tube B ⊓ π⁻¹(UI I), 𝒪_{P^an}) = 0` for
`q ≥ 1`, `I` nonempty and `B` an open box. -/
theorem subsingleton_H_tube_inf_opensUI (a b : Fin m → ℂ) {B : Opens (Fin m → ℂ)}
    (hB : (B : Set (Fin m → ℂ)) = Complex.openBox a b) {I : Finset (Fin (N + 1))}
    (hI : I.Nonempty) (q : ℕ) (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (tube.{u} (N := N) B ⊓ opensUI I)).obj
      (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace.structureSheafAb) q) := by
  obtain ⟨i, hi⟩ := hI
  have hSP : Disjoint {k : ULift.{u} (Fin (N + m)) | N ≤ (k.down : ℕ)}
      {k | ∃ l : Fin N, k.down = Fin.castAdd m l ∧ i.succAbove l ∈ I} := by
    rw [Set.disjoint_left]
    rintro k hk ⟨l, hl, -⟩
    simp only [Set.mem_setOf_eq, hl, Fin.val_castAdd] at hk
    omega
  exact LocallyRingedSpace.subsingleton_H_structureSheafAb_of_image_eq (chartLRS.{u} i)
    (chartPiece B I i) (W := tube B ⊓ opensUI I) (image_chart_tubeUI B hi) q
    (Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb_mixedSet hSP _ _
      (D := chartPiece B I i) (chartPiece_eq_mixedSet a b hB I i) hq)

end relProjectiveSpaceAn

end

end ComplexAnalytic

end
