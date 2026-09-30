/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.Points
public import Other.Oka.AnalyticSpace.Hausdorff
public import Other.Oka.Analytification.GAGA.AffineSpace
public import Other.Oka.Analytification.GAGA.OpenImmersion

/-!
# The analytic projective space `ℙⁿ_an`

`ComplexAnalytic.projectiveSpaceAn n` is the analytification of `ℙⁿ_ℂ`
(`ComplexAnalytic.projectiveSpace n`). Its standard charts
`ComplexAnalytic.projectiveSpaceAnChart i : ℂⁿ ⟶ ℙⁿ_an` are the analytifications of the scheme
charts, read through `analytification (𝔸ⁿ) ≅ ℂⁿ`. They are open immersions, the image of the chart
`i` is the preimage of `U i = D₊(Xᵢ)` under the comparison morphism `π : ℙⁿ_an ⟶ ℙⁿ`, and the
images cover `ℙⁿ_an`.

For `v ∈ ℂⁿ⁺¹ ∖ 0` the point `ComplexAnalytic.projectiveSpaceAn.pointOfVec v` is the image under
the chart `i` of the dehomogenisation `(v_{i.succAbove m} / vᵢ)ₘ`, for any `i` with `vᵢ ≠ 0`
(`pointOfVec_eq`): this is the chart transition `z ↦ (ẑₖ / ẑⱼ)` in coordinates. Two vectors give
the same point if and only if they are proportional, and every point arises this way, so the
points of `ℙⁿ_an` are the lines in `ℂⁿ⁺¹`
(`ComplexAnalytic.projectiveSpaceAn.projectivizationEquiv`).

Topologically, `ℙⁿ_an` is compact (every point lies in the image of the closed unit polydisc of
the chart of a coordinate of maximal modulus), Hausdorff and connected.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-- **The analytic projective space** `ℙⁿ_an`, the analytification of `ℙⁿ_ℂ`. -/
abbrev projectiveSpaceAn (n : ℕ) : AnalyticSpace.{u} :=
  analytification.obj (projectiveSpace.{u} n)

/-- **The standard chart `i` of `ℙⁿ_an`**, `ℂⁿ ⟶ ℙⁿ_an`: the analytification of the scheme chart
`𝔸ⁿ ⟶ ℙⁿ` onto `D₊(Xᵢ)`. -/
def projectiveSpaceAnChart {n : ℕ} (i : Fin (n + 1)) :
    AnalyticSpace.complexAffineSpace.{u} n ⟶ projectiveSpaceAn.{u} n :=
  (analytificationAffineSpaceIso.{u} n).inv ≫ analytification.map (projectiveSpaceChart i)

namespace projectiveSpaceAn

variable {n : ℕ}

instance isOpenImmersion_chart (i : Fin (n + 1)) :
    LocallyRingedSpace.IsOpenImmersion (projectiveSpaceAnChart.{u} i).toLRSHom := by
  haveI : IsIso (analytificationAffineSpaceIso.{u} n).inv.toLRSHom :=
    (forgetToLocallyRingedSpace.mapIso (analytificationAffineSpaceIso.{u} n)).isIso_inv
  exact LocallyRingedSpace.IsOpenImmersion.comp
    (analytificationAffineSpaceIso.{u} n).inv.toLRSHom
    (analytification.map (projectiveSpaceChart.{u} i)).toLRSHom

/-- The comparison morphism `ℙⁿ_an ⟶ ℙⁿ` on points. -/
abbrev π (n : ℕ) : projectiveSpaceAn.{u} n → ℙₒ(n; ULift.{u} ℂ) :=
  (analytificationπ (projectiveSpace.{u} n)).left.base

/-- The charts are open embeddings. -/
theorem isOpenEmbedding_chart (i : Fin (n + 1)) :
    IsOpenEmbedding (projectiveSpaceAnChart.{u} i).toLRSHom.base :=
  PresheafedSpace.IsOpenImmersion.base_open (f := (projectiveSpaceAnChart.{u} i).toLRSHom.toHom)

theorem chart_injective (i : Fin (n + 1)) :
    Function.Injective (projectiveSpaceAnChart.{u} i).toLRSHom.base :=
  (isOpenEmbedding_chart i).injective

/-- **The image of the analytic chart `i` is the preimage of `U i = D₊(Xᵢ)`.** -/
theorem range_chart (i : Fin (n + 1)) :
    Set.range (projectiveSpaceAnChart.{u} i).toLRSHom.base =
      π n ⁻¹' (ProjectiveSpace.U n (ULift.{u} ℂ) i : Set ℙₒ(n; ULift.{u} ℂ)) := by
  have hs := (AnalyticSpace.bijective_base_of_isIso
    (analytificationAffineSpaceIso.{u} n).inv).2.range_eq
  change Set.range ((analytification.map (projectiveSpaceChart.{u} i)).toLRSHom.base ∘
    (analytificationAffineSpaceIso.{u} n).inv.toLRSHom.base) = _
  rw [Set.range_comp, hs, Set.image_univ, range_analytification_map]
  ext y
  change π n y ∈ Set.range (ProjectiveSpace.chart (R := ULift.{u} ℂ) i).base ↔ _
  rw [← ProjectiveSpace.opensRange_chart (R := ULift.{u} ℂ) i]
  rfl

/-- The coordinate vector of a point of `ℂⁿ`, indexed by `Fin n`. -/
def toFin (z : AnalyticSpace.complexAffineSpace.{u} n) : Fin n → ℂ :=
  fun m ↦ (z : ULift.{u} (Fin n) → ℂ) ⟨m⟩

/-- The point of `ℂⁿ` with coordinate vector `w`, indexed by `Fin n`. -/
def ofFin (w : Fin n → ℂ) : AnalyticSpace.complexAffineSpace.{u} n :=
  show ULift.{u} (Fin n) → ℂ from fun k ↦ w k.down

@[simp] lemma toFin_ofFin (w : Fin n → ℂ) : toFin.{u} (ofFin.{u} w) = w := rfl

@[simp] lemma ofFin_toFin (z : AnalyticSpace.complexAffineSpace.{u} n) :
    ofFin.{u} (toFin z) = z := rfl

/-- The coefficient map `ULift ℂ →+* ℂ`. -/
abbrev φ : ULift.{u} ℂ →+* ℂ := ULift.ringEquiv.toRingHom

lemma complexAffineSpaceπ_base (z : AnalyticSpace.complexAffineSpace.{u} n) :
    (complexAffineSpaceπ.{u} n).left.base z = ProjectiveSpace.evalPoint φ.{u} (toFin z) :=
  PrimeSpectrum.ext (complexAffineSpaceπ_base_asIdeal n z)

/-- **The comparison morphism on the chart `i`**: `π (ψᵢ z) = chartᵢ(z)`. -/
theorem π_chart (i : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    π n ((projectiveSpaceAnChart.{u} i).toLRSHom.base z) =
      (ProjectiveSpace.chart (R := ULift.{u} ℂ) i).base
        (ProjectiveSpace.evalPoint φ.{u} (toFin z)) := by
  have h : toOverSpec.map (projectiveSpaceAnChart.{u} i) ≫
      analytificationπ (projectiveSpace.{u} n) =
      complexAffineSpaceπ.{u} n ≫ schemeToOverSpec.map (projectiveSpaceChart.{u} i).hom := by
    rw [projectiveSpaceAnChart, Functor.map_comp, Category.assoc, analytificationπ_naturality,
      analytificationAffineSpaceIso_inv_comp_assoc]
  have := congrArg (fun f ↦ f.left.base z) h
  refine this.trans ?_
  change (ProjectiveSpace.chart i).base ((complexAffineSpaceπ.{u} n).left.base z) = _
  rw [complexAffineSpaceπ_base]

/-- The images of the charts cover `ℙⁿ_an`. -/
theorem exists_mem_range_chart (x : projectiveSpaceAn.{u} n) :
    ∃ i, x ∈ Set.range (projectiveSpaceAnChart.{u} i).toLRSHom.base := by
  have hx : π n x ∈ (⊤ : (ℙₒ(n; ULift.{u} ℂ)).Opens) := trivial
  rw [← ProjectiveSpace.iSup_U, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, by rw [range_chart]; exact hi⟩

theorem iUnion_range_chart :
    ⋃ i, Set.range (projectiveSpaceAnChart.{u} (n := n) i).toLRSHom.base = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 (exists_mem_range_chart x)

/-- **The comparison morphism `ℙⁿ_an ⟶ ℙⁿ` is injective on points.** -/
theorem π_injective : Function.Injective (π.{u} n) := by
  intro x y h
  obtain ⟨i, z, rfl⟩ := exists_mem_range_chart x
  have hy : y ∈ Set.range (projectiveSpaceAnChart.{u} i).toLRSHom.base := by
    rw [range_chart, Set.mem_preimage, ← h, ← Set.mem_preimage, ← range_chart]
    exact ⟨z, rfl⟩
  obtain ⟨w, rfl⟩ := hy
  rw [π_chart, π_chart] at h
  have h' := ProjectiveSpace.evalPoint_injective φ.{u} ULift.ringEquiv.surjective
    ((ProjectiveSpace.chart i).isOpenEmbedding.injective h)
  rw [show z = ofFin (toFin z) from rfl, h']
  rfl

open ProjectiveSpace (dehomogenizeVec)

/-- **Chart transitions in coordinates**: if `vᵢ ≠ 0` and `vⱼ ≠ 0`, the chart `i` at the
dehomogenisation of `v` at `i` and the chart `j` at its dehomogenisation at `j` are the same
point; i.e. the transition map sends `z` to `(ẑ_{j.succAbove m} / ẑⱼ)ₘ`,
`ẑ = (z with 1 at i)`. -/
theorem chart_dehomogenizeVec_eq (i j : Fin (n + 1)) (v : Fin (n + 1) → ℂ) (hi : v i ≠ 0)
    (hj : v j ≠ 0) :
    (projectiveSpaceAnChart.{u} i).toLRSHom.base (ofFin (dehomogenizeVec i v)) =
      (projectiveSpaceAnChart.{u} j).toLRSHom.base (ofFin (dehomogenizeVec j v)) := by
  apply π_injective
  rw [π_chart, π_chart]
  exact ProjectiveSpace.chart_base_evalPoint_eq φ.{u} i j v hi hj

/-- **The image of a point of the chart `i` lies in the chart `j` iff its `j`-th homogeneous
coordinate is nonzero.** -/
theorem chart_dehomogenizeVec_mem_range_iff (i j : Fin (n + 1)) (v : Fin (n + 1) → ℂ)
    (hi : v i ≠ 0) :
    (projectiveSpaceAnChart.{u} i).toLRSHom.base (ofFin (dehomogenizeVec i v)) ∈
      Set.range (projectiveSpaceAnChart.{u} j).toLRSHom.base ↔ v j ≠ 0 := by
  rw [range_chart, Set.mem_preimage, π_chart]
  exact ProjectiveSpace.chart_base_evalPoint_mem_U_iff φ.{u} i j v hi

lemma insertNth_dehomogenizeVec (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) (hi : v i ≠ 0) :
    Fin.insertNth i 1 (dehomogenizeVec i v) = (v i)⁻¹ • v := by
  funext k
  obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove i k
  · simp [inv_mul_cancel₀ hi]
  · simp [dehomogenizeVec, div_eq_inv_mul]

/-- **The point of `ℙⁿ_an` with homogeneous coordinates `v ≠ 0`**: the chart `i` at the
dehomogenisation of `v` at some `i` with `vᵢ ≠ 0` (independent of `i`, `pointOfVec_eq`). -/
def pointOfVec (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) : projectiveSpaceAn.{u} n :=
  (projectiveSpaceAnChart.{u} (Function.ne_iff.1 hv).choose).toLRSHom.base
    (ofFin (dehomogenizeVec (Function.ne_iff.1 hv).choose v))

theorem pointOfVec_eq (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (i : Fin (n + 1)) (hi : v i ≠ 0) :
    pointOfVec.{u} v hv =
      (projectiveSpaceAnChart.{u} i).toLRSHom.base (ofFin (dehomogenizeVec i v)) :=
  chart_dehomogenizeVec_eq _ _ v (Function.ne_iff.1 hv).choose_spec hi

/-- The homogeneous coordinates `(z with 1 inserted at i)` of a point `z` of the chart `i`. -/
def homogCoord (i : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    Fin (n + 1) → ℂ :=
  Fin.insertNth i 1 (toFin z)

@[simp]
lemma homogCoord_self (i : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    homogCoord i z i = 1 := by
  simp [homogCoord]

lemma homogCoord_ne_zero (i : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    homogCoord i z ≠ 0 :=
  Function.ne_iff.2 ⟨i, by simp⟩

@[simp]
lemma dehomogenizeVec_homogCoord (i : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    dehomogenizeVec i (homogCoord i z) = toFin z :=
  ProjectiveSpace.dehomogenizeVec_insertNth i _

/-- The chart `i` at `z` is the point with homogeneous coordinates `homogCoord i z`. -/
theorem chart_eq_pointOfVec (i : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    (projectiveSpaceAnChart.{u} i).toLRSHom.base z =
      pointOfVec.{u} (homogCoord i z) (homogCoord_ne_zero i z) := by
  rw [pointOfVec_eq _ _ i (by simp), dehomogenizeVec_homogCoord]
  rfl

theorem pointOfVec_surjective (x : projectiveSpaceAn.{u} n) :
    ∃ (v : Fin (n + 1) → ℂ) (hv : v ≠ 0), pointOfVec.{u} v hv = x := by
  obtain ⟨i, z, rfl⟩ := exists_mem_range_chart x
  exact ⟨_, _, (chart_eq_pointOfVec i z).symm⟩

theorem pointOfVec_smul (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    pointOfVec.{u} (c • v) (smul_ne_zero hc hv) = pointOfVec.{u} v hv := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  rw [pointOfVec_eq _ _ i hi, pointOfVec_eq _ _ i
    (by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero hc hi),
    ProjectiveSpace.dehomogenizeVec_smul i v hc]

theorem mem_range_chart_pointOfVec_iff (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (j : Fin (n + 1)) :
    pointOfVec.{u} v hv ∈ Set.range (projectiveSpaceAnChart.{u} j).toLRSHom.base ↔ v j ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  rw [pointOfVec_eq _ _ i hi]
  exact chart_dehomogenizeVec_mem_range_iff i j v hi

/-- **Two vectors give the same point of `ℙⁿ_an` iff they are proportional.** -/
theorem pointOfVec_eq_pointOfVec_iff (v w : Fin (n + 1) → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    pointOfVec.{u} v hv = pointOfVec.{u} w hw ↔ ∃ c : ℂ, c ≠ 0 ∧ w = c • v := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    have hwi : w i ≠ 0 := by
      rw [← mem_range_chart_pointOfVec_iff.{u} w hw i, ← h, mem_range_chart_pointOfVec_iff]
      exact hi
    rw [pointOfVec_eq _ _ i hi, pointOfVec_eq _ _ i hwi] at h
    have h' : dehomogenizeVec i v = dehomogenizeVec i w := by
      have := chart_injective i h
      exact congrArg toFin this
    refine ⟨w i / v i, div_ne_zero hwi hi, ?_⟩
    have e1 := insertNth_dehomogenizeVec i v hi
    have e2 := insertNth_dehomogenizeVec i w hwi
    rw [h', e2] at e1
    funext k
    have := congrFun e1 k
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp at this ⊢
    linear_combination this
  · rintro ⟨c, hc, rfl⟩
    exact (pointOfVec_smul v hv hc).symm

lemma pointOfVec_wd (a b : {v : Fin (n + 1) → ℂ // v ≠ 0}) (t : ℂ) (h : a.1 = t • b.1) :
    pointOfVec.{u} a.1 a.2 = pointOfVec.{u} b.1 b.2 := by
  have ht : t ≠ 0 := by rintro rfl; exact a.2 (by simpa using h)
  exact ((pointOfVec_eq_pointOfVec_iff _ _ _ _).2 ⟨t, ht, h⟩).symm

/-- **The points of `ℙⁿ_an` are the lines in `ℂⁿ⁺¹`.** -/
def projectivizationEquiv :
    Projectivization ℂ (Fin (n + 1) → ℂ) ≃ projectiveSpaceAn.{u} n :=
  Equiv.ofBijective
    (Projectivization.lift (fun v ↦ pointOfVec.{u} v.1 v.2) pointOfVec_wd)
    ⟨fun p q h ↦ by
      induction p using Projectivization.ind with | h v hv => ?_
      induction q using Projectivization.ind with | h w hw => ?_
      simp only [Projectivization.lift_mk] at h
      obtain ⟨c, hc, rfl⟩ := (pointOfVec_eq_pointOfVec_iff _ _ _ _).1 h
      exact (Projectivization.mk_eq_mk_iff' ℂ _ _ hv hw).2
        ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩,
    fun x ↦ by
      obtain ⟨v, hv, rfl⟩ := pointOfVec_surjective x
      exact ⟨Projectivization.mk ℂ v hv, Projectivization.lift_mk _ _ _ _⟩⟩

@[simp]
lemma projectivizationEquiv_mk (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    projectivizationEquiv.{u} (Projectivization.mk ℂ v hv) = pointOfVec.{u} v hv :=
  Projectivization.lift_mk (K := ℂ) (fun v ↦ pointOfVec.{u} v.1 v.2) pointOfVec_wd v hv

/-- **The preimage of the intersection `UI I = ⋂_{j ∈ I} U j`** is the intersection of the images
of the charts `j ∈ I`. -/
theorem preimage_UI (I : Finset (Fin (n + 1))) :
    π n ⁻¹' (ProjectiveSpace.UI n (ULift.{u} ℂ) I : Set ℙₒ(n; ULift.{u} ℂ)) =
      ⋂ j ∈ I, Set.range (projectiveSpaceAnChart.{u} j).toLRSHom.base := by
  rw [ProjectiveSpace.UI_eq_iInf]
  ext x
  simp only [TopologicalSpace.Opens.coe_iInf, Set.preimage_iInter, Set.mem_iInter, range_chart,
    Set.mem_preimage]
  refine forall_congr' fun j ↦ ?_
  by_cases hj : j ∈ I
  · rw [iInf_pos hj]
    exact ⟨fun h _ ↦ h, fun h ↦ h hj⟩
  · rw [iInf_neg hj]
    exact iff_of_true trivial fun h ↦ absurd h hj

/-- **The preimage of `UI I` in the chart `i ∈ I`**: it is the image under the chart `i` of the
locus where the homogeneous coordinates `j ∈ I` do not vanish. -/
theorem preimage_UI_eq_image {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} (hi : i ∈ I) :
    π n ⁻¹' (ProjectiveSpace.UI n (ULift.{u} ℂ) I : Set ℙₒ(n; ULift.{u} ℂ)) =
      (projectiveSpaceAnChart.{u} i).toLRSHom.base '' {z | ∀ j ∈ I, homogCoord i z j ≠ 0} := by
  rw [preimage_UI]
  ext x
  simp only [Set.mem_iInter, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := hx i hi
    refine ⟨z, fun j hj ↦ ?_, rfl⟩
    have := hx j hj
    rwa [chart_eq_pointOfVec, mem_range_chart_pointOfVec_iff] at this
  · rintro ⟨z, hz, rfl⟩ j hj
    rw [chart_eq_pointOfVec, mem_range_chart_pointOfVec_iff]
    exact hz j hj

/-! ### Topology: compact, Hausdorff, connected -/

/-- The closed unit polydisc `{z | ∀ k, |zₖ| ≤ 1}` in `ℂⁿ`. -/
def closedUnitPolydisc (n : ℕ) : Set (AnalyticSpace.complexAffineSpace.{u} n) :=
  (Metric.closedBall (0 : ULift.{u} (Fin n) → ℂ) 1 : Set (ULift.{u} (Fin n) → ℂ))

theorem isCompact_closedUnitPolydisc : IsCompact (closedUnitPolydisc.{u} n) :=
  (isCompact_closedBall (0 : ULift.{u} (Fin n) → ℂ) 1 :)

/-- **Every point of `ℙⁿ_an` is the image of a point of the closed unit polydisc** under the chart
of a homogeneous coordinate of maximal modulus. -/
theorem exists_mem_image_closedUnitPolydisc (x : projectiveSpaceAn.{u} n) :
    ∃ i, x ∈ (projectiveSpaceAnChart.{u} i).toLRSHom.base '' closedUnitPolydisc.{u} n := by
  obtain ⟨v, hv, rfl⟩ := pointOfVec_surjective x
  obtain ⟨i, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun k ↦ ‖v k‖)
    Finset.univ_nonempty
  have hi : v i ≠ 0 := by
    intro h0
    refine hv (funext fun k ↦ ?_)
    have := hmax k (Finset.mem_univ k)
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.1 this
  refine ⟨i, ofFin (dehomogenizeVec i v), ?_, (pointOfVec_eq _ _ i hi).symm⟩
  change ((fun k ↦ dehomogenizeVec i v k.down : ULift.{u} (Fin n) → ℂ)) ∈
    (Metric.closedBall (0 : ULift.{u} (Fin n) → ℂ) 1 : Set (ULift.{u} (Fin n) → ℂ))
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro k
  change ‖v (i.succAbove k.down) / v i‖ ≤ 1
  rw [norm_div, div_le_one (norm_pos_iff.2 hi)]
  exact hmax _ (Finset.mem_univ _)

/-- **`ℙⁿ_an` is compact.** -/
instance compactSpace : CompactSpace (projectiveSpaceAn.{u} n) := by
  refine ⟨?_⟩
  have h : (Set.univ : Set (projectiveSpaceAn.{u} n)) = ⋃ i,
      (projectiveSpaceAnChart.{u} i).toLRSHom.base '' closedUnitPolydisc.{u} n :=
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 (exists_mem_image_closedUnitPolydisc x)).symm
  rw [h]
  exact isCompact_iUnion fun i ↦
    isCompact_closedUnitPolydisc.image (isOpenEmbedding_chart i).continuous

lemma continuous_homogCoord (i j : Fin (n + 1)) :
    Continuous fun z : AnalyticSpace.complexAffineSpace.{u} n ↦ homogCoord i z j :=
  (continuous_apply j).comp (Continuous.finInsertNth i continuous_const
    (continuous_pi fun m ↦ continuous_apply (ULift.up m)))

/-- **`ℙⁿ_an` is Hausdorff.** Two points in a common chart are separated there; otherwise, with
`x` in the chart `i` and `y` in the chart `j`, the sets `{|ẑⱼ| < 1}` of the chart `i` and
`{|ŵᵢ| < 1}` of the chart `j` separate them, since on the overlap `ŵᵢ = 1 / ẑⱼ`. -/
instance t2Space : T2Space (projectiveSpaceAn.{u} n) := by
  refine ⟨fun x y hxy ↦ ?_⟩
  by_cases hc : ∃ k, x ∈ Set.range (projectiveSpaceAnChart.{u} k).toLRSHom.base ∧
      y ∈ Set.range (projectiveSpaceAnChart.{u} k).toLRSHom.base
  · obtain ⟨k, ⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hc
    have hab : a ≠ b := fun h ↦ hxy (h ▸ rfl)
    obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hab
    exact ⟨_, _, (isOpenEmbedding_chart k).isOpenMap U hU,
      (isOpenEmbedding_chart k).isOpenMap V hV, ⟨a, haU, rfl⟩, ⟨b, hbV, rfl⟩,
      (Set.disjoint_image_iff (chart_injective k)).2 hUV⟩
  push Not at hc
  obtain ⟨v, hv, rfl⟩ := pointOfVec_surjective x
  obtain ⟨w, hw, rfl⟩ := pointOfVec_surjective y
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  have hwi : w i = 0 := by
    by_contra h
    exact hc i ((mem_range_chart_pointOfVec_iff v hv i).2 hi)
      ((mem_range_chart_pointOfVec_iff w hw i).2 h)
  have hvj : v j = 0 := by
    by_contra h
    exact hc j ((mem_range_chart_pointOfVec_iff v hv j).2 h)
      ((mem_range_chart_pointOfVec_iff w hw j).2 hj)
  refine ⟨(projectiveSpaceAnChart.{u} i).toLRSHom.base ''
      {z | ‖homogCoord i z j‖ < 1},
    (projectiveSpaceAnChart.{u} j).toLRSHom.base '' {z | ‖homogCoord j z i‖ < 1},
    (isOpenEmbedding_chart i).isOpenMap _
      (isOpen_lt (continuous_homogCoord i j).norm continuous_const),
    (isOpenEmbedding_chart j).isOpenMap _
      (isOpen_lt (continuous_homogCoord j i).norm continuous_const),
    ⟨ofFin (dehomogenizeVec i v), ?_, (pointOfVec_eq _ _ i hi).symm⟩,
    ⟨ofFin (dehomogenizeVec j w), ?_, (pointOfVec_eq _ _ j hj).symm⟩, ?_⟩
  · change ‖Fin.insertNth (α := fun _ ↦ ℂ) i 1 (dehomogenizeVec i v) j‖ < 1
    rw [insertNth_dehomogenizeVec i v hi]
    simp [hvj]
  · change ‖Fin.insertNth (α := fun _ ↦ ℂ) j 1 (dehomogenizeVec j w) i‖ < 1
    rw [insertNth_dehomogenizeVec j w hj]
    simp [hwi]
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
  set v' := homogCoord i z with hv'
  have hne : v' ≠ 0 := homogCoord_ne_zero i z
  have hp := chart_eq_pointOfVec i z
  have hv'j : v' j ≠ 0 := by
    rw [← mem_range_chart_pointOfVec_iff v' hne j, ← hp]
    exact ⟨z', hzz'⟩
  rw [hp, pointOfVec_eq _ _ j hv'j] at hzz'
  have hz'' := chart_injective j hzz'
  subst hz''
  change ‖Fin.insertNth (α := fun _ ↦ ℂ) j 1 (dehomogenizeVec j v') i‖ < 1 at hz'
  rw [insertNth_dehomogenizeVec j v' hv'j] at hz'
  simp only [Pi.smul_apply, smul_eq_mul, hv', homogCoord_self, mul_one, norm_inv] at hz'
  change ‖v' j‖ < 1 at hz
  have hpos : 0 < ‖v' j‖ := norm_pos_iff.2 hv'j
  exact absurd hz' (not_lt.2 (one_le_inv₀ hpos |>.2 hz.le))

/-- **`ℙⁿ_an` is connected**: the charts are connected and all contain `[1 : ⋯ : 1]`. -/
instance connectedSpace : ConnectedSpace (projectiveSpaceAn.{u} n) := by
  have h1 : (fun _ ↦ 1 : Fin (n + 1) → ℂ) ≠ 0 := Function.ne_iff.2 ⟨0, one_ne_zero⟩
  haveI : ConnectedSpace (AnalyticSpace.complexAffineSpace.{u} n) :=
    inferInstanceAs (ConnectedSpace (ULift.{u} (Fin n) → ℂ))
  rw [connectedSpace_iff_univ]
  refine ⟨⟨pointOfVec.{u} _ h1, trivial⟩, ?_⟩
  rw [← iUnion_range_chart]
  exact isPreconnected_iUnion ⟨pointOfVec.{u} _ h1, Set.mem_iInter.2 fun i ↦
      (mem_range_chart_pointOfVec_iff _ h1 i).2 one_ne_zero⟩
    fun i ↦ (isConnected_range (isOpenEmbedding_chart i).continuous).isPreconnected

end projectiveSpaceAn

end

end ComplexAnalytic

end
