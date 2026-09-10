/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.Glue
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex

/-!
# R4 — the PoU-localized area-integral functional and the chart-relocation lemma

Step 4 of the Forster §17.3 fine-sheaf residue construction (S3 scoping §2.2/§4.R4, lane R of
`docs/planning/CAMPAIGN_KEYSTONE.md`): integrate a `(1,1)` chart-coefficient family over the
surface, chart by chart, weighted by the partition of unity — and prove that the integral reads
each overlap **chart-independently**, because the Lebesgue area Jacobian of a holomorphic chart
transition is exactly the `normSq φ′` factor of R1's `(1,1)` overlap law `OneOneLawAt`.

* `pouCoeff 𝔇 j` — the chart-pushed PoU weight `ρ̃_j := ρ_j ∘ (chart j).symm`, cut off (by a
  `Set.indicator` over the chart image of `U j`) so it is a *globally* smooth compactly supported
  planar function: off the chart image of `tsupport ρ_j` it vanishes identically, killing the
  junk values of `(chart j).symm` outside the chart target.
* `resIntegralFun` / `resIntegral` — the integral functional

    `I(t) := ∑_j ∫_ℂ ρ̃_j · t_j ∂volume`,

  packaged as a ℂ-linear map `oneOneCoeff 𝔇 →ₗ[ℂ] ℂ` (the Submodule structure of R1 supplies the
  domain; additivity uses the integrability of each summand, `integrable_pouCoeff_mul`, which is
  compact support of the weight × continuity of the coefficient).
* `resFunctional := resNormalization • resIntegral 𝔇` — the residue-normalized functional.  The
  constant is **cited from R0** (`SignTest.resNormalization = −π⁻¹`), not re-derived.
* `setIntegral_image_holomorphic` — the planar change-of-variables atom: for `φ` holomorphic and
  injective on a measurable `s`,

    `∫_{φ '' s} u = ∫_s normSq φ′ · (u ∘ φ)`,

  from `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` with the ℝ-determinant of
  the ℂ-linear derivative computed by `LinearMap.det_restrictScalars` +
  `Algebra.norm_complex_apply` (`det_complexToReal_smul_one`).
* `setIntegral_overlap_relocate` — **the R4 chart-relocation lemma**: for `t ∈ oneOneCoeff 𝔇`
  and any global weight `f : X → ℂ`,

    `∫_{chart-j image of U_j∩U_k} (f ∘ (chart j).symm) · t_j
       = ∫_{chart-k image of U_j∩U_k} (f ∘ (chart k).symm) · t_k`

  — the integral functional does not care which chart reads an overlap.  The Jacobian factor
  produced by the change of variables is literally the `normSq φ′` of `OneOneLawAt` (this is what
  R1 was designed for).

R5 (coboundary Stokes) consumes `resIntegral`, `setIntegral_overlap_relocate`, and the planar
`∫ ∂̄g = 0` atom; R6 (the Mittag–Leffler tie) evaluates `resFunctional` on the bump-cutoff
simple-pole datum via `DbarDisk.cauchyPompeiu_area`, against the **pinned** R0 normalization.
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

-- Same permissive transparency as `RealForms`/`DolbeaultComparisonInverse`/`PoUSplit` (the
-- `SmoothCFunctions` coercions of `rhoC` below need it).
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### The chart-pushed PoU weight -/

/-- The **chart-pushed PoU weight** `ρ̃_j`: the chart-`j` read of the fixed subordinate PoU
weight `ρ_j = rhoC 𝔇 j` (the reused `DolbeaultComparisonInverse` backbone), cut off by the
indicator of the chart image of `U j`.  The cutoff makes the global planar stand-in honest:
`(chart j).symm` has junk values outside the chart target, but `tsupport ρ_j ⊆ U j`
(subordination) means the indicator only ever removes points where the true weight is `0`
(`pouCoeff_eq_zero_of_notMem_image_tsupport`), so `ρ̃_j` is globally smooth
(`contDiff_pouCoeff`) and compactly supported (`hasCompactSupport_pouCoeff`). -/
noncomputable def pouCoeff (j : 𝔇.toFiniteCover.ι) : ℂ → ℂ :=
  (chartMap 𝔇 j '' (𝔇.U j : Set X)).indicator
    fun z => rhoC 𝔇 j ((chartAt ℂ (𝔇.center j)).symm z)

/-- On the chart image of `U j`, the chart-pushed weight is the weight: `ρ̃_j (chart j x) = ρ_j x`
for `x ∈ U j`. -/
theorem pouCoeff_chartMap {j : 𝔇.toFiniteCover.ι} {x : X} (hx : x ∈ (𝔇.U j : Set X)) :
    pouCoeff 𝔇 j (chartMap 𝔇 j x) = rhoC 𝔇 j x := by
  have hmem : chartMap 𝔇 j x ∈ chartMap 𝔇 j '' (𝔇.U j : Set X) := ⟨x, hx, rfl⟩
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
    (chartAt ℂ (𝔇.center j)).left_inv (mem_chartSource_of_mem_U 𝔇 hx)
  rw [pouCoeff, Set.indicator_of_mem hmem, hli]

/-- Off the chart image of `tsupport ρ_j`, the chart-pushed weight vanishes — both off the chart
image of `U j` (indicator) and on it (the weight itself vanishes off its support). -/
theorem pouCoeff_eq_zero_of_notMem_image_tsupport {j : 𝔇.toFiniteCover.ι} {z : ℂ}
    (hz : z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j)) : pouCoeff 𝔇 j z = 0 := by
  by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
  · obtain ⟨x, hxU, rfl⟩ := hzU
    have hxn : x ∉ tsupport (cechPoU 𝔇 j) := fun hx => hz ⟨x, hx, rfl⟩
    have hmem : chartMap 𝔇 j x ∈ chartMap 𝔇 j '' (𝔇.U j : Set X) := ⟨x, hxU, rfl⟩
    have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt ℂ (𝔇.center j)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
    rw [pouCoeff, Set.indicator_of_mem hmem, hli]
    simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hxn]
    rfl
  · exact Set.indicator_of_notMem hzU _

/-- The chart image of `tsupport ρ_j` is compact (closed subset of the compact `X`, pushed
through the chart, which is continuous on its source `⊇ U j ⊇ tsupport ρ_j`). -/
theorem isCompact_image_tsupport_cechPoU (j : 𝔇.toFiniteCover.ι) :
    IsCompact (chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j)) := by
  have hts : IsCompact (tsupport (cechPoU 𝔇 j)) :=
    (isClosed_tsupport (cechPoU 𝔇 j)).isCompact
  refine hts.image_of_continuousOn ?_
  refine (chartAt ℂ (𝔇.center j)).continuousOn.mono fun x hx => ?_
  exact mem_chartSource_of_mem_U 𝔇 (cechPoU_subordinate 𝔇 j hx)

/-- The chart-pushed PoU weight is compactly supported. -/
theorem hasCompactSupport_pouCoeff (j : 𝔇.toFiniteCover.ι) :
    HasCompactSupport (pouCoeff 𝔇 j) :=
  HasCompactSupport.intro (isCompact_image_tsupport_cechPoU 𝔇 j) fun _ hz =>
    pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz

omit [Nonempty X] in
/-- The chart image of an open subset of `U j` is open (the chart is a partial homeomorphism and
`U j` lies in its source). -/
theorem isOpen_chartMap_image (j : 𝔇.toFiniteCover.ι) {s : Set X} (hs : IsOpen s)
    (hsub : s ⊆ (𝔇.U j : Set X)) : IsOpen (chartMap 𝔇 j '' s) :=
  (chartAt ℂ (𝔇.center j)).isOpen_image_of_subset_source hs
    fun _ hx => mem_chartSource_of_mem_U 𝔇 (hsub hx)

/-- **Global smoothness of the chart-pushed PoU weight.**  On the (open) chart image of `U j` it
is the chart read of the smooth `ρ_j`; off the (compact, hence closed) chart image of
`tsupport ρ_j` it vanishes identically — and the two open sets cover `ℂ`. -/
theorem contDiff_pouCoeff (j : 𝔇.toFiniteCover.ι) :
    ContDiff ℝ (⊤ : ℕ∞) (pouCoeff 𝔇 j) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j)
  · -- chart image of a support point: smooth chart read of `rhoC`
    obtain ⟨x, hxs, rfl⟩ := hz
    have hxU : x ∈ (𝔇.U j : Set X) := cechPoU_subordinate 𝔇 j hxs
    have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
    have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
      (chartAt ℂ (𝔇.center j)).map_source hxsrc
    have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartAt ℂ (𝔇.center j)).symm
        (chartMap 𝔇 j x) :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := 𝔇.center j) _
        hzt).contMDiffAt ((chartAt ℂ (𝔇.center j)).open_target.mem_nhds hzt)
    have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt ℂ (𝔇.center j)).left_inv hxsrc
    have hρ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (rhoC 𝔇 j)
        ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
      rw [hli]
      exact (rhoC 𝔇 j).contMDiff x
    have hread : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => rhoC 𝔇 j ((chartAt ℂ (𝔇.center j)).symm w)) (chartMap 𝔇 j x) :=
      contMDiffAt_iff_contDiffAt.1 (hρ.comp (chartMap 𝔇 j x) hsymm)
    refine hread.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_chartMap_image 𝔇 j (𝔇.U j).isOpen (subset_refl _)).mem_nhds
      ⟨x, hxU, rfl⟩] with w hw
    exact Set.indicator_of_mem hw _
  · -- off the compact image of the support: locally identically zero
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇 j).isClosed.isOpen_compl.mem_nhds hz]
      with w hw
    exact pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hw

/-! ### Integrability of the weighted coefficients -/

/-- The weighted integrand `ρ̃_j · t_j` of a `(1,1)` coefficient family is continuous: on the
chart image of `U j` both factors are (the coefficient by `IsOneOneCoeff`), and off the chart
image of `tsupport ρ_j` the weight kills the coefficient's junk values. -/
theorem continuous_pouCoeff_mul {t : 𝔇.toFiniteCover.ι → ℂ → ℂ} (ht : IsOneOneCoeff 𝔇 t)
    (j : 𝔇.toFiniteCover.ι) : Continuous fun z => pouCoeff 𝔇 j z * t j z := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
  · obtain ⟨x, hxU, rfl⟩ := hz
    exact ((contDiff_pouCoeff 𝔇 j).continuous.continuousAt).mul
      (ht.1 j x hxU).continuousAt
  · have hzs : z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j) := fun hc =>
      hz (Set.image_mono (fun y hy => cechPoU_subordinate 𝔇 j hy) hc)
    have hev : (fun w => pouCoeff 𝔇 j w * t j w) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇
        j).isClosed.isOpen_compl.mem_nhds hzs] with w hw
      rw [pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hw, zero_mul]
    exact continuousAt_const.congr hev.symm

/-- **Well-definedness of the R4 summands**: each `ρ̃_j · t_j` is integrable on `ℂ` (continuous
with compact support — the support of the weight). -/
theorem integrable_pouCoeff_mul {t : 𝔇.toFiniteCover.ι → ℂ → ℂ} (ht : IsOneOneCoeff 𝔇 t)
    (j : 𝔇.toFiniteCover.ι) : Integrable fun z => pouCoeff 𝔇 j z * t j z :=
  (continuous_pouCoeff_mul 𝔇 ht j).integrable_of_hasCompactSupport
    ((hasCompactSupport_pouCoeff 𝔇 j).mul_right)

/-! ### The integral functional -/

/-- The raw (unnormalized) **fine-sheaf surface integral** of a chart-coefficient family:

  `I(t) := ∑_j ∫_ℂ ρ̃_j · t_j ∂volume`

— the chart-coefficient incarnation of `∬_X τ` for the `(1,1)`-form `τ` presented by `t`
(S3 scoping §2.2).  Meaningful (finite, chart-relocation-invariant) on `oneOneCoeff 𝔇`
members; see `resIntegral` for the bundled linear map. -/
noncomputable def resIntegralFun (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) : ℂ :=
  ∑ j, ∫ z, pouCoeff 𝔇 j z * t j z

/-- **The R4 integral functional**: `resIntegralFun` as a ℂ-linear map on the `(1,1)`
chart-coefficient submodule (the domain R1's `Submodule` structure supplies for free).
Additivity needs the integrability of each summand (`integrable_pouCoeff_mul`); homogeneity is
unconditional. -/
noncomputable def resIntegral : oneOneCoeff 𝔇 →ₗ[ℂ] ℂ where
  toFun t := resIntegralFun 𝔇 (t : 𝔇.toFiniteCover.ι → ℂ → ℂ)
  map_add' s t := by
    simp only [resIntegralFun, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfun : (fun z => pouCoeff 𝔇 j z * (((s + t) : oneOneCoeff 𝔇) :
          𝔇.toFiniteCover.ι → ℂ → ℂ) j z)
        = fun z => pouCoeff 𝔇 j z * (s : 𝔇.toFiniteCover.ι → ℂ → ℂ) j z
            + pouCoeff 𝔇 j z * (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) j z := by
      funext z
      simp only [Submodule.coe_add, Pi.add_apply]
      ring
    rw [hfun, integral_add (integrable_pouCoeff_mul 𝔇 s.2 j)
      (integrable_pouCoeff_mul 𝔇 t.2 j)]
  map_smul' a t := by
    simp only [resIntegralFun, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfun : (fun z => pouCoeff 𝔇 j z * (((a • t) : oneOneCoeff 𝔇) :
          𝔇.toFiniteCover.ι → ℂ → ℂ) j z)
        = fun z => a * (pouCoeff 𝔇 j z * (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) j z) := by
      funext z
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, integral_const_mul]

@[simp] theorem resIntegral_apply (t : oneOneCoeff 𝔇) :
    resIntegral 𝔇 t = ∑ j, ∫ z, pouCoeff 𝔇 j z * (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) j z := rfl

/-- **The normalized fine-sheaf residue functional**: `resNormalization • resIntegral 𝔇`, with
the constant `resNormalization = −π⁻¹` **cited from R0** (`SignTest.lean`, the pinned
sign/normalization gate — do not re-derive).  On the smeared residue-`1` simple-pole model datum
this evaluates to `+1` (`resNormalization_integral_eq_one`); R6 will evaluate it on genuine
Mittag–Leffler data via `DbarDisk.cauchyPompeiu_area`. -/
noncomputable def resFunctional : oneOneCoeff 𝔇 →ₗ[ℂ] ℂ :=
  resNormalization • resIntegral 𝔇

theorem resFunctional_apply (t : oneOneCoeff 𝔇) :
    resFunctional 𝔇 t = resNormalization * resIntegral 𝔇 t := rfl

/-! ### The planar holomorphic change-of-variables atom -/

/-- The ℝ-determinant of (the real restriction of) multiplication by `c : ℂ` is `normSq c` — the
area Jacobian of a holomorphic map is the `normSq` of its complex derivative.  Computed through
`LinearMap.det_restrictScalars` (`det_ℝ = Norm_{ℂ/ℝ} ∘ det_ℂ`) and `Algebra.norm_complex_apply`
(`Norm_{ℂ/ℝ} = normSq`), exactly the route inventoried in the S3 scoping §2.2. -/
theorem det_complexToReal_smul_one (c : ℂ) :
    (c • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq c := by
  have hlin : ((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ)
      = (c • (1 : ℂ →ₗ[ℂ] ℂ)).restrictScalars ℝ := by
    ext w
    simp
  have h1 : (c • (1 : ℂ →L[ℝ] ℂ)).det
      = LinearMap.det ((c • (1 : ℂ →ₗ[ℂ] ℂ)).restrictScalars ℝ) := by
    rw [← hlin]
    rfl
  have h2 : LinearMap.det (c • (1 : ℂ →ₗ[ℂ] ℂ)) = c := by
    simp
  rw [h1, LinearMap.det_restrictScalars, h2, Algebra.norm_complex_apply]

/-- **Planar holomorphic change of variables**: for `φ` holomorphic and injective on a measurable
`s ⊆ ℂ` and any `u : ℂ → ℂ`,

  `∫_{φ '' s} u = ∫_s normSq φ′ · (u ∘ φ)`.

This is `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` with the ℝ-Jacobian
`|det_ℝ Dφ| = normSq φ′` computed by `det_complexToReal_smul_one` — the factor matching R1's
`OneOneLawAt` on the nose.  No integrability hypotheses: the Mathlib theorem is unconditional. -/
theorem setIntegral_image_holomorphic {φ : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hφ : ∀ z ∈ s, DifferentiableAt ℂ φ z) (hinj : Set.InjOn φ s) (u : ℂ → ℂ) :
    ∫ w in φ '' s, u w = ∫ z in s, (Complex.normSq (deriv φ z) : ℂ) * u (φ z) := by
  have hder : ∀ z ∈ s, HasFDerivWithinAt φ (deriv φ z • (1 : ℂ →L[ℝ] ℂ)) s z := fun z hz =>
    ((hφ z hz).hasDerivAt.complexToReal_fderiv).hasFDerivWithinAt
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume hs hder hinj u]
  refine MeasureTheory.setIntegral_congr_fun hs fun z _ => ?_
  rw [det_complexToReal_smul_one, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.real_smul]

/-! ### Overlap chart images and the relocation lemma -/

/-- The chart-`j` image of the overlap `U j ⊓ U k` — the planar set over which chart `j` reads
the overlap. -/
def overlapImage (j k : 𝔇.toFiniteCover.ι) : Set ℂ :=
  chartMap 𝔇 j '' ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X)

omit [Nonempty X] in
theorem isOpen_overlapImage (j k : 𝔇.toFiniteCover.ι) : IsOpen (overlapImage 𝔇 j k) :=
  isOpen_chartMap_image 𝔇 j (𝔇.U j ⊓ 𝔇.U k).isOpen fun _ hx => hx.1

omit [Nonempty X] in
/-- The transition `φ_{jk}` carries the chart-`j` read of the overlap onto the chart-`k` read
(pointwise relocation `transitionMap_chartMap`, plus commutativity of the overlap). -/
theorem transitionMap_image_overlapImage (j k : 𝔇.toFiniteCover.ι) :
    transitionMap 𝔇 j k '' overlapImage 𝔇 j k = overlapImage 𝔇 k j := by
  rw [overlapImage, overlapImage, Set.image_image]
  rw [Set.image_congr fun x (hx : x ∈ ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X)) =>
    transitionMap_chartMap 𝔇 (k := k) hx.1]
  congr 1
  ext x
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

omit [Nonempty X] in
/-- The transition is injective on the chart-`j` read of the overlap (it relocates to chart-`k`
coordinates, and charts are injective on their sources). -/
theorem injOn_transitionMap_overlapImage (j k : 𝔇.toFiniteCover.ι) :
    Set.InjOn (transitionMap 𝔇 j k) (overlapImage 𝔇 j k) := by
  rintro z ⟨x, hx, rfl⟩ z' ⟨x', hx', rfl⟩ h
  rw [transitionMap_chartMap 𝔇 hx.1, transitionMap_chartMap 𝔇 hx'.1] at h
  rw [(chartAt ℂ (𝔇.center k)).injOn (mem_chartSource_of_mem_U 𝔇 hx.2)
    (mem_chartSource_of_mem_U 𝔇 hx'.2) h]

omit [Nonempty X] in
/-- **R4 chart-relocation lemma.**  The weighted overlap integral of a `(1,1)` chart-coefficient
family is independent of which chart reads the overlap: for `t ∈ oneOneCoeff 𝔇` (only the
`IsOneOneCoeff` predicate is consumed) and any global weight `f : X → ℂ`,

  `∫_{overlapImage j k} (f ∘ (chart j).symm) · t_j = ∫_{overlapImage k j} (f ∘ (chart k).symm) · t_k`.

Proof: change variables through the holomorphic injective transition `φ_{jk}`
(`setIntegral_image_holomorphic`); the area Jacobian `normSq φ′` is **exactly** the factor of
R1's overlap law `OneOneLawAt` (evaluated pointwise on the open overlap image via
`Eventually.self_of_nhds`), and the weight reads the same surface point through either chart.
This is the lemma that makes `resIntegral` a functional of the underlying `(1,1)`-form rather
than of its chart presentation; R5 uses it to re-route PoU-weighted integrals between charts. -/
theorem setIntegral_overlap_relocate {t : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (ht : IsOneOneCoeff 𝔇 t) (j k : 𝔇.toFiniteCover.ι) (f : X → ℂ) :
    ∫ z in overlapImage 𝔇 j k, f ((chartAt ℂ (𝔇.center j)).symm z) * t j z
      = ∫ w in overlapImage 𝔇 k j, f ((chartAt ℂ (𝔇.center k)).symm w) * t k w := by
  have hs : MeasurableSet (overlapImage 𝔇 j k) :=
    (isOpen_overlapImage 𝔇 j k).measurableSet
  have hφ : ∀ z ∈ overlapImage 𝔇 j k, DifferentiableAt ℂ (transitionMap 𝔇 j k) z := by
    rintro z ⟨x, hx, rfl⟩
    exact (transitionMap_analyticAt 𝔇 hx.1 hx.2).differentiableAt
  have hcov := setIntegral_image_holomorphic (φ := transitionMap 𝔇 j k) hs hφ
    (injOn_transitionMap_overlapImage 𝔇 j k)
    fun w => f ((chartAt ℂ (𝔇.center k)).symm w) * t k w
  rw [← transitionMap_image_overlapImage 𝔇 j k, hcov]
  refine MeasureTheory.setIntegral_congr_fun hs ?_
  rintro z ⟨x, hx, rfl⟩
  dsimp only
  have hxj : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
    (chartAt ℂ (𝔇.center j)).left_inv (mem_chartSource_of_mem_U 𝔇 hx.1)
  have hφx : transitionMap 𝔇 j k (chartMap 𝔇 j x) = chartMap 𝔇 k x :=
    transitionMap_chartMap 𝔇 hx.1
  have hxk : (chartAt ℂ (𝔇.center k)).symm (transitionMap 𝔇 j k (chartMap 𝔇 j x)) = x := by
    rw [hφx]
    exact (chartAt ℂ (𝔇.center k)).left_inv (mem_chartSource_of_mem_U 𝔇 hx.2)
  have hlaw := (ht.2 j k x hx).self_of_nhds
  rw [hxj, hxk, hlaw]
  ring

omit [Nonempty X] in
/-- Unweighted form of the relocation lemma (`f = 1`): the raw overlap integral of a `(1,1)`
family is chart-independent. -/
theorem setIntegral_overlap_relocate' {t : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (ht : IsOneOneCoeff 𝔇 t) (j k : 𝔇.toFiniteCover.ι) :
    ∫ z in overlapImage 𝔇 j k, t j z = ∫ w in overlapImage 𝔇 k j, t k w := by
  have h := setIntegral_overlap_relocate 𝔇 ht j k fun _ => (1 : ℂ)
  simpa using h

end Jacobians.Dolbeault.FineResidue
