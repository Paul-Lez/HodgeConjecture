/-
  **Removable singularity for meromorphic 1-forms** (Forster §17.4, the reverse of `holToMeroₗ`).

  Gate (C)'s one isolated analytic gap: a meromorphic 1-form `α` with `formOrderW α ≥ 0` everywhere
  (i.e. `α ∈ omegaD 0`) is — modulo the removable-singularity germ-junk — a genuine *holomorphic*
  1-form.  This is the reverse map `Ω_0 → HolomorphicOneForms` inverse to the injection
  `holToMeroₗ : HolomorphicOneForms ↪ Ω_0` (`MeromorphicOneFormSystem.lean`), giving the §17.4
  equality `omegaDim 0 = kirovGenus X` UNCONDITIONALLY and `FiniteDimensional ℂ (omegaDModule 0)`.

  ## The math

  `α ∈ omegaD 0` means the chart coefficient `formCoeff α.toFun x` is `MeromorphicAt` with
  `meromorphicOrderAt ≥ 0` at `chart x x`, for every `x`.  Order `≥ 0` means the coefficient germ
  agrees, off `x`, with an **analytic** function (`exists_analyticAt_eventuallyEq_…`, the standard
  removable singularity).  We repair `α.toFun` to its analytic value:

  * `repairedCoeff α x₀` is the normal-form `toMeromorphicNFAt` of `localRep`'s pullback — analytic
    on the chart target, and equal to `localRep α.toFun` off the (removed) singular points.
  * `repairedSection α` is the genuine bundle section `y ↦ repaired-coefficient • frame`, smooth
    because its chart pullback is analytic (the section-assembly lemma `holOfLocalRepAnalytic`,
    extracted from the Montel completeness reconstruction `contMDiffOn_totalSpaceMk_L_inner`).

  This `repairedSection α : HolomorphicOneForms X` has `holToMero (repairedSection α)` germ-equal to
  `α` (they agree off the singular points), so `holToOmega0Module` is **surjective**.  With its
  proven injectivity (`holToOmega0Module_injective`) this is a `LinearEquiv`
  `HolomorphicOneForms X ≃ₗ omegaDModule 0`, whence:

  * `FiniteDimensional ℂ (omegaDModule 0)` (transported from `HolomorphicOneForms`, finite-dim);
  * `omegaDim 0 = kirovGenus X` (the §17.4 equality, both directions now proven).

  Chaining with `CanonicalForm17Data.hKgenus` (`CanonicalFormIso.lean`) makes the Serre-duality
  input `lDim K = kirovGenus X` UNCONDITIONAL.

  Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4; Mathlib's
  `MeromorphicAt.analyticAt` / `toMeromorphicNFAt` removable singularity.
-/
import KirovDolbeault.Dolbeault.CanonicalFormDifferential
import KirovDolbeault.Montel

open scoped Manifold ContDiff Topology Bundle
open Module Filter
open Jacobians.Montel

namespace Jacobians.Dolbeault

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1: the section-assembly lemma

The converse of `Montel.localRep_analyticOn_chartTarget`: a bundle section `L` whose chart pullback
`z ↦ L ((chart x₀).symm z) (e.symmL ℂ … 1)` is `AnalyticOn (chart x₀).target` for every chart center
`x₀` is a smooth section, hence a `HolomorphicOneForms X`.

The proof mirrors `Montel.contMDiffOn_totalSpaceMk_L_inner` (the smooth-from-analytic half of the
Montel completeness reconstruction), but feeds analyticity directly (no sequence limit) and works on
the full chart source, so smoothness at any `y` is read in `y`'s own chart. -/

/-- **Scalar smoothness from chart-pullback analyticity** on an open subset `S` of the chart source.
If the chart pullback is analytic on `chart x₀ '' S`, then the scalar `y ↦ L y (e.symmL ℂ y 1)` is
`ContMDiffOn ω` on `S`.  The inverse of `localRep_analyticOn_chartTarget`; the argument is
`Montel.contMDiffOn_limit_inner` with `S` in place of `innerChartOpen`. -/
theorem contMDiffOn_scalar_of_pullback_analyticOn
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y) (x₀ : X)
    {S : Set X} (hSopen : IsOpen S) (hSsub : S ⊆ (chartAt ℂ x₀).source)
    (hAn : letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        ((chartAt ℂ x₀) '' S)) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun y : X => L y (e.symmL ℂ y 1)) S := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  have hs : S ⊆ (extChartAt 𝓘(ℂ, ℂ) x₀).source := by
    have : (extChartAt 𝓘(ℂ, ℂ) x₀).source = (chartAt ℂ x₀).source := by simp [extChartAt]
    rw [this]; exact hSsub
  have h2s : Set.MapsTo (fun y : X => L y (e.symmL ℂ y 1))
      S (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source := by
    have h_src : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source = Set.univ := by simp [extChartAt]
    rw [h_src]; exact fun _ _ => Set.mem_univ _
  rw [contMDiffOn_iff_of_subset_source' hs h2s]
  have h_set_eq : extChartAt 𝓘(ℂ, ℂ) x₀ '' S = (chartAt ℂ x₀) '' S := by simp [extChartAt]
  have h_fun_eq : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ) ∘
      (fun y : X => L y (e.symmL ℂ y 1)) ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm) =
      fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1) := by
    funext z; simp [extChartAt, Function.comp_def]
  rw [h_set_eq, h_fun_eq]
  have hSimg_open : IsOpen ((chartAt ℂ x₀) '' S) :=
    (chartAt ℂ x₀).isOpen_image_iff_of_subset_source hSsub |>.mpr hSopen
  exact (contDiffOn_omega_iff_analyticOn hSimg_open.uniqueDiffOn).mpr hAn

/-- **Section smoothness from chart-pullback analyticity** on an open subset `S` of the chart source.
The bundle-section `y ↦ (y, L y)` is `ContMDiffOn ω` on `S`.  This is
`Montel.contMDiffOn_totalSpaceMk_L_inner` re-derived on an arbitrary open `S ⊆ (chart x₀).source`. -/
theorem contMDiffOn_totalSpaceMk_of_pullback_analyticOn
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y) (x₀ : X)
    {S : Set X} (hSopen : IsOpen S) (hSsub : S ⊆ (chartAt ℂ x₀).source)
    (hAn : letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        ((chartAt ℂ x₀) '' S)) :
    ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)
        y (L y))
      S := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he_def
  have h_scalar : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun y : X => L y (e.symmL ℂ y 1)) S :=
    contMDiffOn_scalar_of_pullback_analyticOn L x₀ hSopen hSsub hAn
  set eHom := trivializationAt (ℂ →L[ℂ] ℂ)
    (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) x₀ with heHom_def
  have h_src_sub_hom : S ⊆ eHom.baseSet := by
    intro y hy
    rw [heHom_def, hom_trivializationAt_baseSet]
    refine ⟨?_tangent, Set.mem_univ _⟩
    rw [TangentBundle.trivializationAt_baseSet]
    exact hSsub hy
  intro y₀ hy₀
  rw [Bundle.Trivialization.contMDiffWithinAt_section _ (h_src_sub_hom hy₀)]
  have h_simpl : ∀ y ∈ S,
      (eHom (Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (L y))).2 =
        (L y (e.symmL ℂ y 1)) • (ContinuousLinearMap.id ℂ ℂ) := by
    intro y hy
    rw [heHom_def, hom_trivializationAt_apply]
    apply ContinuousLinearMap.ext
    intro v
    have h_triv_id : Bundle.Trivialization.continuousLinearMapAt ℂ
        (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀) y = ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ X ℂ y
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp',
               Function.comp_apply, h_triv_id, ContinuousLinearMap.id_apply,
               ContinuousLinearMap.smul_apply]
    have hv : (v : ℂ) = v • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [hv, (e.symmL ℂ y).map_smul]
    rw [(L y).map_smul]
    simp only [smul_eq_mul]; ring
  have h_smul_smooth : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y : X => (L y (e.symmL ℂ y 1)) • (ContinuousLinearMap.id ℂ ℂ))
      S y₀ :=
    (h_scalar y₀ hy₀).smul contMDiffWithinAt_const
  exact h_smul_smooth.congr (fun y hy => h_simpl y hy) (h_simpl y₀ hy₀)

/-- **The section-assembly lemma, local form.**  A bundle section `L` whose chart pullback in *each
point's own chart* is `AnalyticAt` the chart centre is `ContMDiff`, hence a `HolomorphicOneForms X`.
Smoothness at `y` is read in `y`'s own chart: `AnalyticAt` gives analyticity on an open neighbourhood
of `chart y y`, whose chart-preimage is an open neighbourhood of `y`. -/
noncomputable def holOfLocalRepAnalyticAt
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hAn : ∀ x₀ : X,
      letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticAt ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        ((chartAt ℂ x₀) x₀)) :
    HolomorphicOneForms X where
  toFun := L
  contMDiff_toFun := by
    intro y
    set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y
    -- `AnalyticAt` ⇒ analytic on an open ball `U := ball (chart y y) r` around `chart y y`.
    obtain ⟨r, hr, hUan⟩ := (hAn y).exists_ball_analyticOnNhd
    set U : Set ℂ := Metric.ball ((chartAt ℂ y) y) r with hU_def
    have hUopen : IsOpen U := Metric.isOpen_ball
    have hUmem : (chartAt ℂ y) y ∈ U := Metric.mem_ball_self hr
    -- restrict to the chart source ∩ chart⁻¹ U, an open nbhd of `y`.
    set S : Set X := (chartAt ℂ y).source ∩ (chartAt ℂ y) ⁻¹' U with hS_def
    have hSopen : IsOpen S :=
      (chartAt ℂ y).continuousOn.isOpen_inter_preimage (chartAt ℂ y).open_source hUopen
    have hSsub : S ⊆ (chartAt ℂ y).source := Set.inter_subset_left
    have hyS : y ∈ S := ⟨mem_chart_source ℂ y, by
      simp only [Set.mem_preimage]; exact hUmem⟩
    -- pullback analytic on `chart y '' S ⊆ U`.
    have himg : (chartAt ℂ y) '' S ⊆ U := by
      rintro z ⟨w, hw, rfl⟩; exact hw.2
    have hAnS : AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ y).symm z) (e.symmL ℂ ((chartAt ℂ y).symm z) 1))
        ((chartAt ℂ y) '' S) := (hUan.mono himg).analyticOn
    have h_on := contMDiffOn_totalSpaceMk_of_pullback_analyticOn L y hSopen hSsub hAnS
    exact (h_on y hyS).contMDiffAt (hSopen.mem_nhds hyS)

@[simp] theorem holOfLocalRepAnalyticAt_toFun
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hAn : ∀ x₀ : X,
      letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticAt ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        ((chartAt ℂ x₀) x₀)) :
    (holOfLocalRepAnalyticAt L hAn).toFun = L := rfl

/-! ## Part 2: the repaired holomorphic section of an order-`≥ 0` meromorphic 1-form

For `α ∈ omegaD 0`, the chart coefficient `formCoeff α.toFun x` is `MeromorphicAt` with order `≥ 0`
at every chart centre.  We repair the section to its analytic value.

The single key structural fact is that the removable-singularity *junk* of `α.toFun` is isolated to
chart centres: for `w` in a *punctured* neighbourhood of any `x₀`, the covector `α.toFun w` is pinned
by `α`'s meromorphy at `x₀` (`toFun_eq_localRep_smul`), so reading it in `w`'s own chart it equals the
analytic normal-form value (`repVal`).  Hence the per-point repair `repairedSection` is a genuine
holomorphic section whose germ matches `α` everywhere off the centres. -/

/-- `formCoeff` subtracts (combining `formCoeff_add` and `formCoeff_neg`). -/
theorem formCoeff_sub (σ τ : ∀ x, FormFiber X x) (x : X) :
    formCoeff (σ - τ) x = formCoeff σ x - formCoeff τ x := by
  rw [sub_eq_add_neg, formCoeff_add, formCoeff_neg, sub_eq_add_neg]

/-- The frame covector at `y` from the canonical tangent trivialisation: `φ_y : T_y X →L[ℂ] ℂ`. -/
noncomputable def frameCovector (y : X) : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ :=
  letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y
  (e.continuousLinearEquivAt ℂ y (by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source ℂ y) :
    TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ)

/-- `φ_y (e_y.symmL ℂ y 1) = 1`: the frame covector evaluated on the canonical frame vector. -/
theorem frameCovector_symmL_self (y : X) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y
    frameCovector y (e.symmL ℂ y 1) = 1 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y
  have hy : y ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source ℂ y
  set φ := e.continuousLinearEquivAt ℂ y hy with hφ
  show φ (e.symmL ℂ y 1) = 1
  have h_symmL : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) = e.symmL ℂ y :=
    Bundle.Trivialization.symm_continuousLinearEquivAt_eq' e hy
  rw [show e.symmL ℂ y 1 = (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1 from by rw [h_symmL]]
  exact φ.apply_symm_apply 1

/-- The **repaired chart value** of `α` at `y`: the normal-form value of the chart coefficient at the
chart centre — the removable-singularity limit `lim_{z → chart y y} formCoeff α.toFun y (z)`. -/
noncomputable def repVal (α : MeromorphicOneForm X) (y : X) : ℂ :=
  toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y) ((chartAt ℂ y) y)

/-- The repaired chart coefficient `toMeromorphicNFAt (formCoeff α.toFun y) (chart y y)` is
`AnalyticAt (chart y y)` when `α ∈ omegaD 0` (order `≥ 0` ⟹ removable singularity).  Reuses the
repo's `exists_analyticAt_eventuallyEq_of_meromorphicOrderAt_nonneg`. -/
theorem analyticAt_repairedCoeff {α : MeromorphicOneForm X} (hα : α ∈ omegaD (X := X) 0) (y : X) :
    AnalyticAt ℂ (toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y)) ((chartAt ℂ y) y) := by
  have hmero : MeromorphicAt (formCoeff α.toFun y) ((chartAt ℂ y) y) := α.meromorphic y
  have hord : 0 ≤ meromorphicOrderAt (formCoeff α.toFun y) ((chartAt ℂ y) y) := by
    have := hα y
    simpa [MeromorphicOneForm.formOrderW] using this
  have hNF : MeromorphicNFAt (toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y))
      ((chartAt ℂ y) y) := meromorphicNFAt_toMeromorphicNFAt
  have hord_nf : 0 ≤ meromorphicOrderAt (toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y))
      ((chartAt ℂ y) y) := by
    rwa [meromorphicOrderAt_congr hmero.eq_nhdsNE_toMeromorphicNFAt] at hord
  exact hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp hord_nf

/-- The chart coefficient agrees, off the centre, with its repaired (normal-form) coefficient. -/
theorem formCoeff_eventuallyEq_repairedCoeff (α : MeromorphicOneForm X) (y : X) :
    formCoeff α.toFun y =ᶠ[𝓝[≠] ((chartAt ℂ y) y)]
      toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y) :=
  (α.meromorphic y).eq_nhdsNE_toMeromorphicNFAt

/-! ### Raw chart representative of a bare cotangent section, and its chart-transition law

`rawLocalRep σ x₀ y := σ y (e_{x₀}.symmL ℂ y 1)` reads a *bare* section `σ : ∀ x, FormFiber x` in the
`x₀`-trivialisation (the analogue of `Montel.localRep` without the smoothness bundling).  It satisfies
`formCoeff σ x = rawLocalRep σ x ∘ (chart x).symm` and the chart-transition law
`rawLocalRep σ x₀' y = chartTransitionFactor x₀ x₀' y · rawLocalRep σ x₀ y`, re-derived from the
trivialisation identity `symmL_apply_chartTransitionFactor`. -/

/-- The bare chart representative of a section `σ` in the `x₀`-trivialisation. -/
noncomputable def rawLocalRep (σ : ∀ x, FormFiber X x) (x₀ y : X) : ℂ :=
  σ y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)

theorem formCoeff_eq_rawLocalRep (σ : ∀ x, FormFiber X x) (x : X) (z : ℂ) :
    formCoeff σ x z = rawLocalRep σ x ((chartAt ℂ x).symm z) := rfl

/-- `rawLocalRep σ y y = formCoeff σ y (chart y y)`: the chart-centre value. -/
theorem rawLocalRep_self_eq_formCoeff (σ : ∀ x, FormFiber X x) (y : X) :
    rawLocalRep σ y y = formCoeff σ y ((chartAt ℂ y) y) := by
  rw [formCoeff_eq_rawLocalRep, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]

/-- **Chart-transition for `rawLocalRep`** (raw analogue of `Montel.localRep_chart_transition`):
`rawLocalRep σ x₀' y = chartTransitionFactor x₀ x₀' y · rawLocalRep σ x₀ y` for `y` in both base
sets.  The proof reuses the trivialisation identity `symmL_apply_chartTransitionFactor`. -/
theorem rawLocalRep_chart_transition (σ : ∀ x, FormFiber X x) (x₀ x₀' y : X)
    (hy₀' : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet)
    (hy₀ : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet) :
    rawLocalRep σ x₀' y = chartTransitionFactor (X := X) x₀ x₀' y * rawLocalRep σ x₀ y := by
  unfold rawLocalRep
  rw [← symmL_apply_chartTransitionFactor x₀ x₀' y hy₀' hy₀]
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  set c := chartTransitionFactor (X := X) x₀ x₀' y with hc_def
  have h : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
    have : (c : ℂ) = c • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [this]
    exact map_smul (e.symmL ℂ y) c 1
  rw [h, map_smul, smul_eq_mul]

/-- **Self-frame reconstruction** (raw analogue of `Montel.toFun_eq_localRep_smul` at `x₀ = y`):
`σ y = rawLocalRep σ y y • φ_y` where `φ_y = frameCovector y`.  In particular
`σ y (e_{x₀}.symmL ℂ y 1) = rawLocalRep σ y y · φ_y (e_{x₀}.symmL ℂ y 1)`. -/
theorem section_eq_rawLocalRep_smul_frame (σ : ∀ x, FormFiber X x) (y : X) :
    σ y = (rawLocalRep σ y y) • frameCovector y := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y with he
  have hy : y ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source ℂ y
  set φ := e.continuousLinearEquivAt ℂ y hy with hφ
  apply ContinuousLinearMap.ext
  intro v
  change σ y v = (rawLocalRep σ y y) • (φ v)
  have hv_eq : v = (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) (φ v) :=
    (ContinuousLinearEquiv.symm_apply_apply φ v).symm
  have hφv_smul : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) (φ v) =
      (φ v) • ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1) := by
    have h1 : (φ v : ℂ) = (φ v) • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [h1]
    exact (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y).map_smul (φ v) 1
  have h_symmL : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) = e.symmL ℂ y :=
    Bundle.Trivialization.symm_continuousLinearEquivAt_eq' e hy
  calc σ y v
      = σ y ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) (φ v)) := by rw [← hv_eq]
    _ = σ y ((φ v) • ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1)) := by rw [hφv_smul]
    _ = (φ v) • (σ y ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1)) := (σ y).map_smul (φ v) _
    _ = (φ v) • (σ y (e.symmL ℂ y 1)) := by rw [h_symmL]
    _ = (φ v) • (rawLocalRep σ y y) := rfl
    _ = (rawLocalRep σ y y) • (φ v) := by rw [smul_eq_mul, smul_eq_mul]; ring

/-! ### The junk is isolated: off-centre points are repaired automatically

The crux structural fact.  For `w` in a *punctured* neighbourhood of `x₀`, the chart coefficient
`formCoeff α.toFun w` is `ContinuousAt` its own centre, hence (being meromorphic) analytic there, so
its normal-form value `repVal α w` equals the actual value `rawLocalRep α.toFun w w`.  The
continuity comes from the chart-transition law: `rawLocalRep α.toFun w = chartTransitionFactor x₀ w ·
rawLocalRep α.toFun x₀`, where the transition factor is continuous and `rawLocalRep α.toFun x₀` is
continuous at `w` (its chart pullback `formCoeff α.toFun x₀` is analytic off the `x₀`-centre). -/

/-- `formCoeff α.toFun x₀` is analytic at `chart x₀ w`, for `w` in a punctured neighbourhood of `x₀`
(pull `MeromorphicAt.eventually_analyticAt` back through the chart). -/
theorem eventually_analyticAt_formCoeff (α : MeromorphicOneForm X) (x₀ : X) :
    ∀ᶠ w in 𝓝[≠] x₀, AnalyticAt ℂ (formCoeff α.toFun x₀) ((chartAt ℂ x₀) w) := by
  have hmero : MeromorphicAt (formCoeff α.toFun x₀) ((chartAt ℂ x₀) x₀) := α.meromorphic x₀
  have hev : ∀ᶠ z in 𝓝[≠] ((chartAt ℂ x₀) x₀), AnalyticAt ℂ (formCoeff α.toFun x₀) z :=
    hmero.eventually_analyticAt
  have htfwd : Tendsto (chartAt ℂ x₀) (𝓝[≠] x₀) (𝓝[≠] ((chartAt ℂ x₀) x₀)) :=
    (chartAt ℂ x₀).tendsto_nhdsNE (mem_chart_source ℂ x₀)
  exact htfwd.eventually hev

/-- **The junk-free crux.**  For `w` in a punctured neighbourhood of `x₀`, the repaired value at `w`
equals the actual chart-centre value: `repVal α w = rawLocalRep α.toFun w w`.  Hence `α.toFun` carries
no removable-singularity junk away from chart centres. -/
theorem eventually_repVal_eq (α : MeromorphicOneForm X) (x₀ : X) :
    ∀ᶠ w in 𝓝[≠] x₀, repVal α w = rawLocalRep α.toFun w w := by
  set e₀ := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he₀
  -- The overlap of base sets is an open neighbourhood of `x₀` minus nothing; work eventually in it.
  have hx₀_base : x₀ ∈ e₀.baseSet := by
    rw [he₀, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source ℂ x₀
  have hsrc : ∀ᶠ w in 𝓝[≠] x₀, w ∈ (chartAt ℂ x₀).source :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x₀).open_source.mem_nhds (mem_chart_source ℂ x₀))
  filter_upwards [eventually_analyticAt_formCoeff α x₀, hsrc] with w hw_ana hw_src
  -- `w` is in `x₀`'s and `w`'s base sets.
  set e_w := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) w with hew
  have hw_base₀ : w ∈ e₀.baseSet := by rw [he₀, TangentBundle.trivializationAt_baseSet]; exact hw_src
  have hw_base_w : w ∈ e_w.baseSet := by
    rw [hew, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source ℂ w
  -- (1) `rawLocalRep α.toFun x₀` is continuous at `w`.
  have hcont_x₀ : ContinuousAt (rawLocalRep α.toFun x₀) w := by
    -- `rawLocalRep α.toFun x₀ = formCoeff α.toFun x₀ ∘ (chartAt ℂ x₀)` near `w`.
    have heq : rawLocalRep α.toFun x₀ =ᶠ[𝓝 w]
        (fun u => formCoeff α.toFun x₀ ((chartAt ℂ x₀) u)) := by
      filter_upwards [(chartAt ℂ x₀).open_source.mem_nhds hw_src] with u hu
      rw [formCoeff_eq_rawLocalRep, (chartAt ℂ x₀).left_inv hu]
    rw [continuousAt_congr heq]
    exact hw_ana.continuousAt.comp ((chartAt ℂ x₀).continuousAt hw_src)
  -- (2) the transition factor is continuous at `w` (overlap is open, `w` interior).
  have hcont_c : ContinuousAt (chartTransitionFactor (X := X) x₀ w) w := by
    have hopen : IsOpen (e_w.baseSet ∩ e₀.baseSet) := e_w.open_baseSet.inter e₀.open_baseSet
    exact ((continuousOn_chartTransitionFactor x₀ w).continuousAt
      (hopen.mem_nhds ⟨hw_base_w, hw_base₀⟩))
  -- (3) `rawLocalRep α.toFun w` is continuous at `w`, via the transition law.
  have hcont_w : ContinuousAt (rawLocalRep α.toFun w) w := by
    have heq : rawLocalRep α.toFun w =ᶠ[𝓝 w]
        (fun u => chartTransitionFactor (X := X) x₀ w u * rawLocalRep α.toFun x₀ u) := by
      have hopen : IsOpen (e_w.baseSet ∩ e₀.baseSet) := e_w.open_baseSet.inter e₀.open_baseSet
      filter_upwards [hopen.mem_nhds ⟨hw_base_w, hw_base₀⟩] with u hu
      exact rawLocalRep_chart_transition α.toFun x₀ w u hu.1 hu.2
    rw [continuousAt_congr heq]
    exact hcont_c.mul hcont_x₀
  -- (4) `formCoeff α.toFun w` continuous at `chart w w`, hence analytic, hence junk-free.
  have hcont_fc : ContinuousAt (formCoeff α.toFun w) ((chartAt ℂ w) w) := by
    have heq : formCoeff α.toFun w =ᶠ[𝓝 ((chartAt ℂ w) w)]
        (fun z => rawLocalRep α.toFun w ((chartAt ℂ w).symm z)) := by
      filter_upwards with z; rw [formCoeff_eq_rawLocalRep]
    rw [continuousAt_congr heq]
    have hsymm_cont : ContinuousAt (chartAt ℂ w).symm ((chartAt ℂ w) w) := by
      have := (chartAt ℂ w).continuousAt_symm ((chartAt ℂ w).map_source (mem_chart_source ℂ w))
      simpa [(chartAt ℂ w).left_inv (mem_chart_source ℂ w)] using this
    have hcont_w' : ContinuousAt (rawLocalRep α.toFun w)
        ((chartAt ℂ w).symm ((chartAt ℂ w) w)) := by
      rwa [(chartAt ℂ w).left_inv (mem_chart_source ℂ w)]
    exact hcont_w'.comp hsymm_cont
  have hana_w : AnalyticAt ℂ (formCoeff α.toFun w) ((chartAt ℂ w) w) :=
    (α.meromorphic w).analyticAt hcont_fc
  -- analytic ⟹ NF = self ⟹ repVal = value.
  have hNFself : toMeromorphicNFAt (formCoeff α.toFun w) ((chartAt ℂ w) w) = formCoeff α.toFun w :=
    toMeromorphicNFAt_eq_self.mpr hana_w.meromorphicNFAt
  rw [repVal, hNFself, rawLocalRep_self_eq_formCoeff]

/-! ### The repaired section and its holomorphy

`repairedSection α y := repVal α y • frameCovector y` is the per-point removable-singularity repair.
Its chart pullback in *any* chart `x₀` agrees off the centre with `formCoeff α.toFun x₀` (junk-free
crux) and at the centre with the normal-form value, hence equals the analytic normal-form repair near
the centre — so it is a genuine `HolomorphicOneForms X` (`holOfLocalRepAnalyticAt`). -/

/-- The **repaired section** of an order-`≥ 0` meromorphic 1-form: the per-point normal-form value
times the canonical frame covector.  A bare cotangent-bundle section. -/
noncomputable def repairedSection (α : MeromorphicOneForm X) : ∀ y, FormFiber X y :=
  fun y => (repVal α y) • frameCovector y

theorem rawLocalRep_repairedSection_self (α : MeromorphicOneForm X) (y : X) :
    rawLocalRep (repairedSection α) y y = repVal α y := by
  show (repairedSection α y) ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y).symmL ℂ y 1) = _
  rw [repairedSection, ContinuousLinearMap.smul_apply, frameCovector_symmL_self, smul_eq_mul,
    mul_one]

/-- **The repaired section germ-matches `α` off every centre.**  In chart `x₀`, the chart
coefficient of `repairedSection α` agrees on a punctured neighbourhood of the centre with
`formCoeff α.toFun x₀` (the junk-free crux + self-frame reconstruction).  This drives both the
analyticity of the repaired section and the germ-equality `holToMero (repaired) ≡ α`. -/
theorem formCoeff_repairedSection_eventuallyEq (α : MeromorphicOneForm X) (x₀ : X) :
    formCoeff (repairedSection α) x₀ =ᶠ[𝓝[≠] ((chartAt ℂ x₀) x₀)] formCoeff α.toFun x₀ := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he
  set c₀ := (chartAt ℂ x₀) x₀ with hc₀
  -- Transport the junk-free crux from `𝓝[≠] x₀` to `𝓝[≠] c₀` via `(chart x₀).symm`.
  have htsymm : Tendsto (chartAt ℂ x₀).symm (𝓝[≠] c₀) (𝓝[≠] x₀) := by
    have := (chartAt ℂ x₀).symm.tendsto_nhdsNE (x := c₀)
      (by simp [hc₀, (chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀)])
    simpa [hc₀, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)] using this
  have hcrux : ∀ᶠ z in 𝓝[≠] c₀,
      repVal α ((chartAt ℂ x₀).symm z) = rawLocalRep α.toFun ((chartAt ℂ x₀).symm z)
        ((chartAt ℂ x₀).symm z) := htsymm.eventually (eventually_repVal_eq α x₀)
  filter_upwards [hcrux] with z hz_crux
  set w := (chartAt ℂ x₀).symm z with hw
  show rawLocalRep (repairedSection α) x₀ w = rawLocalRep α.toFun x₀ w
  -- `repairedSection α w = repVal α w • φ_w`, so its `x₀`-rawLocalRep at `w` is
  -- `repVal α w · φ_w(e.symmL w 1)`.
  have h1 : rawLocalRep (repairedSection α) x₀ w
      = repVal α w * frameCovector w (e.symmL ℂ w 1) := by
    show (repairedSection α w) (e.symmL ℂ w 1) = _
    rw [repairedSection, ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- `α.toFun w = rawLocalRep α.toFun w w • φ_w` (self-frame), so its `x₀`-rawLocalRep at `w` is
  -- `rawLocalRep α.toFun w w · φ_w(e.symmL w 1)`.
  have h2 : rawLocalRep α.toFun x₀ w = rawLocalRep α.toFun w w * frameCovector w (e.symmL ℂ w 1) := by
    show α.toFun w (e.symmL ℂ w 1) = _
    conv_lhs => rw [section_eq_rawLocalRep_smul_frame α.toFun w]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h1, h2, hz_crux]

/-- **The repaired section's chart pullback is analytic at every centre.**  In chart `x₀`, the
pullback agrees off the centre with `formCoeff α.toFun x₀` (the junk-free crux + self-frame), and at
the centre takes the normal-form value, so it equals the analytic normal-form repair of
`formCoeff α.toFun x₀` near the centre. -/
theorem analyticAt_pullback_repairedSection {α : MeromorphicOneForm X}
    (hα : α ∈ omegaD (X := X) 0) (x₀ : X) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    AnalyticAt ℂ
      (fun z : ℂ => repairedSection α ((chartAt ℂ x₀).symm z)
        (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
      ((chartAt ℂ x₀) x₀) := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he
  set c₀ := (chartAt ℂ x₀) x₀ with hc₀
  -- The pullback is exactly `formCoeff (repairedSection α) x₀`.
  show AnalyticAt ℂ (formCoeff (repairedSection α) x₀) c₀
  set NF : ℂ → ℂ := toMeromorphicNFAt (formCoeff α.toFun x₀) c₀ with hNF
  have hNFana : AnalyticAt ℂ NF c₀ := analyticAt_repairedCoeff hα x₀
  -- `formCoeff (repaired) =ᶠ[𝓝[≠] c₀] formCoeff α ~ NF`, and centre values match.
  have hPunct : formCoeff (repairedSection α) x₀ =ᶠ[𝓝[≠] c₀] NF :=
    (formCoeff_repairedSection_eventuallyEq α x₀).trans
      (α.meromorphic x₀).eq_nhdsNE_toMeromorphicNFAt
  have hCenter : formCoeff (repairedSection α) x₀ c₀ = NF c₀ := by
    have hsymm_center : (chartAt ℂ x₀).symm c₀ = x₀ := by
      rw [hc₀, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)]
    rw [formCoeff_eq_rawLocalRep, hsymm_center, rawLocalRep_repairedSection_self, hNF, repVal]
  exact hNFana.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hPunct hCenter).symm

/-- **The repaired holomorphic 1-form** of an order-`≥ 0` meromorphic 1-form. -/
noncomputable def repairedHOF {α : MeromorphicOneForm X} (hα : α ∈ omegaD (X := X) 0) :
    HolomorphicOneForms X :=
  holOfLocalRepAnalyticAt (repairedSection α) (analyticAt_pullback_repairedSection hα)

@[simp] theorem repairedHOF_toFun {α : MeromorphicOneForm X} (hα : α ∈ omegaD (X := X) 0) :
    (repairedHOF hα).toFun = repairedSection α := rfl

-- From here on, treat the repair definitions as opaque (the wiring uses only their lemmas, never
-- their unfoldings); this keeps the kernel from unfolding the embedded analytic proofs.
attribute [local irreducible] repVal frameCovector repairedSection repairedHOF

/-! ## Part 3: `Ω_0 ≅ HolomorphicOneForms`, finiteness, and the unconditional `hKgenus`

`holToMero (repairedHOF hα)` germ-matches `α` everywhere (the repaired section agrees with `α` off
every centre), so `holToMero (repairedHOF hα) − α ∈ formGermZeroSubmodule`.  Hence the injection
`holToOmega0Module : HolomorphicOneForms X → omegaDModule 0` is **surjective**, giving a `LinearEquiv`,
finite-dimensionality of `omegaDModule 0` (transported from `HolomorphicOneForms`), and the §17.4
equality `omegaDim 0 = kirovGenus X`.  Chaining with `CanonicalForm17Data.hKgenus` makes `lDim K = kirovGenus X`
unconditional. -/

set_option maxHeartbeats 1000000 in
/-- **Every order-`≥ 0` meromorphic 1-form is holomorphic modulo germ-junk.**  There is a holomorphic
1-form `β` (the repaired section) with `holToMero β − α` germ-zero everywhere (order `⊤` at every
centre): their chart coefficients agree on a punctured neighbourhood of each centre.  Packaging it as
an existence keeps the large `repairedHOF` proof term out of downstream goals. -/
theorem exists_holomorphic_germEq_of_mem_omegaD_zero {α : MeromorphicOneForm X}
    (hα : α ∈ omegaD (X := X) 0) :
    ∃ β : HolomorphicOneForms X, holToMero β - α ∈ formGermZeroSubmodule (X := X) := by
  refine ⟨repairedHOF hα, ?_⟩
  intro x
  rw [MeromorphicOneForm.formOrderW, meromorphicOrderAt_eq_top_iff]
  -- chart coefficient of the difference is `formCoeff (repairedSection α) x − formCoeff α.toFun x`.
  have htoFun : (holToMero (repairedHOF hα) - α).toFun = repairedSection α - α.toFun := by
    rw [MeromorphicOneForm.sub_toFun, holToMero_toFun, repairedHOF_toFun]
  have hcoeff : formCoeff (holToMero (repairedHOF hα) - α).toFun x
      = formCoeff (repairedSection α) x - formCoeff α.toFun x := by
    rw [htoFun, formCoeff_sub]
  rw [hcoeff]
  filter_upwards [formCoeff_repairedSection_eventuallyEq α x] with z hz
  show formCoeff (repairedSection α) x z - formCoeff α.toFun x z = 0
  rw [hz, sub_self]

/-- **`holToOmega0Module` is surjective**: every class `[α] ∈ omegaDModule 0` is the image of a
holomorphic form (the removable-singularity repair, which differs from `α` by germ-zero junk). -/
theorem holToOmega0Module_surjective :
    Function.Surjective (holToOmega0Module (X := X)) := by
  intro q
  obtain ⟨⟨α, hα⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨β, hβ⟩ := exists_holomorphic_germEq_of_mem_omegaD_zero hα
  refine ⟨β, ?_⟩
  -- `[holInOmega0 β] = [⟨α, hα⟩]` since their difference `holToMero β − α` lies in the germ-zero sub.
  rw [holToOmega0Module, LinearMap.coe_mk, AddHom.coe_mk, Submodule.Quotient.eq]
  rw [Submodule.submoduleOf, Submodule.mem_comap, map_sub]
  show holToMero β - α ∈ formGermZeroSubmodule (X := X)
  exact hβ

/-- **`Ω_0 ≅ HolomorphicOneForms`** (Forster §17.4 at `D = 0`): the holomorphic-to-meromorphic-1-form
map is a linear isomorphism `HolomorphicOneForms X ≃ₗ[ℂ] omegaDModule 0` (injective from
`holToOmega0Module_injective`, surjective from the removable-singularity repair). -/
noncomputable def holOmega0Equiv : HolomorphicOneForms X ≃ₗ[ℂ] omegaDModule (X := X) 0 :=
  LinearEquiv.ofBijective holToOmega0Module
    ⟨holToOmega0Module_injective, holToOmega0Module_surjective⟩

/-- **`Ω_0` is finite-dimensional** (Forster §17.4): transported across `holOmega0Equiv` from the
finite-dimensional `HolomorphicOneForms X` (Montel/Cartan–Serre). -/
instance : FiniteDimensional ℂ (omegaDModule (X := X) 0) :=
  LinearEquiv.finiteDimensional holOmega0Equiv

/-- **`omegaDim 0 = kirovGenus X`** (Forster §17.4 at `D = 0`), UNCONDITIONAL: the isomorphism
`Ω_0 ≅ HolomorphicOneForms X` preserves finrank, and `kirovGenus X = finrank ℂ (HolomorphicOneForms X)`
by definition. -/
theorem omegaDim_zero_eq_genus : omegaDim (X := X) 0 = kirovGenus X := by
  rw [omegaDim_eq_finrank, ← holOmega0Equiv.finrank_eq]
  rfl

/-- **The reverse bound `omegaDim 0 ≤ kirovGenus X`** (Gate C's removable-singularity direction). -/
theorem omegaDim_zero_le_genus : omegaDim (X := X) 0 ≤ kirovGenus X :=
  le_of_eq omegaDim_zero_eq_genus

end Jacobians.Dolbeault

/-! ## Part 4: the unconditional `hKgenus` headline (Forster §17.4)

`CanonicalForm17Data.hKgenus` takes `FiniteDimensional ℂ (omegaDModule 0)` + `omegaDim 0 ≤ kirovGenus X`
as hypotheses.  Both are now proven unconditionally, so for any `CanonicalForm17Data` (which
`nonempty_canonicalForm17Data` supplies) we get `lDim K = kirovGenus X` with no remaining gaps. -/

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Unconditional `hKgenus`** for a given §17.4 datum: `lDim data.K = kirovGenus X`, with the two
removable-singularity inputs (`Ω_0` finite-dimensional and `omegaDim 0 ≤ kirovGenus X`) now discharged. -/
theorem CanonicalForm17Data.hKgenus_unconditional (data : CanonicalForm17Data X) :
    lDim (X := X) data.K = kirovGenus X :=
  data.hKgenus omegaDim_zero_le_genus

/-- **The unconditional Serre-duality input** `∃ data, lDim data.K = kirovGenus X` (Forster §17.4).  Chains
the proven existence of a §17.4 datum (`nonempty_canonicalForm17Data`) with the now-unconditional
`hKgenus`.  This discharges the `SerreDualityData.hKgenus` field with no hypotheses. -/
theorem exists_canonicalForm17Data_hKgenus :
    ∃ data : CanonicalForm17Data X, lDim (X := X) data.K = kirovGenus X := by
  obtain ⟨data⟩ := nonempty_canonicalForm17Data (X := X)
  exact ⟨data, data.hKgenus_unconditional⟩

end Jacobians.Dolbeault
