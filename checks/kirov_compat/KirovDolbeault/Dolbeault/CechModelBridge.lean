/-
  Čech finiteness — the germ ↔ sup-norm comparison ("K-bridge"), upstream atoms.

  Part of discharging `exists_cechModel` (Forster 14.9). The comparison `cechH1 𝔘 D ≃ supH1` translates
  germ-class `𝒪_D` cochains (the `cechH1` representation) into `BddHol` cochains on chart-images (the
  `supH1`/Montel representation). Its most upstream atom is the **codomain constructor**: every analytic
  bounded function on an open `U ⊆ ℂ` is a `BddHol U` element.

  This file is pure one-variable complex analysis on the `BddHol` side — complete, depends on no
  unproved obligation. The manifold side (chart-pullback of an `𝒪_D` section is analytic) reuses the
  axiom-clean `CechH0.analyticAt_chart_change`.
-/
import KirovDolbeault.Dolbeault.BddHol

open Metric Topology BoundedContinuousFunction

namespace Jacobians.Dolbeault

/-! ### Bounded-continuous precomposition as a continuous-linear map (the shrinking-side transport)

The shrinking-side Čech differentials `δ⁰`/`δ¹` transport a 1-cochain component living in
`(K →ᵇ ℂ)` (bounded-continuous on a compact overlap shrinking) to a SMALLER compact (a finer overlap
shrinking) through a continuous reindexing — either a holomorphic chart transition `τ` or an inclusion.
At the bounded-continuous level this is precomposition with a `C(K', K)`, which Mathlib provides as
`BoundedContinuousFunction.compContinuous`; it is `ℂ`-linear (`add_compContinuous`, `smul`) and
norm-nonincreasing (`norm_compContinuous_le`).  We bundle it as a `(K →ᵇ ℂ) →L[ℂ] (K' →ᵇ ℂ)`. -/

/-- Bounded-continuous precomposition `f ↦ f ∘ g` as a `ℂ`-linear map `(α →ᵇ ℂ) →ₗ[ℂ] (β →ᵇ ℂ)` for
`g : C(β, α)`. -/
noncomputable def bcfCompContinuousₗ {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (g : C(β, α)) : (α →ᵇ ℂ) →ₗ[ℂ] (β →ᵇ ℂ) where
  toFun f := f.compContinuous g
  map_add' f₁ f₂ := by ext z; simp [BoundedContinuousFunction.compContinuous_apply]
  map_smul' c f := by ext z; simp [BoundedContinuousFunction.compContinuous_apply]

@[simp] theorem bcfCompContinuousₗ_apply {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (g : C(β, α)) (f : α →ᵇ ℂ) : bcfCompContinuousₗ g f = f.compContinuous g := rfl

/-- **Bounded-continuous precomposition continuous-linear map** `(α →ᵇ ℂ) →L[ℂ] (β →ᵇ ℂ)` for
`g : C(β, α)`, operator norm `≤ 1`.  The shrinking-side transport of a sup-norm cochain component
(through a chart transition or an inclusion of compacts). -/
noncomputable def bcfCompContinuousCLM {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (g : C(β, α)) : (α →ᵇ ℂ) →L[ℂ] (β →ᵇ ℂ) :=
  (bcfCompContinuousₗ g).mkContinuous 1 fun f => by
    rw [one_mul]; exact (bcfCompContinuousₗ_apply g f).symm ▸ f.norm_compContinuous_le g

@[simp] theorem bcfCompContinuousCLM_apply {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (g : C(β, α)) (f : α →ᵇ ℂ) : bcfCompContinuousCLM g f = f.compContinuous g := rfl

namespace BddHol

variable {U : Set ℂ}

@[simp] theorem toFun_neg (f : BddHol U) : (-f).toFun = -f.toFun := rfl
@[simp] theorem toFun_sub (f g : BddHol U) : (f - g).toFun = f.toFun - g.toFun := rfl

/-- **The `BddHol` codomain constructor (most-upstream K-bridge atom).**  An analytic, bounded function
on an open `U ⊆ ℂ` gives a `BddHol U` element, via the canonical extend-by-zero normal form off `U`
(which `BddHolCarrier` requires and which changes nothing on `U`). -/
noncomputable def ofAnalyticOn (g : ℂ → ℂ) (ha : AnalyticOn ℂ g U)
    (hb : ∃ C, ∀ z ∈ U, ‖g z‖ ≤ C) : BddHol U :=
  ⟨Set.indicator U g, by
    refine ⟨?_, ?_, ?_⟩
    · exact ha.congr (fun z hz => Set.indicator_of_mem hz g)
    · intro z hz
      exact Set.indicator_of_notMem hz g
    · obtain ⟨C, hC⟩ := hb
      refine ⟨C, fun z hz => ?_⟩
      rw [Set.indicator_of_mem hz g]
      exact hC z hz⟩

@[simp] theorem ofAnalyticOn_toFun_of_mem (g : ℂ → ℂ) (ha : AnalyticOn ℂ g U)
    (hb : ∃ C, ∀ z ∈ U, ‖g z‖ ≤ C) {z : ℂ} (hz : z ∈ U) :
    (ofAnalyticOn g ha hb).toFun z = g z :=
  Set.indicator_of_mem hz g

theorem ofAnalyticOn_toFun_eqOn (g : ℂ → ℂ) (ha : AnalyticOn ℂ g U)
    (hb : ∃ C, ∀ z ∈ U, ‖g z‖ ≤ C) :
    Set.EqOn (ofAnalyticOn g ha hb).toFun g U :=
  fun _ hz => ofAnalyticOn_toFun_of_mem g ha hb hz

/-- **Boundedness on a relatively-compact piece.**  An analytic function on `U` is bounded on any
compact `K ⊆ U` (it is continuous, hence bounded on the compact).  This supplies the `BddHol`
boundedness hypothesis: a cochain holomorphic on a cover-open is bounded on the (relatively-compact)
shrinking. -/
theorem bddOn_of_analyticOn_subset_compact {g : ℂ → ℂ} {U K : Set ℂ}
    (hg : AnalyticOn ℂ g U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ z ∈ K, ‖g z‖ ≤ C :=
  hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKU)

/-- **The practical K-bridge constructor.**  A function analytic on an open `U`, restricted to an
open `U'` whose closure is a compact subset of `U` (`U' ⋐ U`), is a `BddHol U'` element — the
boundedness is automatic on the relatively-compact piece.  This is the shape the germ→`BddHol` cochain
map uses: cover-cochains are holomorphic on the cover-open `U`, the model lives on the shrinking
`U' ⋐ U`. -/
noncomputable def ofAnalyticOnOfRelCompact {g : ℂ → ℂ} {U U' : Set ℂ} (hg : AnalyticOn ℂ g U)
    (hsub : closure U' ⊆ U) (hcpt : IsCompact (closure U')) : BddHol U' :=
  ofAnalyticOn g (hg.mono (subset_closure.trans hsub))
    (by
      obtain ⟨C, hC⟩ := bddOn_of_analyticOn_subset_compact hg hcpt hsub
      exact ⟨C, fun z hz => hC z (subset_closure hz)⟩)

@[simp] theorem ofAnalyticOnOfRelCompact_toFun_of_mem {g : ℂ → ℂ} {U U' : Set ℂ}
    (hg : AnalyticOn ℂ g U) (hsub : closure U' ⊆ U) (hcpt : IsCompact (closure U'))
    {z : ℂ} (hz : z ∈ U') :
    (ofAnalyticOnOfRelCompact hg hsub hcpt).toFun z = g z :=
  ofAnalyticOn_toFun_of_mem g _ _ hz

/-! ### Cross-chart transport `BddHol U → BddHol U'` (the open-set, analytic counterpart of
`precompCLM`)

The cross-chart Čech differentials on the COVER side (`δ¹cov`) and the δ-square of the `cechH1 ≃
supH1` comparison transport a cochain component holomorphic on one chart-image to a neighbouring
chart-image and must land back in `BddHol` (analytic on an OPEN set), not merely `→ᵇ` on a compact.
This is precomposition with an **analytic** reindexing `τ : U' → U` (the holomorphic chart transition):
`g ∘ τ` is analytic on `U'` (`AnalyticOn.comp`), bounded there by `‖g‖`, hence a `BddHol U'`. The map
`g ↦ g ∘ τ` is `ℂ`-linear with operator norm `≤ 1` (precomposition cannot increase the sup-norm). The
manifold side supplies `τ` analytic on `U'` mapping into `U` (from `transition_analyticAt_of_mem`).
Cf. `precompCLM`, which lands in `→ᵇ` on a compact and needs only `ContinuousOn`. -/

/-- Transport `g : BddHol U` across an **analytic** reindexing `τ : U' → U`, landing in `BddHol U'`
(value `g ∘ τ`, extended by zero off `U'`). The cross-chart cover-side transport of a sup-norm cochain
component. -/
noncomputable def precompHol {U U' : Set ℂ} {τ : ℂ → ℂ} (hτ : AnalyticOn ℂ τ U')
    (hτmaps : Set.MapsTo τ U' U) (g : BddHol U) : BddHol U' :=
  ofAnalyticOn (g.toFun ∘ τ) (g.analyticOn.comp hτ hτmaps)
    ⟨‖g‖, fun _ hz => g.norm_toFun_le (hτmaps hz)⟩

@[simp] theorem precompHol_toFun_of_mem {U U' : Set ℂ} {τ : ℂ → ℂ} (hτ : AnalyticOn ℂ τ U')
    (hτmaps : Set.MapsTo τ U' U) (g : BddHol U) {z : ℂ} (hz : z ∈ U') :
    (precompHol hτ hτmaps g).toFun z = g.toFun (τ z) :=
  ofAnalyticOn_toFun_of_mem _ _ _ hz

theorem precompHol_add {U U' : Set ℂ} {τ : ℂ → ℂ} (hτ : AnalyticOn ℂ τ U')
    (hτmaps : Set.MapsTo τ U' U) (g₁ g₂ : BddHol U) :
    precompHol hτ hτmaps (g₁ + g₂) = precompHol hτ hτmaps g₁ + precompHol hτ hτmaps g₂ := by
  refine toFun_injective (funext fun z => ?_)
  by_cases hz : z ∈ U'
  · rw [precompHol_toFun_of_mem _ _ _ hz, toFun_add, Pi.add_apply, toFun_add, Pi.add_apply,
      precompHol_toFun_of_mem _ _ _ hz, precompHol_toFun_of_mem _ _ _ hz]
  · rw [toFun_add, Pi.add_apply, (precompHol hτ hτmaps (g₁ + g₂)).zero_off z hz,
      (precompHol hτ hτmaps g₁).zero_off z hz, (precompHol hτ hτmaps g₂).zero_off z hz, add_zero]

theorem precompHol_smul {U U' : Set ℂ} {τ : ℂ → ℂ} (hτ : AnalyticOn ℂ τ U')
    (hτmaps : Set.MapsTo τ U' U) (c : ℂ) (g : BddHol U) :
    precompHol hτ hτmaps (c • g) = c • precompHol hτ hτmaps g := by
  refine toFun_injective (funext fun z => ?_)
  by_cases hz : z ∈ U'
  · rw [precompHol_toFun_of_mem _ _ _ hz, toFun_smul, Pi.smul_apply, toFun_smul, Pi.smul_apply,
      precompHol_toFun_of_mem _ _ _ hz]
  · rw [toFun_smul, Pi.smul_apply, (precompHol hτ hτmaps (c • g)).zero_off z hz,
      (precompHol hτ hτmaps g).zero_off z hz, smul_zero]

/-- Cross-chart transport as a `ℂ`-linear map `BddHol U →ₗ[ℂ] BddHol U'`. -/
noncomputable def precompHolₗ {U U' : Set ℂ} {τ : ℂ → ℂ} (hτ : AnalyticOn ℂ τ U')
    (hτmaps : Set.MapsTo τ U' U) : BddHol U →ₗ[ℂ] BddHol U' where
  toFun := precompHol hτ hτmaps
  map_add' := precompHol_add hτ hτmaps
  map_smul' c g := precompHol_smul hτ hτmaps c g

@[simp] theorem precompHolₗ_apply {U U' : Set ℂ} {τ : ℂ → ℂ} (hτ : AnalyticOn ℂ τ U')
    (hτmaps : Set.MapsTo τ U' U) (g : BddHol U) : precompHolₗ hτ hτmaps g = precompHol hτ hτmaps g :=
  rfl

/-- **Cross-chart transport continuous-linear map** `BddHol U →L[ℂ] BddHol U'` for `τ` analytic
`U' → U`, operator norm `≤ 1`. The open-set (analytic) counterpart of `precompCLM`, used to transport
cover-side sup-norm cochain components across the holomorphic chart transitions. -/
noncomputable def precompHolCLM {U U' : Set ℂ} {τ : ℂ → ℂ} (hτ : AnalyticOn ℂ τ U')
    (hτmaps : Set.MapsTo τ U' U) : BddHol U →L[ℂ] BddHol U' :=
  (precompHolₗ hτ hτmaps).mkContinuous 1 fun g => by
    rw [one_mul, norm_def]
    refine (BoundedContinuousFunction.norm_le (norm_nonneg g)).mpr fun z => ?_
    show ‖(precompHol hτ hτmaps g).toFun z.1‖ ≤ ‖g‖
    rw [precompHol_toFun_of_mem _ _ _ z.2]
    exact g.norm_toFun_le (hτmaps z.2)

@[simp] theorem precompHolCLM_apply {U U' : Set ℂ} {τ : ℂ → ℂ} (hτ : AnalyticOn ℂ τ U')
    (hτmaps : Set.MapsTo τ U' U) (g : BddHol U) :
    precompHolCLM hτ hτmaps g = precompHol hτ hτmaps g := rfl

theorem norm_precompHolCLM_le {U U' : Set ℂ} {τ : ℂ → ℂ} (hτ : AnalyticOn ℂ τ U')
    (hτmaps : Set.MapsTo τ U' U) : ‖precompHolCLM hτ hτmaps‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### Open-subset restriction `BddHol U → BddHol U'` (the diagonal cover-side transport)

The cross-chart Čech differentials on the COVER side also need the *same-chart* (diagonal) component:
restricting a cochain holomorphic on `U` to a smaller OPEN subset `U' ⊆ U`, landing back in `BddHol U'`
(analytic on the OPEN `U'`).  This is `precompHol` with the identity reindexing `τ = id` (`g ∘ id = g`,
analytic on `U'`, mapping `U' → U` by `U' ⊆ U`), but we expose it as a dedicated atom because the
diagonal δ¹/δ⁰ pieces read more clearly as "restrict to the smaller open". -/

/-- Open-subset restriction `g ↦ g|_{U'}` as a `BddHol U →L[ℂ] BddHol U'` (`U' ⊆ U` open),
operator norm `≤ 1`.  The same-chart (diagonal) cover-side transport of a sup-norm cochain component:
`precompHol` with the identity reindexing. -/
noncomputable def restrictOpenCLM {U U' : Set ℂ} (hsub : U' ⊆ U) : BddHol U →L[ℂ] BddHol U' :=
  precompHolCLM (τ := id) analyticOnNhd_id.analyticOn (fun _ hz => hsub hz)

@[simp] theorem restrictOpenCLM_toFun_of_mem {U U' : Set ℂ} (hsub : U' ⊆ U) (g : BddHol U)
    {z : ℂ} (hz : z ∈ U') : (restrictOpenCLM hsub g).toFun z = g.toFun z := by
  rw [restrictOpenCLM, precompHolCLM_apply, precompHol_toFun_of_mem _ _ _ hz, id]

theorem norm_restrictOpenCLM_le {U U' : Set ℂ} (hsub : U' ⊆ U) : ‖restrictOpenCLM hsub‖ ≤ 1 :=
  norm_precompHolCLM_le _ _

end BddHol

/-! ### Non-convex restriction compactness — Step 1: finite convex-disk cover

Toward generalizing `BddHol.isCompactOperator_restrictCLM` to a non-convex compact `K` (needed so a
`DiskOverlapData` can use chart-images of overlaps, which are not convex across charts).  Step 1: any
compact `K ⊆ U` (open) is covered by finitely many *closed balls* (convex compact) each `⊆ U`. -/

/-- **Finite convex-disk cover.**  For `K` compact inside an open `U ⊆ ℂ`, there is a finite family of
closed balls — centred on `K`, each contained in `U` (hence convex compact `⊆ U`) — whose open cores
cover `K`. -/
theorem exists_finite_closedBall_cover {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ (t : Finset K) (r : K → ℝ), (∀ z : K, 0 < r z) ∧
      (∀ z : K, Metric.closedBall (z : ℂ) (r z) ⊆ U) ∧
      K ⊆ ⋃ z ∈ t, Metric.ball (z : ℂ) (r z) := by
  have hr : ∀ z : K, ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (z : ℂ) ρ ⊆ U := by
    intro z
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU z.2))
    exact ⟨ε / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
  choose r hr_pos hr_sub using hr
  have hcover : K ⊆ ⋃ z : K, Metric.ball (z : ℂ) (r z) := fun x hx =>
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr_pos ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => Metric.ball (z : ℂ) (r z))
    (fun _ => Metric.isOpen_ball) hcover
  exact ⟨t, r, hr_pos, hr_sub, ht⟩

/-! ### Non-convex restriction compactness — Step 2: equicontinuity on a non-convex compact

The convex equicontinuity lemma `Montel.uniformEquicontinuousOn_of_bounded_analyticOn` needs a global
mean-value inequality, which fails on a non-convex `K` (segments may leave `U`). We recover uniform
equicontinuity by a *local* mean-value argument with a **uniform Cauchy derivative bound**: thicken `K`
to a compact `K' = cthickening (δ/2) K ⋐ U`, where `δ` satisfies `cthickening δ K ⊆ U`. The repo's
`Montel.exists_cauchy_deriv_bound` (which needs no convexity) gives `‖(f i)' z‖ ≤ L·C` on all of `K'`.
For `x, y ∈ K` with `dist x y < δ/2`, the convex ball `closedBall x (δ/2) ⊆ K'` contains both, so the
1-dim mean-value inequality on that ball yields `‖f i x − f i y‖ ≤ L·C·dist x y` — a single equicontinuity
modulus valid across the whole (non-convex) `K`. This is exactly the Arzelà–Ascoli input. -/

/-- **Uniform equicontinuity of a bounded analytic family on a non-convex compact.** A family of
functions analytic on an open `U ⊆ ℂ` and uniformly bounded by `C` on `U` is uniformly equicontinuous
on *any* compact `K ⊆ U`, with no convexity assumption (cf. `Montel.uniformEquicontinuousOn_of_bounded_analyticOn`
which requires `Convex ℝ K`). -/
theorem uniformEquicontinuousOn_of_bounded_analyticOn_of_compact
    {ι : Type*} {U K : Set ℂ} {f : ι → ℂ → ℂ} {C : ℝ}
    (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U) (hCnn : 0 ≤ C)
    (hf : ∀ i, AnalyticOn ℂ (f i) U)
    (hfb : ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    UniformEquicontinuousOn f K := by
  -- thicken K to a compact K' ⋐ U, so the Cauchy derivative bound is uniform on a neighborhood of K
  obtain ⟨δ, hδpos, hδsub⟩ := hKcpt.exists_cthickening_subset_open hU hKU
  set K' := Metric.cthickening (δ / 2) K with hK'def
  have hK'cpt : IsCompact K' := hKcpt.cthickening
  have hK'U : K' ⊆ U := (Metric.cthickening_mono (by linarith) K).trans hδsub
  obtain ⟨L, hLpos, hLbd⟩ := Jacobians.Montel.exists_cauchy_deriv_bound hU hK'cpt hK'U
  have hLC_nn : 0 ≤ L * C := mul_nonneg hLpos.le hCnn
  -- local mean-value Lipschitz bound on the convex ball `closedBall x (δ/2) ⊆ K'`
  have hmvt : ∀ i, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ / 2 → ‖f i x - f i y‖ ≤ L * C * dist x y := by
    intro i x hx y hy hxy
    set s := Metric.closedBall x (δ / 2) with hsdef
    have hsK' : s ⊆ K' := Metric.closedBall_subset_cthickening hx (δ / 2)
    have hsU : s ⊆ U := hsK'.trans hK'U
    have hxs : x ∈ s := Metric.mem_closedBall_self (by linarith)
    have hys : y ∈ s := by rw [hsdef, Metric.mem_closedBall, dist_comm]; linarith
    have hconv : Convex ℝ s := convex_closedBall x (δ / 2)
    have hderBnd : ∀ z ∈ s, ‖deriv (f i) z‖ ≤ L * C := fun z hz =>
      hLbd (f i) (hf i) C (hfb i) z (hsK' hz)
    have hhasDer : ∀ z ∈ s, HasDerivWithinAt (f i) (deriv (f i) z) s z := by
      intro z hz
      have hz_in_U : z ∈ U := hsU hz
      have hdiff : DifferentiableAt ℂ (f i) z :=
        ((hf i).differentiableOn z hz_in_U).differentiableAt (hU.mem_nhds hz_in_U)
      exact hdiff.hasDerivAt.hasDerivWithinAt
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hhasDer hderBnd hconv hxs hys
    calc ‖f i x - f i y‖ = ‖f i y - f i x‖ := norm_sub_rev _ _
      _ ≤ L * C * ‖y - x‖ := hmv
      _ = L * C * dist x y := by rw [← dist_eq_norm, dist_comm]
  -- assemble `UniformEquicontinuousOn` via the metric ε-δ criterion on the subtype `↥K`
  rw [← uniformEquicontinuous_restrict_iff, Metric.uniformEquicontinuous_iff]
  intro ε hε
  refine ⟨min (δ / 2) (ε / (L * C + 1)), lt_min (by linarith) (by positivity), ?_⟩
  intro x y hxy i
  have hxy2 : dist (x : ℂ) (y : ℂ) < δ / 2 :=
    lt_of_lt_of_le (by rwa [Subtype.dist_eq] at hxy) (min_le_left _ _)
  have hxyε : dist (x : ℂ) (y : ℂ) < ε / (L * C + 1) :=
    lt_of_lt_of_le (by rwa [Subtype.dist_eq] at hxy) (min_le_right _ _)
  have hbd := hmvt i x.1 x.2 y.1 y.2 hxy2
  show dist (f i x.1) (f i y.1) < ε
  rw [dist_eq_norm]
  have hpos1 : (0 : ℝ) < L * C + 1 := by positivity
  calc ‖f i x.1 - f i y.1‖ ≤ L * C * dist (x : ℂ) (y : ℂ) := hbd
    _ ≤ (L * C + 1) * dist (x : ℂ) (y : ℂ) := by gcongr; linarith
    _ < (L * C + 1) * (ε / (L * C + 1)) := mul_lt_mul_of_pos_left hxyε hpos1
    _ = ε := by field_simp

/-- **Non-convex Montel atom.** A sup-`M`-bounded family of functions holomorphic on an open `U ⊆ ℂ`,
restricted to *any* compact `K ⋐ U`, is relatively compact in `K →ᵇ ℂ` — the convexity-free analogue of
`CechFiniteness.isCompact_closure_restrict_bddHolo`. Convexity is no longer needed thanks to
`uniformEquicontinuousOn_of_bounded_analyticOn_of_compact`. -/
theorem isCompact_closure_restrict_bddHolo_of_compact
    {U K : Set ℂ} (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U)
    {M : ℝ} (hMnn : 0 ≤ M)
    {S : Type*} (g : S → ℂ → ℂ)
    (hg_an : ∀ s, AnalyticOn ℂ (g s) U) (hg_bd : ∀ s, ∀ z ∈ U, ‖g s z‖ ≤ M)
    (hg_cont : ∀ s, ContinuousOn (g s) U) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
    IsCompact (closure (Set.range (fun s : S =>
      mkOfCompact ⟨K.restrict (g s), ((hg_cont s).mono hKU).restrict⟩))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
  apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M) (isCompact_closedBall _ _)
  · -- bounded: every value lies in `closedBall 0 M`
    rintro f y ⟨s, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, mkOfCompact_apply]
    exact hg_bd s y.1 (hKU y.2)
  · -- equicontinuous: the non-convex equicontinuity lemma + subtype transfer
    classical
    set F_bcf : S → (K →ᵇ ℂ) :=
      fun s => mkOfCompact ⟨K.restrict (g s), ((hg_cont s).mono hKU).restrict⟩ with hFbcf
    have hequi_on : UniformEquicontinuousOn g K :=
      uniformEquicontinuousOn_of_bounded_analyticOn_of_compact hU hKcpt hKU hMnn hg_an hg_bd
    have hFbcf_fn : Equicontinuous (fun s : S => (⇑(F_bcf s) : K → ℂ)) :=
      (equicontinuous_restrict_iff g).mpr hequi_on.equicontinuousOn
    let u : ↥(Set.range F_bcf) → S := fun x => Classical.choose x.2
    have hu_spec : ∀ x : ↥(Set.range F_bcf), F_bcf (u x) = x.val :=
      fun x => Classical.choose_spec x.2
    have hcomp : (fun x : ↥(Set.range F_bcf) => (⇑x.val : K → ℂ)) =
        (fun s : S => (⇑(F_bcf s) : K → ℂ)) ∘ u := by
      funext x y; simp only [Function.comp]; rw [hu_spec x]
    have hrange : Equicontinuous (fun x : ↥(Set.range F_bcf) => (⇑x.val : K → ℂ)) := by
      rw [hcomp]; exact hFbcf_fn.comp u
    exact hrange

namespace BddHol

/-- **Restriction is a compact operator for a general (non-convex) compact `K ⋐ U`.** The
convexity-free generalization of `BddHol.isCompactOperator_restrictCLM`: for `U` open and `K ⊆ U`
compact (no `Convex ℝ K`), `restrictCLM : BddHol U →L[ℂ] (K →ᵇ ℂ)` is a compact operator. Same Montel
reduction (`isCompactOperator_iff_isCompact_closure_image_closedBall`), now feeding the non-convex
atom `isCompact_closure_restrict_bddHolo_of_compact`. This unblocks `DiskOverlapData` for cross-chart
overlaps, whose chart-images are not convex. -/
theorem isCompactOperator_restrictCLM_of_compact {U K : Set ℂ} [CompactSpace K]
    (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U) :
    IsCompactOperator (restrictCLM (U := U) hKU) := by
  show IsCompactOperator (⇑(restrictCLM (U := U) hKU).toLinearMap)
  rw [isCompactOperator_iff_isCompact_closure_image_closedBall
    (restrictCLM (U := U) hKU).toLinearMap (one_pos)]
  have hatom := isCompact_closure_restrict_bddHolo_of_compact hU hKcpt hKU
    (M := (1 : ℝ)) zero_le_one
    (S := ↥(Metric.closedBall (0 : BddHol U) 1))
    (g := fun s => (s : BddHol U).toFun)
    (hg_an := fun s => (s : BddHol U).analyticOn)
    (hg_bd := fun s z hz => by
      have hs : ‖(s : BddHol U)‖ ≤ 1 := by
        have := s.2
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      exact le_trans ((s : BddHol U).norm_toFun_le hz) hs)
    (hg_cont := fun s => (s : BddHol U).analyticOn.continuousOn)
  convert hatom using 3
  ext φ
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, by rwa [Metric.mem_closedBall, dist_zero_right]⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(s : BddHol U), by
      have := s.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this, rfl⟩

/-- Restriction to a relatively compact open, viewed as a bounded-continuous function on `U'`, is
compact via the compact closure `closure U'`. This is the corrected-model bridge: first restrict to
the compact closure, then postcompose by inclusion `U' ↪ closure U'`. -/
theorem isCompactOperator_restrictCLM_toBcf_of_compact {U U' : Set ℂ} [CompactSpace (closure U')]
    (hU : IsOpen U) (hKcpt : IsCompact (closure U')) (hsub : closure U' ⊆ U) :
    IsCompactOperator (fun f : BddHol U =>
      (restrictCLM (U := U) (K := closure U') hsub f).compContinuous
        (ContinuousMap.inclusion (subset_closure : U' ⊆ closure U'))) := by
  have hρK : IsCompactOperator (restrictCLM (U := U) (K := closure U') hsub) :=
    isCompactOperator_restrictCLM_of_compact (U := U) (K := closure U') hU hKcpt hsub
  have hcomp :
      IsCompactOperator
        ((bcfCompContinuousCLM (ContinuousMap.inclusion (subset_closure : U' ⊆ closure U'))) ∘
          (restrictCLM (U := U) (K := closure U') hsub)) :=
    hρK.clm_comp (bcfCompContinuousCLM (ContinuousMap.inclusion (subset_closure : U' ⊆ closure U')))
  simpa [Function.comp, bcfCompContinuousCLM_apply] using hcomp

/-- The `U'`-level bounded-continuous restriction obtained by restricting to `closure U'` and then
including `U' ↪ closure U'` is the same as the direct open restriction `BddHol U → BddHol U'`
followed by `toBcf`. This is the exact bridge a corrected holomorphic-shrinking model will consume. -/
@[simp] theorem restrictCLM_toBcf_eq_restrictOpenCLM_toBcf {U U' : Set ℂ}
    [CompactSpace (closure U')] (hsub : closure U' ⊆ U) (f : BddHol U) :
    (bcfCompContinuousCLM (ContinuousMap.inclusion (subset_closure : U' ⊆ closure U')))
      (restrictCLM (U := U) (K := closure U') hsub f) =
      (restrictOpenCLM (U := U) (U' := U') (subset_closure.trans hsub) f).toBcf := by
  ext z
  simp [ContinuousMap.inclusion, Set.inclusion, BddHol.restrictCLM_apply, BddHol.toBcf_apply,
    restrictOpenCLM_toFun_of_mem]

/-- The open-to-open holomorphic restriction `BddHol U → BddHol U'` is compact when `U' ⋐ U`.
We prove compactness after embedding into `U' →ᵇ ℂ` via `toBcf`, then pull compactness back
through the closed embedding `toBcf`. -/
theorem isCompactOperator_restrictOpenCLM_of_compact {U U' : Set ℂ}
    (hU : IsOpen U) (hU' : IsOpen U') (hKcpt : IsCompact (closure U')) (hsub : closure U' ⊆ U) :
    IsCompactOperator (restrictOpenCLM (U := U) (U' := U') (subset_closure.trans hsub)) := by
  letI : CompactSpace (closure U') := isCompact_iff_compactSpace.mp hKcpt
  letI : CompleteSpace (BddHol U') := BddHol.completeSpace (hU := hU')
  let r : BddHol U →L[ℂ] BddHol U' :=
    restrictOpenCLM (U := U) (U' := U') (subset_closure.trans hsub)
  let e : BddHol U' → (↥U' →ᵇ ℂ) := toBcf
  have he : IsClosedEmbedding e := (isometry_toBcf).isClosedEmbedding
  have hcomp : IsCompactOperator (fun f : BddHol U => e (r f)) := by
    convert (isCompactOperator_restrictCLM_toBcf_of_compact (U := U) (U' := U') hU hKcpt hsub)
        using 1
    funext f
    simpa [r, e, Function.comp] using
      (restrictCLM_toBcf_eq_restrictOpenCLM_toBcf (U := U) (U' := U') hsub f).symm
  rcases hcomp with ⟨K, hK, hKpre⟩
  refine ⟨e ⁻¹' K, he.isCompact_preimage hK, ?_⟩
  simpa [r, e, Function.comp] using hKpre

end BddHol

end Jacobians.Dolbeault
