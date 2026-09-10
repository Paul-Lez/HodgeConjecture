/-
  Dolbeault ladder — Čech finiteness (Forster 14.9), STEP 1.

  The Banach space `BddHol U` of bounded holomorphic functions on an open `U ⊆ ℂ`, and the fact
  that restriction to a relatively-compact convex inner set `K ⋐ U` is a COMPACT operator
  `BddHol U →L[ℂ] (K →ᵇ ℂ)`. This is the Montel-compactness input to the abstract Schwartz
  finiteness lemma (Forster 14.8), which forces `H¹(X, 𝒪_D)` finite-dimensional.

  The compact-operator statement reduces, via the standard characterization
  `isCompactOperator_iff_isCompact_closure_image_closedBall`, to the proven Montel atom
  `Jacobians.Dolbeault.CechFiniteness.isCompact_closure_restrict_bddHolo`.

  Encoding: `BddHol U` is the `ℂ`-subspace of `ℂ → ℂ` of functions that are analytic on `U`, vanish
  off `U` (a canonical normal form pinning junk values, making the sup-`U` seminorm a genuine norm
  and the bcf-embedding injective), and bounded on `U`. The norm `‖f‖ = ⨆ z, ‖f z‖` over `↥U` is
  induced by the isometric embedding into the Banach space `↥U →ᵇ ℂ`; completeness comes from
  closedness of the holomorphic subspace under `analyticOn_of_tendstoLocallyUniformlyOn`.
-/
import KirovDolbeault.Dolbeault.CechFiniteness

open Metric Topology BoundedContinuousFunction
open Jacobians.Montel

namespace Jacobians.Dolbeault

variable {U : Set ℂ}

/-! ### The carrier submodule -/

/-- The `ℂ`-submodule of `ℂ → ℂ` consisting of functions analytic on `U`, vanishing off `U`, and
bounded on `U`. The "vanishing off `U`" clause is a canonical normal form: it does not affect the
analytic/bounded content (which only sees `U`) but makes the sup-`U` seminorm definite and the
embedding into `↥U →ᵇ ℂ` injective. -/
def BddHolCarrier (U : Set ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {g | AnalyticOn ℂ g U ∧ (∀ z ∉ U, g z = 0) ∧ ∃ C, ∀ z ∈ U, ‖g z‖ ≤ C}
  add_mem' := by
    rintro f g ⟨hfa, hf0, Cf, hfb⟩ ⟨hga, hg0, Cg, hgb⟩
    refine ⟨hfa.add hga, fun z hz => ?_, Cf + Cg, fun z hz => ?_⟩
    · rw [Pi.add_apply, hf0 z hz, hg0 z hz, add_zero]
    · calc ‖(f + g) z‖ = ‖f z + g z‖ := rfl
        _ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
        _ ≤ Cf + Cg := add_le_add (hfb z hz) (hgb z hz)
  zero_mem' := ⟨analyticOn_const, fun _ _ => rfl, 0, fun z _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hfa, hf0, Cf, hfb⟩
    refine ⟨?_, fun z hz => ?_, ‖c‖ * Cf, fun z hz => ?_⟩
    · exact (analyticOn_const (v := c)).smul hfa
    · rw [Pi.smul_apply, hf0 z hz, smul_zero]
    · calc ‖(c • f) z‖ = ‖c‖ * ‖f z‖ := by rw [Pi.smul_apply, norm_smul]
        _ ≤ ‖c‖ * Cf := by gcongr; exact hfb z hz

/-- The Banach space of bounded holomorphic functions on the open set `U ⊆ ℂ`.

Implemented as the subtype `↥(BddHolCarrier U)`, but kept *opaque* (non-`reducible`) so that the
ambient subtype `UniformSpace`/`TopologicalSpace` instances do not leak and clash with the
sup-`U`-norm `NormedAddCommGroup` we install below. -/
def BddHol (U : Set ℂ) : Type := ↥(BddHolCarrier U)

namespace BddHol

noncomputable instance : AddCommGroup (BddHol U) :=
  inferInstanceAs (AddCommGroup ↥(BddHolCarrier U))
noncomputable instance : Module ℂ (BddHol U) := inferInstanceAs (Module ℂ ↥(BddHolCarrier U))

/-- Reinterpret `f : BddHol U` as the underlying subtype element. Definitional identity. -/
def toCarrier (f : BddHol U) : ↥(BddHolCarrier U) := f

@[simp] theorem toCarrier_add (f g : BddHol U) : (f + g).toCarrier = f.toCarrier + g.toCarrier := rfl
@[simp] theorem toCarrier_smul (c : ℂ) (f : BddHol U) : (c • f).toCarrier = c • f.toCarrier := rfl

/-- The underlying `ℂ → ℂ` function of an element of `BddHol U`. -/
def toFun (f : BddHol U) : ℂ → ℂ := (f.toCarrier : ℂ → ℂ)

@[simp] theorem toFun_coe (f : BddHol U) : f.toFun = (f.toCarrier : ℂ → ℂ) := rfl

theorem analyticOn (f : BddHol U) : AnalyticOn ℂ f.toFun U := f.toCarrier.2.1

theorem zero_off (f : BddHol U) : ∀ z ∉ U, f.toFun z = 0 := f.toCarrier.2.2.1

theorem bddOn (f : BddHol U) : ∃ C, ∀ z ∈ U, ‖f.toFun z‖ ≤ C := f.toCarrier.2.2.2

@[simp] theorem toFun_add (f g : BddHol U) : (f + g).toFun = f.toFun + g.toFun := rfl
@[simp] theorem toFun_smul (c : ℂ) (f : BddHol U) : (c • f).toFun = c • f.toFun := rfl
@[simp] theorem toFun_zero : (0 : BddHol U).toFun = 0 := rfl

theorem toFun_injective : Function.Injective (toFun : BddHol U → (ℂ → ℂ)) :=
  fun _ _ h => Subtype.ext h

/-! ### The isometric embedding into `↥U →ᵇ ℂ` and the induced norm

An element of `BddHol U`, restricted to the subtype `↥U`, is a bounded continuous function. The
embedding `f ↦ U.restrict f.toFun` is `ℂ`-linear and injective (thanks to the vanishing-off-`U`
normal form), so it induces a `NormedAddCommGroup`/`NormedSpace` on `BddHol U`, with norm
`‖f‖ = ⨆ z : ↥U, ‖f z‖` (the bcf sup norm). Completeness then follows from closedness of the
holomorphic subspace in the Banach space `↥U →ᵇ ℂ`. -/

/-- The restriction of `f : BddHol U` to `↥U`, as a bounded continuous function. -/
noncomputable def toBcf (f : BddHol U) : ↥U →ᵇ ℂ :=
  ⟨⟨fun z => f.toFun z.1, f.analyticOn.continuousOn.restrict⟩,
    2 * f.bddOn.choose, fun x y => by
      have hC := f.bddOn.choose_spec
      calc dist (f.toFun x.1) (f.toFun y.1) ≤ ‖f.toFun x.1‖ + ‖f.toFun y.1‖ :=
            dist_le_norm_add_norm _ _
        _ ≤ f.bddOn.choose + f.bddOn.choose := add_le_add (hC x.1 x.2) (hC y.1 y.2)
        _ = 2 * f.bddOn.choose := by ring⟩

@[simp] theorem toBcf_apply (f : BddHol U) (z : ↥U) : f.toBcf z = f.toFun z.1 := rfl

/-- The bcf embedding as a `ℂ`-linear map. -/
noncomputable def toBcfₗ : BddHol U →ₗ[ℂ] (↥U →ᵇ ℂ) where
  toFun := toBcf
  map_add' f g := by
    ext z
    show (f + g).toFun z.1 = f.toFun z.1 + g.toFun z.1
    rw [toFun_add]; rfl
  map_smul' c f := by
    ext z
    show (c • f).toFun z.1 = c • f.toFun z.1
    rw [toFun_smul]; rfl

@[simp] theorem toBcfₗ_apply (f : BddHol U) : toBcfₗ f = f.toBcf := rfl

theorem toBcf_injective : Function.Injective (toBcf : BddHol U → (↥U →ᵇ ℂ)) := by
  intro f g h
  apply toFun_injective
  funext z
  by_cases hz : z ∈ U
  · have := congrArg (fun φ => φ (⟨z, hz⟩ : ↥U)) h
    simpa [toBcf_apply] using this
  · rw [f.zero_off z hz, g.zero_off z hz]

/-- The `NormedAddCommGroup` on `BddHol U` induced by the bcf embedding: `‖f‖ = ‖f.toBcf‖`. -/
noncomputable instance : NormedAddCommGroup (BddHol U) :=
  NormedAddCommGroup.induced (BddHol U) (↥U →ᵇ ℂ) toBcfₗ toBcf_injective

/-- `BddHol U` is a normed `ℂ`-space (induced from the bcf embedding). -/
noncomputable instance : NormedSpace ℂ (BddHol U) :=
  NormedSpace.induced ℂ (BddHol U) (↥U →ᵇ ℂ) toBcfₗ

theorem norm_def (f : BddHol U) : ‖f‖ = ‖f.toBcf‖ := rfl

theorem norm_eq_iSup (f : BddHol U) : ‖f‖ = ⨆ z : ↥U, ‖f.toFun z.1‖ := by
  rw [norm_def, BoundedContinuousFunction.norm_eq_iSup_norm]
  rfl

/-! ### Completeness

`toBcf` is an isometry into the Banach space `↥U →ᵇ ℂ`; `BddHol U` is therefore complete once we
know its image is closed. Closedness uses that a uniform limit of functions analytic on `U` is
analytic on `U` (`analyticOn_of_tendstoLocallyUniformlyOn`). -/

theorem toBcf_sub (f g : BddHol U) : (f - g).toBcf = f.toBcf - g.toBcf :=
  map_sub toBcfₗ f g

theorem isometry_toBcf : Isometry (toBcf : BddHol U → (↥U →ᵇ ℂ)) := by
  rw [isometry_iff_dist_eq]
  intro f g
  rw [dist_eq_norm, dist_eq_norm, norm_def, ← toBcf_sub]

theorem isUniformInducing_toBcf : IsUniformInducing (toBcf : BddHol U → (↥U →ᵇ ℂ)) :=
  isometry_toBcf.isUniformInducing

open Classical in
/-- Extend a bounded continuous function `φ : ↥U →ᵇ ℂ` to all of `ℂ` by zero off `U`. This is the
canonical-normal-form preimage candidate for `φ` under `toBcf`. -/
noncomputable def extend (φ : ↥U →ᵇ ℂ) : ℂ → ℂ := fun z => if hz : z ∈ U then φ ⟨z, hz⟩ else 0

theorem extend_mem (φ : ↥U →ᵇ ℂ) {z : ℂ} (hz : z ∈ U) : extend φ z = φ ⟨z, hz⟩ := by
  rw [extend]; exact dif_pos hz

theorem extend_notMem (φ : ↥U →ᵇ ℂ) {z : ℂ} (hz : z ∉ U) : extend φ z = 0 := by
  rw [extend]; exact dif_neg hz

theorem extend_comp_coe (φ : ↥U →ᵇ ℂ) : extend φ ∘ (Subtype.val : ↥U → ℂ) = ⇑φ := by
  funext z; exact extend_mem φ z.2

/-- The limit (in `↥U →ᵇ ℂ`) of `toBcf`-images of `BddHol U` elements is analytic on `U`, after
extending by zero. The uniform-on-`↥U` convergence transfers to uniform-on-`U` (functions on `ℂ`),
hence locally uniform, so the uniform-limit lemma applies. -/
theorem analyticOn_extend_of_tendsto (hU : IsOpen U) {ι : Type*} {p : Filter ι} [p.NeBot]
    (g : ι → BddHol U) (φ : ↥U →ᵇ ℂ) (hφ : Filter.Tendsto (fun n => (g n).toBcf) p (nhds φ)) :
    AnalyticOn ℂ (extend φ) U := by
  -- bcf convergence ⇒ uniform convergence of the coe functions on `↥U`
  have hunif : TendstoUniformly (fun n => ⇑((g n).toBcf)) (⇑φ) p :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφ
  -- transfer to `TendstoUniformlyOn` of the `ℂ → ℂ` functions on `U`
  have huon : TendstoUniformlyOn (fun n => (g n).toFun) (extend φ) p U := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    rw [extend_comp_coe]
    exact hunif
  -- locally uniform ⇒ analytic limit (each `(g n).toFun` is analytic on `U`)
  exact analyticOn_of_tendstoLocallyUniformlyOn hU huon.tendstoLocallyUniformlyOn
    (Filter.Eventually.of_forall fun n => (g n).analyticOn)

/-- `extend φ` is bounded on `U` by `‖φ‖`. -/
theorem norm_extend_le (φ : ↥U →ᵇ ℂ) {z : ℂ} (hz : z ∈ U) : ‖extend φ z‖ ≤ ‖φ‖ := by
  rw [extend_mem φ hz]
  exact φ.norm_coe_le_norm ⟨z, hz⟩

/-- The membership criterion for the image of `toBcf`: if `φ` is the `p`-limit of `toBcf`-images of
`BddHol U` elements (for `U` open), then `φ` lies in the range — its extension by zero is a genuine
element of `BddHol U`. -/
theorem mem_range_toBcf_of_tendsto (hU : IsOpen U) {ι : Type*} {p : Filter ι} [p.NeBot]
    (g : ι → BddHol U) (φ : ↥U →ᵇ ℂ) (hφ : Filter.Tendsto (fun n => (g n).toBcf) p (nhds φ)) :
    φ ∈ Set.range (toBcf : BddHol U → (↥U →ᵇ ℂ)) := by
  -- the extension by zero is a member of the carrier
  have hmem : extend φ ∈ BddHolCarrier U :=
    ⟨analyticOn_extend_of_tendsto hU g φ hφ, fun z hz => extend_notMem φ hz,
      ‖φ‖, fun z hz => norm_extend_le φ hz⟩
  refine ⟨(⟨extend φ, hmem⟩ : ↥(BddHolCarrier U)), ?_⟩
  -- `toBcf` of this element is `φ`
  ext z
  show extend φ z.1 = φ z
  rw [extend_mem φ z.2]

/-- The image of `toBcf` is closed in `↥U →ᵇ ℂ` (uniform limits of bounded-holomorphic restrictions
are bounded-holomorphic restrictions). -/
theorem isClosed_range_toBcf (hU : IsOpen U) :
    IsClosed (Set.range (toBcf : BddHol U → (↥U →ᵇ ℂ))) := by
  rw [← isSeqClosed_iff_isClosed]
  intro xs φ hxs hlim
  -- each `xs n` is `toBcf (g n)` for some `g n`
  choose g hg using hxs
  refine mem_range_toBcf_of_tendsto (p := Filter.atTop) hU g φ ?_
  simpa only [hg] using hlim

/-- The image of `toBcf` is complete (closed in the Banach space `↥U →ᵇ ℂ`). -/
theorem isComplete_range_toBcf (hU : IsOpen U) :
    IsComplete (Set.range (toBcf : BddHol U → (↥U →ᵇ ℂ))) :=
  (isClosed_range_toBcf hU).isComplete

/-- **`BddHol U` is a Banach space.** Completeness follows from the isometric embedding into the
complete `↥U →ᵇ ℂ` whose image is closed. -/
theorem completeSpace (hU : IsOpen U) : CompleteSpace (BddHol U) :=
  isUniformInducing_toBcf.completeSpace (isComplete_range_toBcf hU)

/-- Pointwise bound: the sup-`U` norm dominates `|f|` at every point of `U`. -/
theorem norm_toFun_le (f : BddHol U) {z : ℂ} (hz : z ∈ U) : ‖f.toFun z‖ ≤ ‖f‖ := by
  rw [norm_def]
  exact f.toBcf.norm_coe_le_norm ⟨z, hz⟩

/-! ### The compact-restriction operator `BddHol U →L[ℂ] (K →ᵇ ℂ)`

For a compact `K ⊆ U`, restricting a bounded-holomorphic function to `K` gives a bounded continuous
function on the compact `K`. This restriction is `ℂ`-linear and norm-nonincreasing (operator norm
`≤ 1`). When `K` is moreover convex and `K ⋐ U`, it is a *compact* operator (Montel). -/

variable {K : Set ℂ} [CompactSpace K]

/-- Restriction of `f : BddHol U` to a compact `K ⊆ U`, as a bounded continuous function on `K`.
This is the exact element form consumed by the Montel atom
`CechFiniteness.isCompact_closure_restrict_bddHolo`. -/
noncomputable def restrict (hKU : K ⊆ U) (f : BddHol U) : K →ᵇ ℂ :=
  mkOfCompact ⟨K.restrict f.toFun, (f.analyticOn.continuousOn.mono hKU).restrict⟩

@[simp] theorem restrict_apply (hKU : K ⊆ U) (f : BddHol U) (z : K) :
    restrict hKU f z = f.toFun z.1 := rfl

/-- Restriction to `K ⊆ U` as a `ℂ`-linear map. -/
noncomputable def restrictₗ (hKU : K ⊆ U) : BddHol U →ₗ[ℂ] (K →ᵇ ℂ) where
  toFun := restrict hKU
  map_add' f g := by
    ext z
    show (f + g).toFun z.1 = f.toFun z.1 + g.toFun z.1
    rw [toFun_add]; rfl
  map_smul' c f := by
    ext z
    show (c • f).toFun z.1 = c • f.toFun z.1
    rw [toFun_smul]; rfl

@[simp] theorem restrictₗ_apply (hKU : K ⊆ U) (f : BddHol U) : restrictₗ hKU f = restrict hKU f :=
  rfl

/-- **Restriction continuous-linear map** `BddHol U →L[ℂ] (K →ᵇ ℂ)` for `K ⊆ U` compact, with
operator norm `≤ 1`. -/
noncomputable def restrictCLM (hKU : K ⊆ U) : BddHol U →L[ℂ] (K →ᵇ ℂ) :=
  (restrictₗ hKU).mkContinuous 1 fun f => by
    rw [one_mul]
    -- `‖restrict f‖ ≤ ‖f‖`: every value `|f z|` for `z ∈ K ⊆ U` is `≤ ‖f‖`
    refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun z => ?_
    show ‖f.toFun z.1‖ ≤ ‖f‖
    exact f.norm_toFun_le (hKU z.2)

@[simp] theorem restrictCLM_apply (hKU : K ⊆ U) (f : BddHol U) :
    restrictCLM hKU f = restrict hKU f := rfl

theorem norm_restrictCLM_le (hKU : K ⊆ U) : ‖restrictCLM hKU‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### Precomposition with a continuous reindexing `τ : K → U`

The cross-chart Čech `δ⁰`/`δ¹` transport a cochain component holomorphic on one chart-image to a
neighbouring chart-image through the holomorphic transition `τ = φ_b ∘ φ_a⁻¹`. At the
functional-analysis level this is **precomposition**: `g ↦ (z ↦ g(τ z))`, where `τ` is continuous on a
compact `K ⊆ ℂ` and maps `K` into the open `U` where `g : BddHol U` lives. The result is a
bounded-continuous function on `K` (NOT a `BddHol`, since `τ`'s image need not be open), with operator
norm `≤ 1` (precomposition cannot increase the sup-norm). The manifold side supplies `τ` together with
its `ContinuousOn`/`MapsTo` witnesses (from the analytic transition `transition_analyticAt_of_mem`);
this section is pure one-variable analysis. (`restrictCLM` is the special case `τ = id`.) -/

/-- Bounded-continuous precomposition `g ↦ (z ↦ g(τ z))` on the compact `K`, for `τ` continuous on `K`
mapping into the open `U` where `g` lives. Continuity of the composite is `g.toFun` continuous on `U`
composed with `τ : K → U`. -/
noncomputable def precompBcf {τ : ℂ → ℂ} (hτcont : ContinuousOn τ K) (hτmaps : Set.MapsTo τ K U)
    (g : BddHol U) : K →ᵇ ℂ :=
  mkOfCompact ⟨fun z => g.toFun (τ z.1), by
    exact g.analyticOn.continuousOn.comp_continuous hτcont.restrict (fun z => hτmaps z.2)⟩

@[simp] theorem precompBcf_apply {τ : ℂ → ℂ} (hτcont : ContinuousOn τ K) (hτmaps : Set.MapsTo τ K U)
    (g : BddHol U) (z : K) : precompBcf hτcont hτmaps g z = g.toFun (τ z.1) := rfl

/-- Precomposition as a `ℂ`-linear map `BddHol U →ₗ[ℂ] (K →ᵇ ℂ)`. -/
noncomputable def precompₗ {τ : ℂ → ℂ} (hτcont : ContinuousOn τ K) (hτmaps : Set.MapsTo τ K U) :
    BddHol U →ₗ[ℂ] (K →ᵇ ℂ) where
  toFun := precompBcf hτcont hτmaps
  map_add' f g := by
    ext z; show (f + g).toFun (τ z.1) = f.toFun (τ z.1) + g.toFun (τ z.1)
    rw [toFun_add]; rfl
  map_smul' c f := by
    ext z; show (c • f).toFun (τ z.1) = c • f.toFun (τ z.1)
    rw [toFun_smul]; rfl

@[simp] theorem precompₗ_apply {τ : ℂ → ℂ} (hτcont : ContinuousOn τ K) (hτmaps : Set.MapsTo τ K U)
    (g : BddHol U) : precompₗ hτcont hτmaps g = precompBcf hτcont hτmaps g := rfl

/-- **Precomposition continuous-linear map** `BddHol U →L[ℂ] (K →ᵇ ℂ)` for `τ` continuous `K → U`,
operator norm `≤ 1`. The cross-chart transport of a sup-norm cochain component: a function
bounded-holomorphic on chart-`b`'s image, read on the compact `K` (a chart-`a` overlap shrinking)
through the transition `τ = φ_b ∘ φ_a⁻¹`. -/
noncomputable def precompCLM {τ : ℂ → ℂ} (hτcont : ContinuousOn τ K) (hτmaps : Set.MapsTo τ K U) :
    BddHol U →L[ℂ] (K →ᵇ ℂ) :=
  (precompₗ hτcont hτmaps).mkContinuous 1 fun g => by
    rw [one_mul]
    refine (BoundedContinuousFunction.norm_le (norm_nonneg g)).mpr fun z => ?_
    show ‖g.toFun (τ z.1)‖ ≤ ‖g‖
    exact g.norm_toFun_le (hτmaps z.2)

@[simp] theorem precompCLM_apply {τ : ℂ → ℂ} (hτcont : ContinuousOn τ K) (hτmaps : Set.MapsTo τ K U)
    (g : BddHol U) : precompCLM hτcont hτmaps g = precompBcf hτcont hτmaps g := rfl

theorem norm_precompCLM_le {τ : ℂ → ℂ} (hτcont : ContinuousOn τ K) (hτmaps : Set.MapsTo τ K U) :
    ‖precompCLM hτcont hτmaps‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **The restriction operator is a compact operator** (Montel; Forster 14.9 STEP 1).

For `U` open and `K ⋐ U` a compact *convex* subset, the restriction map
`restrictCLM : BddHol U →L[ℂ] (K →ᵇ ℂ)` is a compact operator. The proof reduces, via the standard
characterization `isCompactOperator_iff_isCompact_closure_image_closedBall`, to the relative
compactness of the restricted closed ball — which is exactly the proven Montel atom
`CechFiniteness.isCompact_closure_restrict_bddHolo` (Cauchy estimates + Arzelà–Ascoli). Convexity of
`K` is required by the atom. -/
theorem isCompactOperator_restrictCLM (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U)
    (hKconv : Convex ℝ K) :
    IsCompactOperator (restrictCLM (U := U) hKU) := by
  -- characterise compactness of the operator by the closed ball image (use radius `1`)
  show IsCompactOperator (⇑(restrictCLM (U := U) hKU).toLinearMap)
  rw [isCompactOperator_iff_isCompact_closure_image_closedBall
    (restrictCLM (U := U) hKU).toLinearMap (one_pos)]
  -- the image of the unit ball is the atom's range, with `S := ↥(closedBall 0 1)`, `M := 1`
  have hatom := CechFiniteness.isCompact_closure_restrict_bddHolo hU hKcpt hKU hKconv
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
  -- match the two closure-of-set expressions
  convert hatom using 3
  ext φ
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, by rwa [Metric.mem_closedBall, dist_zero_right]⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(s : BddHol U), by
      have := s.2; rwa [Metric.mem_closedBall, dist_zero_right] at this, rfl⟩

end BddHol

end Jacobians.Dolbeault
