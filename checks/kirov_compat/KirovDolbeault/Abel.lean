import KirovDolbeault.PeriodLattice
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Data.Finsupp.Weight
import Mathlib.Topology.LocallyFinsupp

/-!
# Abel's theorem on a compact Riemann surface

Abel's theorem (Abel 1826, Forster §20): a divisor `D` of degree 0 on a
compact Riemann surface is principal (i.e., `D = div f` for some
meromorphic function `f`) if and only if its Abel–Jacobi image is
zero in the Jacobian.

**Scope of this file.** Mathlib does not yet have:
* meromorphic functions on a manifold (only on a normed field),
* divisors on a manifold,
* the Picard group of a compact Riemann surface.

We lay out the types and signatures at the manifold level, state
Abel's theorem as an axiomatic class `HasAbelsTheorem`, and derive
`ofCurve_inj` from it. Filling in the class is ~thousands of lines
of Mathlib-contribution-sized work (divisor theory + residue theorem
+ Riemann–Roch).

## References

* Forster, *Lectures on Riemann Surfaces*, §§17–21.
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. V §§1–4.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Topology

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Meromorphic functions on a compact Riemann surface

A function `f : X → ℂ` is meromorphic if it is meromorphic in every
chart. In Mathlib, `Meromorphic` is defined for `𝕜 → E`; the
manifold version below composes with chart inverses. -/

/-- A meromorphic function on `X` is a map `X → ℂ` that is
meromorphic at every chart-image point of every chart. The predicate
and its basic theory (addition, multiplication, order at a point) are
not yet formalised. -/
def IsMeromorphic (f : X → ℂ) : Prop :=
  ∀ x : X, MeromorphicAt (f ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)

/-- The type of meromorphic functions on `X`. -/
structure MeromorphicFunction : Type _ where
  toFun : X → ℂ
  meromorphic : IsMeromorphic X toFun

/-! ### Divisors on a compact Riemann surface

A divisor is a formal ℤ-linear combination of points of `X`, with
finite support. For compact `X`, this is simply `X →₀ ℤ`. -/

/-- A divisor on `X`: a formal ℤ-linear combination of points, with
finite support. For compact `X` (as here), finite support is
automatic from the support condition. -/
abbrev Divisor : Type _ := X →₀ ℤ

/-- The degree of a divisor is the sum of its coefficients. Defines
a group homomorphism `Divisor X →+ ℤ` via `Finsupp.degree`. -/
def Divisor.deg : Divisor X →+ ℤ := Finsupp.degree

/-- The subgroup of degree-zero divisors. On a compact Riemann
surface, every principal divisor has degree 0 (Forster Cor 4.25). -/
noncomputable def DivisorOfDegZero : AddSubgroup (Divisor X) :=
  (Divisor.deg X).ker

/-! ### Basic degree computations -/

@[simp]
theorem Divisor.deg_zero : Divisor.deg X 0 = 0 :=
  map_zero _

@[simp]
theorem Divisor.deg_add (D D' : Divisor X) :
    Divisor.deg X (D + D') = Divisor.deg X D + Divisor.deg X D' :=
  map_add _ _ _

@[simp]
theorem Divisor.deg_neg (D : Divisor X) :
    Divisor.deg X (-D) = -Divisor.deg X D :=
  map_neg _ _

@[simp]
theorem Divisor.deg_sub (D D' : Divisor X) :
    Divisor.deg X (D - D') = Divisor.deg X D - Divisor.deg X D' :=
  map_sub _ _ _

@[simp]
theorem Divisor.deg_single (P : X) (n : ℤ) :
    Divisor.deg X (Finsupp.single P n) = n := by
  show Finsupp.degree (Finsupp.single P n) = n
  by_cases hn : n = 0
  · simp [hn]
  · simp [Finsupp.degree_apply, Finsupp.support_single _ hn,
      Finsupp.single_eq_same]

/-! ### Two-point divisor `P - Q`

The fundamental degree-0 divisor associated with two points. Every
divisor of degree 0 decomposes as a ℤ-linear combination of such
two-point divisors (choose any basepoint and subtract). -/

/-- The divisor `P - Q` (formal difference of points, as a
degree-0 divisor via `Finsupp.single`). -/
noncomputable def twoPointDivisor (P Q : X) : Divisor X :=
  Finsupp.single P 1 - Finsupp.single Q 1

@[simp]
theorem twoPointDivisor_deg (P Q : X) :
    Divisor.deg X (twoPointDivisor X P Q) = 0 := by
  simp [twoPointDivisor]

theorem twoPointDivisor_mem_degZero (P Q : X) :
    twoPointDivisor X P Q ∈ DivisorOfDegZero X := by
  show Divisor.deg X (twoPointDivisor X P Q) = 0
  exact twoPointDivisor_deg X P Q

@[simp]
theorem twoPointDivisor_self (P : X) : twoPointDivisor X P P = 0 := by
  simp [twoPointDivisor]

/-! ### Real divisor construction via `meromorphicOrderAt`

The order of a meromorphic function at a point `x ∈ X` is read off
the chart pullback: pick any chart `φ` around `x`, and compute
`meromorphicOrderAt (f ∘ φ⁻¹) (φ x)`. Mathlib's
`meromorphicOrderAt : (𝕜 → E) → 𝕜 → WithTop ℤ` returns `⊤` if `f`
is identically zero near `x`, and the finite order otherwise. Cast
to `ℤ` via `.untop₀` (sending `⊤ ↦ 0`).

**Chart-independence** (content): orders of meromorphic functions
are invariant under biholomorphic coordinate change. Not proved
here; left as an assumed property of the real construction.

**Finite support** (content): on a compact `X`, a meromorphic
function has finitely many zeros and poles. Classical: zeros/poles
of a non-identically-zero meromorphic function are isolated, and
compactness + isolation ⇒ finite. -/

variable {X} in
/-- The integer order of `f` at `x`, via the chart pullback. -/
noncomputable def MeromorphicFunction.orderAtPoint (f : MeromorphicFunction X) (x : X) : ℤ :=
  (meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm)
    ((chartAt (H := ℂ) x) x)).untop₀

/-! #### Subtasks for finite-support

We decompose the finite-support proof into:

1. **Local finiteness** (`orderAtPoint_locallyFinite`): around each
   `x ∈ X`, a neighborhood exists in which only finitely many points
   have nonzero order. Requires chart-level `MeromorphicAt` isolation
   (`MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`) +
   chart-invariance of order. Remaining gap.
2. **Wrap as `locallyFinsuppWithin Set.univ`** via the structure
   constructor.
3. **Apply `.finiteSupport`** with `isCompact_univ` (from `CompactSpace X`).
4. **Convert** to `Finsupp` via `Finsupp.ofSupportFinite`. -/

/-! #### Two classical lemmas, following Forster §6

Forster's `div f` is built from two classical facts:

1. **Order is chart-invariant** (`orderAtPoint_invariant`): for `y` in
   any chart source, `meromorphicOrderAt (f ∘ chart.symm) (chart y)`
   has the same `.untop₀` as via `chart_y`. Follows from
   `meromorphicOrderAt_comp_of_deriv_ne_zero` applied to chart
   transitions; the latter are biholomorphic by `IsManifold 𝓘(ℂ) ω`.

2. **Zeros/poles are isolated** (`orderAtPoint_isolated_at`): around
   any point, meromorphicity + dichotomy + isolation gives a
   neighborhood in chart_z.source where the order is 0 except
   possibly at the center point.

Together, these close `supportLocallyFiniteWithinDomain'`. Both are
textbook lemmas (Forster §6.4, Miranda II.4). -/

/-! #### The Mathlib-missing pieces for `orderAtPoint_isolated_at`

Two textbook lemmas that Mathlib does not currently have for
manifold-level meromorphic functions:

**Lemma A** (`orderAtPoint_eq_zero_of_eventually_zero`): if `f` is
identically zero in a neighborhood of `y` (as a function on `X`),
then `orderAtPoint f y = 0`. Follows from `.untop₀ ⊤ = 0`: f ≡ 0
near y ⇒ (f ∘ chart_y.symm) = 0 eventually ⇒ meromorphicOrderAt = ⊤.

**Lemma B** (`orderAtPoint_chart_invariant`): the order is
chart-invariant. Specifically, `orderAtPoint f y = (meromorphicOrderAt
(f ∘ chart_z.symm) (chart_z y)).untop₀` for `y ∈ chart_z.source`.
Follows from `meromorphicOrderAt_comp_of_deriv_ne_zero` applied to
the chart transition `chart_z ∘ chart_y.symm`, which is analytic
with nonzero derivative (from `IsManifold 𝓘(ℂ) ω`). -/

variable {X} in
/-- **Lemma A**: f identically zero near y ⇒ orderAtPoint f y = 0. -/
theorem MeromorphicFunction.orderAtPoint_eq_zero_of_eventually_zero
    (f : MeromorphicFunction X) (y : X)
    (h : ∀ᶠ x in 𝓝 y, f.toFun x = 0) : f.orderAtPoint y = 0 := by
  -- chart.symm (chart y) = y.
  have h_symm_eq : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) = y :=
    (chartAt (H := ℂ) y).left_inv (mem_chart_source ℂ y)
  -- chart.symm maps chart y continuously to y.
  have h_cont : ContinuousAt (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) :=
    (chartAt (H := ℂ) y).continuousAt_symm
      ((chartAt (H := ℂ) y).map_source (mem_chart_source ℂ y))
  -- Rewrite h to use chart.symm (chart y) = y.
  have h' : ∀ᶠ x in 𝓝 ((chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y)),
      f.toFun x = 0 := by rw [h_symm_eq]; exact h
  -- So for w near chart y, (f ∘ chart.symm) w = f(chart.symm w) → 0.
  have h_chart : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) y) y),
      (f.toFun ∘ (chartAt (H := ℂ) y).symm) w = 0 := h_cont.eventually h'
  -- Eventually zero on a pointed nbhd too.
  have h_pw : ∀ᶠ w in 𝓝[{((chartAt (H := ℂ) y) y)}ᶜ] ((chartAt (H := ℂ) y) y),
      (f.toFun ∘ (chartAt (H := ℂ) y).symm) w = 0 :=
    h_chart.filter_mono nhdsWithin_le_nhds
  -- meromorphicOrderAt is ⊤ for eventually-zero in pointed nbhd.
  have h_order : meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) y).symm)
      ((chartAt (H := ℂ) y) y) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr h_pw
  show (meromorphicOrderAt _ _).untop₀ = 0
  rw [h_order]
  exact WithTop.untop₀_top

variable {X} in
/-- **Lemma B** (Mathlib-missing): chart-invariance of the order.
The order computed via an arbitrary chart `e` matches `orderAtPoint`
(computed via `chart_y`).

Proof outline (Forster §6):
1. Show `f ∘ chart_y.symm =ᶠ (f ∘ e.symm) ∘ (e ∘ chart_y.symm)` in a
   pointed nbhd of `chart_y y`, using `e.left_inv` on points where
   `chart_y.symm w ∈ e.source` (guaranteed by continuity of
   `chart_y.symm` + openness of `e.source`).
2. Apply `meromorphicOrderAt_congr` to turn LHS into the composition.
3. Apply `meromorphicOrderAt_comp_of_deriv_ne_zero` with
   `g := e ∘ chart_y.symm` analytic at `chart_y y` with nonzero
   derivative (both from `IsManifold 𝓘(ℂ) ω` — chart transitions
   are biholomorphic).

**Currently unproved** — formalizing chart-transition analyticity
(`g` analytic) + nonzero derivative on a ℂ-manifold requires
~50-100 lines of manifold + Mathlib bridging. -/
theorem MeromorphicFunction.orderAtPoint_chart_invariant
    (f : MeromorphicFunction X) {y : X}
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (hy : y ∈ e.source) :
    (meromorphicOrderAt (f.toFun ∘ e.symm) (e y)).untop₀ =
      f.orderAtPoint y := by
  suffices h : meromorphicOrderAt (f.toFun ∘ e.symm) (e y) =
      meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) by
    show (meromorphicOrderAt (f.toFun ∘ e.symm) (e y)).untop₀ = _
    rw [h]
    rfl
  -- Step 1: `chart_y.symm w ∈ e.source` for w near `chart_y y`.
  have h_y_eq : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) = y :=
    (chartAt (H := ℂ) y).left_inv (mem_chart_source ℂ y)
  have h_cont_symm : ContinuousAt (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) :=
    (chartAt (H := ℂ) y).continuousAt_symm
      ((chartAt (H := ℂ) y).map_source (mem_chart_source ℂ y))
  have h_source : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) y) y),
      (chartAt (H := ℂ) y).symm w ∈ e.source := by
    have : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) y) y),
        (chartAt (H := ℂ) y).symm w ∈ e.source := by
      have h1 : (chartAt (H := ℂ) y).symm ⁻¹' e.source ∈ 𝓝 ((chartAt (H := ℂ) y) y) := by
        apply h_cont_symm.preimage_mem_nhds
        rw [h_y_eq]
        exact e.open_source.mem_nhds hy
      exact h1
    exact this
  -- Step 2: eventual equality of chart pullbacks.
  have h_eq : (f.toFun ∘ (chartAt (H := ℂ) y).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) y) y)]
      (f.toFun ∘ e.symm) ∘ (e ∘ (chartAt (H := ℂ) y).symm) := by
    filter_upwards [h_source] with w hw
    show f.toFun ((chartAt (H := ℂ) y).symm w) =
      f.toFun (e.symm (e ((chartAt (H := ℂ) y).symm w)))
    rw [e.left_inv hw]
  -- Step 3: apply congr to get meromorphicOrderAt equality via composition.
  have h_ord_congr : meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) y).symm)
      ((chartAt (H := ℂ) y) y) =
      meromorphicOrderAt ((f.toFun ∘ e.symm) ∘ (e ∘ (chartAt (H := ℂ) y).symm))
        ((chartAt (H := ℂ) y) y) :=
    meromorphicOrderAt_congr (h_eq.filter_mono nhdsWithin_le_nhds)
  -- Step 4: `e ∘ chart_y.symm` evaluated at `chart_y y` equals `e y`.
  have h_ey : (e ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) = e y := by
    show e ((chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y)) = e y
    rw [h_y_eq]
  -- Step 5: apply `meromorphicOrderAt_comp_of_deriv_ne_zero` to reduce composition.
  have h_comp_ord : meromorphicOrderAt ((f.toFun ∘ e.symm) ∘ (e ∘ (chartAt (H := ℂ) y).symm))
      ((chartAt (H := ℂ) y) y) =
      meromorphicOrderAt (f.toFun ∘ e.symm) (e y) := by
    rw [show meromorphicOrderAt (f.toFun ∘ e.symm) (e y) =
      meromorphicOrderAt (f.toFun ∘ e.symm) ((e ∘ (chartAt (H := ℂ) y).symm)
        ((chartAt (H := ℂ) y) y)) by rw [h_ey]]
    -- Remaining two atomic sub-sorries: chart-transition is analytic +
    -- has nonzero derivative. Both follow from
    -- `OpenPartialHomeomorph.contDiffOn_extend_coord_change` + compositions,
    -- but the bridging (extChartAt → chartAt, ω ↔ analytic, biholomorphism
    -- inverse function theorem) is ~100+ lines each.
    -- Step A1-A2: e and chart_y are both in maximalAtlas 𝓘(ℂ) ω.
    have he_max : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
      IsManifold.subset_maximalAtlas _he
    have hchart_max : chartAt (H := ℂ) y ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
      IsManifold.chart_mem_maximalAtlas y
    -- Step A3-A6: chart-transition is ContDiffWithinAt ℂ ω at the point, using
    -- Mathlib's point-based lemma. For I boundaryless, range I = univ, so
    -- ContDiffWithinAt univ = ContDiffAt.
    have hy_chart_src : y ∈ (chartAt (H := ℂ) y).source := mem_chart_source ℂ y
    have h_contDiffAt : ContDiffAt ℂ ω
        (↑(𝓘(ℂ).extendCoordChange (chartAt (H := ℂ) y) e))
        ((chartAt (H := ℂ) y).extend 𝓘(ℂ) y) := by
      have h := ModelWithCorners.contDiffWithinAt_extendCoordChange'
        hchart_max he_max hy_chart_src hy
      rwa [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
    -- Step A7: AnalyticAt at the point (ω = ⊤ definitionally).
    have h_analyticAt : AnalyticAt ℂ (↑(𝓘(ℂ).extendCoordChange (chartAt (H := ℂ) y) e))
        ((chartAt (H := ℂ) y).extend 𝓘(ℂ) y) :=
      h_contDiffAt.analyticAt
    -- Step A8: bridge extendCoordChange's coe to e ∘ chart_y.symm (rfl pointwise).
    have h_analytic : AnalyticAt ℂ (e ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) :=
      h_analyticAt
    -- Sub-gap B: nonzero derivative via biholomorphism.
    -- Inverse direction: `chart_y ∘ e.symm` is also analytic at `e y`.
    have h_analytic_inv : AnalyticAt ℂ ((chartAt (H := ℂ) y) ∘ e.symm) (e y) := by
      have h_contDiffAt' : ContDiffAt ℂ ω
          (↑(𝓘(ℂ).extendCoordChange e (chartAt (H := ℂ) y)))
          (e.extend 𝓘(ℂ) y) := by
        have h := ModelWithCorners.contDiffWithinAt_extendCoordChange'
          he_max hchart_max hy (mem_chart_source ℂ y)
        rwa [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
      exact h_contDiffAt'.analyticAt
    -- Composition `(chart_y ∘ e.symm) ∘ (e ∘ chart_y.symm) =ᶠ id` near chart_y y.
    have h_comp_id : ((chartAt (H := ℂ) y) ∘ e.symm) ∘ (e ∘ (chartAt (H := ℂ) y).symm)
        =ᶠ[𝓝 ((chartAt (H := ℂ) y) y)] id := by
      have h_target_nhd : (chartAt (H := ℂ) y).target ∈ 𝓝 ((chartAt (H := ℂ) y) y) :=
        (chartAt (H := ℂ) y).open_target.mem_nhds
          ((chartAt (H := ℂ) y).map_source (mem_chart_source ℂ y))
      filter_upwards [h_source, h_target_nhd] with w hw_e hw_target
      show (chartAt (H := ℂ) y) (e.symm (e ((chartAt (H := ℂ) y).symm w))) = w
      rw [e.left_inv hw_e, (chartAt (H := ℂ) y).right_inv hw_target]
    -- Chain rule: deriv of composition = deriv(id) = 1.
    have h_nonzero : deriv (e ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) ≠ 0 := by
      intro h_deriv_zero
      have h_diff_outer : DifferentiableAt ℂ ((chartAt (H := ℂ) y) ∘ e.symm) (e y) :=
        h_analytic_inv.differentiableAt
      have h_diff_inner : DifferentiableAt ℂ (e ∘ (chartAt (H := ℂ) y).symm)
          ((chartAt (H := ℂ) y) y) :=
        h_analytic.differentiableAt
      have h_comp_deriv := deriv_comp ((chartAt (H := ℂ) y) y)
        (h_ey ▸ h_diff_outer) h_diff_inner
      rw [h_comp_id.deriv_eq] at h_comp_deriv
      rw [h_ey] at h_comp_deriv
      rw [deriv_id] at h_comp_deriv
      rw [h_deriv_zero, mul_zero] at h_comp_deriv
      exact one_ne_zero h_comp_deriv
    exact meromorphicOrderAt_comp_of_deriv_ne_zero
      (g := e ∘ (chartAt (H := ℂ) y).symm) (f := f.toFun ∘ e.symm)
      (x := (chartAt (H := ℂ) y) y)
      h_analytic h_nonzero
  -- Assemble.
  rw [h_comp_ord.symm]
  exact h_ord_congr.symm

variable {X} in
/-- **Isolation of zeros/poles** around a point (Forster §6 /
Miranda II.4). Combines Lemma A (identically zero case) and
Lemma B (chart invariance, Mathlib-missing) with the dichotomy
`MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`. -/
theorem MeromorphicFunction.orderAtPoint_isolated_at
    (f : MeromorphicFunction X) (z : X) :
    ∃ t ∈ 𝓝 z, ∀ y ∈ t, y ≠ z → f.orderAtPoint y = 0 := by
  -- Apply the dichotomy at chart_z z.
  have hmero := f.meromorphic z
  rcases hmero.eventually_eq_zero_or_eventually_ne_zero with h_zero | h_nz
  · -- Case A: (f ∘ chart_z.symm) w = 0 eventually in pointed nbhd of chart_z z.
    -- Transfer to X: get an open nbhd V of z in X with f ≡ 0 on V \ {z}.
    have h_chart_nhd : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) z) z),
        w ∉ ({(chartAt (H := ℂ) z) z} : Set ℂ) → (f.toFun ∘ (chartAt (H := ℂ) z).symm) w = 0 := by
      have : ∀ᶠ (y : ℂ) in 𝓝 ((chartAt (H := ℂ) z) z),
          y ∉ ({(chartAt (H := ℂ) z) z} : Set ℂ) →
          (f.toFun ∘ (chartAt (H := ℂ) z).symm) y = 0 := by
        rw [Filter.Eventually, mem_nhdsWithin_iff_eventually] at h_zero
        filter_upwards [h_zero] with y hy hys
        exact hy hys
      exact this
    -- Pull back via chart_z continuity.
    have h_at_z : ContinuousAt (chartAt (H := ℂ) z) z :=
      (chartAt (H := ℂ) z).continuousAt (mem_chart_source ℂ z)
    have h_X_cond : ∀ᶠ x in 𝓝 z, x ≠ z →
        (f.toFun ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) x) = 0 := by
      have := h_at_z.eventually h_chart_nhd
      filter_upwards [this,
        (chartAt (H := ℂ) z).open_source.mem_nhds (mem_chart_source ℂ z)] with x hx hx_src hx_ne
      apply hx
      intro heq
      rw [Set.mem_singleton_iff] at heq
      exact hx_ne ((chartAt (H := ℂ) z).injOn hx_src (mem_chart_source ℂ z) heq)
    -- Rewrite using left_inv to get f ≡ 0 near z except at z.
    have h_X : ∀ᶠ x in 𝓝 z, x ≠ z → f.toFun x = 0 := by
      filter_upwards [h_X_cond,
        (chartAt (H := ℂ) z).open_source.mem_nhds (mem_chart_source ℂ z)] with x hx hx_src hx_ne
      have := hx hx_ne
      rwa [Function.comp_apply, (chartAt (H := ℂ) z).left_inv hx_src] at this
    -- Extract an open nbhd V ⊆ 𝓝 z where x ∈ V ∧ x ≠ z → f x = 0.
    rw [Filter.eventually_iff_exists_mem] at h_X
    obtain ⟨V, hV_mem, hV⟩ := h_X
    obtain ⟨U, hU_V, hU_open, hz_U⟩ := mem_nhds_iff.mp hV_mem
    refine ⟨U, hU_open.mem_nhds hz_U, ?_⟩
    intro y hy_U hy_ne
    -- f ≡ 0 in a neighborhood of y (namely, U \ {z} which is open and contains y).
    apply f.orderAtPoint_eq_zero_of_eventually_zero y
    have hU_y : U ∈ 𝓝 y := hU_open.mem_nhds hy_U
    have h_y_ne_z : {z}ᶜ ∈ 𝓝 y :=
      isOpen_compl_singleton.mem_nhds (by simpa using hy_ne)
    filter_upwards [hU_y, h_y_ne_z] with x hx_U hx_ne
    exact hV x (hU_V hx_U) hx_ne
  · -- Case B: f ∘ chart_z.symm ≠ 0 eventually in pointed nbhd of chart_z z.
    -- Strategy: extract Laurent expansion (f ∘ chart_z.symm =ᶠ (w - chart_z z)^n • g).
    -- For w near chart_z z with w ≠ chart_z z, this gives an analytic nonzero
    -- function at w, so meromorphicOrderAt at w = 0. Then use Lemma B to
    -- transfer to orderAtPoint f y.
    have hmero_ne_top : meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) z).symm)
        ((chartAt (H := ℂ) z) z) ≠ ⊤ :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmero).mpr h_nz
    obtain ⟨g, hg_analytic, hg_ne_zero, h_laurent⟩ :=
      (meromorphicOrderAt_ne_top_iff hmero).mp hmero_ne_top
    -- Let n := the finite order.
    set n := (meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) z).symm)
      ((chartAt (H := ℂ) z) z)).untop₀
    -- g is analytic in a nbhd of chart_z z, nonzero, and locally analytic around each point.
    have hg_ne_zero_nbhd : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) z) z), g w ≠ 0 :=
      hg_analytic.continuousAt.eventually_ne hg_ne_zero
    have hg_analyticAt_nbhd : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) z) z), AnalyticAt ℂ g w :=
      hg_analytic.eventually_analyticAt
    -- Also need a nbhd of chart_z z where h_laurent holds (subset of pointed nbhd).
    -- h_laurent : f ∘ chart_z.symm =ᶠ g' near chart_z z (pointed).
    obtain ⟨U, hU_mem, hU_eq⟩ : ∃ U ∈ 𝓝 ((chartAt (H := ℂ) z) z),
        ∀ w ∈ U, w ≠ (chartAt (H := ℂ) z) z →
          (f.toFun ∘ (chartAt (H := ℂ) z).symm) w =
            (w - (chartAt (H := ℂ) z) z)^n • g w := by
      have h_lau_ev : ∀ᶠ w in 𝓝[≠] (chartAt (H := ℂ) z) z,
          (f.toFun ∘ (chartAt (H := ℂ) z).symm) w =
            (w - (chartAt (H := ℂ) z) z)^n • g w := h_laurent
      rw [eventually_nhdsWithin_iff, Filter.eventually_iff_exists_mem] at h_lau_ev
      obtain ⟨U, hU_mem, hU_eq⟩ := h_lau_ev
      exact ⟨U, hU_mem, fun w hw hne => hU_eq w hw (by simpa using hne)⟩
    -- Extract an open V ⊆ U containing chart_z z so V ∈ 𝓝 (chart_z y) whenever chart_z y ∈ V.
    obtain ⟨V, hV_sub_U, hV_open, hz_V⟩ := mem_nhds_iff.mp hU_mem
    have hV_mem : V ∈ 𝓝 ((chartAt (H := ℂ) z) z) := hV_open.mem_nhds hz_V
    -- Continuity of chart_z at z.
    have h_chart_cont : ContinuousAt (chartAt (H := ℂ) z) z :=
      (chartAt (H := ℂ) z).continuousAt (mem_chart_source ℂ z)
    -- Pull everything back to a nbhd of z, threading V through.
    have h_X_nbhd : ∀ᶠ y in 𝓝 z,
        y ∈ (chartAt (H := ℂ) z).source ∧
        AnalyticAt ℂ g ((chartAt (H := ℂ) z) y) ∧
        g ((chartAt (H := ℂ) z) y) ≠ 0 ∧
        ((chartAt (H := ℂ) z) y ∈ V) := by
      filter_upwards [(chartAt (H := ℂ) z).open_source.mem_nhds (mem_chart_source ℂ z),
        h_chart_cont.preimage_mem_nhds hg_ne_zero_nbhd,
        h_chart_cont.preimage_mem_nhds hg_analyticAt_nbhd,
        h_chart_cont.preimage_mem_nhds hV_mem] with y hy_src hy_g hy_ana hy_V
      exact ⟨hy_src, hy_ana, hy_g, hy_V⟩
    obtain ⟨t, ht_nhds, ht⟩ := Filter.eventually_iff_exists_mem.mp h_X_nbhd
    refine ⟨t, ht_nhds, ?_⟩
    intro y hy_t hy_ne
    obtain ⟨hy_src, hy_ana, hy_g', hy_V⟩ := ht y hy_t
    -- chart_z y ≠ chart_z z since y ≠ z and chart_z is injective on source.
    have h_chart_ne : (chartAt (H := ℂ) z) y ≠ (chartAt (H := ℂ) z) z := by
      intro heq
      exact hy_ne ((chartAt (H := ℂ) z).injOn hy_src (mem_chart_source ℂ z) heq)
    -- Apply Lemma B to transfer: orderAtPoint f y = (meromorphicOrderAt (f ∘ chart_z.symm) (chart_z y)).untop₀.
    rw [← f.orderAtPoint_chart_invariant (chartAt (H := ℂ) z) (chart_mem_atlas ℂ z) hy_src]
    -- Set g' := fun w => (w - chart_z z)^n • g w.
    set g' : ℂ → ℂ := fun w => (w - (chartAt (H := ℂ) z) z)^n • g w with hg'_def
    -- g' is analytic at chart_z y (product of nonzero analytic factors).
    have hg'_analytic : AnalyticAt ℂ g' ((chartAt (H := ℂ) z) y) := by
      rw [hg'_def]
      exact (((analyticAt_id).sub analyticAt_const).zpow
        (sub_ne_zero_of_ne h_chart_ne)).smul hy_ana
    -- g'(chart_z y) ≠ 0 via product of nonzero factors.
    have hg'_ne : g' ((chartAt (H := ℂ) z) y) ≠ 0 := by
      rw [hg'_def]
      exact smul_ne_zero (zpow_ne_zero _ (sub_ne_zero_of_ne h_chart_ne)) hy_g'
    -- f ∘ chart_z.symm =ᶠ g' in pointed nbhd of chart_z y (using V and {chart_z z}ᶜ).
    have hV_nhd_y : V ∈ 𝓝 ((chartAt (H := ℂ) z) y) := hV_open.mem_nhds hy_V
    have h_ne_cz : {(chartAt (H := ℂ) z) z}ᶜ ∈ 𝓝 ((chartAt (H := ℂ) z) y) :=
      isOpen_compl_singleton.mem_nhds h_chart_ne
    have h_ev_eq :
        (f.toFun ∘ (chartAt (H := ℂ) z).symm) =ᶠ[𝓝[≠] (chartAt (H := ℂ) z) y] g' := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hV_nhd_y,
        mem_nhdsWithin_of_mem_nhds h_ne_cz] with w hw_V hw_ne_cz
      rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw_ne_cz
      exact hU_eq w (hV_sub_U hw_V) hw_ne_cz
    -- Conclude via meromorphicOrderAt_congr + analytic order at nonzero point = 0.
    rw [meromorphicOrderAt_congr h_ev_eq, hg'_analytic.meromorphicOrderAt_eq,
      (hg'_analytic.analyticOrderAt_eq_zero).mpr hg'_ne]
    rfl

variable {X} in
/-- The order function as a `locallyFinsuppWithin` on `Set.univ`.
Wraps `orderAtPoint` together with the local-finiteness proof
derived from `orderAtPoint_isolated_at`. -/
noncomputable def MeromorphicFunction.orderLocallyFinsupp (f : MeromorphicFunction X) :
    Function.locallyFinsuppWithin (Set.univ : Set X) ℤ where
  toFun := MeromorphicFunction.orderAtPoint f
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := by
    intro z _
    obtain ⟨t, ht_nhds, ht⟩ := f.orderAtPoint_isolated_at z
    refine ⟨t, ht_nhds, ?_⟩
    -- Support ∩ t ⊆ {z} (since ht says y ∈ t ∧ y ≠ z ⇒ order = 0 ⇒ y ∉ support).
    apply Set.Finite.subset (Set.finite_singleton z)
    intro y ⟨hy_t, hy_supp⟩
    by_contra hne
    exact hy_supp (ht y hy_t hne)

/-- **Real divisor of a meromorphic function**. Uses the
`locallyFinsuppWithin` wrapper + `finiteSupport` + `ofSupportFinite`.
The content gap is `supportLocallyFiniteWithinDomain'` above. -/
noncomputable def MeromorphicFunction.divViaOrder (f : MeromorphicFunction X) : Divisor X :=
  Finsupp.ofSupportFinite (MeromorphicFunction.orderAtPoint f)
    ((MeromorphicFunction.orderLocallyFinsupp f).finiteSupport isCompact_univ)

/-- **The divisor of a meromorphic function** (classical construction
`div f = (zeros of f) - (poles of f)` with multiplicities). Now real
via `divViaOrder`, now that `orderAtPoint_isolated_at` is closed. -/
noncomputable def MeromorphicFunction.div (f : MeromorphicFunction X) : Divisor X :=
  MeromorphicFunction.divViaOrder X f

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The zero function is trivially meromorphic: chart pullbacks of constant functions are constant,
hence meromorphic. Needs only the charted-space structure (no compactness / connectedness), so it
applies to open submanifolds `↥U` too. -/
theorem IsMeromorphic.zero : IsMeromorphic X (fun _ => 0) := by
  intro x
  show MeromorphicAt (fun _ => (0 : ℂ)) ((chartAt (H := ℂ) x) x)
  exact MeromorphicAt.const 0 _

/-! ### Principal-divisor scaffolding removed

The `PrincipalDivisors` subgroup, the residue-theorem leaf `deg_div`
(`deg (div f) = 0`), and `PrincipalDivisors_le_DivisorOfDegZero` were
dead: nothing downstream consumed them. `ofCurve_inj` does not route
through the principal-divisor formulation of Abel's theorem; it needs
`abelJacobi_twoPoint_ne_zero` directly (the remaining gap below). The
degree-0 *target* subgroup `DivisorOfDegZero` survives — `abelJacobi`
is defined on it. -/

/-! ### Abel–Jacobi map (on divisors of degree 0)

For a divisor `D = ∑ n_i · P_i` with `∑ n_i = 0`, the Abel–Jacobi
image is `∑ n_i · ofCurve P₀ P_i` for a chosen basepoint `P₀`
(the result is independent of `P₀` because `∑ n_i = 0`).

Note this depends on `ofCurve` being a real path-integrated map, not
the current placeholder. -/

variable {X} in
/-- Abel–Jacobi map: sends a degree-0 divisor `D = ∑ n_i · P_i` to
`∑ n_i · [ofCurve basepoint P_i]` in the Jacobian `(Fin gX → ℂ) ⧸ lattice`.

**Well-definedness** (independence of basepoint): uses `∑ n_i = 0`
to absorb the basepoint choice. For any two basepoints P₀, P₀':
`AJ_{P₀} D - AJ_{P₀'} D = (∑ n_i) · [smoothPath P₀' P₀] = 0` (since ∑ n_i = 0).

Now real: uses `smoothPath` from `HasSmoothPaths` typeclass
and sums `periodVec` of paths from a fixed basepoint `P₀` to each
point in the support of `D`, weighted by multiplicities, projected
to the Jacobian quotient. -/
noncomputable def abelJacobi (D : DivisorOfDegZero X) :
    (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup := by
  classical
  exact ∑ P ∈ (D : Divisor X).support,
    ((D : Divisor X) P) •
      QuotientAddGroup.mk (periodVec (smoothPath (Classical.arbitrary X) P))

variable {X} in
/-- **Abel-Jacobi on a two-point divisor.** For `A ≠ B`:
`abelJacobi (A - B) = ofCurve P₀ A - ofCurve P₀ B` where `P₀ =
Classical.arbitrary X`. Direct computation from the definition:
`twoPointDivisor A B = single A 1 - single B 1` has support `{A, B}`
for `A ≠ B`, and the weighted `periodVec` sum unfolds to the
difference. -/
theorem abelJacobi_twoPointDivisor (A B : X) (hne : A ≠ B) :
    abelJacobi ⟨twoPointDivisor X A B, twoPointDivisor_mem_degZero X A B⟩ =
      QuotientAddGroup.mk (periodVec (smoothPath (Classical.arbitrary X) A)) -
      QuotientAddGroup.mk (periodVec (smoothPath (Classical.arbitrary X) B)) := by
  classical
  unfold abelJacobi
  -- Compute: `(twoPointDivisor A B).sum` over support with value (D P) • mk(periodVec(sp(P₀,P)))
  have hAnB : ¬ A = B := hne
  have hBnA : ¬ B = A := Ne.symm hne
  have hsupp : (twoPointDivisor X A B).support = ({A, B} : Finset X) := by
    ext P
    simp only [twoPointDivisor, Finsupp.mem_support_iff, Finsupp.coe_sub, Pi.sub_apply,
      Finsupp.single_apply, Finset.mem_insert, Finset.mem_singleton]
    by_cases hPA : A = P
    · subst hPA
      simp [hBnA]
    · by_cases hPB : B = P
      · subst hPB
        simp [hAnB]
      · simp [hPA, hPB, show (P = A ↔ A = P) from eq_comm,
          show (P = B ↔ B = P) from eq_comm]
  have hA : (twoPointDivisor X A B : Divisor X) A = 1 := by
    simp [twoPointDivisor, Finsupp.coe_sub, Pi.sub_apply, hBnA]
  have hB : (twoPointDivisor X A B : Divisor X) B = -1 := by
    simp [twoPointDivisor, Finsupp.coe_sub, Pi.sub_apply, hAnB]
  show ∑ P ∈ (twoPointDivisor X A B).support,
    (twoPointDivisor X A B : Divisor X) P • _ = _
  rw [hsupp, Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  rw [hA, hB]
  show (1 : ℤ) • _ + (-1 : ℤ) • _ = _ - _
  simp [sub_eq_add_neg]

/-! ### Abel's theorem itself

**Statement** (Forster 21.4): A degree-0 divisor `D` is principal iff
its Abel–Jacobi image is zero. Equivalently: the Abel–Jacobi map
induces an isomorphism `Pic⁰(X) ≃ Jacobian X`.

Axiomatized via a typeclass so downstream consequences can be
stated. Filling in this class is the Mathlib-contribution-scale
work to formalize divisor theory + residue theorem + Abel's proof. -/

-- `HasAbelsTheorem` class removed: reverted to hypothesis-based
-- `abelJacobi_twoPoint_ne_zero` below.

/-! ### Consequence: two-point divisors on positive-kirovGenus surfaces

For `X` of kirovGenus ≥ 1, the divisor `P - Q` with `P ≠ Q` is NOT
principal (Forster §21.5 / Miranda Ch. V §2.8). The classical
argument:

A principal divisor `P - Q` with `P ≠ Q` means some meromorphic
function `f` has a simple zero at `P` and a simple pole at `Q` and
no other zeros/poles. Such an `f` is a degree-1 map `X → ℙ¹`, which
must be a biholomorphism (by Riemann-Hurwitz: deg-1 covers are
isomorphisms). But then `X ≃ ℙ¹`, which has kirovGenus 0 — contradiction.

Axiomatized as a typeclass field `twoPointDivisor_not_principal_of_pos_genus`,
alongside Abel's theorem itself. This is the piece that, combined
with Abel, implies `abelJacobi (P - Q) ≠ 0`, the lemma needed for
`ofCurve_inj`. -/

variable {X} in
/-- **Consequence of Abel's theorem + non-existence of degree-1 maps
to ℙ¹ on positive-kirovGenus surfaces**: the Abel–Jacobi image of a
two-point divisor `P - Q` is nonzero when `P ≠ Q` on a surface of
positive kirovGenus.

Classical argument: if `abelJacobi (P - Q) = 0`, then by Abel's theorem
`P - Q` is principal — some meromorphic function `f` has a simple zero
at `P` and a simple pole at `Q` and no other zeros/poles. Such an `f`
is a degree-1 map `X → ℙ¹`, hence a biholomorphism (Riemann-Hurwitz).
But then `X ≃ ℙ¹`, which has kirovGenus 0 — contradiction. -/
theorem abelJacobi_twoPoint_ne_zero
    (h : 0 < kirovGenus X) {P Q : X} (hPQ : P ≠ Q) :
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ ≠ 0 :=
  sorry

/-! ### `no_distinct_points_placeholder` removed

The previous `HasAbelsTheorem.no_distinct_points_placeholder`
theorem used the placeholder `div ≡ 0` to conclude "every two
points are equal". With `div` now real (`divViaOrder`), this
placeholder chain no longer exists. Real `ofCurve_inj` requires
the genuine Abel theorem chain via `abelJacobi_twoPoint_ne_zero`,
which needs real `abelJacobi` connected to `ofCurve`. -/

/-! ### Derivation of `ofCurve_inj` from Abel's theorem

**Sketch** (Forster §21.5): if `ofCurve P Q = ofCurve P Q'` for
`Q ≠ Q'` on a surface with kirovGenus ≥ 1, then `Q - Q'` is a degree-0
divisor whose Abel–Jacobi image is zero. By Abel, `Q - Q'` is
principal: there exists a meromorphic `f` with a simple zero at `Q`
and a simple pole at `Q'`. Such an `f` defines a degree-1 map
`X → ℙ¹`, which is a biholomorphism (by Riemann-Hurwitz / the
hyperelliptic argument), making `X` of kirovGenus 0 — contradicting
`0 < kirovGenus X`.

Formalizing this fully requires:
* `ofCurve` to be the real path-integrated map.
* The Picard-group interpretation.
* Riemann-Hurwitz / degree-1 maps to ℙ¹.

These are still sorries downstream; `ofCurve_inj` in `Jacobians.lean`
remains axiomatic pending this chain. -/

end Jacobians
