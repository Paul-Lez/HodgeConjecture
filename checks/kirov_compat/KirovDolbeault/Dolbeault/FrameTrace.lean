/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.ResidueAtom
import KirovDolbeault.Dolbeault.FormTraceFibre
import KirovDolbeault.Dolbeault.FormTracePrincipalPart
import KirovDolbeault.Dolbeault.CanonicalFormDifferential
import KirovDolbeault.Dolbeault.FrameTraceWallInfty

/-!
# The frame-trace datum for the canonical `ω₀ = df` frame (T lane)

Construction layer for `CanonicalForm17Data.FrameTraceHypothesis` — the LAST residual input of
the keystone (`ResidueAtom.lean`): for the canonical datum with frame `ω₀ = df`, every global
meromorphic `F` admits a `FrameResidueTrace data F`.

## The reduction (proven here): the trace datum from a `LaurentForm` alone

The key structural observation: the `FibreTrace` fields of `FrameResidueTrace` are a
*representation device*, not independent content.  Given the partial-fraction `LaurentForm L`
of the trace, the per-centre fibre datum can be taken to be the **principal-part fibre**
(`principalPartFibre L p`): the single identity sheet over `p` carrying `L.R` itself as its
coefficient.  Its Lemma-3.2 field `hL32` and the finite-centre trace residue are then
*definitional* (`resAt L.R p` on both sides).  Consequently (`frameResidueTrace_of_laurentForm`)
a `FrameResidueTrace data F` exists as soon as a `LaurentForm L` realizes the two honest
geometric identities of Miranda §VIII.3:

* **(fin)** `∑_{p ∈ centres L} Res_p(L.R) = ∑_{y ≠ ∞} ∑_{a ∈ S, F a = y} Res_a(F·ω₀)` — the
  finite-fibre residue transport, and
* **(inf)** `Res_∞(L.R) = ∑_{a ∈ S, F a = ∞} Res_a(F·ω₀)` — the `∞`-fibre residue transport,

over any pole superset `S ⊇ supp(div F) ∪ supp K`.  These two identities are exactly the
content of "`L` represents the trace `Tr_F(F·ω₀)`"; everything else is proven.

## The unramified per-fibre layer (proven here)

Mirroring `FormTraceFibre` with the meromorphic-frame integrand: over a fibre of regular
non-pole points (`FibreRegularData`, frame-free, reused as-is) the `frameFibreTrace` has
per-sheet coefficients the atom's own chart integrands, the per-sheet residue bridge is
`resAt_frameChartIntegrand` (via the proven contour ↔ planar bridge
`resAt_eq_planarCoeff_neg_one`), and Lemma 3.2 over the fibre
(`resAt_traceCoeff_frameFibreTrace`) is unconditional.  For `ω₀ = df` and cover `= f`, the
per-sheet pushforward collapses to the **plain value trace** `F ∘ sheet`
(`frameFibreTrace_traceCoeff_df_eventuallyEq`) — `(f̂ ∘ sheet)' = 1` kills the Jacobian.

## The wall, CLOSED

`exists_frameTraceFunctionData_df` — the §VIII.3 trace assembly for the plain value trace —
is **proven**: the trace-function datum is constructed from the conservation-of-number engine
(`FrameTraceWallEngine`), the unweighted symmetric descent (`FrameTraceWallDescent`), the
per-centre cluster descents (`FrameTraceWallCluster`), and Lemma 3.2 at `∞`
(`FrameTraceWallInfty`).  Hence `frameTraceHypothesis_of_df`, the existential
`exists_canonicalData_frameTraceHypothesis`, and the unconditional keystone atom
`exists_canonicalData_residueAtom` are all sorry-free.

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), §VIII.3; Forster,
*Lectures on Riemann Surfaces* (GTM 81), §17.3.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical Real
open Filter Complex Metric

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace Jacobians

namespace Dolbeault

open Jacobians.TraceResidue Jacobians.MeromorphicTrace Jacobians.Dolbeault.FormTraceFibre

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The principal-part fibre: `FrameResidueTrace`'s fibre fields from the `LaurentForm` alone -/

/-- The partial-fraction coefficient `L.R` is meromorphic at every point (finite sum of Laurent
monomials, each meromorphic everywhere). -/
theorem meromorphicAt_laurentR (L : LaurentForm) (p : ℂ) : MeromorphicAt L.R p :=
  MeromorphicAt.fun_sum fun i _ => LaurentForm.meromorphicAt_monomial (L.c i) (L.a i) (L.n i) p

/-- **The principal-part fibre over a centre `p`**: the single identity sheet carrying `L.R`
itself as its coefficient.  Its trace coefficient *is* `L.R`, so the Lemma-3.2 bookkeeping of a
`FrameResidueTrace` built on it is definitional — the honest content moves entirely into the
two aggregate residue identities of the `LaurentForm`. -/
def principalPartFibre (L : LaurentForm) (p : ℂ) : FibreTrace where
  ι := Unit
  fintype_ι := inferInstance
  b := p
  sheet := fun _ => id
  pre := fun _ => p
  sheet_analytic := fun _ => analyticAt_id
  sheet_deriv_ne := fun _ => by simp
  sheet_base := fun _ => rfl
  coeff := fun _ => L.R
  coeff_mero := fun _ => meromorphicAt_laurentR L p

/-- The trace coefficient of the principal-part fibre is `L.R` itself (`deriv id = 1`). -/
theorem principalPartFibre_traceCoeff (L : LaurentForm) (p : ℂ) :
    (principalPartFibre L p).traceCoeff = L.R := by
  funext w
  show ∑ _i : Unit, L.R (id w) * deriv id w = L.R w
  simp

/-! ## The trace datum from a `LaurentForm` realizing the two residue identities -/

/-- **`FrameResidueTrace` from a `LaurentForm` alone (proven reduction).**  Given a
partial-fraction form `L` whose finite residues aggregate to the finite-fibre `frameRes` sums
(**fin**) and whose `∞`-residue is the `∞`-fibre `frameRes` sum (**inf**), the full trace datum
exists: take the principal-part fibres, for which `hL32` and the finite-centre trace residues
are definitional.  This isolates the honest content of the §VIII.3 assembly into the two
hypotheses `hfin`/`hinf`. -/
def frameResidueTrace_of_laurentForm (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (f : MeromorphicFunction X) (S : Finset X)
    (hS : F.div.support ∪ data.K.support ⊆ S) (L : LaurentForm)
    (hfin : ∑ p ∈ Finset.univ.image L.a, resAt L.R p
      = ∑ y ∈ (S.image f.toRiemannSphere).erase OnePoint.infty,
          ∑ a ∈ S with f.toRiemannSphere a = y, frameRes data F a)
    (hinf : resAtInfty L.R L.ρ
      = ∑ a ∈ S with f.toRiemannSphere a = OnePoint.infty, frameRes data F a) :
    FrameResidueTrace data F where
  f := f
  S := S
  hS := hS
  L := L
  fibre := principalPartFibre L
  hL32 := fun p _hp => by
    show ∑ _i : Unit, resAt L.R p = resAt L.R p
    simp
  infty_eq := hinf
  finite_eq := by
    have hcong : ∀ p ∈ Finset.univ.image L.a,
        resAt (principalPartFibre L p).traceCoeff (principalPartFibre L p).b = resAt L.R p :=
      fun p _ => by rw [principalPartFibre_traceCoeff]; rfl
    rw [Finset.sum_congr rfl hcong]
    exact hfin

/-! ## The unramified per-fibre layer for the frame integrand

The mirror of `FormTraceFibre` with the meromorphic-frame chart integrand of the atom itself
(`frameRes`'s integrand) in place of `chartIntegrand ω₀ g`.  The regularity interface
`FibreRegularData` is frame-free and reused as-is (with `g := F.toFun`). -/

/-- **The frame chart integrand** of `α = F·ω₀` at `a`: the integrand of `frameRes data F a`,
named.  `frameRes data F a` is its order-`(−1)` planar coefficient at the chart centre. -/
def frameChartIntegrand (data : CanonicalForm17Data X) (F : MeromorphicFunction X) (a : X) :
    ℂ → ℂ :=
  fun ζ => F.toFun ((chartAt (H := ℂ) a).symm ζ) * formCoeff data.ω₀.toFun a ζ

/-- The frame chart integrand is meromorphic at the chart centre. -/
theorem meromorphicAt_frameChartIntegrand (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (a : X) :
    MeromorphicAt (frameChartIntegrand data F a) ((chartAt (H := ℂ) a) a) :=
  frameRes_integrand_meromorphicAt data F a

/-- **Bridge (c) for the frame integrand**: the contour residue of the frame chart integrand
at the chart centre is `frameRes data F a` — the proven contour ↔ planar bridge
`resAt_eq_planarCoeff_neg_one` applied to the atom's integrand. -/
theorem resAt_frameChartIntegrand (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (a : X) :
    resAt (frameChartIntegrand data F a) ((chartAt (H := ℂ) a) a) = frameRes data F a :=
  resAt_eq_planarCoeff_neg_one (meromorphicAt_frameChartIntegrand data F a)

/-- The chart pullback of `f.holoRepr` at `pre i` evaluates to the base value `b` (frame-free
re-statement of `FibreRegularData.gval`, without the unused holomorphic-frame argument). -/
theorem FormTraceFibre.FibreRegularData.gval' {g : X → ℂ} (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b) (i : D.ι) :
    (fun z => f.holoRepr ((chartAt ℂ (D.xs i)).symm z)) ((chartAt ℂ (D.xs i)) (D.xs i)) = b := by
  show f.holoRepr ((chartAt ℂ (D.xs i)).symm ((chartAt ℂ (D.xs i)) (D.xs i))) = b
  rw [(chartAt ℂ (D.xs i)).left_inv (mem_chart_source ℂ (D.xs i))]
  exact D.hval i

/-- **The frame fibre trace over an unramified fibre**: the `FibreTrace` whose sheets are the
planar section germs of the cover (frame-free, `exists_planar_section`) and whose per-sheet
coefficients are the atom's own frame chart integrands. -/
def frameFibreTrace (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData F.toFun f b) : FibreTrace where
  ι := D.ι
  fintype_ι := D.fintype_ι
  b := b
  sheet := fun i =>
    Classical.choose (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval' f i))
  pre := fun i => (chartAt ℂ (D.xs i)) (D.xs i)
  sheet_analytic := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval' f i))).1
  sheet_deriv_ne := fun i =>
    (Classical.choose_spec
      (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval' f i))).2.2.1
  sheet_base := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval' f i))).2.1
  coeff := fun i => frameChartIntegrand data F (D.xs i)
  coeff_mero := fun i => meromorphicAt_frameChartIntegrand data F (D.xs i)

@[simp] theorem frameFibreTrace_b (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData F.toFun f b) :
    (frameFibreTrace data F f D).b = b := rfl

@[simp] theorem frameFibreTrace_pre (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData F.toFun f b) (i : D.ι) :
    (frameFibreTrace data F f D).pre i = (chartAt ℂ (D.xs i)) (D.xs i) := rfl

@[simp] theorem frameFibreTrace_coeff (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData F.toFun f b) (i : D.ι) :
    (frameFibreTrace data F f D).coeff i = frameChartIntegrand data F (D.xs i) := rfl

/-- **Lemma 3.2 over the unramified fibre, frame form (proven, unconditional)**: the trace
residue of the frame fibre trace at the base equals the fibre sum of the atom's `frameRes`. -/
theorem resAt_traceCoeff_frameFibreTrace (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData F.toFun f b) :
    resAt (frameFibreTrace data F f D).traceCoeff (frameFibreTrace data F f D).b
      = ∑ i, frameRes data F (D.xs i) := by
  rw [(frameFibreTrace data F f D).resAt_traceCoeff']
  exact Finset.sum_congr rfl fun i _ => resAt_frameChartIntegrand data F (D.xs i)

/-- **Per-fibre `frameRes` sum = fibre-restricted pole-set sum** (pure `Finset` re-indexing,
mirror of `fibreResidueSum_eq_filter`): if `xs` injectively enumerates exactly the points of
`S` in the fibre over `coe p`, the per-fibre sum is the filtered sum over `S`. -/
theorem frameFibreResidueSum_eq_filter (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (f : MeromorphicFunction X) {p : ℂ}
    (D : FibreRegularData F.toFun f p) (S : Finset X)
    (hxs_inj : Function.Injective D.xs)
    (hxs_mem : ∀ i, D.xs i ∈ S ∧ f.toRiemannSphere (D.xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ a ∈ S, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) → ∃ i, D.xs i = a) :
    ∑ i, frameRes data F (D.xs i)
      = ∑ a ∈ S with f.toRiemannSphere a = ((p : ℂ) : RiemannSphere), frameRes data F a := by
  classical
  have hImg : (Finset.univ : Finset D.ι).image D.xs
      = S.filter (fun a => f.toRiemannSphere a = ((p : ℂ) : RiemannSphere)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨(hxs_mem i).1, (hxs_mem i).2⟩
    · rintro ⟨ha_mem, ha_fib⟩; exact hxs_surj a ha_mem ha_fib
  rw [← hImg, Finset.sum_image (fun i _ j _ h => hxs_inj h)]

/-! ### The `ω₀ = df` value-trace collapse over an unramified fibre

For the canonical frame `ω₀ = df` and the cover `f` ITSELF, the per-sheet pushforward of the
atom's integrand collapses to the **plain value** of `F` along the sheet: the sheet is a
section of `f̂`, so the change-of-variables Jacobian `(f̂ ∘ sheet)' = 1` exactly cancels the
frame coefficient.  The trace coefficient of `frameFibreTrace` is therefore germ-equal at the
base to the PLAIN VALUE TRACE `w ↦ ∑ᵢ F(sheet i w)` — the datum the residual wall asks for. -/

/-- **The per-sheet `df` collapse**: along the `i`-th sheet, the pushforward of the atom's
integrand is the plain value read `w ↦ F(sheet i w)` (germ at the base). -/
theorem frameFibreTrace_summand_df (data : CanonicalForm17Data X)
    (F f : MeromorphicFunction X) (hω : data.ω₀ = differentialForm f) {b : ℂ}
    (D : FibreRegularData F.toFun f b) (i : D.ι) :
    (fun w => (frameFibreTrace data F f D).coeff i ((frameFibreTrace data F f D).sheet i w)
        * deriv ((frameFibreTrace data F f D).sheet i) w)
      =ᶠ[𝓝[≠] b]
      fun w => F.toFun ((chartAt ℂ (D.xs i)).symm ((frameFibreTrace data F f D).sheet i w)) := by
  classical
  set x : X := D.xs i with hx
  set ch := chartAt (H := ℂ) x with hch
  set pre : ℂ := ch x with hpre
  set s : ℂ → ℂ := (frameFibreTrace data F f D).sheet i with hs
  set φ : ℂ → ℂ := fun z => f.holoRepr (ch.symm z) with hφ
  -- The sheet's defining properties (the planar section germ).
  have hspec := Classical.choose_spec (exists_planar_section (D.hg_an i) (D.hg_deriv i)
    (D.gval' f i))
  have hs_an : AnalyticAt ℂ s b := hspec.1
  have hs_b : s b = pre := hspec.2.1
  have hs' : deriv s b ≠ 0 := hspec.2.2.1
  have hrinv : ∀ᶠ w in 𝓝 b, φ (s w) = w := hspec.2.2.2
  have hpre_tgt : pre ∈ ch.target := ch.map_source (mem_chart_source ℂ x)
  -- The sheet enters the punctured neighbourhood of `pre` (local injectivity from `s' ≠ 0`).
  have hne : ∀ᶠ w in 𝓝[≠] b, s w ≠ pre := by
    have hg_an : AnalyticAt ℂ (fun w => s w - pre) b := hs_an.sub analyticAt_const
    rcases hg_an.eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      have hsconst : s =ᶠ[𝓝 b] fun _ => pre := by
        filter_upwards [hcase] with w hw
        exact sub_eq_zero.mp hw
      have hzero : deriv s b = 0 := by
        rw [Filter.EventuallyEq.deriv_eq hsconst]
        exact deriv_const b pre
      exact hs' hzero
    · filter_upwards [hcase] with w hw
      exact sub_ne_zero.mp hw
  have hcont : Tendsto s (𝓝[≠] b) (𝓝 pre) := by
    have h1 := hs_an.continuousAt.tendsto
    rw [hs_b] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have htend : Tendsto s (𝓝[≠] b) (𝓝[≠] pre) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hcont, hne.mono fun w hw => Set.mem_compl_singleton_iff.mpr hw⟩
  -- The frame coefficient reads the chart derivative of `f` along the sheet.
  have hform : ∀ᶠ w in 𝓝[≠] b,
      deriv (f.toFun ∘ ch.symm) (s w) = formCoeff (differentialSection f) x (s w) :=
    htend.eventually (formCoeff_differentialSection_eventuallyEq f x)
  -- The chart derivative of `f.toFun` agrees with that of the junk-free `φ` near `pre`.
  have hderiv_eq : ∀ᶠ w in 𝓝[≠] b,
      deriv (f.holoRepr ∘ ch.symm) (s w) = deriv (f.toFun ∘ ch.symm) (s w) :=
    htend.eventually (deriv_eventuallyEq_punctured
      (Jacobians.ProperMapDegreeSheets.holoRepr_pullback_eventuallyEq_toFun f x hpre_tgt))
  -- The section Jacobian: `(φ ∘ s)' = 1` near the base.
  have hone : ∀ᶠ w in 𝓝 b, deriv (fun w => φ (s w)) w = 1 := by
    have hid : (fun w => φ (s w)) =ᶠ[𝓝 b] id := by
      filter_upwards [hrinv] with w hw
      exact hw
    filter_upwards [hid.deriv] with w hw
    rw [hw, deriv_id]
  -- The chain rule splits the section Jacobian.
  have hφs_ev : ∀ᶠ w in 𝓝[≠] b, AnalyticAt ℂ φ (s w) :=
    htend.eventually ((D.hg_an i).eventually_analyticAt.filter_mono nhdsWithin_le_nhds)
  have hs_ev : ∀ᶠ w in 𝓝 b, AnalyticAt ℂ s w := hs_an.eventually_analyticAt
  have hchain : ∀ᶠ w in 𝓝[≠] b, deriv φ (s w) * deriv s w = 1 := by
    filter_upwards [hφs_ev, hs_ev.filter_mono nhdsWithin_le_nhds,
      hone.filter_mono nhdsWithin_le_nhds] with w h1 h2 h3
    have hcomp : deriv (φ ∘ s) w = deriv φ (s w) * deriv s w :=
      deriv_comp w h1.differentiableAt h2.differentiableAt
    rw [show φ ∘ s = fun w => φ (s w) from rfl] at hcomp
    rw [← hcomp]
    exact h3
  -- Assemble the per-sheet collapse.
  filter_upwards [hform, hderiv_eq, hchain] with w h1 h2 h3
  show F.toFun (ch.symm (s w)) * formCoeff data.ω₀.toFun x (s w) * deriv s w
    = F.toFun (ch.symm (s w))
  have hcoeff : formCoeff data.ω₀.toFun x (s w)
      = deriv (f.holoRepr ∘ ch.symm) (s w) := by
    rw [hω]
    rw [show formCoeff (differentialForm f).toFun x (s w)
        = formCoeff (differentialSection f) x (s w) from rfl, ← h1, ← h2]
  rw [hcoeff, mul_assoc, show deriv (f.holoRepr ∘ ch.symm) = deriv φ from rfl, h3, mul_one]

/-- **The `df` value-trace collapse over the fibre**: the trace coefficient of the frame fibre
trace is germ-equal at the base to the plain value trace `w ↦ ∑ᵢ F(sheet i w)`. -/
theorem frameFibreTrace_traceCoeff_df (data : CanonicalForm17Data X)
    (F f : MeromorphicFunction X) (hω : data.ω₀ = differentialForm f) {b : ℂ}
    (D : FibreRegularData F.toFun f b) :
    (frameFibreTrace data F f D).traceCoeff =ᶠ[𝓝[≠] b]
      fun w => ∑ i, F.toFun ((chartAt ℂ (D.xs i)).symm
        ((frameFibreTrace data F f D).sheet i w)) := by
  have hall : ∀ᶠ w in 𝓝[≠] b, ∀ i : D.ι,
      (frameFibreTrace data F f D).coeff i ((frameFibreTrace data F f D).sheet i w)
          * deriv ((frameFibreTrace data F f D).sheet i) w
        = F.toFun ((chartAt ℂ (D.xs i)).symm ((frameFibreTrace data F f D).sheet i w)) :=
    Filter.eventually_all.mpr fun i => frameFibreTrace_summand_df data F f hω D i
  filter_upwards [hall] with w hw
  exact Finset.sum_congr rfl fun i _ => hw i

/-- **The `hres` field at an unramified centre (proven)**: if the global trace `T` germ-agrees
at `p` with the fibre trace coefficient of a `FibreRegularData` whose `xs` injectively
enumerates the `S`-points of the fibre, then `T`'s residue at `p` is the fibre-restricted
`frameRes` sum — the exact `FrameTraceFunctionData.hres` obligation at that centre. -/
theorem resAt_eq_filter_sum_of_traceCoeff_germ (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (f : MeromorphicFunction X) {p : ℂ}
    (D : FibreRegularData F.toFun f p) (S : Finset X) (T : ℂ → ℂ)
    (hT : T =ᶠ[𝓝[≠] p] (frameFibreTrace data F f D).traceCoeff)
    (hxs_inj : Function.Injective D.xs)
    (hxs_mem : ∀ i, D.xs i ∈ S ∧ f.toRiemannSphere (D.xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ a ∈ S, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) → ∃ i, D.xs i = a) :
    resAt T p
      = ∑ a ∈ S with f.toRiemannSphere a = ((p : ℂ) : RiemannSphere), frameRes data F a := by
  rw [resAt_congr hT]
  calc resAt (frameFibreTrace data F f D).traceCoeff p
      = ∑ i, frameRes data F (D.xs i) := resAt_traceCoeff_frameFibreTrace data F f D
    _ = _ := frameFibreResidueSum_eq_filter data F f D S hxs_inj hxs_mem hxs_surj

/-! ## The one-variable rationality reduction

`Miranda §VIII.3 steps 2–3, proven`: from a coefficient `T : ℂ → ℂ` analytic off a finite
centre set `C` and meromorphic at each centre, build a `LaurentForm` (the finite principal
parts of `T`, padded to uniform depth) whose finite residues equal `T`'s and whose `∞`-residue
equals `T`'s.  The entire remainder `T − L.R` is killed on the large contour by Cauchy–Goursat
(after repairing the finitely many junk values).  Built on the frame-free principal-part
extraction `FormTracePrincipalPart.exists_principalPart_meromorphicAt`. -/

open Jacobians.Dolbeault.FormTracePrincipalPart

/-- A finite sum of circle-integrable functions is circle-integrable. -/
theorem circleIntegrable_finsum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ} {ρ : ℝ}
    (hf : ∀ i ∈ s, CircleIntegrable (f i) c ρ) :
    CircleIntegrable (fun z => ∑ i ∈ s, f i z) c ρ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact circleIntegrable_const (0 : ℂ) c ρ
  | insert j s hj ih =>
    have hsplit : (fun z => ∑ i ∈ insert j s, f i z)
        = f j + fun z => ∑ i ∈ s, f i z := by
      funext z; rw [Finset.sum_insert hj]; rfl
    rw [hsplit]
    exact (hf j (Finset.mem_insert_self j s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The partial-fraction coefficient `L.R` is circle-integrable on the enclosing contour
(termwise `circleIntegrable_monomial`). -/
theorem circleIntegrable_laurentR (L : LaurentForm) : CircleIntegrable L.R 0 L.ρ :=
  circleIntegrable_finsum Finset.univ _ fun i _ => L.circleIntegrable_monomial i

/-- The padded `Fin`-indexed tail sum collapses to the `negTail` of depth `N ≤ M`. -/
theorem sum_fin_pad_eq_negTail (cv : ℂ) (b : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M) (z : ℂ) :
    (∑ j : Fin M, (if (j : ℕ) + 1 ≤ N then b ((j : ℕ) + 1) else 0)
        * (z - cv) ^ (-(((j : ℕ) : ℤ) + 1)))
      = negTail cv b N z := by
  rw [negTail]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => (if j + 1 ≤ N then b (j + 1) else 0) * (z - cv) ^ (-((j : ℤ) + 1)))]
  have h1 : ∀ j ∈ Finset.range M,
      (if j + 1 ≤ N then b (j + 1) else 0) * (z - cv) ^ (-((j : ℤ) + 1))
        = if j + 1 ≤ N then b (j + 1) * (z - cv) ^ (-((j : ℤ) + 1)) else 0 := by
    intro j _
    split <;> simp
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 : (Finset.range M).filter (fun j => j + 1 ≤ N) = Finset.range N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h2, show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by rw [Finset.Ico_add_one_right_eq_Icc],
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  · rw [Nat.add_comm]
  · congr 1
    push_cast
    ring

/-- **The principal-part `LaurentForm`** over a finite centre set `C ⊆ ball 0 ρ`: per centre
`c ∈ C` the depth-`M` padded tail with coefficients `b c` (zero beyond depth `N c`). -/
def tailLaurentForm (C : Finset ℂ) (ρ : ℝ) (hball : ∀ c ∈ C, c ∈ Metric.ball (0 : ℂ) ρ)
    (N : {x // x ∈ C} → ℕ) (b : {x // x ∈ C} → ℕ → ℂ) (M : ℕ) : LaurentForm where
  ι := {x // x ∈ C} × Fin M
  fintype_ι := inferInstance
  decEq_ι := Classical.decEq _
  c := fun i => if (i.2 : ℕ) + 1 ≤ N i.1 then b i.1 ((i.2 : ℕ) + 1) else 0
  a := fun i => i.1.1
  n := fun i => -(((i.2 : ℕ) : ℤ) + 1)
  ρ := ρ
  centers_mem := fun i => hball i.1.1 i.1.2

/-- The coefficient of the principal-part form is the sum of the per-centre `negTail`s. -/
theorem tailLaurentForm_R (C : Finset ℂ) (ρ : ℝ)
    (hball : ∀ c ∈ C, c ∈ Metric.ball (0 : ℂ) ρ)
    (N : {x // x ∈ C} → ℕ) (b : {x // x ∈ C} → ℕ → ℂ) {M : ℕ}
    (hNM : ∀ c, N c ≤ M) :
    (tailLaurentForm C ρ hball N b M).R
      = fun z => ∑ c ∈ C.attach, negTail c.1 (b c) (N c) z := by
  funext z
  show ∑ i : {x // x ∈ C} × Fin M, _ = _
  rw [Fintype.sum_prod_type, ← Finset.univ_eq_attach]
  exact Finset.sum_congr rfl fun c _ => sum_fin_pad_eq_negTail c.1 (b c) (hNM c) z

/-- The centres of the principal-part form are exactly `C` (the padding keeps every centre's
index inhabited). -/
theorem tailLaurentForm_image_a (C : Finset ℂ) (ρ : ℝ)
    (hball : ∀ c ∈ C, c ∈ Metric.ball (0 : ℂ) ρ)
    (N : {x // x ∈ C} → ℕ) (b : {x // x ∈ C} → ℕ → ℂ) {M : ℕ} (hM : 0 < M) :
    Finset.univ.image (tailLaurentForm C ρ hball N b M).a = C := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.1.2
  · intro hx
    exact ⟨⟨⟨x, hx⟩, ⟨0, hM⟩⟩, rfl⟩

/-- **The one-variable rationality reduction (Miranda §VIII.3 steps 2–3, proven).**  For
`T : ℂ → ℂ` analytic off the finite centre set `C ⊆ ball 0 ρ` and meromorphic at each centre,
there is a `LaurentForm` on the contour `C(0, ρ)` with centres exactly `C`, the same finite
residues as `T`, and the same residue at infinity.  (`L` is the finite principal part of `T`;
the remainder is entire after junk repair, so it contributes nothing to any of the contours.) -/
theorem exists_laurentForm_of_traceData (T : ℂ → ℂ) (C : Finset ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ∀ c ∈ C, c ∈ Metric.ball (0 : ℂ) ρ)
    (hoff : ∀ z : ℂ, z ∉ C → AnalyticAt ℂ T z)
    (hmero : ∀ c ∈ C, MeromorphicAt T c) :
    ∃ L : LaurentForm, L.ρ = ρ ∧ Finset.univ.image L.a = C ∧
      (∀ c ∈ C, resAt L.R c = resAt T c) ∧
      resAtInfty L.R L.ρ = resAtInfty T ρ := by
  classical
  -- Principal parts at each centre.
  choose N b R hR_an hT_eq using
    fun c : {x // x ∈ C} => exists_principalPart_meromorphicAt (hmero c.1 c.2)
  -- Uniform padding depth.
  set M : ℕ := max (C.attach.sup fun c => N c) 1 with hMdef
  have hM1 : 0 < M := lt_of_lt_of_le Nat.one_pos (le_max_right _ 1)
  have hNM : ∀ c : {x // x ∈ C}, N c ≤ M :=
    fun c => le_trans (Finset.le_sup (Finset.mem_attach C c)) (le_max_left _ _)
  set L : LaurentForm := tailLaurentForm C ρ hball N b M with hLdef
  have hLR : L.R = fun z => ∑ c ∈ C.attach, negTail c.1 (b c) (N c) z :=
    tailLaurentForm_R C ρ hball N b hNM
  -- `L.R` is analytic away from `C`.
  have hLR_off : ∀ z : ℂ, z ∉ C → AnalyticAt ℂ L.R z := by
    intro z hz
    rw [hLR]
    refine Finset.analyticAt_fun_sum _ fun c _ => ?_
    exact analyticAt_negTail_of_ne (b c) (N c) (fun h => hz (h ▸ c.2))
  -- The germ-analytic remainder at each centre.
  have hgerm : ∀ c₀ : {x // x ∈ C},
      ∃ Efun : ℂ → ℂ, AnalyticAt ℂ Efun c₀.1 ∧
        (fun z => T z - L.R z) =ᶠ[𝓝[≠] (c₀.1 : ℂ)] Efun := by
    intro c₀
    refine ⟨fun z => R c₀ z - ∑ c ∈ C.attach.erase c₀, negTail c.1 (b c) (N c) z, ?_, ?_⟩
    · refine (hR_an c₀).sub (Finset.analyticAt_fun_sum _ fun c hc => ?_)
      refine analyticAt_negTail_of_ne (b c) (N c) fun h => ?_
      exact (Finset.mem_erase.mp hc).1 (Subtype.ext h.symm)
    · filter_upwards [hT_eq c₀] with z hz
      have hLRz : L.R z = ∑ c ∈ C.attach, negTail c.1 (b c) (N c) z := by rw [hLR]
      have hsplit : ∑ c ∈ C.attach, negTail c.1 (b c) (N c) z
          = negTail c₀.1 (b c₀) (N c₀) z
            + ∑ c ∈ C.attach.erase c₀, negTail c.1 (b c) (N c) z :=
        (Finset.add_sum_erase _ _ (Finset.mem_attach C c₀)).symm
      rw [hz, hLRz, hsplit]
      ring
  -- The finite residues agree.
  have hres : ∀ c ∈ C, resAt L.R c = resAt T c := by
    intro c hc
    obtain ⟨Efun, hEfun_an, hEgerm⟩ := hgerm ⟨c, hc⟩
    have hTsplit : T = L.R + fun z => T z - L.R z := by
      funext z
      simp only [Pi.add_apply]
      ring
    have hE_mero : MeromorphicAt (fun z => T z - L.R z) c :=
      (hmero c hc).sub (meromorphicAt_laurentR L c)
    have hadd : resAt T c = resAt L.R c + resAt (fun z => T z - L.R z) c := by
      conv_lhs => rw [hTsplit]
      exact resAt_add (MeromorphicAt.holoPunctured (meromorphicAt_laurentR L c))
        (MeromorphicAt.holoPunctured hE_mero)
    rw [hadd, resAt_congr hEgerm, resAt_eq_zero_of_analyticAt hEfun_an, add_zero]
  -- The residues at infinity agree: the remainder is entire after junk repair, so its large
  -- contour integral vanishes (Cauchy–Goursat off the countable junk set).
  have hinfty : resAtInfty L.R ρ = resAtInfty T ρ := by
    set E : ℂ → ℂ := fun z => T z - L.R z with hEdef
    -- The junk-repaired remainder.
    set E' : ℂ → ℂ := fun z =>
      if hz : z ∈ C then Classical.choose (hgerm ⟨z, hz⟩) z else E z with hE'def
    -- `E` is analytic off `C`.
    have hE_an : ∀ z : ℂ, z ∉ C → AnalyticAt ℂ E z :=
      fun z hz => (hoff z hz).sub (hLR_off z hz)
    -- Off `C`, `E'` agrees with `E` on a full neighbourhood.
    have hE'_eq_off : ∀ z : ℂ, z ∉ C → E' =ᶠ[𝓝 z] E := by
      intro z hz
      have hop : IsOpen ((↑C : Set ℂ))ᶜ := C.finite_toSet.isClosed.isOpen_compl
      filter_upwards [hop.mem_nhds hz] with w hw
      have hwC : w ∉ C := by simpa using hw
      simp only [hE'def]
      rw [dif_neg hwC]
    -- At a centre, `E'` agrees with the analytic continuation on a full neighbourhood.
    have hE'_eq_centre : ∀ (c : ℂ) (hc : c ∈ C),
        E' =ᶠ[𝓝 c] Classical.choose (hgerm ⟨c, hc⟩) := by
      intro c hc
      have hpure : E' =ᶠ[pure c] Classical.choose (hgerm ⟨c, hc⟩) := by
        rw [Filter.EventuallyEq, Filter.eventually_pure, hE'def]
        simp only
        rw [dif_pos hc]
      have hpunct : E' =ᶠ[𝓝[≠] c] Classical.choose (hgerm ⟨c, hc⟩) := by
        have hop : IsOpen ((↑(C.erase c) : Set ℂ))ᶜ :=
          (C.erase c).finite_toSet.isClosed.isOpen_compl
        have hmem : ((↑(C.erase c) : Set ℂ))ᶜ ∈ 𝓝[≠] c :=
          nhdsWithin_le_nhds (hop.mem_nhds (by simp))
        filter_upwards [(Classical.choose_spec (hgerm ⟨c, hc⟩)).2, hmem,
          self_mem_nhdsWithin] with w hw1 hw2 hw3
        have hwc : w ≠ c := hw3
        have hwC : w ∉ C := by
          intro hwC
          exact hw2 (by simp [hwc, hwC])
        simp only [hE'def]
        rw [dif_neg hwC]
        exact hw1
      have hsup : E' =ᶠ[𝓝[≠] c ⊔ pure c] Classical.choose (hgerm ⟨c, hc⟩) :=
        Filter.eventually_sup.mpr ⟨hpunct, hpure⟩
      rwa [nhdsNE_sup_pure] at hsup
    -- `E'` is continuous on the closed disk.
    have hE'_cont : ContinuousOn E' (Metric.closedBall (0 : ℂ) ρ) := by
      intro z _
      by_cases hz : z ∈ C
      · exact ((Classical.choose_spec (hgerm ⟨z, hz⟩)).1.continuousAt.congr
          (hE'_eq_centre z hz).symm).continuousWithinAt
      · exact ((hE_an z hz).continuousAt.congr (hE'_eq_off z hz).symm).continuousWithinAt
    -- `E'` is differentiable off the (countable) centre set.
    have hE'_diff : ∀ z ∈ Metric.ball (0 : ℂ) ρ \ (↑C : Set ℂ), DifferentiableAt ℂ E' z := by
      intro z hz
      exact (hE_an z hz.2).differentiableAt.congr_of_eventuallyEq (hE'_eq_off z hz.2)
    -- Cauchy–Goursat: the repaired remainder's large contour integral vanishes.
    have hE'_zero : (∮ z in C((0 : ℂ), ρ), E' z) = 0 :=
      circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le
        C.finite_toSet.countable hE'_cont hE'_diff
    -- `E` and `E'` agree on the contour (which avoids `C ⊆ ball`).
    have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, z ∉ C := by
      intro z hz hzC
      have h1 : dist z 0 = ρ := Metric.mem_sphere.mp hz
      have h2 : dist z 0 < ρ := Metric.mem_ball.mp (hball z hzC)
      exact absurd h1 (ne_of_lt h2)
    have hE_zero : (∮ z in C((0 : ℂ), ρ), E z) = 0 := by
      rw [show (∮ z in C((0 : ℂ), ρ), E z) = ∮ z in C((0 : ℂ), ρ), E' z from
        circleIntegral.integral_congr hρ.le fun z hz => by
          simp only [hE'def]
          rw [dif_neg (hsphere z hz)]]
      exact hE'_zero
    -- Split the large contour integral of `T` and conclude.
    have hEint : CircleIntegrable E 0 ρ := by
      refine ContinuousOn.circleIntegrable hρ.le fun z hz => ?_
      exact ((hE_an z (hsphere z hz)).continuousAt).continuousWithinAt
    have hPint : CircleIntegrable L.R 0 ρ := circleIntegrable_laurentR L
    have hTsplit : (∮ z in C((0 : ℂ), ρ), T z)
        = (∮ z in C((0 : ℂ), ρ), L.R z) + ∮ z in C((0 : ℂ), ρ), E z := by
      have h1 : T = L.R + E := by
        funext z
        simp only [Pi.add_apply, hEdef]
        ring
      rw [h1]
      simpa using circleIntegral.integral_add hPint hEint
    rw [resAtInfty, resAtInfty, hTsplit, hE_zero, add_zero]
  exact ⟨L, rfl, tailLaurentForm_image_a C ρ hball N b hM1, hres, hinfty⟩

/-! ## The trace-function datum, and the wall conclusion from it (proven)

The honest remaining content of Miranda §VIII.3 step 1, packaged at the level of the **trace
function** alone: a coefficient `T : ℂ → ℂ` (the value trace `Tr(F)(w) = ∑_{sheets over w}
F(sheet)` read in the base chart), analytic off a finite exceptional value set `C`,
meromorphic at each exceptional value, whose local residues are the fibre `frameRes` sums
(Lemma 3.2, including the ramified clusters), and whose large-contour residue is the
`∞`-fibre sum (Lemma 3.2 at `∞`).  Given this, the wall conclusion — the `LaurentForm` with
its two residue transports — is **proven** via the one-variable rationality reduction. -/

/-- **The trace-function datum** for `α = F·ω₀` through `F = f.toRiemannSphere` over the pole
superset `S`: the value-chart trace coefficient `T` with its exceptional finite-value set `C`,
local meromorphy, the per-value residue transport (`hres`, Lemma 3.2 at the finite values,
ramified clusters included), the value coverage (`hcover`), and the `∞`-transport (`hinf`,
Lemma 3.2 at `∞` on the contour `C(0, ρ)` enclosing `C`).  Every field is a TRUE statement of
the §VIII.3 assembly for the plain value trace. -/
structure FrameTraceFunctionData (data : CanonicalForm17Data X) (F : MeromorphicFunction X)
    (f : MeromorphicFunction X) (S : Finset X) where
  /-- The value-chart trace coefficient on the finite part of `ℂℙ¹`. -/
  T : ℂ → ℂ
  /-- The finite exceptional value set (chart coordinates). -/
  C : Finset ℂ
  /-- The enclosing contour radius. -/
  ρ : ℝ
  /-- The contour radius is positive. -/
  hρ : 0 < ρ
  /-- Every exceptional value lies inside the contour. -/
  hball : ∀ c ∈ C, c ∈ Metric.ball (0 : ℂ) ρ
  /-- The trace is analytic off the exceptional values. -/
  hoff : ∀ z : ℂ, z ∉ C → AnalyticAt ℂ T z
  /-- The trace is meromorphic at each exceptional value. -/
  hmero : ∀ c ∈ C, MeromorphicAt T c
  /-- Lemma 3.2 at each exceptional value: the trace residue is the fibre `frameRes` sum. -/
  hres : ∀ c ∈ C, resAt T c
    = ∑ a ∈ S with f.toRiemannSphere a = ((c : ℂ) : RiemannSphere), frameRes data F a
  /-- Every finite value of `f` on `S` is an exceptional value (so no fibre is missed). -/
  hcover : (S.image f.toRiemannSphere).erase OnePoint.infty
    ⊆ C.image (fun c : ℂ => ((c : ℂ) : RiemannSphere))
  /-- Lemma 3.2 at `∞`: the trace residue at infinity is the `∞`-fibre `frameRes` sum. -/
  hinf : resAtInfty T ρ
    = ∑ a ∈ S with f.toRiemannSphere a = OnePoint.infty, frameRes data F a

/-- **The wall conclusion from the trace-function datum (proven).**  Given a
`FrameTraceFunctionData`, the principal-part `LaurentForm` of `T` realizes both residue
transports: the one-variable rationality reduction transfers the finite residues and the
`∞`-residue from `T` to `L`, and the value coverage re-indexes the centre sum into the
fibrewise sum. -/
theorem exists_traceLaurentForm_of_functionData (data : CanonicalForm17Data X)
    (F : MeromorphicFunction X) (f : MeromorphicFunction X) (S : Finset X)
    (D : FrameTraceFunctionData data F f S) :
    ∃ L : LaurentForm,
      (∑ p ∈ Finset.univ.image L.a, resAt L.R p
        = ∑ y ∈ (S.image f.toRiemannSphere).erase OnePoint.infty,
            ∑ a ∈ S with f.toRiemannSphere a = y, frameRes data F a) ∧
      resAtInfty L.R L.ρ
        = ∑ a ∈ S with f.toRiemannSphere a = OnePoint.infty, frameRes data F a := by
  classical
  obtain ⟨L, hLρ, hLa, hLres, hLinf⟩ :=
    exists_laurentForm_of_traceData D.T D.C D.ρ D.hρ D.hball D.hoff D.hmero
  refine ⟨L, ?_, ?_⟩
  · -- The finite transport: centres = `C`, residues = `T`'s = the fibre sums, re-indexed.
    rw [hLa]
    have h1 : ∀ c ∈ D.C, resAt L.R c
        = ∑ a ∈ S with f.toRiemannSphere a = ((c : ℂ) : RiemannSphere), frameRes data F a :=
      fun c hc => (hLres c hc).trans (D.hres c hc)
    rw [Finset.sum_congr rfl h1]
    -- Re-index `∑_{c ∈ C}` to `∑_{y ∈ C.image coe}` (`coe` injective), then shrink to the
    -- finite value set (`hcover`; off it the fibre filter is empty).
    have himg : ∑ y ∈ D.C.image (fun c : ℂ => ((c : ℂ) : RiemannSphere)),
          ∑ a ∈ S with f.toRiemannSphere a = y, frameRes data F a
        = ∑ c ∈ D.C, ∑ a ∈ S with f.toRiemannSphere a = ((c : ℂ) : RiemannSphere),
            frameRes data F a :=
      Finset.sum_image (fun p _ q _ h => OnePoint.coe_injective h)
    rw [← himg]
    refine (Finset.sum_subset D.hcover fun y hy hynot => ?_).symm
    -- An exceptional value that is not a value of `f` on `S` has an empty fibre filter.
    have hempty : (S.filter (fun a => f.toRiemannSphere a = y)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro a haS hay
      -- `y = F a` is a value of `f` on `S`; it is finite (`y ∈ C.image coe`), so it lies in
      -- the erased image — contradicting `hynot`.
      obtain ⟨c, _, hcy⟩ := Finset.mem_image.mp hy
      refine hynot (Finset.mem_erase.mpr ⟨?_, hay ▸ Finset.mem_image_of_mem _ haS⟩)
      rw [← hcy]
      exact fun h => OnePoint.coe_ne_infty c h
    rw [hempty, Finset.sum_empty]
  · -- The `∞`-transport: `L`'s `∞`-residue is `T`'s, which is the `∞`-fibre sum.
    rw [hLρ] at hLinf ⊢
    exact hLinf.trans D.hinf

/-! ## The wall, closed: the trace-function datum for `ω₀ = df`

The §VIII.3 trace assembly for the canonical `ω₀ = df` frame at the **trace-function level**,
CONSTRUCTED over the `FrameTraceWall` engine: the plain value trace
`Tr(F)(w) = ∑_{fibre over w} F.holoRepr` of `F` through the branched cover
`𝔉 = f.toRiemannSphere` is analytic off the finitely many exceptional values
(conservation-of-number section sums), meromorphic at each of them with the fibre residue sums
of `F·df` as residues (the per-centre cluster descents, ramified clusters included), and its
`∞`-residue is the `∞`-fibre sum (the reciprocal-chart clusters + the large-contour
computation). -/

/-- **The trace-function datum of the plain value trace** of `F` through `f`, for the canonical
`ω₀ = df` datum — Miranda §VIII.3 step 1 + Lemma 3.2 at the exceptional values, CONSTRUCTED:

* `T := valueTrace F f` (the junk-free fibre sum), `C :=` the finite `f`-values of
  `supp(div F) ∪ supp K`, `S :=` the fibre saturation of `supp(div F) ∪ supp K` (plus the
  `∞`-fibre) — since `supp K` contains every ramification point and every pole of `f`, all the
  branch values are exceptional and `hcover` holds by construction;
* `hoff` — off `C` every fibre point is an unramified (`K = 0` ⟹ `localDeg = 1`) non-`F`-pole
  point, so the conservation-of-number section sum applies
  (`analyticAt_valueTrace_of_sections`);
* `hmero`/`hres` — the per-centre cluster descent (`valueTrace_meromorphicAt_and_resAt`),
  ramified clusters included;
* `hinf` — Lemma 3.2 at `∞` (`valueTrace_resAtInfty_df`, the reciprocal-chart cluster). -/
theorem exists_frameTraceFunctionData_df (f : MeromorphicFunction X)
    (hf : ¬ IsGermConstant f) (data : CanonicalForm17Data X)
    (hω : data.ω₀ = differentialForm f) (F : MeromorphicFunction X) :
    ∃ S : Finset X, F.div.support ∪ data.K.support ⊆ S ∧
      Nonempty (FrameTraceFunctionData data F f S) := by
  classical
  have hdiv : (f.div : Divisor X) ≠ 0 :=
    SerreResidueTheorem.div_ne_zero_of_not_isGermConstant f hf
  -- the exceptional sets: base support, its finite value set, and the fibre saturation
  set S₀ : Finset X := F.div.support ∪ data.K.support with hS₀_def
  set C : Finset ℂ := (S₀.filter (fun a => 0 ≤ f.orderAtPoint a)).image f.holoRepr with hC_def
  set S : Finset X := (S₀ ∪ C.biUnion
      (fun c => FrameTraceWall.fibreFinset f hdiv (((c : ℂ) : RiemannSphere))))
      ∪ FrameTraceWall.fibreFinset f hdiv OnePoint.infty with hS_def
  -- the contour radius
  obtain ⟨ρ₀, hρ₀⟩ := C.finite_toSet.isBounded.subset_closedBall 0
  set ρ : ℝ := max ρ₀ 0 + 1 with hρ_def
  have hρ : 0 < ρ := by
    have h0 : (0 : ℝ) ≤ max ρ₀ 0 := le_max_right _ _
    rw [hρ_def]
    linarith
  have hball : ∀ c ∈ C, c ∈ Metric.ball (0 : ℂ) ρ := by
    intro c hc
    have h1 : c ∈ Metric.closedBall (0 : ℂ) ρ₀ := hρ₀ (Finset.mem_coe.mpr hc)
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball]
    calc dist c 0 ≤ ρ₀ := h1
      _ ≤ max ρ₀ 0 := le_max_left _ _
      _ < ρ := by rw [hρ_def]; linarith
  -- the finite value of a non-pole base-support point is exceptional
  have hmemC : ∀ a ∈ S₀, 0 ≤ f.orderAtPoint a → f.holoRepr a ∈ C := fun a ha hnp =>
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨ha, hnp⟩)
  -- fibres over exceptional values are inside the saturated `S`
  have hfibS : ∀ c ∈ C, ∀ y : X,
      f.toRiemannSphere y = (((c : ℂ) : RiemannSphere)) → y ∈ S := by
    intro c hc y hy
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    exact Finset.mem_biUnion.mpr ⟨c, hc, FrameTraceWall.mem_fibreFinset.mpr hy⟩
  -- `hoff`: analyticity off the exceptional values, by the unramified section sum
  have hoff : ∀ z : ℂ, z ∉ C → AnalyticAt ℂ (FrameTraceWall.valueTrace F f) z := by
    intro z hzC
    set P : Jacobians.MultiplicityPatching.MultiplicityPatchingData f
        (((z : ℂ) : RiemannSphere)) :=
      FrameTraceWall.patchAt f hdiv (((z : ℂ) : RiemannSphere)) with hP_def
    have hPfib : ∀ y, y ∈ P.xs → f.toRiemannSphere y = (((z : ℂ) : RiemannSphere)) := by
      intro y hy
      have h1 : y ∈ (P.xs : Set X) := hy
      rwa [P.xs_coe] at h1
    have hnotS₀ : ∀ y ∈ P.xs, y ∉ S₀ := by
      intro y hy hyS₀
      have hyfib := hPfib y hy
      have hnp := FrameTraceWall.nonpole_of_fibre_coe hyfib
      have hmem := hmemC y hyS₀ hnp
      rw [FrameTraceWall.holoRepr_of_fibre_coe hyfib] at hmem
      exact hzC hmem
    have hderiv : ∀ y ∈ P.xs,
        deriv (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ))
          ((chartAt (H := ℂ) y) y) ≠ 0 := by
      intro y hy
      have hyfib := hPfib y hy
      have hnp := FrameTraceWall.nonpole_of_fibre_coe hyfib
      have hK0 : data.K y = 0 := Finsupp.notMem_support_iff.mp
        (fun hc => hnotS₀ y hy (Finset.mem_union_right _ hc))
      have hKord : meromorphicOrderAt (deriv (f.toFun ∘ (chartAt (H := ℂ) y).symm))
          ((chartAt (H := ℂ) y) y) = 0 := by
        have h := data.order_eq y
        rw [hω, formOrderW_differentialForm] at h
        rw [h, hK0]
        norm_num
      exact FrameTraceWall.holoRepr_pullback_deriv_ne_zero_of_derivOrder_zero f hnp hKord
    have hm1 : ∀ y ∈ P.xs, P.m y = 1 := by
      intro y hy
      rw [FrameTraceWall.patch_m_eq_localDeg hdiv P hy,
        FrameTraceWall.localDeg_eq_one_of_deriv_ne_zero f hdiv (hPfib y hy) (hderiv y hy)]
    have hsec : ∀ y : {a // a ∈ P.xs}, ∃ s : ℂ → ℂ, AnalyticAt ℂ s z ∧
        s z = (chartAt (H := ℂ) y.1) y.1 ∧ deriv s z ≠ 0 ∧
        ∀ᶠ w in 𝓝 z, f.holoRepr ((chartAt (H := ℂ) y.1).symm (s w)) = w := by
      intro y
      have hyfib := hPfib y.1 y.2
      have hnp := FrameTraceWall.nonpole_of_fibre_coe hyfib
      have hφ_an : AnalyticAt ℂ (fun ζ => f.holoRepr ((chartAt (H := ℂ) y.1).symm ζ))
          ((chartAt (H := ℂ) y.1) y.1) :=
        f.analyticAt_holoRepr_chartPullback_of_orderNonneg hnp
      have hφval : (fun ζ => f.holoRepr ((chartAt (H := ℂ) y.1).symm ζ))
          ((chartAt (H := ℂ) y.1) y.1) = z := by
        show f.holoRepr ((chartAt (H := ℂ) y.1).symm ((chartAt (H := ℂ) y.1) y.1)) = z
        rw [(chartAt (H := ℂ) y.1).left_inv (mem_chart_source ℂ y.1)]
        exact FrameTraceWall.holoRepr_of_fibre_coe hyfib
      obtain ⟨s, h1, h2, h3, h4⟩ := exists_planar_section hφ_an (hderiv y.1 y.2) hφval
      exact ⟨s, h1, h2, h3, h4⟩
    choose sfun hs_an hs_base hs_dne hrinv using hsec
    refine FrameTraceWall.analyticAt_valueTrace_of_sections F f hdiv P
      (fun y : {a // a ∈ P.xs} => y.1) Subtype.val_injective ?_ (fun i => hm1 i.1 i.2)
      sfun hs_an hs_base hrinv ?_
    · intro y
      constructor
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact i.2
    · intro i
      have h0 : F.orderAtPoint i.1 = 0 := Finsupp.notMem_support_iff.mp
        (fun hc => hnotS₀ i.1 i.2 (Finset.mem_union_left _ hc))
      exact le_of_eq h0.symm
  -- `hres`: the per-centre cluster residue, re-read over the saturated `S`
  have hres : ∀ c ∈ C, resAt (FrameTraceWall.valueTrace F f) c
      = ∑ a ∈ S with f.toRiemannSphere a = (((c : ℂ) : RiemannSphere)),
          frameRes data F a := by
    intro c hc
    rw [(FrameTraceWall.valueTrace_meromorphicAt_and_resAt data F f hω hdiv c).2]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext y
    rw [FrameTraceWall.mem_fibreFinset, Finset.mem_filter]
    exact ⟨fun hy => ⟨hfibS c hc y hy, hy⟩, fun hy => hy.2⟩
  -- `hcover`: every finite `f`-value of `S` is exceptional
  have hcover : (S.image f.toRiemannSphere).erase OnePoint.infty
      ⊆ C.image (fun c : ℂ => ((c : ℂ) : RiemannSphere)) := by
    intro v hv
    rw [Finset.mem_erase] at hv
    obtain ⟨hvne, hvmem⟩ := hv
    obtain ⟨a, haS, hav⟩ := Finset.mem_image.mp hvmem
    have hnp : 0 ≤ f.orderAtPoint a := by
      by_contra h
      rw [f.toRiemannSphere_of_pole (not_le.mp h)] at hav
      exact hvne hav.symm
    rw [f.toRiemannSphere_of_nonneg hnp] at hav
    have hC : f.holoRepr a ∈ C := by
      rcases Finset.mem_union.mp haS with h01 | hinfty
      · rcases Finset.mem_union.mp h01 with h0 | hbi
        · exact hmemC a h0 hnp
        · obtain ⟨c, hcC, hcfib⟩ := Finset.mem_biUnion.mp hbi
          have hcv := FrameTraceWall.mem_fibreFinset.mp hcfib
          rw [FrameTraceWall.holoRepr_of_fibre_coe hcv]
          exact hcC
      · -- an `∞`-fibre point is a pole, contradicting `0 ≤ order`
        exfalso
        have hpole := FrameTraceWall.mem_fibreFinset.mp hinfty
        rw [f.toRiemannSphere_of_nonneg hnp] at hpole
        exact OnePoint.coe_ne_infty _ hpole
    rw [← hav]
    exact Finset.mem_image_of_mem _ hC
  -- `hinf`: Lemma 3.2 at `∞`, re-read over the saturated `S`
  have hinf : resAtInfty (FrameTraceWall.valueTrace F f) ρ
      = ∑ a ∈ S with f.toRiemannSphere a = OnePoint.infty, frameRes data F a := by
    rw [FrameTraceWall.valueTrace_resAtInfty_df data F f hω hdiv C hρ hball hoff]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext y
    rw [FrameTraceWall.mem_fibreFinset, Finset.mem_filter]
    constructor
    · intro hy
      exact ⟨Finset.mem_union_right _ (FrameTraceWall.mem_fibreFinset.mpr hy), hy⟩
    · exact fun hy => hy.2
  -- assemble
  refine ⟨S, ?_, ⟨{
      T := FrameTraceWall.valueTrace F f
      C := C
      ρ := ρ
      hρ := hρ
      hball := hball
      hoff := hoff
      hmero := fun c _ =>
        (FrameTraceWall.valueTrace_meromorphicAt_and_resAt data F f hω hdiv c).1
      hres := hres
      hcover := hcover
      hinf := hinf }⟩⟩
  calc F.div.support ∪ data.K.support = S₀ := rfl
    _ ⊆ S₀ ∪ C.biUnion
        (fun c => FrameTraceWall.fibreFinset f hdiv (((c : ℂ) : RiemannSphere))) :=
      Finset.subset_union_left
    _ ⊆ S := Finset.subset_union_left

/-- **The `LaurentForm` wall conclusion** (proven over `exists_frameTraceFunctionData_df`):
the partial-fraction form of the value trace with its two residue transports. -/
theorem exists_traceLaurentForm_df (f : MeromorphicFunction X) (hf : ¬ IsGermConstant f)
    (data : CanonicalForm17Data X) (hω : data.ω₀ = differentialForm f)
    (F : MeromorphicFunction X) :
    ∃ (S : Finset X) (L : LaurentForm),
      F.div.support ∪ data.K.support ⊆ S ∧
      (∑ p ∈ Finset.univ.image L.a, resAt L.R p
        = ∑ y ∈ (S.image f.toRiemannSphere).erase OnePoint.infty,
            ∑ a ∈ S with f.toRiemannSphere a = y, frameRes data F a) ∧
      resAtInfty L.R L.ρ
        = ∑ a ∈ S with f.toRiemannSphere a = OnePoint.infty, frameRes data F a := by
  obtain ⟨S, hS, ⟨D⟩⟩ := exists_frameTraceFunctionData_df f hf data hω F
  obtain ⟨L, hfin, hinf⟩ := exists_traceLaurentForm_of_functionData data F f S D
  exact ⟨S, L, hS, hfin, hinf⟩

/-! ## The trace hypothesis from the wall (proven) -/

/-- **The trace hypothesis for any `ω₀ = df` datum**, conditional on exactly
`exists_traceLaurentForm_df`: every `F` admits a `FrameResidueTrace`, assembled by the proven
reduction `frameResidueTrace_of_laurentForm`. -/
theorem frameTraceHypothesis_of_df (f : MeromorphicFunction X) (hf : ¬ IsGermConstant f)
    (data : CanonicalForm17Data X) (hω : data.ω₀ = differentialForm f) :
    data.FrameTraceHypothesis := by
  intro F
  obtain ⟨S, L, hS, hfin, hinf⟩ := exists_traceLaurentForm_df f hf data hω F
  exact ⟨frameResidueTrace_of_laurentForm data F f S hS L hfin hinf⟩

/-- **The keystone's exact input shape**: a canonical datum with the trace hypothesis exists —
the canonical `ω₀ = df` datum of `exists_nonconstant_meromorphic`, with the hypothesis from
`frameTraceHypothesis_of_df`. -/
theorem exists_canonicalData_frameTraceHypothesis :
    ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis := by
  obtain ⟨_D, f, _hmem, hf⟩ := exists_nonconstant_meromorphic (X := X)
  obtain ⟨K, hK⟩ := exists_differentialForm_divisor f (differentialForm_ne_zero hf)
  exact ⟨canonicalForm17DataOfDivisor f hf K hK,
    frameTraceHypothesis_of_df f hf (canonicalForm17DataOfDivisor f hf K hK) rfl⟩

/-- **The keystone atom, unconditional**: a canonical `ω₀ = df` datum satisfying its own
residue atom `∑_{p ∈ supp(div F) ∪ supp K} Res_p(F·ω₀) = 0` (for EVERY global meromorphic
`F`) exists on every compact connected Riemann surface. -/
theorem exists_canonicalData_residueAtom :
    ∃ data : CanonicalForm17Data X, data.ResidueAtom :=
  exists_residueAtom_of_exists_frameTrace exists_canonicalData_frameTraceHypothesis

end Dolbeault

end Jacobians

end
