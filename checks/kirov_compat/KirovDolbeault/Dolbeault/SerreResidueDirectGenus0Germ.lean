/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueDirectGenus0Assemble

/-!
# Gate A `∑Res = 0` — eliminating the false junk-freeness `hcont_int` (germ-Cauchy at `∞`)

`Jacobians.Dolbeault.SerreResidueTheorem.residueTheorem_ofCanonicalSimpleInfty_genus0`
(`SerreResidueDirectGenus0Assemble.lean`) closes Gate A `∑Res = 0` modulo, among the residuals, the
**finite junk-freeness** `hcont_int`: the literal continuity of `valueChartTracePatched ω₀ f Φ br − L.R`
at each finite pole-centre `cs j`.

## The soundness finding (`hcont_int` is FALSE for the canonical full-fibre selection)

`hcont_int` is `ContinuousAt (T − L.R) (cs j)`, which (since `T − L.R` germ-equals an analytic
representative `R` off `cs j`) is **equivalent to the literal-value match** `(T − L.R)(cs j) = R(cs j)`,
where `R(cs j)` is the removable (regular-part) limit.  But the *literal value*
`T(cs j) = valueChartTrace ω₀ f Φ (cs j)` (when `cs j ∉ br`) is, by definition,

> `valueChartTrace ω₀ f Φ b = ∑ i, (coeffAt ω₀ ((Φ b).xs i) (chart (Φ b).xs i) * g ((Φ b).xs i))
>   · deriv (sheetᵢ) b`

(verified directly: `FormTraceFibre.chartIntegrand` reads `g` *at* the fibre point).  At a pole-value
`cs j` the canonical full-fibre selection enumerates the **entire** fibre `F⁻¹(coe cs j)`, which —
because `cs j` is a pole-*value* (`hcenters_cs`) — contains a genuine `α`-pole `a` (an element of
`poles`).  So the summand for `a` carries the factor `g a` — the value of `g` *at its own pole*, a
junk value.  Changing `g` only at the isolated point `a` changes `T(cs j)` (coefficient
`coeffAt ω₀ a · deriv(sheet_a)(cs j)`, generically nonzero) **without** changing the germ of `T` on the
punctured `𝓝[≠] cs j` (hence without changing `R(cs j)` or `L.R(cs j)`).  Therefore the equation
`(T − L.R)(cs j) = R(cs j)` cannot hold for all `g`: **`hcont_int` is junk-value-dependent, not a
theorem.**  (The branch-patch fixes the analogous falsity at *branch* values, where the trace is
*bounded*; it provides no fix at pole-centres, where the trace genuinely *diverges* — `limUnder` of a
divergent function is again junk.)

This is the same class of defect the repo already records for the *raw* trace at branch values
(`FormTraceGlobalTPatched.lean:432–433`), surfacing at the pole-centres where the `valueChartTrace`
route cannot repair it.

## The non-circular fix (germ-Cauchy: literal-entire is not needed)

The kirovGenus-`0` close (`SerreResidueDirectGenus0.lean`) used `hcont_int` *only* to obtain `hentire :
AnalyticOnNhd ℂ (T − L.R) Set.univ` (the **literal**-entire remainder), feeding the Cauchy-at-`∞`
residue `resAt (recipCoeff (T − L.R)) 0 = 0` (`resAt_recipCoeff_eq_zero_of_entire`, global primitive).
But the `∞`-residue depends only on the *germ* of `T − L.R` for large `z` — the junk values at the
finitely-many pole-centres are irrelevant.  So **literal-entire is unnecessarily strong**: it suffices
that `T − L.R` is *germ-regular* (has an analytic representative at every finite point — `T − L.R`
analytic off the centres + the pole removed at the centres), which is **free** from
`exists_laurentForm_principalPart` (`hT_off` + `hrem`), with *no* junk-freeness.

The germ-Cauchy lemma (`resAt_recipCoeff_eq_zero_of_regular`): from germ-regularity off a finite set
`S`, construct (`exists_entire_agree_of_regular`) a genuinely-**entire** `h'` agreeing with `h` off `S`
(patch the junk values to the regular-part values; analytic continuation makes `h'` entire); then
`recipCoeff h =ᶠ[𝓝[≠] 0] recipCoeff h'` (they agree for large `z`, `S` bounded) and `resAt (recipCoeff
h') 0 = 0` by the *existing* Cauchy-at-`∞` for the entire `h'`.  This is sound and non-circular — it
uses only analytic continuation + Cauchy for a genuinely-entire function, never `∑Res = 0`.

So this file **eliminates `hcont_int`** from the kirovGenus-`0` Gate-A capstones, replacing it with the free
germ-regularity already supplied by the principal-part extraction.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `exists_entire_agree_of_regular` — from germ-regular data off a finite `S`, a genuinely-entire
  function agreeing with `h` off `S` (the analytic-continuation patch).
* `recipCoeff_eventuallyEq_of_agree_off_finset` — `recipCoeff h =ᶠ[𝓝[≠] 0] recipCoeff h'` from cofinite
  agreement (`S` bounded ⟹ for large `z = ζ⁻¹` they agree).
* `HoloPunctured.congr_nhdsNE` — `HoloPunctured` transfers along a punctured germ-equality.
* `resAt_recipCoeff_eq_zero_of_regular` / `holoPunctured_recipCoeff_of_regular` — **germ-Cauchy at `∞`**:
  the `∞`-residue / isolated-singularity of `recipCoeff h` from germ-regularity (no literal continuity).
* `infty_eq_of_remainderRegular` — the `∞`-residue identity from germ-regularity + `hcoh_full` (the
  `hcont_int`-free replacement of `infty_eq_of_remainderResZero`).
* `globalTraceData_of_genus0_germ` / `residueTheorem_of_directGeometry_genus0_germ` — the residue-level
  close **without** `hcont_int`.
* `residueTheorem_ofAdapted_genus0_germ` / `…SimpleInfty_germ` / `…ofCanonicalSimpleInfty_germ` — the
  adapted-cover / canonical-selection capstones, `hcont_int` **dropped**.
* `…_holomorphic` — end-to-end non-vacuity (empty pole set).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3.
* `Jacobians/Dolbeault/SerreResidueDirectGenus0.lean` (the literal-entire route this file generalises).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceLiouville
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceFullFibre
  Jacobians.Dolbeault.FormTracePrincipalPart

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ## Germ-Cauchy at infinity (the `hcont_int`-free `∞`-residue vanishing)

The `∞`-residue of `recipCoeff h` depends only on the germ of `h` for large `z`; junk values at
finitely-many finite points are irrelevant.  We therefore weaken the *literal*-entire hypothesis of
`resAt_recipCoeff_eq_zero_of_entire` to **germ-regularity** off a finite set, which is free from the
principal-part extraction. -/

/-- **An entire function agreeing with `h` off a finite set, from germ-regularity.**  If `h` is analytic
off a finite set `S` (`hoff`) and, at each `p ∈ S`, germ-equals an analytic representative off `p`
(`hrem` — the pole removed), then there is a genuinely-**entire** `h'` with `h' = h` off `S`.  At
`p ∈ S`, `h'` takes the regular-part value `R p` (so it is continuous there, unlike the junk literal
`h p`); analytic continuation (`AnalyticAt.congr` from the germ rep, the other `S`-points avoided on a
punctured ball) makes `h'` analytic everywhere. -/
theorem exists_entire_agree_of_regular {h : ℂ → ℂ} {S : Finset ℂ}
    (hoff : ∀ z ∉ S, AnalyticAt ℂ h z)
    (hrem : ∀ p ∈ S, ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ h =ᶠ[𝓝[≠] p] R) :
    ∃ h' : ℂ → ℂ, AnalyticOnNhd ℂ h' Set.univ ∧ (∀ z ∉ S, h' z = h z) := by
  classical
  set Rof : (p : ℂ) → ℂ → ℂ := fun p => if hp : p ∈ S then (hrem p hp).choose else h with hRof
  set h' : ℂ → ℂ := fun z => if z ∈ S then Rof z z else h z with hh'
  have hoffeq : ∀ z ∉ S, h' z = h z := fun z hz => by simp only [hh', if_neg hz]
  refine ⟨h', ?_, hoffeq⟩
  intro z _
  by_cases hz : z ∈ S
  · -- At a centre: `h' =ᶠ[𝓝 z] Rof z`, and `Rof z` is analytic at `z`.
    have hRz_an : AnalyticAt ℂ (Rof z) z := by
      simp only [hRof, dif_pos hz]; exact (hrem z hz).choose_spec.1
    have hRz_eq : h =ᶠ[𝓝[≠] z] (Rof z) := by
      simp only [hRof, dif_pos hz]; exact (hrem z hz).choose_spec.2
    have hfin : ((S : Set ℂ) \ {z}).Finite := (S.finite_toSet).diff
    have hcompl : (((S : Set ℂ) \ {z}))ᶜ ∈ 𝓝 z := hfin.isClosed.compl_mem_nhds (by simp)
    have hpunct : h' =ᶠ[𝓝[≠] z] (Rof z) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hcompl, hRz_eq]
        with z' hz'ne hz'compl hz'h
      have hz'ne' : z' ≠ z := by simpa using hz'ne
      have hz'notS : z' ∉ S := fun hmem => hz'compl ⟨hmem, fun he => hz'ne' (by simpa using he)⟩
      rw [hoffeq z' hz'notS, hz'h]
    have hval : h' z = (Rof z) z := by simp only [hh', if_pos hz]
    have heq : h' =ᶠ[𝓝 z] (Rof z) := by
      rw [Filter.EventuallyEq, ← nhdsNE_sup_pure z, Filter.eventually_sup]
      exact ⟨hpunct, by simp [Filter.eventually_pure, hval]⟩
    exact hRz_an.congr heq.symm
  · -- Off `S`: `h' = h` on a full nbhd (a ball avoiding `S`), analytic by `hoff`.
    refine (hoff z hz).congr (Filter.eventuallyEq_of_mem
      (((S.finite_toSet).isClosed.compl_mem_nhds (by simpa using hz)))
      (fun z' hz' => ?_)).symm
    have hz'notS : z' ∉ S := by simpa using hz'
    simp only [hh', if_neg hz'notS]

/-- **`recipCoeff` germ-equality from cofinite agreement.**  If `h' = h` off a finite set `S`, then
`recipCoeff h =ᶠ[𝓝[≠] 0] recipCoeff h'`: as `ζ → 0` (`ζ ≠ 0`), `‖ζ⁻¹‖ → ∞` escapes the bounded `S`, so
`h (ζ⁻¹) = h' (ζ⁻¹)`, hence the reciprocal coefficients `−·(ζ⁻¹)·ζ⁻²` agree. -/
theorem recipCoeff_eventuallyEq_of_agree_off_finset {h h' : ℂ → ℂ} {S : Finset ℂ}
    (hag : ∀ z ∉ S, h' z = h z) :
    recipCoeff h =ᶠ[𝓝[≠] 0] recipCoeff h' := by
  obtain ⟨R, hR⟩ := (S.finite_toSet).isBounded.subset_ball (0 : ℂ)
  have htend : Tendsto (fun ζ : ℂ => ‖ζ⁻¹‖) (𝓝[≠] 0) atTop := by
    simp only [norm_inv]
    exact (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp (tendsto_norm_nhdsNE_zero (E := ℂ))
  filter_upwards [htend.eventually_gt_atTop R] with ζ hζ
  have hζnotS : ζ⁻¹ ∉ S := by
    intro hmem
    have : ζ⁻¹ ∈ ball (0 : ℂ) R := hR hmem
    rw [mem_ball, dist_zero_right] at this
    linarith
  show -(h (ζ⁻¹)) * ζ ^ (-2 : ℤ) = -(h' (ζ⁻¹)) * ζ ^ (-2 : ℤ)
  rw [hag (ζ⁻¹) hζnotS]

/-- **`HoloPunctured` transfers along a punctured germ-equality.**  If `f` has an isolated singularity
at `c` (`HoloPunctured f c`) and `f =ᶠ[𝓝[≠] c] g`, then so does `g`: on a small punctured ball where
they agree, `g` is differentiable since `f` is (`DifferentiableAt.congr_of_eventuallyEq`). -/
theorem HoloPunctured.congr_nhdsNE {f g : ℂ → ℂ} {c : ℂ} (hf : HoloPunctured f c)
    (hfg : f =ᶠ[𝓝[≠] c] g) : HoloPunctured g c := by
  obtain ⟨ρ, hρ, hdiff⟩ := hf
  rw [Filter.eventuallyEq_iff_exists_mem] at hfg
  obtain ⟨U, hU, hUeq⟩ := hfg
  rw [mem_nhdsWithin] at hU
  obtain ⟨V, hVopen, hcV, hVU⟩ := hU
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVopen c hcV
  refine ⟨min ρ δ, lt_min hρ hδ, fun z hz => ?_⟩
  have hzc : z ≠ c := fun h => hz.2 (by rw [h]; exact Set.mem_singleton c)
  have hzρ : z ∈ ball c ρ \ {c} := ⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
  have hzV : z ∈ V := hball (ball_subset_ball (min_le_right _ _) hz.1)
  have hgf_nhds : g =ᶠ[𝓝 z] f := by
    have hVne : (V ∩ {c}ᶜ) ∈ 𝓝 z :=
      (hVopen.inter isOpen_compl_singleton).mem_nhds ⟨hzV, hzc⟩
    filter_upwards [hVne] with w hw
    exact (hUeq (hVU ⟨hw.1, hw.2⟩)).symm
  exact (hdiff z hzρ).congr_of_eventuallyEq hgf_nhds

/-- **Germ-Cauchy at infinity (the `∞`-residue of a germ-regular `1`-form coefficient is `0`).**  If
`h : ℂ → ℂ` is analytic off a finite set `S` and germ-regular (the pole removed) at each `p ∈ S`, then
`resAt (recipCoeff h) 0 = 0`.  The genuine `hcont_int`-free replacement of
`resAt_recipCoeff_eq_zero_of_entire`: build the entire `h'` agreeing off `S`
(`exists_entire_agree_of_regular`), transfer the residue along the `∞`-germ-equality
(`recipCoeff_eventuallyEq_of_agree_off_finset`), and apply Cauchy at `∞` to the entire `h'`. -/
theorem resAt_recipCoeff_eq_zero_of_regular {h : ℂ → ℂ} {S : Finset ℂ}
    (hoff : ∀ z ∉ S, AnalyticAt ℂ h z)
    (hrem : ∀ p ∈ S, ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ h =ᶠ[𝓝[≠] p] R) :
    resAt (recipCoeff h) 0 = 0 := by
  obtain ⟨h', hh'_an, hag⟩ := exists_entire_agree_of_regular hoff hrem
  rw [resAt_congr (recipCoeff_eventuallyEq_of_agree_off_finset hag)]
  exact resAt_recipCoeff_eq_zero_of_entire hh'_an

/-- **`recipCoeff` of a germ-regular coefficient has an isolated singularity at `0`.**  The
`HoloPunctured` input of `resAt` additivity at `0`, from germ-regularity (the entire-`h'` proxy + the
`∞`-germ-equality transferred by `HoloPunctured.congr_nhdsNE`). -/
theorem holoPunctured_recipCoeff_of_regular {h : ℂ → ℂ} {S : Finset ℂ}
    (hoff : ∀ z ∉ S, AnalyticAt ℂ h z)
    (hrem : ∀ p ∈ S, ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ h =ᶠ[𝓝[≠] p] R) :
    HoloPunctured (recipCoeff h) 0 := by
  obtain ⟨h', hh'_an, hag⟩ := exists_entire_agree_of_regular hoff hrem
  exact HoloPunctured.congr_nhdsNE (holoPunctured_recipCoeff_entire hh'_an)
    (recipCoeff_eventuallyEq_of_agree_off_finset hag).symm

/-! ## The `∞`-residue identity from germ-regularity (the `hcont_int`-free `infty_eq`)

`infty_eq_of_remainderResZero` took the *literal*-entire remainder `hentire` (= the false junk-freeness).
This germ form takes instead the **germ-regular** data `hoff`/`hrem` of `T − L.R` — free from the
principal-part extraction — and routes the `∞`-residue vanishing through germ-Cauchy. -/

/-- **The `∞`-residue identity from the germ-regular remainder + the `∞`-coherence (non-circular,
`hcont_int`-free).**  Given that `T − L.R` (`T = valueChartTracePatched ω₀ f Φ br`) is analytic off the
centre set `image L.a` (`hoff`) and germ-regular at each centre (`hrem`) — both free from the
principal-part extraction — together with the `∞`-coherence `hcoh_full` and the `∞`-fibre enumeration,

> `resAtInfty L.R L.ρ = ∑_{a ∈ poles, F a = ∞} formFnResidue ω₀ g a`.

The remainder's `∞`-residue `resAt (recipCoeff (T − L.R)) 0 = 0` is **germ-Cauchy**
(`resAt_recipCoeff_eq_zero_of_regular`), not literal-entire — eliminating the junk-freeness. -/
theorem infty_eq_of_remainderRegular
    {Φ : (b : ℂ) → FibreRegularData g f b} {br : Finset ℂ} {L : LaurentForm}
    (hoff : ∀ z ∉ Finset.univ.image L.a,
      AnalyticAt ℂ (valueChartTracePatched ω₀ f Φ br - L.R) z)
    (hrem : ∀ p ∈ Finset.univ.image L.a, ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧
      (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] p] R)
    (Dinf_full : InftyFibreDataNF g f)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full))
    (hfull_inj : Function.Injective Dinf_full.xs)
    {ιP : Type} [Fintype ιP] (xsInf_po : ιP → X)
    (hpo_inj : Function.Injective xsInf_po)
    (hpo_mem : ∀ j, xsInf_po j ∈ poles ∧ f.toRiemannSphere (xsInf_po j) = OnePoint.infty)
    (hpo_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ j, xsInf_po j = a)
    (hpole_image : (Finset.univ.image Dinf_full.xs).filter (· ∈ poles)
      = Finset.univ.image xsInf_po)
    (hnonpole : ∀ k, Dinf_full.xs k ∉ poles → formFnResidue ω₀ g (Dinf_full.xs k) = 0) :
    resAtInfty L.R L.ρ
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a := by
  classical
  set T := valueChartTracePatched ω₀ f Φ br with hT
  rw [resAtInfty_eq_resAt_recipCoeff]
  have hsplit : recipCoeff T = recipCoeff L.R + recipCoeff (T - L.R) := by
    rw [recipCoeff_sub]; funext ζ; simp
  have hhp_rem : HoloPunctured (recipCoeff (T - L.R)) 0 :=
    holoPunctured_recipCoeff_of_regular hoff hrem
  have hLRhp : HoloPunctured (recipCoeff L.R) 0 := (meromorphicAt_recipCoeff_laurent L).holoPunctured
  have hadd := resAt_add hLRhp hhp_rem
  rw [← hsplit] at hadd
  have hrem_res0 : resAt (recipCoeff (T - L.R)) 0 = 0 :=
    resAt_recipCoeff_eq_zero_of_regular hoff hrem
  have hLR_eq_T : resAt (recipCoeff L.R) 0 = resAt (recipCoeff T) 0 := by
    rw [hadd, hrem_res0, add_zero]
  rw [hLR_eq_T]
  have hcoh : recipCoeff T =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf_full).traceCoeff :=
    hcoh_inf_of_inftyMovingCoherenceNF ω₀ g f Φ br Dinf_full hcoh_full
  rw [resAt_congr hcoh, resAt_traceCoeff_inftyFibreTraceNF ω₀ f Dinf_full,
    residueSum_full_eq_poleOnly Dinf_full.xs xsInf_po hfull_inj hpo_inj hpole_image hnonpole]
  exact residueSum_xs_eq_inftyFilter xsInf_po hpo_inj hpo_mem hpo_surj

/-! ## The residue-level close of Gate A, `hcont_int`-free

Mirrors `globalTraceData_of_genus0` but with `hcont_int` **dropped**: the finite junk-freeness is
replaced by the *free* germ-regularity (`hT_off` off the centres + the principal-part remainder `hLrem`
at the centres), and the `∞`-residue identity routes through `infty_eq_of_remainderRegular`. -/

/-- **`GlobalTraceData` from the residue-level geometry, `hcont_int`-free.**  Identical to
`globalTraceData_of_genus0` except the **finite junk-freeness `hcont_int` is removed**: the `∞`-residue
identity is re-derived from the *free* germ-regularity of `T − L.R` (analytic off the centres via
`hT_off_patched`, germ-regular at the centres via `exists_laurentForm_principalPart`) through germ-Cauchy
(`infty_eq_of_remainderRegular`).  Producing one ⇒ Gate A `∑Res = 0`. -/
noncomputable def globalTraceData_of_genus0_germ
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (D : (p : ℂ) → FibreRegularData g f p)
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hpole_image : ∀ i, (Finset.univ.image (Cfull i).D.xs).filter (· ∈ poles)
      = Finset.univ.image (D (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (Dinf_full : InftyFibreDataNF g f)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full))
    (hfullInf_inj : Function.Injective Dinf_full.xs)
    {ιInfP : Type} [Fintype ιInfP] (xsInf_po : ιInfP → X)
    (hpoInf_inj : Function.Injective xsInf_po)
    (hpoInf_mem : ∀ j, xsInf_po j ∈ poles ∧ f.toRiemannSphere (xsInf_po j) = OnePoint.infty)
    (hpoInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ j, xsInf_po j = a)
    (hpole_image_inf : (Finset.univ.image Dinf_full.xs).filter (· ∈ poles)
      = Finset.univ.image xsInf_po)
    (hnonpole_inf_an : ∀ k, Dinf_full.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (Dinf_full.xs k)).symm z))
        ((chartAt ℂ (Dinf_full.xs k)) (Dinf_full.xs k))) :
    GlobalTraceData ω₀ g f poles := by
  classical
  set T := valueChartTracePatched ω₀ f Φ br with hT
  -- Meromorphy of `T` at the centres from the full-fibre coherence.
  have hT_mero : ∀ i, MeromorphicAt T (cs i) := by
    intro i
    have hgerm : T =ᶠ[𝓝[≠] (cs i)] (fibreTrace ω₀ f (Cfull i).D).traceCoeff :=
      (valueChartTracePatched_eventuallyEq ω₀ f Φ br (cs i)).trans (Cfull i).coherent_punctured
    exact (meromorphicAt_traceCoeff_fibreTrace ω₀ f (Cfull i).D).congr hgerm.symm
  -- Principal-part `LaurentForm`.
  set hPP := exists_laurentForm_principalPart cs ρ hcs_ball hcs_inj hT_mero with hPP_def
  set L := hPP.choose with hL_def
  have hLcenters : Finset.univ.image L.a = Finset.univ.image cs := hPP.choose_spec.1
  have hLrem : ∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧ (T - L.R) =ᶠ[𝓝[≠] (cs j)] R :=
    hPP.choose_spec.2
  -- The remainder `T − L.R` is germ-regular (FREE): analytic off the centres + the pole removed at them.
  have hT_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ T z := by
    intro z hz; rw [hLcenters] at hz; exact hT_off_patched hreg hbnd hz
  -- `L.R` is analytic off its centre set (its monomial centres lie in `image L.a`).
  have hLR_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ L.R z := by
    intro z hz
    show AnalyticAt ℂ (fun w => ∑ p, L.c p * (w - L.a p) ^ L.n p) z
    refine Finset.analyticAt_fun_sum _ (fun p _ => ?_)
    refine analyticAt_const.mul ?_
    have hbase : AnalyticAt ℂ (fun w : ℂ => w - L.a p) z := analyticAt_id.sub analyticAt_const
    have hzap : z ≠ L.a p := fun h => hz (h ▸ Finset.mem_image_of_mem L.a (Finset.mem_univ p))
    exact hbase.zpow (sub_ne_zero.mpr hzap)
  have hoff_rem : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ (T - L.R) z := fun z hz =>
    (hT_off z hz).sub (hLR_off z hz)
  have hrem : ∀ p ∈ Finset.univ.image L.a,
      ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ (T - L.R) =ᶠ[𝓝[≠] p] R := by
    intro p hp; rw [hLcenters] at hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp; exact hLrem i
  refine
    { L := L
      D := D
      hxs_inj := hxs_inj
      hxs_mem := hxs_mem
      hxs_surj := hxs_surj
      hcenters := by rw [hLcenters]; exact hcenters_cs
      hL32 := ?_
      infty_eq := ?_ }
  · -- Finite Lemma 3.2 (verbatim from `globalTraceData_of_genus0`).
    intro p hp
    rw [hLcenters] at hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hLHS :
        (∑ j, resAt ((fibreTrace ω₀ f (D (cs i))).coeff j) ((fibreTrace ω₀ f (D (cs i))).pre j))
          = ∑ j, formFnResidue ω₀ g ((D (cs i)).xs j) :=
      Finset.sum_congr rfl (fun j _ => resAt_fibreTrace_coeff ω₀ f (D (cs i)) j)
    have hres_fin : resAt T (cs i) = ∑ j, formFnResidue ω₀ g ((D (cs i)).xs j) :=
      hres_fin_of_fullFibreCoherence D i (Cfull i) (hfull_inj i) (hxs_inj (cs i)) (hpole_image i)
        (fun k hk => formFnResidue_eq_zero_of_analyticAt ω₀ g _ (hnonpole_an i k hk))
    obtain ⟨R, hR_an, hR_eq⟩ := hLrem i
    rw [hLHS, ← hres_fin, resAt_eq_laurentR_of_principalPart (hT_mero i) hR_an hR_eq]
  · -- The `∞`-residue identity via germ-Cauchy (the `hcont_int`-free route).
    exact infty_eq_of_remainderRegular hoff_rem hrem Dinf_full hcoh_full hfullInf_inj xsInf_po
      hpoInf_inj hpoInf_mem hpoInf_surj hpole_image_inf
      (fun k hk => formFnResidue_eq_zero_of_analyticAt ω₀ g _ (hnonpole_inf_an k hk))

/-- **Gate A `∑Res = 0` from the residue-level geometry, `hcont_int`-free.**  Routes through
`globalTraceData_of_genus0_germ`: the finite junk-freeness `hcont_int` is **eliminated** (replaced by
the free germ-regularity + germ-Cauchy at `∞`); only the `∞`-coherence `hcoh_full` remains of the
residual-#5/#6 group. -/
theorem residueTheorem_of_directGeometry_genus0_germ
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (D : (p : ℂ) → FibreRegularData g f p)
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hpole_image : ∀ i, (Finset.univ.image (Cfull i).D.xs).filter (· ∈ poles)
      = Finset.univ.image (D (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (Dinf_full : InftyFibreDataNF g f)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full))
    (hfullInf_inj : Function.Injective Dinf_full.xs)
    {ιInfP : Type} [Fintype ιInfP] (xsInf_po : ιInfP → X)
    (hpoInf_inj : Function.Injective xsInf_po)
    (hpoInf_mem : ∀ j, xsInf_po j ∈ poles ∧ f.toRiemannSphere (xsInf_po j) = OnePoint.infty)
    (hpoInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ j, xsInf_po j = a)
    (hpole_image_inf : (Finset.univ.image Dinf_full.xs).filter (· ∈ poles)
      = Finset.univ.image xsInf_po)
    (hnonpole_inf_an : ∀ k, Dinf_full.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (Dinf_full.xs k)).symm z))
        ((chartAt ℂ (Dinf_full.xs k)) (Dinf_full.xs k))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_of_traceExists ω₀ g poles
    (serreTraceExists_of_globalTraceData
      (globalTraceData_of_genus0_germ Φ m cs ρ hcs_ball hcs_inj br hreg hbnd Cfull D hxs_inj hxs_mem
        hxs_surj hcenters_cs hfull_inj hpole_image hnonpole_an Dinf_full hcoh_full
        hfullInf_inj xsInf_po hpoInf_inj hpoInf_mem hpoInf_surj hpole_image_inf hnonpole_inf_an))

/-! ## The adapted-cover / canonical-selection capstones, `hcont_int`-free

Mirror the proven combinatorial field-groups of `residueTheorem_ofAdapted_genus0` /
`…SimpleInfty_genus0` / `…ofCanonicalSimpleInfty_genus0` (pole sub-fibre `poleSubfibre`, the `∞`-pole
sub-enumeration `poleSubEnum`, the simple-`∞` full fibre `inftyFibreDataNF_full`, the canonical-`Φ`
enumeration), but route through the `hcont_int`-**free** `residueTheorem_of_directGeometry_genus0_germ`.
The finite junk-freeness `hcont_int` is **gone**; the remaining analytic inputs are `hreg`/`hbnd` and the
`∞`-coherence `hcoh_full` (the per-centre `Cfull` and the `∞` enumeration are the genuine §VIII.3
geometry). -/

/-- **Gate A `∑Res = 0` from an adapted cover, `hcont_int`-free.**  The germ analogue of
`residueTheorem_ofAdapted_genus0` with the finite junk-freeness `hcont_int` **dropped** (eliminated via
germ-Cauchy at `∞`). -/
theorem residueTheorem_ofAdapted_genus0_germ
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (hΦ_inj : ∀ p, Function.Injective (Φ p).xs)
    (hΦ_mem : ∀ p, ∀ i, f.toRiemannSphere ((Φ p).xs i) = (((p : ℂ) : RiemannSphere)))
    (hΦ_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere)) →
      ∃ i, (Φ p).xs i = a)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hCfull_image : ∀ i, Finset.univ.image (Cfull i).D.xs = Finset.univ.image (Φ (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (Dinf_full : InftyFibreDataNF g f) (hfullInf_inj : Function.Injective Dinf_full.xs)
    (hinf_mem : ∀ k, f.toRiemannSphere (Dinf_full.xs k) = OnePoint.infty)
    (hinf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ k, Dinf_full.xs k = a)
    (hnonpole_inf_an : ∀ k, Dinf_full.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (Dinf_full.xs k)).symm z))
        ((chartAt ℂ (Dinf_full.xs k)) (Dinf_full.xs k)))
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full)) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_of_directGeometry_genus0_germ Φ m cs ρ hcs_ball hcs_inj br hreg hbnd Cfull
    (fun p => poleSubfibre poles (Φ p))
    (fun p => poleSubfibre_xs_injective poles (Φ p) (hΦ_inj p))
    (fun p i => poleSubfibre_xs_mem poles (Φ p) (hΦ_mem p) i)
    (fun p a ha hfa => by
      obtain ⟨i, rfl⟩ := hΦ_surj p a ha hfa
      exact ⟨⟨i, ha⟩, rfl⟩)
    hcenters_cs hCfull_inj
    (fun i => by rw [hCfull_image i]; exact poleSubfibre_hpole_image poles (Φ (cs i)))
    hnonpole_an Dinf_full hcoh_full hfullInf_inj
    (ιInfP := {k // Dinf_full.xs k ∈ poles}) (fun k => Dinf_full.xs k.1)
    (poleSubEnum_injective poles Dinf_full.xs hfullInf_inj)
    (fun k => poleSubEnum_mem poles Dinf_full.xs hinf_mem k)
    (fun a ha hfa => poleSubEnum_surj poles Dinf_full.xs hinf_surj a ha hfa)
    (poleSubEnum_hpole_image poles Dinf_full.xs)
    hnonpole_inf_an

/-- **Gate A `∑Res = 0` from an adapted cover with simple `∞`-poles, `hcont_int`-free.**  The germ
analogue of `residueTheorem_ofAdaptedSimpleInfty_genus0`, `hcont_int` **dropped**. -/
theorem residueTheorem_ofAdaptedSimpleInfty_genus0_germ
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (hΦ_inj : ∀ p, Function.Injective (Φ p).xs)
    (hΦ_mem : ∀ p, ∀ i, f.toRiemannSphere ((Φ p).xs i) = (((p : ℂ) : RiemannSphere)))
    (hΦ_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere)) →
      ∃ i, (Φ p).xs i = a)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hCfull_image : ∀ i, Finset.univ.image (Cfull i).D.xs = Finset.univ.image (Φ (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofAdapted_genus0_germ Φ hΦ_inj hΦ_mem hΦ_surj m cs ρ hcs_ball hcs_inj br hcenters_cs
    Cfull hCfull_inj hCfull_image hnonpole_an
    (inftyFibreDataNF_full g f hsimpleInf hmeroInf)
    (inftyFibreEnum_injective f)
    (fun k => inftyFibreEnum_mem f k)
    (fun _a _ha hfa => inftyFibreEnum_surj f hfa)
    hnonpole_inf_an hreg hbnd hcoh_full

/-- **Gate A `∑Res = 0` from the canonical selection with simple `∞`-poles, `hcont_int`-free.**  The
sound, `hcont_int`-eliminated form of the most-wired capstone
`residueTheorem_ofCanonicalSimpleInfty_genus0`: the canonical full-fibre selection + simple `∞`-poles,
with the kirovGenus-`0` `∞`-vanishing discharged internally (germ-Cauchy) **and** the finite junk-freeness
`hcont_int` removed (replaced by the free germ-regularity of the trace remainder).  Gate A rests on
*exactly* the per-centre full-fibre coherence `Cfull`, the off-centre analyticity `hreg`/`hbnd`, and the
`∞`-coherence `hcoh_full` — the false `hcont_int` is **gone**. -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0_germ (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f (canonicalFibreSelection g f hdiv) (cs i))
    (hCfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hCfull_image : ∀ i,
      Finset.univ.image (Cfull i).D.xs = Finset.univ.image (canonicalFibreSelection g f hdiv (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
        (𝓝[≠] b₀) (𝓝 0))
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofAdaptedSimpleInfty_genus0_germ (canonicalFibreSelection g f hdiv)
    (canonicalFibreSelection_hΦ_inj f hdiv)
    (canonicalFibreSelection_hΦ_mem f hdiv)
    (canonicalFibreSelection_hΦ_surj f hdiv hgood)
    m cs ρ hcs_ball hcs_inj br hcenters_cs Cfull hCfull_inj hCfull_image hnonpole_an
    hsimpleInf hmeroInf hnonpole_inf_an hreg hbnd hcoh_full

/-! ## Non-vacuity (end-to-end soundness)

The `hcont_int`-free capstones are satisfiable, not a disguised `False`: for the empty pole set the empty
fibre selection (`Φ` empty, `m = 0`, `br = ∅`, the zero trace) satisfies every input — and there is no
`hcont_int` to discharge.  Confirms the `hcont_int`-eliminated inputs are honest. -/

/-- **Non-vacuity of the `hcont_int`-free residue-level close.**  For the empty pole set,
`residueTheorem_of_directGeometry_genus0_germ` is satisfiable via the empty selection and `br = ∅`,
yielding `∑_{a ∈ ∅} formFnResidue ω₀ g a = 0`.  Confirms the inputs are not a disguised `False`. -/
theorem residueTheorem_of_directGeometry_genus0_germ_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 := by
  have hpatch0 : valueChartTracePatched ω₀ f (fun p => emptyFibreRegularData g f p) ∅
      = fun _ => (0 : ℂ) := by
    funext z
    rw [valueChartTracePatched_of_not_mem ω₀ f _ _ (Finset.notMem_empty z),
      valueChartTrace_emptySelection ω₀ f]
  refine residueTheorem_of_directGeometry_genus0_germ (g := g) (poles := (∅ : Finset X))
    (fun p => emptyFibreRegularData g f p)
    0 Fin.elim0 0 (fun i => i.elim0) (fun i => i.elim0) (∅ : Finset ℂ)
    (fun w _ => by rw [valueChartTrace_emptySelection ω₀ f]; exact analyticAt_const)
    (fun b₀ hb₀ _ => absurd hb₀ (Finset.notMem_empty b₀))
    (fun i => i.elim0)
    (fun p => emptyFibreRegularData g f p)
    (fun _ i => i.elim) (fun _ i => i.elim)
    (fun _ a ha => absurd ha (Finset.notMem_empty a))
    (by simp)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (emptyInftyFibreDataNF g f) ?_ (by intro i; exact i.elim)
    (ιInfP := Empty) Empty.elim (by intro i; exact i.elim)
    (fun i => i.elim) (fun a ha => absurd ha (Finset.notMem_empty a))
    (by simp) (fun i => i.elim)
  · -- the `∞`-coherence: `recipCoeff 0 =ᶠ recipCoeff (inftyMovingSumNF empty) = recipCoeff 0`.
    have hmoving0 : inftyMovingSumNF ω₀ f (emptyInftyFibreDataNF g f) = fun _ => (0 : ℂ) := by
      funext b'; rw [inftyMovingSumNF]
      exact @Finset.sum_of_isEmpty _ _ _ _ (inferInstanceAs (IsEmpty Empty)) _
    rw [hpatch0, hmoving0]

end Jacobians.Dolbeault.SerreResidueTheorem
