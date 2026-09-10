/-
  Forster §17.4 — the canonical meromorphic 1-form `ω₀ = df` and its canonical divisor `K = div ω₀`,
  instantiating `CanonicalForm17Data X` (which makes the already-proven §17.4 isomorphism
  `omega17Equiv : L(D+K) ≃ₗ[ℂ] Ω_D` of `CanonicalFormIso` unconditional).

  ## The construction (Forster GTM 81, §17.4: `ω = df`)

  Fix the nonconstant meromorphic function `f` of `exists_nonconstant_meromorphic`
  (`Jacobians.Dolbeault.SerreOmega0`).  Its **differential**

      `df.toFun x := mfderiv 𝓘(ℂ) 𝓘(ℂ) f x`

  is a section of the cotangent bundle (`TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`); it is the genuine intrinsic
  differential (the *junk-value* defect — `mfderiv` is `0` where `f` is not `MDifferentiableAt`, i.e.
  at poles — is invisible to the germ object `MeromorphicOneForm`, which only cares that `formCoeff`
  is `MeromorphicAt`).

  The keystone identity (`mfderiv_apply_symmL_eq_deriv`) is, in the chart at `x`,

      `mfderiv f y (symmL y 1) = (f ∘ chart⁻¹)' (chart y)`        (`y` regular, in chart source)

  so the chart coefficient `formCoeff (df) x` agrees, on a punctured neighbourhood of `chart x x`,
  with `(f ∘ chart⁻¹)'`, which is `MeromorphicAt` (`MeromorphicAt.deriv`).  Hence `df` is a genuine
  `MeromorphicOneForm`.

  Sanity check (Forster): `f(z) = z` ⟹ `df = dz`, `K = 0`.

  Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4; Mathlib `mfderiv`,
  `MeromorphicAt.deriv`, `TangentBundle.symmL_trivializationAt`, `mdifferentiableAt_iff_of_mem_source`.
-/
import KirovDolbeault.Dolbeault.CanonicalFormIso
import KirovDolbeault.Dolbeault.SerreOmega0

open scoped Manifold ContDiff Topology Bundle
open Module

namespace Jacobians.Dolbeault

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1: the two intrinsic-differential bridges

`mfderiv f` paired with the spanning tangent vector `symmL 1` of the canonical trivialization reads,
in the chart at `x`, as the chart-pullback derivative `(f ∘ chart⁻¹)'`.  The two lemmas below carry
this (and the analytic ⇒ `MDifferentiableAt` converse) — they are pure Mathlib manifold-calculus,
independent of the meromorphic structure. -/

/-- **The intrinsic-differential / chart-derivative bridge.**  For `y` in the chart source at `x`
where `f` is `MDifferentiableAt`, the covector `mfderiv f y` paired with the spanning tangent vector
`symmL ℂ y 1` equals the ordinary derivative of the chart pullback `f ∘ chart⁻¹` at `chart y`.

This is the chain rule `mfderiv f ∘ mfderiv chart⁻¹ = mfderiv (f ∘ chart⁻¹)`, with
`symmL ℂ y = mfderiv chart⁻¹ (chart y)` (`TangentBundle.symmL_trivializationAt`) and
`mfderiv (f ∘ chart⁻¹) = fderiv` on the model space (`mfderiv_eq_fderiv`). -/
theorem mfderiv_apply_symmL_eq_deriv (f : X → ℂ) {x y : X} (hy : y ∈ (chartAt ℂ x).source)
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) f y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1)
      = deriv (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) := by
  have hytarget : (extChartAt 𝓘(ℂ) x) y ∈ (extChartAt 𝓘(ℂ) x).target :=
    (extChartAt 𝓘(ℂ) x).map_source (by rwa [extChartAt_source])
  have hyback : (extChartAt 𝓘(ℂ) x).symm ((extChartAt 𝓘(ℂ) x) y) = y :=
    (extChartAt 𝓘(ℂ) x).left_inv (by rwa [extChartAt_source])
  have hsymm_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x y) := by
    have h1 := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ)) (x := x) hytarget
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at h1
  have hf_mf' : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) f ((extChartAt 𝓘(ℂ) x).symm ((extChartAt 𝓘(ℂ) x) y))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) f y) := by rw [hyback]; exact hf.hasMFDerivAt
  have hcomp := hf_mf'.comp (extChartAt 𝓘(ℂ) x y) hsymm_diff.hasMFDerivAt
  have hcomp_app := DFunLike.congr_fun hcomp.mfderiv (1 : ℂ)
  have hsymmL : (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x y) := by
    rw [TangentBundle.symmL_trivializationAt hy, ModelWithCorners.range_eq_univ, mfderivWithin_univ]
  rw [hsymmL]
  rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv,
     show (f ∘ (chartAt ℂ x).symm) = (f ∘ (extChartAt 𝓘(ℂ) x).symm) from rfl,
     show ((chartAt ℂ x) y) = ((extChartAt 𝓘(ℂ) x) y) from rfl]
  exact hcomp_app.symm

/-- **Chart-pullback differentiability ⇒ `MDifferentiableAt f`.**  If `f ∘ chart⁻¹` is
`DifferentiableAt` at a chart-target point `z`, then `f` is `MDifferentiableAt` at `chart⁻¹ z`.
(For the codomain `ℂ` the extended chart is the identity, so the manifold-differentiability
criterion `mdifferentiableAt_iff_of_mem_source` is just chart-pullback differentiability.) -/
theorem mdifferentiableAt_of_differentiableAt_comp (f : X → ℂ) {x : X} {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target)
    (hdiff : DifferentiableAt ℂ (f ∘ (chartAt ℂ x).symm) z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f ((chartAt ℂ x).symm z) := by
  have hztarget : z ∈ (extChartAt 𝓘(ℂ) x).target := by
    rw [extChartAt_target, ModelWithCorners.range_eq_univ]; simpa using hz
  have hys : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := by
    rw [← extChartAt_source 𝓘(ℂ) x]; exact (extChartAt 𝓘(ℂ) x).map_target hztarget
  have hfy : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f ((chartAt ℂ x).symm z))).source :=
    mem_chart_source ℂ _
  rw [mdifferentiableAt_iff_of_mem_source hys hfy, ModelWithCorners.range_eq_univ,
    differentiableWithinAt_univ]
  have hzeq : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z := (chartAt ℂ x).right_inv hz
  have hcont : ContinuousAt f ((chartAt ℂ x).symm z) := by
    have h1 : ContinuousAt (f ∘ (chartAt ℂ x).symm) z := hdiff.continuousAt
    have h2 : ContinuousAt (chartAt ℂ x) ((chartAt ℂ x).symm z) := (chartAt ℂ x).continuousAt hys
    have h3 : ContinuousAt ((f ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) ((chartAt ℂ x).symm z) :=
      h1.comp_of_eq h2 hzeq
    refine h3.congr ?_
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds hys] with w hw
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hw]
  refine ⟨hcont, ?_⟩
  have heq : (extChartAt 𝓘(ℂ) (f ((chartAt ℂ x).symm z))) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm
       = (f ∘ (chartAt ℂ x).symm) := by ext w; rfl
  rw [heq, show (extChartAt 𝓘(ℂ) x) ((chartAt ℂ x).symm z) = z from hzeq]
  exact hdiff

/-! ## Part 2: the differential `df` as a meromorphic 1-form

`df.toFun x := mfderiv 𝓘(ℂ) 𝓘(ℂ) f x` (junk-`0` at poles).  Its chart coefficient agrees on a
punctured neighbourhood with `(f ∘ chart⁻¹)'` (`MeromorphicAt.deriv`), so `df` is a genuine
`MeromorphicOneForm`. -/

/-- The underlying cotangent-bundle section of the differential `df`: `x ↦ mfderiv f x`. -/
noncomputable def differentialSection (f : MeromorphicFunction X) : ∀ x, FormFiber X x :=
  fun x => mfderiv 𝓘(ℂ) 𝓘(ℂ) f.toFun x

/-- `formCoeff (df) x` agrees with the chart-pullback derivative `(f ∘ chart⁻¹)'` on a punctured
neighbourhood of `chart x x` (precisely where `f ∘ chart⁻¹` is analytic, hence `f` is
`MDifferentiableAt`). -/
theorem formCoeff_differentialSection_eventuallyEq (f : MeromorphicFunction X) (x : X) :
    (fun z => deriv (f.toFun ∘ (chartAt ℂ x).symm) z) =ᶠ[𝓝[≠] ((chartAt ℂ x) x)]
      formCoeff (differentialSection f) x := by
  have hmero : MeromorphicAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt ℂ x) x) :=
    f.meromorphic x
  have htarget : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  filter_upwards [hmero.eventually_analyticAt, nhdsWithin_le_nhds htarget] with z hz_an hz_target
  have hdiff : DifferentiableAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) z := hz_an.differentiableAt
  have hmdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f.toFun ((chartAt ℂ x).symm z) :=
    mdifferentiableAt_of_differentiableAt_comp f.toFun hz_target hdiff
  have hysrc : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := by
    rw [← extChartAt_source 𝓘(ℂ) x]
    apply (extChartAt 𝓘(ℂ) x).map_target
    rw [extChartAt_target, ModelWithCorners.range_eq_univ]; simpa using hz_target
  have hzeq : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z := (chartAt ℂ x).right_inv hz_target
  show deriv (f.toFun ∘ (chartAt ℂ x).symm) z = _
  rw [show formCoeff (differentialSection f) x z
        = mfderiv 𝓘(ℂ) 𝓘(ℂ) f.toFun ((chartAt ℂ x).symm z)
            ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ ((chartAt ℂ x).symm z) 1)
        from rfl]
  rw [mfderiv_apply_symmL_eq_deriv f.toFun hysrc hmdiff, hzeq]

/-- `df` is a **meromorphic 1-form**: its chart coefficient is `MeromorphicAt` because it germ-agrees
with `(f ∘ chart⁻¹)'`, the derivative of a meromorphic function (`MeromorphicAt.deriv`). -/
theorem isMeromorphicOneForm_differentialSection (f : MeromorphicFunction X) :
    IsMeromorphicOneForm (differentialSection f) := by
  intro x
  have hderiv : MeromorphicAt (deriv (f.toFun ∘ (chartAt ℂ x).symm)) ((chartAt ℂ x) x) :=
    (f.meromorphic x).deriv
  exact hderiv.congr (formCoeff_differentialSection_eventuallyEq f x)

/-- The **canonical meromorphic 1-form `ω₀ = df`** of a meromorphic function `f`. -/
noncomputable def differentialForm (f : MeromorphicFunction X) : MeromorphicOneForm X :=
  ⟨differentialSection f, isMeromorphicOneForm_differentialSection f⟩

@[simp] theorem differentialForm_toFun (f : MeromorphicFunction X) (x : X) :
    (differentialForm f).toFun x = mfderiv 𝓘(ℂ) 𝓘(ℂ) f.toFun x := rfl

/-- `formOrderW (df)` at `x` is the meromorphic order of the chart-pullback derivative
`(f ∘ chart⁻¹)'` (via the germ-agreement of `formCoeff (df)` with it). -/
theorem formOrderW_differentialForm (f : MeromorphicFunction X) (x : X) :
    (differentialForm f).formOrderW x
      = meromorphicOrderAt (deriv (f.toFun ∘ (chartAt ℂ x).symm)) ((chartAt ℂ x) x) := by
  rw [MeromorphicOneForm.formOrderW]
  exact (meromorphicOrderAt_congr (formCoeff_differentialSection_eventuallyEq f x)).symm

/-! ## Part 3: `df ≠ 0` for a nonconstant `f` (the soundness-critical field)

If `f` is nonconstant (`¬ IsGermConstant`), then `df ≠ 0` (`∃ x, formOrderW (df) x ≠ ⊤`).  The
contrapositive `df = 0 ⟹ IsGermConstant f` goes through the **no-pole reduction**: if
`deriv (f ∘ chart⁻¹)` vanishes on a punctured neighbourhood at every point, then `f` has no pole
(`deriv_eventually_zero_meromorphicOrderAt_nonneg`: a pole of order `n < 0` forces `deriv` to have a
pole of order `n − 1 < 0 ≠ ⊤`), so `f ∈ L(0)`, and then the repo's Liouville
`germ_eq_const_of_mem_linearSystem_zero` makes `f` germ-constant. -/

/-- **No pole from a vanishing-derivative germ.**  If `g` is meromorphic at `z₀` and its derivative
vanishes on a punctured neighbourhood of `z₀`, then `g` has *no pole* at `z₀`
(`meromorphicOrderAt g z₀ ≥ 0`).  Proof: were `meromorphicOrderAt g z₀ = n < 0`, the Laurent form
`g =ᶠ (·−z₀)ⁿ • G` (`G` analytic, `G z₀ ≠ 0`) makes `deriv g =ᶠ (n·(·−z₀)ⁿ⁻¹)·G + (·−z₀)ⁿ·G'`, whose
order is exactly `n − 1` (the first term dominates, as `n ≠ 0`, `G z₀ ≠ 0`); but `deriv g =ᶠ 0` forces
order `⊤ ≠ n − 1`.  Pure planar complex analysis (mirrors Mathlib's `MeromorphicAt.deriv`). -/
theorem deriv_eventually_zero_meromorphicOrderAt_nonneg {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : MeromorphicAt g z₀) (hdz : ∀ᶠ z in 𝓝[≠] z₀, deriv g z = 0) :
    0 ≤ meromorphicOrderAt g z₀ := by
  by_contra hlt
  push Not at hlt
  have hne_top : meromorphicOrderAt g z₀ ≠ ⊤ := hlt.ne_top
  lift meromorphicOrderAt g z₀ to ℤ using hne_top with n hn
  have hn_neg : n < 0 := by exact_mod_cast hlt
  obtain ⟨G, hG_an, hG_ne, hG_eq⟩ := (meromorphicOrderAt_eq_int_iff hg).1 hn.symm
  have hderiv_eq1 : deriv g =ᶠ[𝓝[≠] z₀] deriv (fun z => (z - z₀) ^ n • G z) :=
    Filter.EventuallyEq.nhdsNE_deriv hG_eq
  -- the explicit derivative of `(·−z₀)ⁿ • G` (mirror of the computation in `MeromorphicAt.deriv`)
  have hderiv_eq2 : deriv (fun z => (z - z₀) ^ n • G z)
      =ᶠ[𝓝[≠] z₀] fun z => (n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hG_an.eventually_analyticAt,
      eventually_nhdsWithin_of_forall fun _ a => a] with z h₁ h₂
    rw [deriv_fun_smul (DifferentiableAt.zpow (by fun_prop) (by simp_all [sub_ne_zero_of_ne h₂]))
      (by fun_prop), add_comm, deriv_comp_sub_const (f := (· ^ n))]
    aesop
  have hsum_eq : (fun z => (n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z)
      =ᶠ[𝓝[≠] z₀] (0 : ℂ → ℂ) := (hderiv_eq2.symm.trans hderiv_eq1.symm).trans hdz
  have hord_sum_top : meromorphicOrderAt
      (fun z => (n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z) z₀ = ⊤ := by
    rw [meromorphicOrderAt_congr hsum_eq, meromorphicOrderAt_eq_top_iff]
    exact eventually_nhdsWithin_of_forall (fun _ _ => rfl)
  have hcoeff_mero : MeromorphicAt (fun z => (n : ℂ) * (z - z₀) ^ (n - 1)) z₀ := by
    apply MeromorphicAt.mul (MeromorphicAt.const _ _)
    exact (MeromorphicAt.id z₀ |>.sub (MeromorphicAt.const z₀ z₀)).zpow _
  have hterm2_mero : MeromorphicAt (fun z => (z - z₀) ^ n • deriv G z) z₀ := by
    apply MeromorphicAt.smul _ hG_an.meromorphicAt.deriv
    exact (MeromorphicAt.id z₀ |>.sub (MeromorphicAt.const z₀ z₀)).zpow _
  -- the first term has order exactly `n − 1`
  have hord1 : meromorphicOrderAt (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z) z₀
      = ((n - 1 : ℤ) : WithTop ℤ) := by
    rw [show (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z)
          = (fun z => (n : ℂ) * (z - z₀) ^ (n - 1)) • G from rfl,
        meromorphicOrderAt_smul hcoeff_mero hG_an.meromorphicAt,
        hG_an.meromorphicOrderAt_eq, (hG_an.analyticOrderAt_eq_zero).mpr hG_ne]
    have hcoeff_ord : meromorphicOrderAt (fun z => (n : ℂ) * (z - z₀) ^ (n - 1)) z₀
        = ((n - 1 : ℤ) : WithTop ℤ) := by
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn_neg.ne
      rw [meromorphicOrderAt_eq_int_iff hcoeff_mero]
      exact ⟨fun _ => (n : ℂ), analyticAt_const, hn0,
        by filter_upwards [] with z; rw [smul_eq_mul, mul_comm]⟩
    rw [hcoeff_ord]; simp
  -- the second term has order ≥ n
  have hord2_ge : (n : WithTop ℤ) ≤ meromorphicOrderAt (fun z => (z - z₀) ^ n • deriv G z) z₀ := by
    have hm : MeromorphicAt (fun z => (z - z₀) ^ n) z₀ :=
      (MeromorphicAt.id z₀ |>.sub (MeromorphicAt.const z₀ z₀)).zpow _
    rw [show (fun z => (z - z₀) ^ n • deriv G z) = (fun z => (z - z₀) ^ n) • deriv G from rfl,
        meromorphicOrderAt_smul hm hG_an.meromorphicAt.deriv]
    have hzpow_ord : meromorphicOrderAt (fun z => (z - z₀) ^ n) z₀ = (n : WithTop ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hm]
      exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, by filter_upwards [] with z; simp⟩
    rw [hzpow_ord]
    calc (n : WithTop ℤ) = (n : WithTop ℤ) + 0 := by rw [add_zero]
      _ ≤ (n : WithTop ℤ) + meromorphicOrderAt (deriv G) z₀ := by
            gcongr; exact hG_an.deriv.meromorphicOrderAt_nonneg
  have hlt12 : meromorphicOrderAt (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z) z₀
      < meromorphicOrderAt (fun z => (z - z₀) ^ n • deriv G z) z₀ := by
    rw [hord1]
    exact lt_of_lt_of_le (by exact_mod_cast (by omega : (n - 1 : ℤ) < n)) hord2_ge
  have hsum_ord : meromorphicOrderAt
      (fun z => (n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z) z₀
      = ((n - 1 : ℤ) : WithTop ℤ) := by
    rw [show (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z)
          = (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z) + (fun z => (z - z₀) ^ n • deriv G z) from rfl,
        meromorphicOrderAt_add_eq_left_of_lt hterm2_mero hlt12, hord1]
  rw [hsum_ord] at hord_sum_top
  exact WithTop.coe_ne_top hord_sum_top

/-- **`df ≠ 0` for a nonconstant `f`** (Forster §17.4's nontriviality of `ω₀ = df`).  If `f` is not
germ-constant then `df`'s germ is nonzero somewhere.  Contrapositive: if `formOrderW (df) = ⊤`
everywhere, then `deriv (f ∘ chart⁻¹)` vanishes on a punctured neighbourhood at every point, so `f`
has no pole anywhere (`deriv_eventually_zero_meromorphicOrderAt_nonneg`), i.e. `f ∈ L(0)`; then `f`
is germ-constant by the repo Liouville `germ_eq_const_of_mem_linearSystem_zero`. -/
theorem differentialForm_ne_zero {f : MeromorphicFunction X} (hf : ¬ IsGermConstant f) :
    ∃ x, (differentialForm f).formOrderW x ≠ ⊤ := by
  by_contra hcon
  push Not at hcon
  apply hf
  have hf0 : f ∈ linearSystem (X := X) 0 := by
    intro x
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    show (0 : WithTop ℤ) ≤ MeromorphicFunction.orderW f x
    rw [MeromorphicFunction.orderW]
    have htop := hcon x
    rw [formOrderW_differentialForm, meromorphicOrderAt_eq_top_iff] at htop
    exact deriv_eventually_zero_meromorphicOrderAt_nonneg (f.meromorphic x) htop
  exact germ_eq_const_of_mem_linearSystem_zero f hf0

/-! ## Part 4: the canonical divisor `K = div ω₀` and the `CanonicalForm17Data` instance

`K = div (df)` is the order function `x ↦ (formOrderW (df) x).untop₀`; it has **finite support** because
`df`'s zeros/poles are isolated (the chart coefficient `formCoeff (df)` is meromorphic, plus
chart-invariance of `formOrderW`).  Given `K`, the §17.4 datum assembles immediately (`ω₀ = df`,
`nontrivial = differentialForm_ne_zero`, `order_eq`).  The final `canonicalForm17Data` wires this
through the nonconstant `f` of `exists_nonconstant_meromorphic`. -/

/-- **Assembly of `CanonicalForm17Data` from `f`, `df ≠ 0`, and the canonical divisor `K`.**  Given a
meromorphic function `f` (whose `df ≠ 0` is supplied by `hf : ¬ IsGermConstant f`) together with its
form-divisor `K` (a `Divisor X` with `formOrderW (df) x = K x` for all `x`), this is the Forster §17.4
canonical-form datum `ω₀ = df`, `K = div ω₀`.  Fully proven (modulo the divisor input). -/
noncomputable def canonicalForm17DataOfDivisor (f : MeromorphicFunction X)
    (hf : ¬ IsGermConstant f) (K : Divisor X)
    (hK : ∀ x, (differentialForm f).formOrderW x = (K x : WithTop ℤ)) :
    CanonicalForm17Data X where
  ω₀ := differentialForm f
  nontrivial := differentialForm_ne_zero hf
  K := K
  order_eq := hK

/-- **Frame-change law for the canonical trivialization.**  The spanning tangent vector `symmL_x q 1`
(of the canonical trivialization at `x`, read at `q`) and `symmL_y q 1` (at `y`) are related by the
holomorphic chart-transition derivative: `symmL_x q 1 = (chart_y ∘ chart_x⁻¹)' (chart_x q) • symmL_y q 1`.
This is the chain rule `mfderiv (chart_x⁻¹) = mfderiv (chart_y⁻¹) ∘ mfderiv (chart_y ∘ chart_x⁻¹)`
(`symmL_· = mfderiv (chart_·⁻¹)`). -/
theorem symmL_frame_change {x y q : X} (hqx : q ∈ (chartAt ℂ x).source)
    (hqy : q ∈ (chartAt ℂ y).source) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ q (1 : ℂ)
      = deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q)
          • (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ q (1 : ℂ) := by
  have hqx_target : (extChartAt 𝓘(ℂ) x) q ∈ (extChartAt 𝓘(ℂ) x).target :=
    (extChartAt 𝓘(ℂ) x).map_source (by rwa [extChartAt_source])
  have hqx_back : (extChartAt 𝓘(ℂ) x).symm ((extChartAt 𝓘(ℂ) x) q) = q :=
    (extChartAt 𝓘(ℂ) x).left_inv (by rwa [extChartAt_source])
  have hchartx_symm_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm ((chartAt ℂ x) q) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ)) (x := x) hqx_target
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at this
  have hchartY_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) q := by
    have h := mdifferentiableAt_extChartAt (I := 𝓘(ℂ)) (x := y) hqy
    have heq : (extChartAt 𝓘(ℂ) y : X → ℂ) = (chartAt ℂ y : X → ℂ) := rfl
    rwa [heq] at h
  have hψ_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q) := by
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) ((chartAt ℂ x).symm ((chartAt ℂ x) q)) := by
      rw [(chartAt ℂ x).left_inv hqx]; exact hchartY_diff
    exact h2.comp _ hchartx_symm_diff
  have hcomp_eq : (chartAt ℂ x).symm =ᶠ[𝓝 ((chartAt ℂ x) q)]
      (chartAt ℂ y).symm ∘ (chartAt ℂ y ∘ (chartAt ℂ x).symm) := by
    have htarget : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) q) :=
      (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hqx)
    have hpre : (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source ∈ 𝓝 ((chartAt ℂ x) q) := by
      apply (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hqx_target).preimage_mem_nhds
      rw [hqx_back]; exact (chartAt ℂ y).open_source.mem_nhds hqy
    filter_upwards [htarget, hpre] with w _ hw_pre
    show (chartAt ℂ x).symm w = (chartAt ℂ y).symm (chartAt ℂ y ((chartAt ℂ x).symm w))
    rw [(chartAt ℂ y).left_inv hw_pre]
  have hψ_val : (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q) = (chartAt ℂ y) q := by
    show (chartAt ℂ y) ((chartAt ℂ x).symm ((chartAt ℂ x) q)) = _
    rw [(chartAt ℂ x).left_inv hqx]
  have hchartY_symm_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y).symm
      ((chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q)) := by
    rw [hψ_val]
    have hqy_target : (extChartAt 𝓘(ℂ) y) q ∈ (extChartAt 𝓘(ℂ) y).target :=
      (extChartAt 𝓘(ℂ) y).map_source (by rwa [extChartAt_source])
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ)) (x := y) hqy_target
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at this
  have hsymmL_x : (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ q =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm ((chartAt ℂ x) q) := by
    rw [TangentBundle.symmL_trivializationAt hqx, ModelWithCorners.range_eq_univ,
      mfderivWithin_univ]; rfl
  have hsymmL_y : (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ q =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y).symm ((chartAt ℂ y) q) := by
    rw [TangentBundle.symmL_trivializationAt hqy, ModelWithCorners.range_eq_univ,
      mfderivWithin_univ]; rfl
  have hchain : mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm ((chartAt ℂ x) q)
      = (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y).symm
            ((chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q))).comp
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q)) := by
    rw [hcomp_eq.mfderiv_eq]
    exact mfderiv_comp ((chartAt ℂ x) q) hchartY_symm_diff hψ_diff
  -- the inner factor applied to `1` is the chart-transition derivative
  have hf1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q) (1 : ℂ)
      = deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q) := by
    rw [mfderiv_eq_fderiv]; rfl
  have happ := DFunLike.congr_fun hchain (1 : ℂ)
  rw [hsymmL_x, hsymmL_y]
  refine happ.trans ?_
  show mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y).symm ((chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q) (1 : ℂ)) = _
  rw [hf1, hψ_val]
  -- `g (c) = c • g 1`  via linearity (`c • 1 = c`, the tangent-fibre smul being `ℂ`-mul)
  have hsmul := (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y).symm ((chartAt ℂ y) q)).map_smul
    (deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) q)) (1 : ℂ)
  convert hsmul using 2
  change _ = _ * (1 : ℂ)
  ring

/-- **The chart-coefficient transformation law.**  Near `chart_z y`, the coefficient of `α` read in
the chart at `z` equals `ψ' · (coeff at `y` ∘ ψ)`, where `ψ = chart_y ∘ chart_z⁻¹` is the chart
transition: `formCoeff α z (w) = ψ'(w) · formCoeff α y (ψ w)`.  (From `symmL_frame_change` + covector
linearity; the classical `c_z = ψ' · c_y` law for 1-form coefficients.) -/
theorem formCoeff_change (α : MeromorphicOneForm X) (z y : X) (hy : y ∈ (chartAt ℂ z).source) :
    formCoeff α.toFun z =ᶠ[𝓝 ((chartAt ℂ z) y)]
      (fun w => deriv (chartAt ℂ y ∘ (chartAt ℂ z).symm) w
          • formCoeff α.toFun y ((chartAt ℂ y ∘ (chartAt ℂ z).symm) w)) := by
  have hztarget : (chartAt ℂ z).target ∈ 𝓝 ((chartAt ℂ z) y) :=
    (chartAt ℂ z).open_target.mem_nhds ((chartAt ℂ z).map_source hy)
  have hyt : (extChartAt 𝓘(ℂ) z) y ∈ (extChartAt 𝓘(ℂ) z).target :=
    (extChartAt 𝓘(ℂ) z).map_source (by rwa [extChartAt_source])
  have hpre : (chartAt ℂ z).symm ⁻¹' (chartAt ℂ y).source ∈ 𝓝 ((chartAt ℂ z) y) := by
    apply (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hyt).preimage_mem_nhds
    rw [show (extChartAt 𝓘(ℂ) z).symm ((extChartAt 𝓘(ℂ) z) y) = y from
      (extChartAt 𝓘(ℂ) z).left_inv (by rwa [extChartAt_source])]
    exact (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)
  filter_upwards [hztarget, hpre] with w hw_target hw_pre
  set q := (chartAt ℂ z).symm w with hq
  have hqz : q ∈ (chartAt ℂ z).source := (chartAt ℂ z).map_target hw_target
  have hqy : q ∈ (chartAt ℂ y).source := hw_pre
  have hwq : (chartAt ℂ z) q = w := (chartAt ℂ z).right_inv hw_target
  show α.toFun q ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) z).symmL ℂ q 1) = _
  rw [symmL_frame_change hqz hqy, hwq, ContinuousLinearMap.map_smul]
  congr 1
  show α.toFun q ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ q 1)
      = formCoeff α.toFun y ((chartAt ℂ y) q)
  rw [show formCoeff α.toFun y ((chartAt ℂ y) q)
        = α.toFun ((chartAt ℂ y).symm ((chartAt ℂ y) q))
            ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ
              ((chartAt ℂ y).symm ((chartAt ℂ y) q)) 1)
        from rfl, (chartAt ℂ y).left_inv hqy]

/-- **Chart-invariance of `formOrderW`.**  The order of `α` at `y` (read in the canonical chart at
`y`) equals the `meromorphicOrderAt` of `α`'s coefficient in the chart at `z`, at `chart_z y`.  The
two coefficients differ by `ψ'` (non-vanishing holomorphic transition Jacobian) and composition with
the biholomorphism `ψ`, both order-preserving (`meromorphicOrderAt_smul`,
`meromorphicOrderAt_comp_of_deriv_ne_zero`).  This makes the form's zeros/poles a chart-independent
set, the key to the finite support of `K = div ω₀`. -/
theorem formOrderW_chart_invariant (α : MeromorphicOneForm X) (z y : X)
    (hy : y ∈ (chartAt ℂ z).source) :
    α.formOrderW y = meromorphicOrderAt (formCoeff α.toFun z) ((chartAt ℂ z) y) := by
  set ψ := chartAt ℂ y ∘ (chartAt ℂ z).symm with hψ
  have hz_max : chartAt ℂ z ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := IsManifold.chart_mem_maximalAtlas z
  have hy_max : chartAt ℂ y ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := IsManifold.chart_mem_maximalAtlas y
  have hψ_an : AnalyticAt ℂ ψ ((chartAt ℂ z) y) := by
    have h := ModelWithCorners.contDiffWithinAt_extendCoordChange' hz_max hy_max hy
      (mem_chart_source ℂ y)
    rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h; exact h.analyticAt
  have hψ_val : ψ ((chartAt ℂ z) y) = (chartAt ℂ y) y := by
    show (chartAt ℂ y) ((chartAt ℂ z).symm ((chartAt ℂ z) y)) = _; rw [(chartAt ℂ z).left_inv hy]
  have hφ_an : AnalyticAt ℂ (chartAt ℂ z ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) := by
    have h := ModelWithCorners.contDiffWithinAt_extendCoordChange' hy_max hz_max
      (mem_chart_source ℂ y) hy
    rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h; exact h.analyticAt
  have hcomp_id : (chartAt ℂ z ∘ (chartAt ℂ y).symm) ∘ ψ =ᶠ[𝓝 ((chartAt ℂ z) y)] id := by
    have hztarget : (chartAt ℂ z).target ∈ 𝓝 ((chartAt ℂ z) y) :=
      (chartAt ℂ z).open_target.mem_nhds ((chartAt ℂ z).map_source hy)
    have hyt : (extChartAt 𝓘(ℂ) z) y ∈ (extChartAt 𝓘(ℂ) z).target :=
      (extChartAt 𝓘(ℂ) z).map_source (by rwa [extChartAt_source])
    have hpre : (chartAt ℂ z).symm ⁻¹' (chartAt ℂ y).source ∈ 𝓝 ((chartAt ℂ z) y) := by
      apply (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hyt).preimage_mem_nhds
      rw [show (extChartAt 𝓘(ℂ) z).symm ((extChartAt 𝓘(ℂ) z) y) = y from
        (extChartAt 𝓘(ℂ) z).left_inv (by rwa [extChartAt_source])]
      exact (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)
    filter_upwards [hztarget, hpre] with w hw_target hw_pre
    show (chartAt ℂ z) ((chartAt ℂ y).symm ((chartAt ℂ y) ((chartAt ℂ z).symm w))) = w
    rw [(chartAt ℂ y).left_inv hw_pre, (chartAt ℂ z).right_inv hw_target]
  have hderiv_ne : deriv ψ ((chartAt ℂ z) y) ≠ 0 := by
    intro h0
    have hchain := deriv_comp ((chartAt ℂ z) y)
      (hψ_val ▸ hφ_an.differentiableAt) hψ_an.differentiableAt
    rw [hcomp_id.deriv_eq, deriv_id, h0, mul_zero] at hchain
    exact one_ne_zero hchain
  have hfy_mero : MeromorphicAt (formCoeff α.toFun y) (ψ ((chartAt ℂ z) y)) := by
    rw [hψ_val]; exact α.meromorphic y
  have hcomp_mero : MeromorphicAt (formCoeff α.toFun y ∘ ψ) ((chartAt ℂ z) y) :=
    (meromorphicAt_comp_iff_of_deriv_ne_zero hψ_an hderiv_ne).mpr hfy_mero
  rw [meromorphicOrderAt_congr ((formCoeff_change α z y hy).filter_mono nhdsWithin_le_nhds),
    show (fun w => deriv ψ w • formCoeff α.toFun y (ψ w))
        = (fun w => deriv ψ w) • (formCoeff α.toFun y ∘ ψ) from rfl,
    meromorphicOrderAt_smul hψ_an.deriv.meromorphicAt hcomp_mero,
    hψ_an.deriv.meromorphicOrderAt_eq, (hψ_an.deriv.analyticOrderAt_eq_zero).mpr hderiv_ne,
    meromorphicOrderAt_comp_of_deriv_ne_zero hψ_an hderiv_ne, hψ_val]
  rw [MeromorphicOneForm.formOrderW]; simp

/-- **Isolated zeros/poles of a meromorphic function (planar).**  A meromorphic `g` of finite order
at `c` has `meromorphicOrderAt g w = 0` for all `w` on a punctured neighbourhood of `c`: the Laurent
form `g =ᶠ (·−c)ⁿ • G` (`G` analytic, `G c ≠ 0`) is analytic and nonvanishing at every `w ≠ c` near
`c`.  The planar core of `MeromorphicFunction.orderAtPoint_isolated_at`. -/
theorem planar_order_zero (g : ℂ → ℂ) (c : ℂ) (hg : MeromorphicAt g c)
    (hne : meromorphicOrderAt g c ≠ ⊤) :
    ∀ᶠ w in 𝓝[≠] c, meromorphicOrderAt g w = 0 := by
  lift meromorphicOrderAt g c to ℤ using hne with n hn
  obtain ⟨G, hG_an, hG_ne, hG_eq⟩ := (meromorphicOrderAt_eq_int_iff hg).1 hn.symm
  have hcombined : ∀ᶠ w in 𝓝[≠] c,
      g w = (w - c) ^ n • G w ∧ AnalyticAt ℂ G w ∧ G w ≠ 0 := by
    filter_upwards [hG_eq, eventually_nhdsWithin_of_eventually_nhds hG_an.eventually_analyticAt,
      eventually_nhdsWithin_of_eventually_nhds (hG_an.continuousAt.eventually_ne hG_ne)]
      with w h1 h2 h3 using ⟨h1, h2, h3⟩
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at hcombined
  obtain ⟨U, hU, hUopen, hcU⟩ := hcombined
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
  refine ⟨U, ?_, hUopen, hcU⟩
  intro w hwU hwc
  obtain ⟨_, hGw_an, hGw_ne⟩ := hU w hwU hwc
  have hwc' : w ≠ c := hwc
  have hlocal_an : AnalyticAt ℂ (fun u => (u - c) ^ n • G u) w :=
    (((analyticAt_id).sub analyticAt_const).zpow (sub_ne_zero_of_ne hwc')).smul hGw_an
  have hlocal_ne : (fun u => (u - c) ^ n • G u) w ≠ 0 :=
    smul_ne_zero (zpow_ne_zero _ (sub_ne_zero_of_ne hwc')) hGw_ne
  have heq_w : g =ᶠ[𝓝[≠] w] (fun u => (u - c) ^ n • G u) := by
    have hUnhd : U ∈ 𝓝 w := hUopen.mem_nhds hwU
    have hne_w : {c}ᶜ ∈ 𝓝 w := isOpen_compl_singleton.mem_nhds hwc'
    filter_upwards [nhdsWithin_le_nhds hUnhd, nhdsWithin_le_nhds hne_w] with u huU huc
    exact (hU u huU (by simpa using huc)).1
  rw [meromorphicOrderAt_congr heq_w, hlocal_an.meromorphicOrderAt_eq,
    (hlocal_an.analyticOrderAt_eq_zero).mpr hlocal_ne]; rfl

/-- **Isolated zeros/poles of a nonzero meromorphic 1-form.**  If `α`'s germ is nonzero everywhere
(`formOrderW α ≠ ⊤`), then around each `z` the only point of nonzero order is `z` itself: in the chart
at `z` the coefficient `formCoeff α z` is meromorphic of finite order, so its zeros/poles are isolated
(`planar_order_zero`), and `formOrderW` is chart-invariant. -/
theorem formOrderW_isolated (α : MeromorphicOneForm X) (hα : ∀ x, α.formOrderW x ≠ ⊤) (z : X) :
    ∃ t ∈ 𝓝 z, ∀ y ∈ t, y ≠ z → α.formOrderW y = 0 := by
  have hzero := planar_order_zero (formCoeff α.toFun z) ((chartAt ℂ z) z) (α.meromorphic z) (hα z)
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at hzero
  obtain ⟨V, hV, hVopen, hzV⟩ := hzero
  have hcont : ContinuousAt (chartAt ℂ z) z := (chartAt ℂ z).continuousAt (mem_chart_source ℂ z)
  have hpreV : (chartAt ℂ z) ⁻¹' V ∈ 𝓝 z := hcont.preimage_mem_nhds (hVopen.mem_nhds hzV)
  have hsrc : (chartAt ℂ z).source ∈ 𝓝 z :=
    (chartAt ℂ z).open_source.mem_nhds (mem_chart_source ℂ z)
  refine ⟨(chartAt ℂ z) ⁻¹' V ∩ (chartAt ℂ z).source, Filter.inter_mem hpreV hsrc, ?_⟩
  intro y ⟨hyV, hysrc⟩ hyne
  have hchart_ne : (chartAt ℂ z) y ≠ (chartAt ℂ z) z := fun heq =>
    hyne ((chartAt ℂ z).injOn hysrc (mem_chart_source ℂ z) heq)
  rw [formOrderW_chart_invariant α z y hysrc]
  exact hV ((chartAt ℂ z) y) hyV hchart_ne

/-- **The canonical divisor of a nonzero meromorphic 1-form** `div α`.  The order function
`x ↦ (formOrderW α x).untop₀` has finite support (zeros/poles isolated by `formOrderW_isolated`,
finite on the compact `X` via `locallyFinsuppWithin.finiteSupport`), and since `formOrderW α ≠ ⊤`
everywhere the `untop₀` loses nothing, so `formOrderW α x = (div α) x`.  The 1-form analog of
`MeromorphicFunction.div`. -/
theorem exists_form_divisor (α : MeromorphicOneForm X) (hα : ∀ x, α.formOrderW x ≠ ⊤) :
    ∃ K : Divisor X, ∀ x, α.formOrderW x = (K x : WithTop ℤ) := by
  -- the order function has locally finite support (isolation), hence finite support (compact `X`)
  have hloc : LocallyFiniteSupport (fun x => (α.formOrderW x).untop₀) := by
    intro z
    obtain ⟨t, ht_nhds, ht⟩ := formOrderW_isolated α hα z
    refine ⟨t, ht_nhds, Set.Finite.subset (Set.finite_singleton z) ?_⟩
    intro y ⟨hy_t, hy_supp⟩
    by_contra hne
    exact hy_supp (show (α.formOrderW y).untop₀ = 0 by rw [ht y hy_t hne]; rfl)
  have hfin : (Function.support (fun x => (α.formOrderW x).untop₀)).Finite := by
    have := hloc.finite_inter_support_of_isCompact (isCompact_univ (X := X))
    rwa [Set.univ_inter] at this
  refine ⟨Finsupp.ofSupportFinite (fun x => (α.formOrderW x).untop₀) hfin, fun x => ?_⟩
  rw [Finsupp.ofSupportFinite_coe]
  exact (WithTop.coe_untop₀_of_ne_top (hα x)).symm

/-- **The canonical divisor `K = div (df)`.**  The form-divisor of `df` (a nonzero form, by `hf` +
the form identity theorem), via `exists_form_divisor`. -/
theorem exists_differentialForm_divisor (f : MeromorphicFunction X)
    (hf : ∃ x, (differentialForm f).formOrderW x ≠ ⊤) :
    ∃ K : Divisor X, ∀ x, (differentialForm f).formOrderW x = (K x : WithTop ℤ) :=
  exists_form_divisor (differentialForm f)
    (fun x => MeromorphicOneForm.formOrderW_ne_top_of_exists (differentialForm f) hf x)

/-- **Forster §17.4 — the canonical-form datum `ω₀ = df`, `K = div ω₀` exists.**  Combining the
nonconstant meromorphic function `f` of `exists_nonconstant_meromorphic` (`SerreOmega0`), its
differential `df` (a genuine `MeromorphicOneForm`, nonzero by `differentialForm_ne_zero`), and its
canonical divisor `K` (`exists_differentialForm_divisor`), this instantiates `CanonicalForm17Data X`
— making the already-proven §17.4 isomorphism `omega17Equiv : L(D+K) ≃ₗ[ℂ] Ω_D` of `CanonicalFormIso`
unconditional. -/
theorem nonempty_canonicalForm17Data : Nonempty (CanonicalForm17Data X) := by
  obtain ⟨_D, f, _hmem, hf⟩ := exists_nonconstant_meromorphic (X := X)
  obtain ⟨K, hK⟩ := exists_differentialForm_divisor f (differentialForm_ne_zero hf)
  exact ⟨canonicalForm17DataOfDivisor f hf K hK⟩

end Jacobians.Dolbeault
