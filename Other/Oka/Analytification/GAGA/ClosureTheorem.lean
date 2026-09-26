/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.HolomorphicFrechetOps
public import Other.Oka.Analytic.Laurent.Several
public import Other.Oka.MaximalIdeal
public import Other.Oka.Noetherian
public import Mathlib.RingTheory.Filtration

/-!
# Cartan's closure theorem

Let `U ⊆ ℂ^ι` be open, `x ∈ U`, and `N` a submodule of `𝒪ₓ^σ = σ → LocalOkaRing ι`. Then the set
of `f ∈ 𝒪(U)^σ` whose germ at `x` lies in `N` is closed for the topology of compact convergence.

The proof avoids Weierstrass division with bounds:

1. *Taylor coefficients are continuous* (`OkaRing.continuous_coeffGerm`): the `d`-th Taylor
   coefficient at `x` is a multi-Laurent coefficient on a small torus about `x`
   (`MvPowerSeries.coeff_eq_mcoeff`), hence satisfies the Cauchy estimate
   `|c_d(f)| ≤ ρ^{-|d|} sup_{‖y - x‖ ≤ ρ} |f(y)|` (`OkaRing.norm_coeff_germ_le`).
2. Hence the preimage of `N ⊔ 𝔪^k • ⊤` is closed: it is a subspace containing the kernel of the
   continuous `k`-jet map to a finite-dimensional space
   (`Submodule.isClosed_of_ker_le_of_finiteDimensional`).
3. `N = ⋂_k (N ⊔ 𝔪^k • ⊤)` by the Krull intersection theorem in the Noetherian local ring `𝒪ₓ`
   applied to the finite module `𝒪ₓ^σ ⧸ N` (`Submodule.mem_of_forall_mem_sup_pow_smul_top`).

## Main definitions

- `OkaRing.coeffGermCLM hx d : OkaRing U →L[ℂ] ℂ`: the `d`-th Taylor coefficient at `x`.
- `OkaRing.germVec hx : (σ → OkaRing U) →ₗ[ℂ] (σ → LocalOkaRing ι)`: germs at `x`, componentwise.

## Main results

- `OkaRing.isClosed_setOf_germVec_mem`: **local closure theorem**.
- `OkaRing.isClosed_setOf_forall_germVec_mem_span`: **global closure theorem**: for a matrix `A`
  of holomorphic functions, the set of `f` whose germ at every point of `U` lies in the span of
  the germs of the columns of `A` is closed; it contains the closure of the range of
  `Matrix.toOkaCLM A` (`OkaRing.closure_range_toOkaCLM_subset`).
-/

@[expose] public section

open Filter Set Topology TopologicalSpace Metric
open scoped Matrix

universe u

/-! ### Two algebraic lemmas -/

/-- A subspace containing the kernel of a continuous linear map to a finite-dimensional Hausdorff
space is closed. -/
theorem Submodule.isClosed_of_ker_le_of_finiteDimensional {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F] [FiniteDimensional 𝕜 F]
    (J : E →L[𝕜] F) (S : Submodule 𝕜 E) (h : LinearMap.ker (J : E →ₗ[𝕜] F) ≤ S) :
    IsClosed (S : Set E) := by
  have hS : (S : Set E) = J ⁻¹' (S.map (J : E →ₗ[𝕜] F)) := by
    ext v
    refine ⟨fun hv ↦ ⟨v, hv, rfl⟩, ?_⟩
    rintro ⟨s, hs, hsv⟩
    have hker : v - s ∈ LinearMap.ker (J : E →ₗ[𝕜] F) := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact hsv.symm
    simpa using S.add_mem (h hker) hs
  rw [hS]
  exact (Submodule.closed_of_finiteDimensional _).preimage J.continuous

open IsLocalRing in
/-- **Krull's intersection theorem**, for a submodule `N` of a finite module over a Noetherian
local ring: `N = ⋂ₖ (N ⊔ 𝔪^k • ⊤)`. -/
theorem Submodule.mem_of_forall_mem_sup_pow_smul_top {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) {v : M} (h : ∀ k : ℕ, v ∈ N ⊔ maximalIdeal R ^ k • (⊤ : Submodule R M)) :
    v ∈ N := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M ⧸ N) (maximalIdeal R)
    (maximalIdeal.isMaximal R).ne_top
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mem_bot R, ← hbot, Submodule.mem_iInf]
  intro k
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h k)
  have hb' : N.mkQ b ∈ (maximalIdeal R ^ k • ⊤ : Submodule R M).map N.mkQ :=
    Submodule.mem_map_of_mem hb
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hb'
  rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero N).2 ha, zero_add]
  exact hb'

/-- A tuple all of whose entries lie in the ideal `I` lies in `I • ⊤`. -/
theorem Submodule.pi_mem_smul_top {R σ : Type*} [CommRing R] [Finite σ]
    {I : Ideal R} {v : σ → R} (hv : ∀ i, v i ∈ I) : v ∈ I • (⊤ : Submodule R (σ → R)) := by
  classical
  have := Fintype.ofFinite σ
  rw [pi_eq_sum_univ v]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hv i) trivial

/-! ### Taylor coefficients as multi-Laurent coefficients -/

namespace MvPowerSeries

variable {ι : Type u} {n : ℕ}

/-- A multi-index on `ι` as a Laurent exponent on `Fin n`, along `e : ι ≃ Fin n`. -/
def laurentExp (e : ι ≃ Fin n) (d : ι →₀ ℕ) : Fin n → ℤ := fun j ↦ (d (e.symm j) : ℤ)

lemma laurentExp_injective (e : ι ≃ Fin n) : Function.Injective (laurentExp e) := by
  intro d d' h
  ext i
  simpa [laurentExp] using congrFun h (e i)

/-- The coefficients of a power series on `ι`, as a family of Laurent coefficients on `Fin n`
along `e : ι ≃ Fin n` (zero off the image of `laurentExp e`). -/
noncomputable def laurentCoeff (e : ι ≃ Fin n) (P : MvPowerSeries ι ℂ) : (Fin n → ℤ) → ℂ :=
  Function.extend (laurentExp e) (fun d ↦ coeff d P) 0

lemma laurentCoeff_laurentExp (e : ι ≃ Fin n) (P : MvPowerSeries ι ℂ) (d : ι →₀ ℕ) :
    laurentCoeff e P (laurentExp e d) = coeff d P :=
  (laurentExp_injective e).extend_apply _ _ d

lemma laurentCoeff_of_notMem (e : ι ≃ Fin n) (P : MvPowerSeries ι ℂ) {k : Fin n → ℤ}
    (hk : k ∉ range (laurentExp e)) : laurentCoeff e P k = 0 :=
  Function.extend_apply' _ _ _ (by simpa using hk)

lemma monomial_laurentExp [Finite ι] (e : ι ≃ Fin n) (d : ι →₀ ℕ) (w : Fin n → ℂ) :
    Laurent.monomial (laurentExp e d) w = evalMonomial d (fun i ↦ w (e i)) := by
  have := Fintype.ofFinite ι
  rw [evalMonomial_eq_prod, Laurent.monomial, ← e.prod_comp]
  simp [laurentExp]

lemma hasSum_laurentCoeff [Finite ι] (e : ι ≃ Fin n) (P : MvPowerSeries ι ℂ) {w : Fin n → ℂ} {a : ℂ}
    (h : HasSum (P.term fun i ↦ w (e i)) a) :
    HasSum (fun k ↦ laurentCoeff e P k * Laurent.monomial k w) a := by
  rw [← (laurentExp_injective e).hasSum_iff fun k hk ↦ by
    rw [laurentCoeff_of_notMem e P hk, zero_mul]]
  refine h.congr_fun fun d ↦ ?_
  rw [Function.comp_apply, laurentCoeff_laurentExp, monomial_laurentExp]
  rfl

lemma summable_laurentCoeff [Finite ι] (e : ι ≃ Fin n) (P : MvPowerSeries ι ℂ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (h : P.SummableAt fun _ ↦ (ρ : ℂ)) :
    Summable fun k ↦ ‖laurentCoeff e P k‖ * ∏ i, ρ ^ k i := by
  have := Fintype.ofFinite ι
  refine ((laurentExp_injective e).summable_iff fun k hk ↦ by
    rw [laurentCoeff_of_notMem e P hk, norm_zero, zero_mul]).1 ?_
  refine Summable.congr h fun d ↦ ?_
  rw [Function.comp_apply, laurentCoeff_laurentExp, term, norm_mul, norm_evalMonomial,
    ← e.prod_comp]
  simp [laurentExp, abs_of_nonneg hρ]

/-- The Taylor coefficients of a locally convergent power series representing a function `G`
holomorphic on the polydisc `ball 0 R` are the multi-Laurent coefficients of `G` on the torus of
any radius `ρ < R` (after identifying `ι` with `Fin n`). -/
theorem coeff_eq_mcoeff [Fintype ι] {G : (ι → ℂ) → ℂ} {P : MvPowerSeries ι ℂ}
    (hconv : P.LocallyConvergent) (hP : P.Represents G) {R : ℝ}
    (hG : DifferentiableOn ℂ G (ball 0 R)) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : ι ≃ Fin n) (d : ι →₀ ℕ) :
    coeff d P = Laurent.mcoeff (fun w ↦ G fun i ↦ w (e i)) (fun _ ↦ ρ) (laurentExp e d) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and hconv)
  set ρ' := min ρ (δ / 2)
  have hρ'0 : 0 < ρ' := lt_min hρ (half_pos hδ)
  have hρ'δ : ρ' < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hR : 0 < R := hρ.trans hρR
  have hmem : ∀ w ∈ Laurent.torus (fun _ ↦ ρ'), (fun i ↦ w (e i)) ∈ ball (0 : ι → ℂ) δ := by
    intro w hw
    rw [mem_ball_zero_iff, pi_norm_lt_iff hδ]
    intro i
    rw [Laurent.mem_torus.1 hw (e i)]
    exact hρ'δ
  have hconst : (fun _ : ι ↦ (ρ' : ℂ)) ∈ ball (0 : ι → ℂ) δ := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hδ]
    intro _
    rw [Complex.norm_of_nonneg hρ'0.le]
    exact hρ'δ
  have h1 : Laurent.mcoeff (fun w ↦ G fun i ↦ w (e i)) (fun _ ↦ ρ') (laurentExp e d) =
      coeff d P := by
    rw [Laurent.mcoeff_eq_of_hasSum (fun _ ↦ hρ'0) (b := laurentCoeff e P)
      (summable_laurentCoeff e P hρ'0.le (hball _ hconst).2)
      (fun w hw ↦ hasSum_laurentCoeff e P (hball _ (hmem w hw)).1), laurentCoeff_laurentExp]
  have hrad : ∀ {s : ℝ}, 0 < s → s < R → Laurent.IsRadius (-1) (ENNReal.ofReal R) s :=
    fun hs hsR ↦ ⟨hs, by linarith, (ENNReal.ofReal_lt_ofReal_iff hR).2 hsR⟩
  have hdiff : DifferentiableOn ℂ (fun w : Fin n → ℂ ↦ G fun i ↦ w (e i))
      (Laurent.polyAnnulus (fun _ ↦ -1) fun _ ↦ ENNReal.ofReal R) := by
    refine hG.comp (differentiable_pi.2 fun i ↦ differentiable_apply (e i)).differentiableOn ?_
    intro w hw
    rw [Laurent.mem_polyAnnulus] at hw
    rw [mem_ball_zero_iff, pi_norm_lt_iff hR]
    intro i
    have := (hw (e i)).2
    rw [Laurent.enorm_lt_iff_ofReal_lt, ENNReal.ofReal_lt_ofReal_iff hR] at this
    exact this
  rw [← h1]
  exact Laurent.mcoeff_eq_of_isRadius hdiff (fun _ ↦ hrad hρ'0 ((min_le_left _ _).trans_lt hρR))
    (fun _ ↦ hrad hρ hρR) _

end MvPowerSeries

/-! ### Continuity of Taylor coefficients -/

namespace OkaRing

open MvPowerSeries

variable {ι : Type u} [Fintype ι] {U : Opens (ι → ℂ)} {x : ι → ℂ}

/-- The **Cauchy estimate** for Taylor coefficients: if the closed polydisc of radius `ρ` about
`x` lies (with some bigger polydisc) in `U` and `|f| ≤ M` on it, then
`|c_d(f)| ≤ M ρ^{-|d|}`. -/
theorem norm_coeff_germ_le (hx : x ∈ U) {R ρ : ℝ} (hball : ball x R ⊆ U) (hρ : 0 < ρ)
    (hρR : ρ < R) (d : ι →₀ ℕ) (f : OkaRing U) {M : ℝ}
    (hM : ∀ y ∈ closedBall x ρ, ‖f.toGlobalFun U y‖ ≤ M) :
    ‖coeff d (germ hx f : MvPowerSeries ι ℂ)‖ ≤
      M * ∏ j, ρ ^ (-laurentExp (Fintype.equivFin ι) d j) := by
  have hG : DifferentiableOn ℂ (fun z ↦ f.toGlobalFun U (z + x)) (ball 0 R) := by
    refine f.differentiableOn_toGlobalFun.comp (differentiableOn_id.add_const x) ?_
    intro z hz
    apply hball
    simpa [mem_ball, dist_eq_norm] using hz
  rw [coeff_eq_mcoeff (germ hx f).2 (germ_represents hx f) hG hρ hρR]
  refine Laurent.norm_mcoeff_le (fun _ ↦ hρ) (fun w hw ↦ hM _ ?_) _
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, pi_norm_le_iff_of_nonneg hρ.le]
  intro i
  rw [Laurent.mem_torus.1 hw]

/-- The `d`-th Taylor coefficient at `x`, as a `ℂ`-linear map on `OkaRing U`. -/
noncomputable def coeffGerm (hx : x ∈ U) (d : ι →₀ ℕ) : OkaRing U →ₗ[ℂ] ℂ :=
  (coeff d).comp ((localOkaSubring ι).val.toLinearMap.comp (germ hx).toLinearMap)

@[simp]
lemma coeffGerm_apply (hx : x ∈ U) (d : ι →₀ ℕ) (f : OkaRing U) :
    coeffGerm hx d f = coeff d (germ hx f : MvPowerSeries ι ℂ) :=
  rfl

/-- **Taylor coefficients depend continuously on the function** for the topology of compact
convergence (Cauchy estimates). -/
theorem continuous_coeffGerm (hx : x ∈ U) (d : ι →₀ ℕ) : Continuous (coeffGerm hx d) := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 U.isOpen x hx
  set ρ := R / 2
  have hρ : 0 < ρ := half_pos hR
  have hρR : ρ < R := half_lt_self hR
  have hsub : closedBall x ρ ⊆ U := (closedBall_subset_ball hρR).trans hball
  set C := ∏ j, ρ ^ (-laurentExp (Fintype.equivFin ι) d j)
  have hC : 0 ≤ C := Finset.prod_nonneg fun _ _ ↦ zpow_nonneg hρ.le _
  set K : Set U := Subtype.val ⁻¹' closedBall x ρ
  have hK : IsCompact K := by
    have : Subtype.val '' K = closedBall x ρ := by
      ext y
      exact ⟨fun ⟨z, hz, hzy⟩ ↦ hzy ▸ hz, fun hy ↦ ⟨⟨y, hsub hy⟩, hy, rfl⟩⟩
    rw [Subtype.isCompact_iff, this]
    exact isCompact_closedBall x ρ
  refine continuous_of_continuousAt_zero (coeffGerm hx d) ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  set η := ε / (C + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hN : toContinuousMap U ⁻¹' {g | MapsTo g K (ball 0 η)} ∈ 𝓝 (0 : OkaRing U) := by
    refine continuous_toContinuousMap.continuousAt.preimage_mem_nhds
      ((ContinuousMap.isOpen_setOf_mapsTo hK Metric.isOpen_ball).mem_nhds ?_)
    intro y _
    simpa using hη
  filter_upwards [hN] with f hf
  rw [dist_zero_right, coeffGerm_apply]
  have hM : ∀ y ∈ closedBall x ρ, ‖f.toGlobalFun U y‖ ≤ η := by
    intro y hy
    have := hf (show (⟨y, hsub hy⟩ : U) ∈ K from hy)
    rw [mem_ball_zero_iff] at this
    rw [toGlobalFun_apply _ (hsub hy)]
    exact this.le
  calc _ ≤ η * C := norm_coeff_germ_le hx hball hρ hρR d f hM
    _ < η * (C + 1) := mul_lt_mul_of_pos_left (lt_add_one C) hη
    _ = ε := div_mul_cancel₀ ε (by linarith)

/-- The `d`-th Taylor coefficient at `x`, as a continuous `ℂ`-linear functional on
`OkaRing U`. -/
noncomputable def coeffGermCLM (hx : x ∈ U) (d : ι →₀ ℕ) : OkaRing U →L[ℂ] ℂ :=
  ⟨coeffGerm hx d, continuous_coeffGerm hx d⟩

@[simp]
lemma coeffGermCLM_apply (hx : x ∈ U) (d : ι →₀ ℕ) (f : OkaRing U) :
    coeffGermCLM hx d f = coeff d (germ hx f : MvPowerSeries ι ℂ) :=
  rfl

/-! ### The closure theorem -/

variable {σ : Type*}

/-- The germs at `x` of a tuple of holomorphic functions on `U`. -/
noncomputable def germVec (hx : x ∈ U) : (σ → OkaRing U) →ₗ[ℂ] (σ → LocalOkaRing ι) :=
  LinearMap.pi fun i ↦ (germ hx).toLinearMap ∘ₗ LinearMap.proj i

@[simp]
lemma germVec_apply (hx : x ∈ U) (f : σ → OkaRing U) (i : σ) :
    germVec hx f i = germ hx (f i) :=
  rfl

open IsLocalRing in
/-- **Cartan's closure theorem**, local form: for a submodule `N` of `𝒪ₓ^σ`, the set of tuples of
holomorphic functions on `U` whose germ at `x` lies in `N` is closed. -/
theorem isClosed_setOf_germVec_mem [Finite σ] (hx : x ∈ U)
    (N : Submodule (LocalOkaRing ι) (σ → LocalOkaRing ι)) :
    IsClosed {f : σ → OkaRing U | germVec hx f ∈ N} := by
  classical
  have := Fintype.ofFinite σ
  have hS : {f : σ → OkaRing U | germVec hx f ∈ N} = ⋂ k : ℕ,
      (((N ⊔ maximalIdeal (LocalOkaRing ι) ^ k • ⊤).restrictScalars ℂ).comap
        (germVec hx) : Set (σ → OkaRing U)) := by
    ext f
    simp only [mem_setOf_eq, mem_iInter, SetLike.mem_coe, Submodule.mem_comap,
      Submodule.restrictScalars_mem]
    exact ⟨fun h _ ↦ Submodule.mem_sup_left h, Submodule.mem_of_forall_mem_sup_pow_smul_top N⟩
  rw [hS]
  refine isClosed_iInter fun k ↦ ?_
  let T := (Finset.range k).biUnion (degFinset ι)
  let J : (σ → OkaRing U) →L[ℂ] (σ × T → ℂ) :=
    ContinuousLinearMap.pi fun p ↦ (coeffGermCLM hx p.2.1).comp (ContinuousLinearMap.proj p.1)
  refine Submodule.isClosed_of_ker_le_of_finiteDimensional J _ fun f hf ↦ ?_
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
  refine Submodule.mem_sup_right (Submodule.pi_mem_smul_top fun i ↦ ?_)
  rw [germVec_apply, LocalOkaRing.mem_maximalIdeal_pow_iff]
  intro d hd
  have := congrFun (LinearMap.mem_ker.1 hf)
    (i, ⟨d, Finset.mem_biUnion.2 ⟨_, Finset.mem_range.2 hd, self_mem_degFinset d⟩⟩)
  simpa [J] using this

/-- **Cartan's closure theorem**, global form: for a matrix `A` of holomorphic functions on `U`,
the set of `f ∈ 𝒪(U)^σ` whose germ at every point of `U` lies in the span of the germs of the
columns of `A` is closed. -/
theorem isClosed_setOf_forall_germVec_mem_span [Finite σ] {τ : Type*}
    (A : Matrix σ τ (OkaRing U)) :
    IsClosed {f : σ → OkaRing U | ∀ (x : ι → ℂ) (hx : x ∈ U), germVec hx f ∈
      Submodule.span (LocalOkaRing ι) (range fun j ↦ germVec hx fun i ↦ A i j)} := by
  simp only [setOf_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun hx ↦ isClosed_setOf_germVec_mem hx _

/-- The germ of `A *ᵥ g` lies in the span of the germs of the columns of `A`. -/
theorem germVec_mulVec_mem_span {τ : Type*} [Fintype τ] (A : Matrix σ τ (OkaRing U))
    (g : τ → OkaRing U) (hx : x ∈ U) :
    germVec hx (A *ᵥ g) ∈
      Submodule.span (LocalOkaRing ι) (range fun j ↦ germVec hx fun i ↦ A i j) := by
  have h : germVec hx (A *ᵥ g) = ∑ j, germ hx (g j) • germVec hx fun i ↦ A i j := by
    ext i : 1
    simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The closure of the image of the map `𝒪(U)^τ → 𝒪(U)^σ` given by a matrix `A` consists of
tuples whose germs lie pointwise in the image of `A` on germs. -/
theorem closure_range_toOkaCLM_subset [Finite σ] {τ : Type*} [Fintype τ]
    (A : Matrix σ τ (OkaRing U)) :
    closure (range (Matrix.toOkaCLM A)) ⊆
      {f : σ → OkaRing U | ∀ (x : ι → ℂ) (hx : x ∈ U), germVec hx f ∈
        Submodule.span (LocalOkaRing ι) (range fun j ↦ germVec hx fun i ↦ A i j)} := by
  refine closure_minimal ?_ (isClosed_setOf_forall_germVec_mem_span A)
  rintro _ ⟨g, rfl⟩ x hx
  exact germVec_mulVec_mem_span A g hx

end OkaRing

end
