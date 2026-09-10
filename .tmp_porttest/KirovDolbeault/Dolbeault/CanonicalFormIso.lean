/-
  Forster §17.4 — the canonical-form multiplication isomorphism `ω₀·: 𝒪_{D+K} ≅ Ω_D`, the
  canonical divisor `K = div ω₀`, and `lDim K = kirovGenus X` (17.4 at `D = 0`).

  Built directly on **Gate (C)** (`Jacobians.Dolbeault.MeromorphicOneFormSystem`): the
  meromorphic-1-form linear system `Ω_D = omegaD D`, its junk-free module `omegaDModule D`,
  `omegaDim`, the §17.4 multiplication map `meroFormSMul f α` (= `f·α`) with its order additivity
  `formOrderW (f·α) = orderW f + formOrderW α`, and the `Ω_0 ≅ HolomorphicOneForms` wiring
  (`omegaDim_zero_eq_genus_of_le`).

  ## The Forster §17.4 content (close reading of GTM 81, §17.4)

  Fix a nonzero meromorphic 1-form `ω₀` (Forster takes `ω₀ = df` for a nonconstant meromorphic `f`,
  which exists by the Riemann–Roch inequality — `exists_nonconstant_meromorphic`). Let
  `K := div ω₀` (the canonical divisor). The map `f ↦ f·ω₀` is, for each divisor `D`, an isomorphism

      `ω₀· : L(D + K) ≅ Ω_D`,

  i.e. on the junk-free modules `lSysModule (D + K) ≃ₗ[ℂ] omegaDModule D`. It is well-defined and
  injective because multiplication by the nonzero `ω₀` is injective on germ-junk-free modules
  (order additivity + the form identity theorem for `ω₀ ≠ 0`); surjective because every `α ∈ Ω_D`
  is `f₀·ω₀` with `f₀ = α/ω₀` a meromorphic function — and the covector ratio `α/ω₀` is *intrinsic*
  (both `α x` and `ω₀ x` lie in the 1-dim cotangent fibre at `x`), so it is chart-independent and
  meromorphic, with `div f₀ = div α − K`, placing `f₀ ∈ L(D + K)`.

  At `D = 0` this is `𝒪_K ≅ Ω_0`, and composing with `Ω_0 ≅ HolomorphicOneForms` (Gate C's
  `omegaDim_zero_eq_genus_of_le`) gives `lDim K = kirovGenus X` — the `hKgenus` field of
  `SerreDualityData`.

  ## The one isolated analytic input

  The **canonical divisor** `K = div ω₀` of a *nonzero* meromorphic 1-form: the order function
  `x ↦ (formOrderW ω₀ x).untop₀` has finite support (`ω₀` has finitely many zeros/poles on the
  compact `X`), so it is a genuine `Divisor X` with `formOrderW ω₀ x = (K x : WithTop ℤ)` for all
  `x` (the form identity theorem gives `formOrderW ω₀ x ≠ ⊤` everywhere, so the `untop₀` loses no
  information). This existence-of-the-form-divisor is the 1-form analog of `MeromorphicFunction.div`
  (the local-finiteness `orderAtPoint_isolated_at` of `Jacobians.Abel`), and the construction of `ω₀`
  itself (`ω₀ = df`) is the analytic differential. Both are bundled, with `ω₀ ≠ 0`, into the isolated
  hypothesis structure `CanonicalForm17Data` below; **every theorem built on it is genuine** (the
  structure is non-vacuous — `df` of a nonconstant `f` witnesses it — and at `D = 0` both sides of
  the iso have dimension `kirovGenus X`, so the iso is non-vacuous, not a junk identity).

  Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4 (`ω·: 𝒪_{D+K} ≅ Ω_D`); the
  `linearSystem`/`lSysModule`/`lDim` pattern in `Jacobians.LinearSystem`; the `Ω_D` Gate-C build in
  `Jacobians.Dolbeault.MeromorphicOneFormSystem`.
-/
import KirovDolbeault.Dolbeault.MeromorphicOneFormSystem

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.Dolbeault

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The **junk-free linear-system module** `L(D)` (= `H⁰(X, 𝒪_D)`): the linear system with the
`toFun`-germ junk quotiented out, `lDim D = finrank ℂ (lSysModule D)`. (A local copy of the
abbreviation in `SerreDualityPairing`, so this §17.4 layer stays independent of the downstream
`exists_serreDualityData`.) -/
abbrev lSysModule (D : Divisor X) : Type _ :=
  ↥(linearSystem (X := X) D) ⧸ (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) D)

/-! ## Part 1: the form identity theorem (`ω₀ ≠ 0` ⟹ `formOrderW ω₀ ≠ ⊤` everywhere)

The order of a meromorphic 1-form vanishes (`= ⊤`) at `x` exactly when the *section* `α.toFun`
vanishes on a punctured neighbourhood of `x` — an **intrinsic** statement (no chart-coefficient
change-of-variables needed): the chart coefficient `formCoeff α.toFun x` reads `α.toFun y` against
the spanning tangent vector `symmL 1`, so the coefficient vanishes near `chart x x` iff the covector
`α.toFun y` vanishes near `x`.  This makes `{x | formOrderW α x = ⊤}` clopen on the connected `X`
(mirror of `MeromorphicFunction.orderW_ne_top_of_exists`), giving the identity theorem. -/

namespace MeromorphicOneForm

/-- A covector in the (1-dim) cotangent fibre that kills the spanning tangent vector `symmL 1`
of the trivialization at `x` is the zero covector — because every tangent vector is a scalar
multiple of `symmL 1` (mirror of the argument in `FormCoeff.exists_localRep_self_ne_zero`). -/
theorem toFun_eq_zero_of_formCoeff_zero (α : MeromorphicOneForm X) {x y : X}
    (hy : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).baseSet)
    (h : α.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1) = 0) :
    α.toFun y = 0 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.zero_apply]
  have hv : e.symmL ℂ y (e.continuousLinearMapAt ℂ y v) = v :=
    e.symmL_continuousLinearMapAt hy v
  set c := e.continuousLinearMapAt ℂ y v with hc
  have hsm : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
    have h2 := (e.symmL ℂ y).map_smul c (1 : ℂ)
    rwa [smul_eq_mul, mul_one] at h2
  calc α.toFun y v = α.toFun y (e.symmL ℂ y c) := by rw [hv]
    _ = α.toFun y (c • e.symmL ℂ y 1) := by rw [hsm]
    _ = c • α.toFun y (e.symmL ℂ y 1) := by rw [(α.toFun y).map_smul]
    _ = 0 := by rw [h, smul_zero]

/-- **Intrinsic vanishing characterization.** `formOrderW α x = ⊤` (the form's germ vanishes at `x`)
iff the *section* `α.toFun` vanishes on a punctured neighbourhood of `x`.  No chart-coefficient
change-of-variables — the chart coefficient is `α.toFun` paired with the spanning tangent vector. -/
theorem formOrderW_eq_top_iff (α : MeromorphicOneForm X) (x : X) :
    α.formOrderW x = ⊤ ↔ ∀ᶠ y in 𝓝[≠] x, α.toFun y = 0 := by
  rw [formOrderW, meromorphicOrderAt_eq_top_iff]
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  have hbase : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ _ x)
  -- The chart coefficient is the intrinsic "covector against the spanning tangent vector",
  -- read in the chart at `x`: `formCoeff = (fun y => α y (symmL y 1)) ∘ chart.symm`.
  have hcoeff : formCoeff α.toFun x = (fun y => α.toFun y (e.symmL ℂ y 1)) ∘ (chartAt ℂ x).symm := rfl
  rw [hcoeff, MeromorphicFunction.eventually_comp_chart_iff
    (fun y => α.toFun y (e.symmL ℂ y 1)) x (· = 0)]
  constructor
  · -- covector kills `symmL 1` near `x` ⟹ covector is `0` near `x` (on the base set).
    intro h
    filter_upwards [h, nhdsWithin_le_nhds hbase] with y hy hybase
    exact α.toFun_eq_zero_of_formCoeff_zero hybase hy
  · -- section vanishes ⟹ its pairing with `symmL 1` vanishes.
    intro h
    filter_upwards [h] with y hy
    rw [hy, ContinuousLinearMap.zero_apply]

/-- `formOrderW α x ≠ ⊤` (the form's germ is nonzero) iff the section `α.toFun` is eventually
nonzero on a punctured neighbourhood of `x`. -/
theorem formOrderW_ne_top_iff (α : MeromorphicOneForm X) (x : X) :
    α.formOrderW x ≠ ⊤ ↔ ∀ᶠ y in 𝓝[≠] x, α.toFun y ≠ 0 := by
  rw [formOrderW, meromorphicOrderAt_ne_top_iff_eventually_ne_zero (α.meromorphic x)]
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  have hbase : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ _ x)
  have hcoeff : formCoeff α.toFun x = (fun y => α.toFun y (e.symmL ℂ y 1)) ∘ (chartAt ℂ x).symm := rfl
  rw [hcoeff, MeromorphicFunction.eventually_comp_chart_iff
    (fun y => α.toFun y (e.symmL ℂ y 1)) x (· ≠ 0)]
  constructor
  · intro h
    filter_upwards [h] with y hy
    intro hzero; exact hy (by rw [hzero, ContinuousLinearMap.zero_apply])
  · intro h
    filter_upwards [h, nhdsWithin_le_nhds hbase] with y hy hybase
    intro hpair; exact hy (α.toFun_eq_zero_of_formCoeff_zero hybase hpair)

/-- **Form identity theorem.** If the germ of `α` is nonzero (`formOrderW ≠ ⊤`) at even one point,
it is nonzero at *every* point.  The set `{x | formOrderW α x = ⊤}` and its complement are both open
(via the two intrinsic characterizations above), so on the connected `X` it is empty.  Mirror of
`MeromorphicFunction.orderW_ne_top_of_exists`. -/
theorem formOrderW_ne_top_of_exists (α : MeromorphicOneForm X)
    (h₀ : ∃ x₀, α.formOrderW x₀ ≠ ⊤) (x : X) : α.formOrderW x ≠ ⊤ := by
  obtain ⟨x₀, hx₀⟩ := h₀
  have hUopen : IsOpen {y : X | α.formOrderW y = ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [Set.mem_setOf_eq, formOrderW_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hy
    obtain ⟨V, hV, hVopen, hyV⟩ := hy
    refine Filter.mem_of_superset (hVopen.mem_nhds hyV) fun y' hy'V => ?_
    rw [Set.mem_setOf_eq, formOrderW_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    rcases eq_or_ne y' y with rfl | hy'
    · exact ⟨V, hV, hVopen, hy'V⟩
    · exact ⟨V \ {y}, fun z hz _ => hV z hz.1 hz.2, hVopen.sdiff isClosed_singleton, ⟨hy'V, hy'⟩⟩
  have hUclosed : IsClosed {y : X | α.formOrderW y = ⊤} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    have hyne : α.formOrderW y ≠ ⊤ := hy
    rw [formOrderW_ne_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hyne
    obtain ⟨W, hW, hWopen, hyW⟩ := hyne
    refine Filter.mem_of_superset (hWopen.mem_nhds hyW) fun y' hy'W => ?_
    show α.formOrderW y' ≠ ⊤
    rw [formOrderW_ne_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    rcases eq_or_ne y' y with rfl | hy'ne
    · exact ⟨W, hW, hWopen, hy'W⟩
    · exact ⟨W \ {y}, fun z hz _ => hW z hz.1 hz.2, hWopen.sdiff isClosed_singleton, ⟨hy'W, hy'ne⟩⟩
  rcases isClopen_iff.mp ⟨hUclosed, hUopen⟩ with hU | hU
  · show x ∉ {y : X | α.formOrderW y = ⊤}
    rw [hU]; exact Set.notMem_empty x
  · exact absurd (hU.ge (Set.mem_univ x₀)) hx₀

end MeromorphicOneForm

/-! ## Part 2: the canonical form `ω₀`, its divisor `K`, and the isolated analytic input

Forster §17.4 fixes a nonzero meromorphic 1-form `ω₀` (he takes `ω₀ = df` for a nonconstant
meromorphic `f`) and sets `K := div ω₀`.  The whole §17.4 tower is *algebraic* once we have:
  * `ω₀ : MeromorphicOneForm X` with germ nonzero somewhere (`∃ x, formOrderW ω₀ x ≠ ⊤`);
  * its divisor `K : Divisor X` (the order function `(formOrderW ω₀ ·).untop₀`, which has finite
    support since `ω₀` has finitely many zeros/poles on the compact `X`), satisfying
    `formOrderW ω₀ x = (K x : WithTop ℤ)` for all `x`.

The form identity theorem (`formOrderW_ne_top_of_exists`) upgrades "germ nonzero somewhere" to
`formOrderW ω₀ x ≠ ⊤` *everywhere*, which is exactly what makes `formOrderW ω₀ = K` consistent
(`untop₀` loses nothing).  We bundle this — the construction of `ω₀ = df` and its finite-support
divisor `K = div ω₀` — into one isolated hypothesis structure; it is **non-vacuous** (witnessed by
`df` of `exists_nonconstant_meromorphic` + the 1-form analog of `MeromorphicFunction.div`). -/

/-- **[ISOLATED ANALYTIC INPUT].**  The canonical-form datum of Forster §17.4: a nonzero meromorphic
1-form `ω₀` together with its canonical divisor `K = div ω₀`.

The two fields encode `ω₀ ≠ 0` (`nontrivial`) and `K = div ω₀` (`order_eq`, i.e. the divisor's
coefficients are the form's orders).  Both are TRUE for `ω₀ = df` of a nonconstant meromorphic
function `f` (which exists by Riemann–Roch — `exists_nonconstant_meromorphic`); the finite support
of `K` is the 1-form analog of `MeromorphicFunction.div`'s local finiteness
(`Jacobians.Abel.orderAtPoint_isolated_at`).  The remaining §17.4 content built on this datum is
purely algebraic and fully proven below. -/
structure CanonicalForm17Data (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  /-- The canonical meromorphic 1-form `ω₀` (Forster's `ω₀ = df`). -/
  ω₀ : MeromorphicOneForm X
  /-- `ω₀ ≠ 0`: its germ is nonzero at some point (so, by the identity theorem, everywhere). -/
  nontrivial : ∃ x, ω₀.formOrderW x ≠ ⊤
  /-- The canonical divisor `K = div ω₀`. -/
  K : Divisor X
  /-- `K = div ω₀`: the divisor's coefficients are exactly the form's orders. -/
  order_eq : ∀ x, ω₀.formOrderW x = (K x : WithTop ℤ)

namespace CanonicalForm17Data

variable (data : CanonicalForm17Data X)

/-- `ω₀`'s germ is nonzero at **every** point (the form identity theorem applied to `nontrivial`). -/
theorem formOrderW_ω₀_ne_top (x : X) : data.ω₀.formOrderW x ≠ ⊤ :=
  MeromorphicOneForm.formOrderW_ne_top_of_exists data.ω₀ data.nontrivial x

/-- `ω₀.toFun` is eventually nonzero on a punctured neighbourhood of every point (so the covector
ratio `α/ω₀` is well-defined as a meromorphic function). -/
theorem ω₀_eventually_ne_zero (x : X) : ∀ᶠ y in 𝓝[≠] x, data.ω₀.toFun y ≠ 0 :=
  (MeromorphicOneForm.formOrderW_ne_top_iff data.ω₀ x).mp (data.formOrderW_ω₀_ne_top x)

end CanonicalForm17Data

/-! ## Part 3: the intrinsic covector ratio and the division `α/ω₀`

The cotangent fibre at `y` is 1-dimensional, so for two covectors `a, b` with `b ≠ 0`, the ratio
`a v / b v` is **independent of the test vector `v`** (as long as `b v ≠ 0`).  This makes the
function-level division `α/ω₀` intrinsic: `(α/ω₀)(y) := α y v / ω₀ y v` is chart-independent, and
its chart coefficient is `formCoeff α / formCoeff ω₀`, hence meromorphic.  This is the surjectivity
content of Forster §17.4 (`α = (α/ω₀)·ω₀`). -/

/-- **Covector ratio is test-vector-independent.**  For covectors `a b : TangentSpace 𝓘(ℂ) y →L[ℂ] ℂ`,
the trivialization `e = trivializationAt _ _ x` with `y ∈ e.baseSet`, and any `v`, the ratio
`a v / b v` equals the ratio on the frame vector `a (e.symmL 1) / b (e.symmL 1)` (the cotangent fibre
being 1-dim, every `v` is a scalar multiple of `e.symmL 1`, and the scalar cancels). -/
theorem covector_ratio_eq {x y : X} (a b : TangentSpace 𝓘(ℂ) (M := X) y →L[ℂ] ℂ)
    (hy : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).baseSet)
    (v : TangentSpace 𝓘(ℂ) (M := X) y) (hbv0 : b v ≠ 0) :
    a v / b v = a ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1)
      / b ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1) := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  set c := e.continuousLinearMapAt ℂ y v with hc
  have hv : e.symmL ℂ y c = v := e.symmL_continuousLinearMapAt hy v
  have hsm : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
    have h2 := (e.symmL ℂ y).map_smul c (1 : ℂ); rwa [smul_eq_mul, mul_one] at h2
  have hav : a v = c • a (e.symmL ℂ y 1) := by
    rw [← hv, hsm, (a).map_smul]
  have hbv : b v = c • b (e.symmL ℂ y 1) := by
    rw [← hv, hsm, (b).map_smul]
  have hc0 : c ≠ 0 := by
    intro h; apply hbv0; rw [hbv, h, zero_smul]
  rw [hav, hbv, smul_eq_mul, smul_eq_mul, mul_div_mul_left _ _ hc0]

/-- A nonzero covector on the (1-dim) cotangent fibre is nonzero on the frame vector `symmL 1`
(contrapositive of `MeromorphicOneForm.toFun_eq_zero_of_formCoeff_zero`). -/
theorem apply_symmL_ne_zero_of_ne_zero {x y : X}
    (a : TangentSpace 𝓘(ℂ) (M := X) y →L[ℂ] ℂ) (ha : a ≠ 0)
    (hy : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).baseSet) :
    a ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1) ≠ 0 := by
  intro h
  apply ha
  -- the covector kills the frame vector, hence (1-dim) it is zero
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.zero_apply]
  set c := e.continuousLinearMapAt ℂ y v with hc
  have hv : e.symmL ℂ y c = v := e.symmL_continuousLinearMapAt hy v
  have hsm : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
    have h2 := (e.symmL ℂ y).map_smul c (1 : ℂ); rwa [smul_eq_mul, mul_one] at h2
  calc a v = a (e.symmL ℂ y c) := by rw [hv]
    _ = a (c • e.symmL ℂ y 1) := by rw [hsm]
    _ = c • a (e.symmL ℂ y 1) := by rw [a.map_smul]
    _ = 0 := by rw [h, smul_zero]

namespace CanonicalForm17Data

variable (data : CanonicalForm17Data X)

/-- **The division `α/ω₀` as a meromorphic function.**  Pointwise the intrinsic covector ratio
`(α/ω₀)(y) := α y v / ω₀ y v` (test vector `v = symmL 1` in `y`'s own trivialization).  It is
chart-independent (`covector_ratio_eq`), with chart coefficient `formCoeff α / formCoeff ω₀`, hence
meromorphic.  This is the surjectivity witness of Forster §17.4: `α = (α/ω₀)·ω₀`. -/
noncomputable def meroFormDiv (α : MeromorphicOneForm X) : MeromorphicFunction X where
  toFun y := α.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ y 1)
    / data.ω₀.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ y 1)
  meromorphic := by
    intro x
    -- The chart pullback agrees, on a punctured neighbourhood of `chart x x`, with
    -- `formCoeff α x / formCoeff ω₀ x` (covector-ratio independence), which is meromorphic.
    have hquot : MeromorphicAt (formCoeff α.toFun x / formCoeff data.ω₀.toFun x) ((chartAt ℂ x) x) :=
      (α.meromorphic x).div (data.ω₀.meromorphic x)
    refine hquot.congr ?_
    -- Goal: `(formCoeff α x / formCoeff ω₀ x) =ᶠ[𝓝[≠] (chart x x)] (div ∘ chart.symm)`.
    -- Pull `ω₀.toFun ≠ 0 near x` to the ℂ-side, plus chart-target membership.
    have htarget : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
      (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    -- ℂ-side nonvanishing of ω₀: `ω₀.toFun (chart.symm z) ≠ 0` near `chart x x` (punctured).
    have hneC : ∀ᶠ z in 𝓝[≠] ((chartAt ℂ x) x),
        data.ω₀.toFun ((chartAt ℂ x).symm z) ≠ 0 := by
      -- transfer `ω₀.toFun ≠ 0 near x (punctured)` via continuity of `chart.symm`.
      have hyt : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).map_source (mem_chart_source ℂ x)
      have hey : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
      have hsymm : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
        (chartAt ℂ x).continuousAt_symm hyt
      have hev0 : ∀ᶠ w in 𝓝 x, w ∈ ({x} : Set X)ᶜ → data.ω₀.toFun w ≠ 0 := by
        rw [← eventually_nhdsWithin_iff]; exact data.ω₀_eventually_ne_zero x
      have h2 := hsymm.eventually (p := fun w => w ∈ ({x} : Set X)ᶜ → data.ω₀.toFun w ≠ 0)
        (by rw [hey]; exact hev0)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [h2, (chartAt ℂ x).open_target.mem_nhds hyt] with w hw hw_tgt hw_mem
      apply hw
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      apply hw_mem
      have hr := (chartAt ℂ x).right_inv hw_tgt
      rw [heq] at hr; rw [Set.mem_singleton_iff]; exact hr.symm
    filter_upwards [hneC, nhdsWithin_le_nhds htarget] with z hz hztgt
    set y := (chartAt ℂ x).symm z with hy
    have hysrc : y ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hztgt
    have hybase : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hysrc
    -- LHS: `(formCoeff α x / formCoeff ω₀ x) z`; rewrite `chart.symm z = y` and `chart y = ...`.
    show formCoeff α.toFun x z / formCoeff data.ω₀.toFun x z =
      α.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ y 1)
        / data.ω₀.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ y 1)
    have hω0 : data.ω₀.toFun y ≠ 0 := hz
    simp only [formCoeff]
    exact (covector_ratio_eq (x := x) (α.toFun y) (data.ω₀.toFun y) hybase
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ y 1)
      (apply_symmL_ne_zero_of_ne_zero (x := y) (data.ω₀.toFun y) hω0
        (mem_baseSet_trivializationAt ℂ _ y))).symm

/-- The chart pullback of `α/ω₀` agrees, on a punctured neighbourhood of `chart x x`, with the
quotient `formCoeff α x / formCoeff ω₀ x` (the covector-ratio identity of the `meromorphic` field,
extracted for reuse in the order computation). -/
theorem meroFormDiv_comp_chart_eq (α : MeromorphicOneForm X) (x : X) :
    (data.meroFormDiv α).toFun ∘ (chartAt ℂ x).symm
      =ᶠ[𝓝[≠] ((chartAt ℂ x) x)] formCoeff α.toFun x / formCoeff data.ω₀.toFun x := by
  -- this is the (symmetrised) `EventuallyEq` proven inside `meroFormDiv.meromorphic`.
  have htarget : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have hneC : ∀ᶠ z in 𝓝[≠] ((chartAt ℂ x) x),
      data.ω₀.toFun ((chartAt ℂ x).symm z) ≠ 0 := by
    have hyt : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have hey : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have hsymm : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
      (chartAt ℂ x).continuousAt_symm hyt
    have hev0 : ∀ᶠ w in 𝓝 x, w ∈ ({x} : Set X)ᶜ → data.ω₀.toFun w ≠ 0 := by
      rw [← eventually_nhdsWithin_iff]; exact data.ω₀_eventually_ne_zero x
    have h2 := hsymm.eventually (p := fun w => w ∈ ({x} : Set X)ᶜ → data.ω₀.toFun w ≠ 0)
      (by rw [hey]; exact hev0)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [h2, (chartAt ℂ x).open_target.mem_nhds hyt] with w hw hw_tgt hw_mem
    apply hw
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    apply hw_mem
    have hr := (chartAt ℂ x).right_inv hw_tgt
    rw [heq] at hr; rw [Set.mem_singleton_iff]; exact hr.symm
  filter_upwards [hneC, nhdsWithin_le_nhds htarget] with z hz hztgt
  set y := (chartAt ℂ x).symm z with hy
  have hysrc : y ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hztgt
  have hybase : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hysrc
  show (data.meroFormDiv α).toFun y = formCoeff α.toFun x z / formCoeff data.ω₀.toFun x z
  show α.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ y 1)
      / data.ω₀.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ y 1)
      = formCoeff α.toFun x z / formCoeff data.ω₀.toFun x z
  simp only [formCoeff]
  exact covector_ratio_eq (x := x) (α.toFun y) (data.ω₀.toFun y) hybase
    ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y).symmL ℂ y 1)
    (apply_symmL_ne_zero_of_ne_zero (x := y) (data.ω₀.toFun y) hz
      (mem_baseSet_trivializationAt ℂ _ y))

/-- **Order subtractivity of `α/ω₀`** (Forster §17.4 bookkeeping): `orderW (α/ω₀) x = formOrderW α x
− formOrderW ω₀ x = formOrderW α x − (K x)`.  From `meroFormDiv_comp_chart_eq` + `meromorphicOrderAt_div`
+ `order_eq`. -/
theorem meroFormDiv_orderW (α : MeromorphicOneForm X) (x : X) :
    (data.meroFormDiv α).orderW x = α.formOrderW x - (data.K x : WithTop ℤ) := by
  rw [MeromorphicFunction.orderW, meromorphicOrderAt_congr (data.meroFormDiv_comp_chart_eq α x)]
  rw [show (formCoeff α.toFun x / formCoeff data.ω₀.toFun x)
      = (formCoeff α.toFun x) / (formCoeff data.ω₀.toFun x) from rfl,
    meromorphicOrderAt_div (α.meromorphic x) (data.ω₀.meromorphic x)]
  rw [show meromorphicOrderAt (formCoeff α.toFun x) ((chartAt ℂ x) x) = α.formOrderW x from rfl,
    show meromorphicOrderAt (formCoeff data.ω₀.toFun x) ((chartAt ℂ x) x) = data.ω₀.formOrderW x from rfl,
    data.order_eq x]

/-! ### `(α/ω₀)·ω₀ = α` modulo germ-junk, and the `meroFormSMul ω₀` order law -/

/-- **Covector extensionality on the frame vector.**  Two covectors on the (1-dim) cotangent fibre
at `y` are equal iff they agree on the spanning frame vector `symmL 1` of any trivialization. -/
theorem covector_ext_symmL {x y : X} (a b : TangentSpace 𝓘(ℂ) (M := X) y →L[ℂ] ℂ)
    (hy : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).baseSet)
    (h : a ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1)
       = b ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1)) :
    a = b := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  refine ContinuousLinearMap.ext fun v => ?_
  set c := e.continuousLinearMapAt ℂ y v with hc
  have hvexp : v = c • e.symmL ℂ y 1 := by
    have h1 : e.symmL ℂ y c = v := e.symmL_continuousLinearMapAt hy v
    have h2 : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
      have := (e.symmL ℂ y).map_smul c (1 : ℂ); rwa [smul_eq_mul, mul_one] at this
    rw [← h1, h2]
  rw [hvexp, a.map_smul, b.map_smul, h]

/-- **The reconstruction identity** `(α/ω₀)·ω₀ = α` where `ω₀ ≠ 0`.  At a point `y` with
`ω₀.toFun y ≠ 0`, the covector `α.toFun y` is the scalar `(α/ω₀)(y)` times `ω₀.toFun y` (covectors
are proportional on the 1-dim fibre), so `meroFormSMul (α/ω₀) ω₀` agrees with `α` there. -/
theorem meroFormSMul_meroFormDiv_apply (α : MeromorphicOneForm X) {y : X}
    (hy : data.ω₀.toFun y ≠ 0) :
    (meroFormSMul (data.meroFormDiv α) data.ω₀).toFun y = α.toFun y := by
  rw [meroFormSMul_toFun]
  show (data.meroFormDiv α).toFun y • data.ω₀.toFun y = α.toFun y
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) y with he
  have hbase : y ∈ e.baseSet := mem_baseSet_trivializationAt ℂ _ y
  have hω0v : data.ω₀.toFun y (e.symmL ℂ y 1) ≠ 0 :=
    apply_symmL_ne_zero_of_ne_zero (x := y) (data.ω₀.toFun y) hy hbase
  -- it suffices that both covectors agree on the frame vector `e.symmL y 1`.
  refine covector_ext_symmL (x := y) _ _ hbase ?_
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  show (data.meroFormDiv α).toFun y * data.ω₀.toFun y (e.symmL ℂ y 1) = α.toFun y (e.symmL ℂ y 1)
  show (α.toFun y (e.symmL ℂ y 1) / data.ω₀.toFun y (e.symmL ℂ y 1)) * data.ω₀.toFun y (e.symmL ℂ y 1)
      = α.toFun y (e.symmL ℂ y 1)
  field_simp

/-- **`(α/ω₀)·ω₀` and `α` have the same class** in `omegaDModule D`: their difference is germ-zero
everywhere (they agree on a punctured neighbourhood of every point, where `ω₀ ≠ 0`). -/
theorem formOrderW_meroFormSMul_meroFormDiv_sub_top (α : MeromorphicOneForm X) (x : X) :
    (meroFormSMul (data.meroFormDiv α) data.ω₀ - α).formOrderW x = ⊤ := by
  rw [MeromorphicOneForm.formOrderW_eq_top_iff]
  filter_upwards [data.ω₀_eventually_ne_zero x] with y hy
  show (meroFormSMul (data.meroFormDiv α) data.ω₀).toFun y - α.toFun y = 0
  rw [data.meroFormSMul_meroFormDiv_apply α hy, sub_self]

/-- **Order law for `meroFormSMul · ω₀`** (Forster §17.4): `formOrderW (f·ω₀) x = orderW f x + (K x)`
(order additivity `formOrderW_meroFormSMul` + `K = div ω₀`). -/
theorem formOrderW_meroFormSMul_ω₀ (f : MeromorphicFunction X) (x : X) :
    (meroFormSMul f data.ω₀).formOrderW x = f.orderW x + (data.K x : WithTop ℤ) := by
  rw [formOrderW_meroFormSMul, data.order_eq x]

/-! ## Part 4: Forster §17.4 — `ω₀· : 𝒪_{D+K} ≅ Ω_D`

The multiplication map `f ↦ f·ω₀` is, for each `D`, an isomorphism `lSysModule (D + K) ≃ omegaDModule D`.
Well-defined (`L(D+K)·ω₀ ⊆ Ω_D`, order law), injective (kernel = germ-junk), surjective (division). -/

/-- **`L(D+K)·ω₀ ⊆ Ω_D`** (Forster §17.4 well-definedness): if `f ∈ L(D+K)` then `f·ω₀ ∈ Ω_D`.
Orders add: `formOrderW (f·ω₀) = orderW f + K ≥ −(D+K) + K = −D`. -/
theorem meroFormSMul_ω₀_mem_omegaD {D : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (D + data.K)) :
    meroFormSMul f data.ω₀ ∈ omegaD (X := X) D := by
  intro x
  rw [data.formOrderW_meroFormSMul_ω₀ f x]
  have h1 : (-((D + data.K) x) : WithTop ℤ) ≤ f.orderW x := hf x
  have heq : (-((D + data.K) x) : WithTop ℤ) = (-(D x) : WithTop ℤ) + (-(data.K x) : WithTop ℤ) := by
    rw [Finsupp.add_apply]; norm_cast; ring
  rw [heq] at h1
  -- `−D + (−K) ≤ orderW f` ⟹ `−D ≤ orderW f + K` (add `K` to both sides, cancel).
  have hstep : (-(D x) + -(data.K x) : WithTop ℤ) + (data.K x : WithTop ℤ)
      ≤ f.orderW x + (data.K x : WithTop ℤ) := by gcongr
  calc (-(D x) : WithTop ℤ) = (-(D x) + -(data.K x) : WithTop ℤ) + (data.K x : WithTop ℤ) := by
            norm_cast; ring
        _ ≤ f.orderW x + (data.K x : WithTop ℤ) := hstep

/-- The multiplication-by-`ω₀` linear map `MeromorphicFunction X →ₗ[ℂ] MeromorphicOneForm X`,
`f ↦ f·ω₀` (the §17.4 structure map at the section level). -/
noncomputable def meroFormSMulω₀ₗ : MeromorphicFunction X →ₗ[ℂ] MeromorphicOneForm X where
  toFun f := meroFormSMul f data.ω₀
  map_add' f g := by
    refine MeromorphicOneForm.ext ?_
    funext y
    show (f.toFun y + g.toFun y) • data.ω₀.toFun y
      = f.toFun y • data.ω₀.toFun y + g.toFun y • data.ω₀.toFun y
    module
  map_smul' c f := by
    refine MeromorphicOneForm.ext ?_
    funext y
    show (c * f.toFun y) • data.ω₀.toFun y = c • (f.toFun y • data.ω₀.toFun y)
    module

@[simp] theorem meroFormSMulω₀ₗ_apply (f : MeromorphicFunction X) :
    data.meroFormSMulω₀ₗ f = meroFormSMul f data.ω₀ := rfl

/-- **The §17.4 map on representatives** `L(D+K) → omegaDModule D`, `f ↦ [f·ω₀]` (multiply by `ω₀`,
land in `Ω_D` by `meroFormSMul_ω₀_mem_omegaD`, project to the junk-free quotient).  ℂ-linear. -/
noncomputable def omega17Map (D : Divisor X) :
    ↥(linearSystem (X := X) (D + data.K)) →ₗ[ℂ] omegaDModule (X := X) D where
  toFun f := Submodule.Quotient.mk ⟨meroFormSMul f.1 data.ω₀, data.meroFormSMul_ω₀_mem_omegaD f.2⟩
  map_add' f g := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    refine Subtype.ext (MeromorphicOneForm.ext ?_)
    funext y
    show (f.1 + g.1).toFun y • data.ω₀.toFun y
      = f.1.toFun y • data.ω₀.toFun y + g.1.toFun y • data.ω₀.toFun y
    show (f.1.toFun y + g.1.toFun y) • data.ω₀.toFun y
      = f.1.toFun y • data.ω₀.toFun y + g.1.toFun y • data.ω₀.toFun y
    module
  map_smul' c f := by
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    refine Subtype.ext (MeromorphicOneForm.ext ?_)
    funext y
    show (c • f.1).toFun y • data.ω₀.toFun y = c • (f.1.toFun y • data.ω₀.toFun y)
    show (c * f.1.toFun y) • data.ω₀.toFun y = c • (f.1.toFun y • data.ω₀.toFun y)
    module

@[simp] theorem omega17Map_mk (D : Divisor X) (f : ↥(linearSystem (X := X) (D + data.K))) :
    data.omega17Map D f =
      Submodule.Quotient.mk ⟨meroFormSMul f.1 data.ω₀, data.meroFormSMul_ω₀_mem_omegaD f.2⟩ := rfl

/-- **`f·ω₀` is germ-zero iff `f` is germ-zero** (multiplication by `ω₀ ≠ 0` preserves and reflects
the germ-junk): `formOrderW (f·ω₀) x = orderW f x + K x`, and `K x ≠ ⊤`, so `= ⊤ ↔ orderW f x = ⊤`. -/
theorem meroFormSMul_ω₀_formGermZero_iff (f : MeromorphicFunction X) :
    meroFormSMul f data.ω₀ ∈ formGermZeroSubmodule (X := X) ↔ f ∈ germZeroSubmodule (X := X) := by
  constructor
  · intro h x
    have hx : (meroFormSMul f data.ω₀).formOrderW x = ⊤ := h x
    rw [data.formOrderW_meroFormSMul_ω₀ f x] at hx
    -- `orderW f x + (K x) = ⊤` with `K x ≠ ⊤` forces `orderW f x = ⊤`.
    by_contra hne
    rw [WithTop.add_eq_top] at hx
    rcases hx with h1 | h2
    · exact hne h1
    · exact (WithTop.coe_ne_top : ((data.K x : ℤ) : WithTop ℤ) ≠ ⊤) h2
  · intro h x
    have hx : f.orderW x = ⊤ := h x
    rw [data.formOrderW_meroFormSMul_ω₀ f x, hx, top_add]

/-- **The §17.4 map has kernel exactly the germ-junk.**  `ker (omega17Map D) = germZeroSubmodule.submoduleOf`.
(`[f·ω₀] = 0 ↔ f·ω₀` germ-zero `↔ f` germ-zero, by `meroFormSMul_ω₀_formGermZero_iff`.) -/
theorem ker_omega17Map (D : Divisor X) :
    LinearMap.ker (data.omega17Map D)
      = (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) (D + data.K)) := by
  ext f
  rw [LinearMap.mem_ker, omega17Map_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.submoduleOf, Submodule.mem_comap, Submodule.submoduleOf, Submodule.mem_comap]
  -- LHS: `⟨f·ω₀, _⟩ ∈ formGermZeroSubmodule.submoduleOf (omegaD D)` i.e. `f·ω₀ ∈ formGermZeroSubmodule`.
  -- RHS: `f.1 ∈ germZeroSubmodule`.
  exact data.meroFormSMul_ω₀_formGermZero_iff f.1

/-- **`α/ω₀ ∈ L(D+K)`** for `α ∈ Ω_D` (the surjectivity preimage of §17.4): orders subtract,
`orderW (α/ω₀) x = formOrderW α x − K x ≥ −D − K = −(D+K)`. -/
theorem meroFormDiv_mem_linearSystem {D : Divisor X} {α : MeromorphicOneForm X}
    (hα : α ∈ omegaD (X := X) D) :
    data.meroFormDiv α ∈ linearSystem (X := X) (D + data.K) := by
  intro x
  rw [data.meroFormDiv_orderW α x, sub_eq_add_neg]
  have h1 : (-(D x) : WithTop ℤ) ≤ α.formOrderW x := hα x
  -- `−(D+K) = −D + (−K) ≤ formOrderW α + (−K)`.
  have heq : (-((D + data.K) x) : WithTop ℤ) = (-(D x) : WithTop ℤ) + (-(data.K x) : WithTop ℤ) := by
    rw [Finsupp.add_apply]; norm_cast; ring
  rw [heq]
  -- add `−K x` to both sides of `−D ≤ formOrderW α`.
  gcongr

/-- **Forster §17.4 surjectivity.**  `omega17Map D` is surjective: every class `[α] ∈ omegaDModule D`
is the image of `[α/ω₀]` (with `α/ω₀ ∈ L(D+K)`), since `(α/ω₀)·ω₀` and `α` have the same class. -/
theorem omega17Map_surjective (D : Divisor X) : Function.Surjective (data.omega17Map D) := by
  intro q
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨⟨data.meroFormDiv α.1, data.meroFormDiv_mem_linearSystem α.2⟩, ?_⟩
  rw [omega17Map_mk]
  -- `[ (α/ω₀)·ω₀ ] = [α]`: difference germ-zero everywhere.
  rw [Submodule.Quotient.eq, Submodule.submoduleOf, Submodule.mem_comap]
  intro x
  exact data.formOrderW_meroFormSMul_meroFormDiv_sub_top α.1 x

/-! ### The descended §17.4 map on the junk-free modules, and the isomorphism -/

/-- **The §17.4 map descended to `lSysModule (D+K)`** (the junk-free domain), via `liftQ` using
`germZero.submoduleOf ≤ ker (omega17Map D)` (in fact equality, `ker_omega17Map`). -/
noncomputable def omega17 (D : Divisor X) :
    lSysModule (X := X) (D + data.K) →ₗ[ℂ] omegaDModule (X := X) D :=
  Submodule.liftQ _ (data.omega17Map D) (le_of_eq (data.ker_omega17Map D).symm)

@[simp] theorem omega17_mk (D : Divisor X) (f : ↥(linearSystem (X := X) (D + data.K))) :
    data.omega17 D (Submodule.Quotient.mk f) = data.omega17Map D f :=
  Submodule.liftQ_apply _ _ _

/-- **`omega17 D` is injective** (Forster §17.4 injectivity): its kernel is `⊥` because
`ker (omega17Map D) = germZeroSubmodule.submoduleOf` (the submodule we quotient by). -/
theorem omega17_injective (D : Divisor X) : Function.Injective (data.omega17 D) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot' _ _ (data.ker_omega17Map D).symm

/-- **`omega17 D` is surjective** (Forster §17.4 surjectivity), lifted from `omega17Map_surjective`. -/
theorem omega17_surjective (D : Divisor X) : Function.Surjective (data.omega17 D) := by
  intro q
  obtain ⟨f, hf⟩ := data.omega17Map_surjective D q
  exact ⟨Submodule.Quotient.mk f, by rw [omega17_mk]; exact hf⟩

/-- **Forster §17.4 — `ω₀· : 𝒪_{D+K} ≅ Ω_D`.**  The multiplication-by-`ω₀` isomorphism
`lSysModule (D + K) ≃ₗ[ℂ] omegaDModule D` for every divisor `D`.  Injective (mult by `ω₀ ≠ 0`,
kernel = germ-junk) and surjective (the division `α/ω₀`). -/
noncomputable def omega17Equiv (D : Divisor X) :
    lSysModule (X := X) (D + data.K) ≃ₗ[ℂ] omegaDModule (X := X) D :=
  LinearEquiv.ofBijective (data.omega17 D) ⟨data.omega17_injective D, data.omega17_surjective D⟩

/-- **Forster §17.4 as a dimension equality**: `lDim (D + K) = omegaDim D` (the iso `𝒪_{D+K} ≅ Ω_D`
preserves finrank). -/
theorem lDim_add_K_eq_omegaDim (D : Divisor X) :
    lDim (X := X) (D + data.K) = omegaDim (X := X) D := by
  have h := (data.omega17Equiv D).finrank_eq
  rwa [show lDim (X := X) (D + data.K) = finrank ℂ (lSysModule (X := X) (D + data.K)) from rfl,
    show omegaDim (X := X) D = finrank ℂ (omegaDModule (X := X) D) from rfl]

/-! ## Part 5: `lDim K = kirovGenus X` (Forster §17.4 at `D = 0`)

At `D = 0` the §17.4 iso is `𝒪_K ≅ Ω_0`, giving `lDim K = omegaDim 0` **unconditionally** (no gaps).
Composing with Gate C's `Ω_0 ≅ HolomorphicOneForms` (`omegaDim_zero_eq_genus_of_le`) gives
`lDim K = kirovGenus X` — the `hKgenus` field of `SerreDualityData`.  The remaining input is exactly Gate
C's isolated removable-singularity reverse bound `omegaDim 0 ≤ kirovGenus X` (an order-`≥ 0` meromorphic
1-form is, modulo germ-junk, holomorphic). -/

/-- **`lDim K = omegaDim 0`** (Forster §17.4 at `D = 0`, the iso `𝒪_K ≅ Ω_0`) — UNCONDITIONAL.
A direct corollary of `lDim_add_K_eq_omegaDim` at `D = 0` (`0 + K = K`). -/
theorem lDim_K_eq_omegaDim_zero : lDim (X := X) data.K = omegaDim (X := X) 0 := by
  have h := data.lDim_add_K_eq_omegaDim 0
  rwa [zero_add] at h

/-- **`hKgenus` — `lDim K = kirovGenus X`** (Forster §17.4 at `D = 0`).  Chains the unconditional
`lDim K = omegaDim 0` with `omegaDim 0 = kirovGenus X` (Gate C's `omegaDim_zero_eq_genus_of_le`).  The two
hypotheses are exactly Gate C's isolated removable-singularity inputs: finiteness of `Ω_0` and the
reverse bound `omegaDim 0 ≤ kirovGenus X` (an order-`≥ 0` meromorphic 1-form is holomorphic modulo
germ-junk).  This is the `SerreDualityData.hKgenus` field. -/
theorem hKgenus [FiniteDimensional ℂ (omegaDModule (X := X) 0)]
    (hle : omegaDim (X := X) 0 ≤ kirovGenus X) :
    lDim (X := X) data.K = kirovGenus X := by
  rw [data.lDim_K_eq_omegaDim_zero]
  exact omegaDim_zero_eq_genus_of_le hle

/-! ### Non-vacuity / soundness sanity check

The §17.4 iso is genuine (not a junk dimension-identity): the kirovGenus-dimensional holomorphic forms
inject into `Ω_0 ≅ 𝒪_K`, so `kirovGenus X ≤ lDim K`.  In particular, for a positive-kirovGenus surface both
sides of the `D = 0` iso have dimension `≥ kirovGenus ≥ 1`, so it is a non-vacuous isomorphism of nonzero
modules. -/

/-- **Soundness lower bound:** `kirovGenus X ≤ lDim K` (when `Ω_0` is finite-dimensional).  The §17.4 iso
sends the kirovGenus-dimensional holomorphic forms faithfully into `𝒪_K`, so `lSysModule K` is at least
kirovGenus-dimensional — the iso is non-vacuous. -/
theorem genus_le_lDim_K [FiniteDimensional ℂ (omegaDModule (X := X) 0)] :
    kirovGenus X ≤ lDim (X := X) data.K := by
  rw [data.lDim_K_eq_omegaDim_zero]
  exact genus_le_omegaDim_zero

end CanonicalForm17Data

end Jacobians.Dolbeault
