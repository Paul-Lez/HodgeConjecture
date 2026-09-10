/-
  The **L3 kernel** — Dolbeault's comparison theorem `H^{0,1}(X) ≅ H¹(X, 𝒪)`, the single hardest
  analytic input of the `D = 0` Serre route (`arithmeticGenus_eq_genus`).

  Target (proven standalone as `cechH1_dolbeault_comparison_proof`; the `IsLeray`-free form is
  `GoodCover.cechH1_dolbeault_comparison'`):

    `cechH1_dolbeault_comparison_proof (𝔘 : FiniteCover X) :`
    `    finrank ℝ (DolbeaultH01 X) = 2 * finrank ℂ (𝔘.cechH1 0)`

  the `ℝ`-vs-`ℂ` dimension count of Dolbeault's iso (`H^{0,1}` is `Module ℝ` of real-dim `2g`;
  `cechH1` is `Module ℂ` of complex-dim `g`).

  MATH (Dolbeault's theorem). Two mutually-inverse maps:
  * **Dolbeault → Čech.** A smooth `(0,1)`-form `g`: on each chart-disk `U_i` solve `∂̄u_i = g`
    *locally* (`DbarLocal.dbar_solvable_locally`, DONE). Then `∂̄(u_i − u_j) = g − g = 0` on
    `U_i ∩ U_j`, so `{u_i − u_j}` is a holomorphic Čech `1`-cocycle; its class lands in `cechH1`.
  * **Čech → Dolbeault.** A holomorphic cocycle `{f_ij}`: with a partition of unity `{ρ_k}`
    subordinate to the cover, set `h_i := ∑_k ρ_k f_ik`; then `f_ij = h_j − h_i` (smooth) and
    `∂̄h_i = ∂̄h_j` on overlaps (`f_ij` holomorphic) glue to a global `(0,1)`-form; its class.

  These are mutually inverse, giving a linear iso and hence the `finrank` relation.

  HONESTY. This file builds the connective tissue with no gaps and isolates each genuinely-hard
  analytic sub-kernel as a *named honest obligation with a TRUE statement*. We never weaken the target.

  SPLIT. This file holds the **forward direction** (`dolbeault_to_cech`, now fully proven) and the
  shared analytic infrastructure (chart bridge, Wirtinger chain rule, cutoff/planar primitives, the
  forward cocycle operator). The **inverse direction** (`cech_to_dolbeault`), the assembled
  `ℝ`-linear equivalence `comparison_linearEquiv`, the target `cechH1_dolbeault_comparison_proof`, and
  the closing honest-status summary live in `Jacobians.Dolbeault.DolbeaultComparisonInverse`.
-/
import KirovDolbeault.Dolbeault.DolbeaultComparison
import KirovDolbeault.Dolbeault.DbarLocal
import KirovDolbeault.Dolbeault.ChartDiskCover
import KirovDolbeault.Dolbeault.CechH0
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.BumpFunction

open scoped Manifold ContDiff Bundle Topology
open TopologicalSpace (Opens)

-- Same permissive transparency as `RealForms`/`DolbeaultH01`/`DolbeaultComparison` (the section
-- hom-bundle instances need it).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The two comparison maps and their assembly into an `ℝ`-linear equivalence

Dolbeault's theorem is realised by two mutually-inverse `ℝ`-linear maps between `DolbeaultH01 X`
(an `ℝ`-module) and `𝔘.cechH1 0` (a `ℂ`-module, viewed as an `ℝ`-module via `ℝ ↪ ℂ`). We state each
map and the two round-trip identities as honest named obligations (each is a TRUE statement — the real
analytic content), then assemble the equivalence and the `finrank` count completely. The factor `2`
is the `ℝ`-vs-`ℂ` dimension (`finrank_real_of_complex` on the `ℂ`-module `cechH1`); it needs **no**
`Module ℂ` on `DolbeaultH01` — the `ℝ`-linear equivalence carries `finrank ℝ (DolbeaultH01) =
finrank ℝ (cechH1) = 2 · finrank ℂ (cechH1)`. -/

variable (𝔘 : FiniteCover X)

/-! ### Sorry-free algebraic backbone of the Dolbeault → Čech map

The Dolbeault → Čech construction sends a `(0,1)`-form `g` with local primitives `∂̄u_i = g` to the
Čech `1`-cochain `{[u_i] − [u_j]}` (germ-classes on overlaps) = `cechDelta0 {[u_i]}`. We record the
two *algebraic* facts that make this a genuine `cechH1` class, both **complete**:
* it is automatically a Čech cocycle (`δ¹∘δ⁰ = 0`), for ANY 0-cochain of germ-classes — even though
  the `u_i` are smooth-not-holomorphic, the germ-class cochains `MGerm` impose no holomorphy, so the
  `δ²=0` identity applies verbatim;
* the coboundary subspace lands in the cocycles (so the `cechH1` quotient is well-formed against it). -/

/-- **(Algebraic backbone, complete.)** `cechDelta0` of any germ-class 0-cochain is a Čech
`1`-cocycle. This is the abstract reason `{[u_i] − [u_j]}` (the Dolbeault → Čech cochain) lies in
`ker cechDelta1`; it holds for the smooth-not-holomorphic primitives `u_i` because germ-class
cochains carry no holomorphy constraint. Immediate from `δ¹ ∘ δ⁰ = 0`. -/
theorem cechDelta0_mem_ker_cechDelta1 (c : 𝔘.Cochain0) :
    𝔘.cechDelta0 c ∈ LinearMap.ker 𝔘.cechDelta1 := by
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, 𝔘.cechDelta1_comp_cechDelta0,
    LinearMap.zero_apply]

/-- **(Algebraic backbone, complete.)** The image of `cechDelta0` (the Čech coboundaries at the raw
germ-class level) is contained in the kernel of `cechDelta1` (the cocycles), for the same `δ²=0`
reason. The submodule form of `cechDelta0_mem_ker_cechDelta1`. -/
theorem range_cechDelta0_le_ker_cechDelta1 :
    LinearMap.range 𝔘.cechDelta0 ≤ LinearMap.ker 𝔘.cechDelta1 := by
  rintro _ ⟨c, rfl⟩
  exact cechDelta0_mem_ker_cechDelta1 𝔘 c

/-! ### The analytic heart: local `∂̄`-solvability on the manifold (honest named sub-kernel)

The Dolbeault → Čech map solves `∂̄u_i = g` on each chart-disk. The DONE input
`DbarLocal.dbar_solvable_locally` solves `∂̄u = g` for the *chart-coordinate* operator `DbarDisk.dbar`
on `ℂ → ℂ`. Transporting it to the *manifold* operator `RealForms.dbar` on smooth sections requires
the (currently absent) bridge `dbar u` (manifold) read in a holomorphic chart `=` `DbarDisk.dbar`
(chart-coordinate) of `u ∘ chart⁻¹` — a genuine, chart-transport lemma with no Mathlib path. We
isolate the consequence as the named analytic sub-kernel below; it is the *only* place the file
appeals to PDE content, and it is exactly `dbar_solvable_locally` modulo that chart bridge. -/

/-! #### The `(0,1)`-fiber algebra: a `(0,1)`-form is determined by its value at the vector `1`

`proj01 α` is the conjugate-`ℂ`-linear (Cauchy–Riemann) part of `α`. We record three purely
fiberwise facts, all **complete**, that make the chart transport go through:
* `proj01_apply_one` — `proj01 α 1 = ½(α 1 + i·α i)`, the Wirtinger scalar (this is *exactly*
  `DbarDisk.dbar`'s defining combination, evaluated on the differential);
* `proj01_conjLinear`/`proj01_eq_conj_smul` — `proj01 α` is conjugate-linear, so `proj01 α v =
  conj v · proj01 α 1`;
* `proj01_ext_of_apply_one` — hence a `(0,1)`-form is determined by its value at `1`. -/

/-- `proj01 α 1 = ½(α 1 + i·α i)` — the value of the `(0,1)`-projection at the tangent vector `1`
is the Wirtinger combination (the same `½(· + i·(i·))` that defines `DbarDisk.dbar`). -/
theorem proj01_apply_one (α : ℂ →L[ℝ] ℂ) :
    proj01 α 1 = (2 : ℂ)⁻¹ * (α 1 + Complex.I * α Complex.I) := by
  rw [proj01_apply]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  show (2 : ℝ)⁻¹ • (α 1 + mulI (α (mulI 1))) = _
  rw [mulI]
  simp only [ContinuousLinearMap.mul_apply', mul_one, Complex.real_smul]
  push_cast; ring

/-- `proj01 α` is conjugate-`ℂ`-linear: `(proj01 α)(i·v) = −i·(proj01 α) v`. (It is the `(0,1)` =
anti-holomorphic part, by construction.) -/
theorem proj01_conjLinear (α : ℂ →L[ℝ] ℂ) (v : ℂ) :
    proj01 α (Complex.I * v) = -(Complex.I * proj01 α v) := by
  rw [proj01_apply]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, mulI, ContinuousLinearMap.mul_apply',
    Complex.real_smul]
  have hII : α (Complex.I * (Complex.I * v)) = -α v := by
    have h : Complex.I * (Complex.I * v) = (-1 : ℝ) • v := by
      rw [Complex.real_smul]; push_cast; rw [← mul_assoc, Complex.I_mul_I]
    rw [h, map_smul, neg_one_smul]
  rw [hII]; ring_nf; rw [Complex.I_sq]; ring

/-- A `(0,1)`-form's value is `conj`-homogeneous: `proj01 α v = conj v · (proj01 α 1)`. -/
theorem proj01_eq_conj_smul (α : ℂ →L[ℝ] ℂ) (v : ℂ) :
    proj01 α v = (starRingEnd ℂ) v * proj01 α 1 := by
  set β := proj01 α
  have hI : β Complex.I = -(Complex.I * β 1) := by
    have := proj01_conjLinear α 1; rwa [mul_one] at this
  have hv : ((v.re : ℝ) • (1 : ℂ)) + (v.im : ℝ) • Complex.I = v := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]; exact Complex.re_add_im v
  conv_lhs => rw [← hv]
  rw [map_add, map_smul, map_smul, hI, Complex.real_smul, Complex.real_smul,
    show (starRingEnd ℂ) v = (v.re : ℂ) - (v.im : ℂ) * Complex.I from by
      apply Complex.ext <;> simp]
  ring

/-- **A `(0,1)`-form is determined by its value at the tangent vector `1`.** Anything in the range
of `proj01` (fixed by it) that agrees at `1` agrees everywhere — this is what lets the single scalar
equation `DbarDisk.dbar … = g …` recover the full CLM equation `dbar u x = g x`. -/
theorem proj01_ext_of_apply_one {α β : ℂ →L[ℝ] ℂ} (hαβ : proj01 α 1 = proj01 β 1) :
    proj01 α = proj01 β := by
  ext v; rw [proj01_eq_conj_smul α v, proj01_eq_conj_smul β v, hαβ]

/-! #### The chart bridge: intrinsic `dbar` read in a chart `=` `DbarDisk.dbar` of the pullback

The genuine chart-transport identity (mirroring `RealForms.dbar`'s own `mfderiv`-in-a-chart
mechanics and the `extChartAt 𝓘(ℝ,ℂ) = extChartAt 𝓘(ℂ)` `rfl`), proven **completely**:
`mfderiv` of `u` equals the plain `fderiv` of the chart-pullback `u ∘ (extChartAt _ x).symm`
(`MDifferentiableAt.mfderiv` + boundaryless `range = univ` + `writtenInExtChartAt` = the pullback,
since the codomain `ℂ`'s chart is the identity), and then the `(0,1)`-value at `1` is precisely
`DbarDisk.dbar` of that pullback. -/

/-- `mfderiv` of `u` at `x`, applied to a tangent vector `v`, is the plain `fderiv` of the
chart-pullback `u ∘ (extChartAt _ x).symm` at the chart coordinate `extChartAt _ x x`, applied to
`v`. (The boundaryless model has `range = univ`, so `fderivWithin = fderiv`; the codomain chart on
`ℂ` is the identity, so `writtenInExtChartAt` is the bare pullback.) -/
theorem mfderiv_apply_eq_fderiv_pullback (u : SmoothCFunctions X) (x : X) (v : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) v =
      fderiv ℝ (fun z => u ((extChartAt 𝓘(ℝ, ℂ) x).symm z)) (extChartAt 𝓘(ℝ, ℂ) x x) v := by
  have hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x := (u.contMDiff x).mdifferentiableAt (by simp)
  have hmf : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x =
      fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x ⇑u) (extChartAt 𝓘(ℝ, ℂ) x x) := by
    rw [hu.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  have hpull : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x ⇑u =
      fun z => u ((extChartAt 𝓘(ℝ, ℂ) x).symm z) := by
    ext z; simp only [writtenInExtChartAt, Function.comp_apply]; rfl
  rw [hpull] at hmf
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hmf

/-- **The chart bridge.** The intrinsic `dbar u` at `x` (i.e. `proj01 (mfderiv … u x)`), evaluated at
the tangent vector `1`, equals the planar Wirtinger `DbarDisk.dbar` of the chart-pullback of `u`,
read at the chart coordinate of `x`. This is the `dbar`(intrinsic)`= DbarDisk.dbar`(chart) identity
that transports the DONE planar solvability to the manifold. -/
theorem dbar_apply_one_eq_dbarDisk (u : SmoothCFunctions X) (x : X) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) (1 : ℂ) =
      DbarDisk.dbar (fun z => u ((extChartAt 𝓘(ℝ, ℂ) x).symm z)) (extChartAt 𝓘(ℝ, ℂ) x x) := by
  rw [proj01_apply_one, DbarDisk.dbar]
  congr 1
  congr 1
  · exact mfderiv_apply_eq_fderiv_pullback u x 1
  · congr 1
    exact mfderiv_apply_eq_fderiv_pullback u x Complex.I

/-- **Generalized chart bridge** for a *bare* `MDifferentiableAt` function `w : X → ℂ` (not just a
`SmoothCFunctions`): `mfderiv w x v` is the plain `fderiv` of the chart-pullback. Same proof as
`mfderiv_apply_eq_fderiv_pullback` but with the smoothness replaced by the weaker `MDifferentiableAt`
hypothesis — used to read the intrinsic `∂̄` of a *locally*-smooth value function like
`planarPrimitive ∘ extChartAt`. -/
theorem mfderiv_apply_eq_fderiv_pullback' {w : X → ℂ} {x : X}
    (hw : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w x) (v : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w x) v =
      fderiv ℝ (fun z => w ((extChartAt 𝓘(ℝ, ℂ) x).symm z)) (extChartAt 𝓘(ℝ, ℂ) x x) v := by
  have hmf : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w x =
      fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x w) (extChartAt 𝓘(ℝ, ℂ) x x) := by
    rw [hw.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  have hpull : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x w =
      fun z => w ((extChartAt 𝓘(ℝ, ℂ) x).symm z) := by
    ext z; simp only [writtenInExtChartAt, Function.comp_apply]; rfl
  rw [hpull] at hmf
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hmf

/-- **Generalized chart bridge at `1`** for a bare `MDifferentiableAt` function: the intrinsic
Wirtinger scalar `proj01 (mfderiv w x) 1` equals the planar `DbarDisk.dbar` of the chart-pullback.
The `MDifferentiableAt` form of `dbar_apply_one_eq_dbarDisk`. -/
theorem dbar_apply_one_eq_dbarDisk' {w : X → ℂ} {x : X}
    (hw : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w x) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w x) (1 : ℂ) =
      DbarDisk.dbar (fun z => w ((extChartAt 𝓘(ℝ, ℂ) x).symm z)) (extChartAt 𝓘(ℝ, ℂ) x x) := by
  rw [proj01_apply_one, DbarDisk.dbar]
  congr 1
  congr 1
  · exact mfderiv_apply_eq_fderiv_pullback' hw 1
  · congr 1
    exact mfderiv_apply_eq_fderiv_pullback' hw Complex.I

/-- **A value-at-`1` equation upgrades to the full CLM equation `dbar u x = g x`** (complete).
Both `dbar u x = proj01 (mfderiv … u x)` and (since `g ∈ OneFormsZeroOne X`) `g x = proj01 (β x)`
are `(0,1)`-forms, hence determined by their value at the tangent vector `1`
(`proj01_ext_of_apply_one`). So matching the single Wirtinger scalar suffices. This is the
mechanism by which the planar (scalar) `∂̄`-solvability recovers the intrinsic CLM-valued equation. -/
theorem dbar_eq_of_apply_one {g : SmoothCOneForms X} (hg : g ∈ OneFormsZeroOne X)
    (u : SmoothCFunctions X) (x : X)
    (h1 : proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) (1 : ℂ) = (g x) (1 : ℂ)) :
    (dbar u) x = g x := by
  obtain ⟨β, hβ⟩ := hg
  have hgx : g x = proj01 (β x) := by rw [← hβ]; rfl
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) = g x
  rw [hgx]
  exact proj01_ext_of_apply_one (by rw [← hgx]; exact h1)

/-- **The smooth lift of a chart-local planar function to a global manifold function** (complete).
Given a smooth `f : ℂ → ℂ` and a base point `x₀`, the cutoff product `χ • (f ∘ extChartAt x₀)` —
with `χ` a `SmoothBumpFunction` at `x₀` (`= 1` near `x₀`, supported in the chart) — is a *global*
`SmoothCFunctions X` (via `SmoothBumpFunction.contMDiff_smul`) that equals `f ∘ extChartAt x₀` on the
open neighborhood where `χ = 1`. This is the "extend a chart-local smooth function to the whole
manifold" half of the smooth-section ↔ chart-function dictionary; it is exactly how the planar local
primitive `ũ` becomes a global `u`. -/
theorem exists_smoothLift_of_chartFun (f : ℂ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x₀ : X) :
    ∃ (V : Set X) (u : SmoothCFunctions X), IsOpen V ∧ x₀ ∈ V ∧
      ∀ x ∈ V, (u x : ℂ) = f (extChartAt 𝓘(ℝ, ℂ) x₀ x) := by
  obtain ⟨χ⟩ : Nonempty (SmoothBumpFunction 𝓘(ℝ, ℂ) x₀) := inferInstance
  have hg : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun x => f (extChartAt 𝓘(ℝ, ℂ) x₀ x))
      (chartAt ℂ x₀).source := hf.contMDiff.comp_contMDiffOn contMDiffOn_extChartAt
  have hsmul : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun x => (χ x : ℝ) • f (extChartAt 𝓘(ℝ, ℂ) x₀ x)) := χ.contMDiff_smul hg
  have h1 : {x : X | χ x = 1} ∈ 𝓝 x₀ := χ.eventuallyEq_one
  obtain ⟨V, hVsub, hVopen, hx₀V⟩ := mem_nhds_iff.mp h1
  refine ⟨V, ⟨fun x => (χ x : ℝ) • f (extChartAt 𝓘(ℝ, ℂ) x₀ x), hsmul⟩, hVopen, hx₀V, ?_⟩
  intro x hx
  show (χ x : ℝ) • f (extChartAt 𝓘(ℝ, ℂ) x₀ x) = f (extChartAt 𝓘(ℝ, ℂ) x₀ x)
  rw [hVsub hx]; simp

/-! #### The Wirtinger chain rule for a holomorphic inner map

The single piece of genuine analytic content needed to transport the planar `∂̄`-solve (which lives
in the `x₀`-chart) to the intrinsic value (read in the chart at the evaluation point `x`): under a
*holomorphic* change of coordinates `τ`, the planar Wirtinger operator transforms by `conj(τ′)`. This
is the chart-transition equivariance of `∂̄`; it is a Mathlib-gap-filling lemma (no `analyticGroupoid`
Wirtinger calculus exists), proven here from `fderiv_comp` + `HasDerivAt.complexToReal_fderiv` (the
holomorphic `fderiv ℝ τ ζ = (deriv τ ζ) • 1`). Reusable; could later move to `DbarDisk.lean`. -/

/-- **Wirtinger chain rule for a holomorphic inner map.** For `f` real-differentiable and `τ`
holomorphic at `ζ`, the planar `∂̄` of the composite transforms by the conjugate of the complex
derivative of `τ`:
`DbarDisk.dbar (f ∘ τ) ζ = conj(τ′(ζ)) · DbarDisk.dbar f (τ ζ)`.
(The anti-holomorphic Wirtinger derivative is conjugate-linear in the holomorphic frame change — the
defining feature of a `(0,1)`-quantity.) -/
theorem dbarDisk_comp_holo (f : ℂ → ℂ) (τ : ℂ → ℂ) (ζ : ℂ)
    (hf : DifferentiableAt ℝ f (τ ζ)) (hτ : DifferentiableAt ℂ τ ζ) :
    DbarDisk.dbar (f ∘ τ) ζ = (starRingEnd ℂ) (deriv τ ζ) * DbarDisk.dbar f (τ ζ) := by
  have hτℝ : DifferentiableAt ℝ τ ζ := hτ.hasDerivAt.complexToReal_fderiv.differentiableAt
  have hτfd : fderiv ℝ τ ζ = (deriv τ ζ) • (1 : ℂ →L[ℝ] ℂ) :=
    hτ.hasDerivAt.complexToReal_fderiv.fderiv
  set c := deriv τ ζ with hc
  set L := fderiv ℝ f (τ ζ) with hL
  have hchain : fderiv ℝ (f ∘ τ) ζ = L.comp (fderiv ℝ τ ζ) := fderiv_comp ζ hf hτℝ
  have e1 : fderiv ℝ (f ∘ τ) ζ 1 = L (c * 1) := by rw [hchain, hτfd]; simp [smul_eq_mul]
  have eI : fderiv ℝ (f ∘ τ) ζ Complex.I = L (c * Complex.I) := by
    rw [hchain, hτfd]; simp [smul_eq_mul]
  rw [DbarDisk.dbar, DbarDisk.dbar, e1, eI, ← hL]
  set a := c.re with ha
  set b := c.im with hb
  have hcab : c = (a : ℂ) + (b : ℂ) * Complex.I := (Complex.re_add_im c).symm
  have hLc1 : L (c * 1) = (a : ℂ) * L 1 + (b : ℂ) * L Complex.I := by
    rw [mul_one, hcab,
      show ((a : ℂ) + (b : ℂ) * Complex.I) = (a : ℝ) • (1 : ℂ) + (b : ℝ) • Complex.I by
        simp [Complex.real_smul],
      map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hLcI : L (c * Complex.I) = -(b : ℂ) * L 1 + (a : ℂ) * L Complex.I := by
    have hci : c * Complex.I = (-b : ℝ) • (1 : ℂ) + (a : ℝ) • Complex.I := by
      rw [hcab, Complex.real_smul, Complex.real_smul]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [hci, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]; push_cast; ring
  rw [hLc1, hLcI,
    show (starRingEnd ℂ) c = (a : ℂ) - (b : ℂ) * Complex.I from by
      apply Complex.ext <;> simp [ha, hb]]
  linear_combination (2⁻¹ * (b : ℂ) * L Complex.I) * Complex.I_sq

/-- `DbarDisk.dbar` depends only on the germ of its argument: it agrees on functions equal in a
neighborhood of the base point (it is a fixed combination of `fderiv ℝ`, which respects
`Filter.EventuallyEq`). -/
theorem dbarDisk_congr {f₁ f₂ : ℂ → ℂ} {z : ℂ} (h : f₁ =ᶠ[nhds z] f₂) :
    DbarDisk.dbar f₁ z = DbarDisk.dbar f₂ z := by
  rw [DbarDisk.dbar, DbarDisk.dbar, h.fderiv_eq]

/-- **The chart-transition `e₀ ∘ eₓ.symm` is holomorphic (`ℂ`-differentiable).** On the analytic
(`ω`) manifold `X`, chart transition maps are holomorphic; here at the chart coordinate `eₓ x` of any
point `x` in the `x₀`-chart's source. (`ContMDiffAt` of the two charts composed, transferred to
`ContDiffAt ℂ ω` and hence `DifferentiableAt ℂ`; `chartAt ℂ = extChartAt 𝓘(ℝ,ℂ)` for the identity
model.) -/
theorem differentiableAt_chartTransition (x₀ x : X)
    (hxsrc : x ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).source) :
    DifferentiableAt ℂ ((extChartAt 𝓘(ℝ, ℂ) x₀) ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm)
      ((extChartAt 𝓘(ℝ, ℂ) x) x) := by
  have hsrc_x : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hcx_tgt : (chartAt ℂ x) x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hsrc_x
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := x)) _ hcx_tgt).contMDiffAt
      ((chartAt ℂ x).open_target.mem_nhds hcx_tgt)
  have hez : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv hsrc_x
  have hxsrc' : x ∈ (chartAt ℂ x₀).source := by rwa [extChartAt_source] at hxsrc
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x₀)
      ((chartAt ℂ x).symm ((chartAt ℂ x) x)) := by
    rw [hez]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := x₀)) _ hxsrc').contMDiffAt
      ((chartAt ℂ x₀).open_source.mem_nhds hxsrc')
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((chartAt ℂ x₀) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    ContMDiffAt.comp (I' := 𝓘(ℂ)) ((chartAt ℂ x) x) h2 h1
  have hda : DifferentiableAt ℂ ((chartAt ℂ x₀) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    (contMDiffAt_iff_contDiffAt.1 hcomp).differentiableAt (by norm_num)
  have he : ((chartAt ℂ x₀) ∘ (chartAt ℂ x).symm)
      = ((extChartAt 𝓘(ℝ, ℂ) x₀) ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm) := by
    funext z; simp [mfld_simps]
  have hpt : ((chartAt ℂ x) x) = ((extChartAt 𝓘(ℝ, ℂ) x) x) := by simp [mfld_simps]
  rw [he, hpt] at hda
  exact hda

/-- **The inverse chart-transition `eₓ ∘ e₀.symm` is holomorphic at `e₀ x`.** Companion to
`differentiableAt_chartTransition` with the two charts swapped and read at the point `e₀ x = τ_x(eₓ x)`
(rather than `eₓ x`); the local inverse of the transition `e₀ ∘ eₓ.symm`. Same mechanism: the two
charts of the analytic (`ω`) manifold composed, transferred to `DifferentiableAt ℂ`. -/
theorem differentiableAt_chartTransition_symm (x₀ x : X)
    (hxsrc : x ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).source) :
    DifferentiableAt ℂ ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) x₀).symm)
      ((extChartAt 𝓘(ℝ, ℂ) x₀) x) := by
  have hxsrc' : x ∈ (chartAt ℂ x₀).source := by rwa [extChartAt_source] at hxsrc
  have hcx_tgt : (chartAt ℂ x₀) x ∈ (chartAt ℂ x₀).target := (chartAt ℂ x₀).map_source hxsrc'
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := x₀)) _ hcx_tgt).contMDiffAt
      ((chartAt ℂ x₀).open_target.mem_nhds hcx_tgt)
  have hez : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x) = x := (chartAt ℂ x₀).left_inv hxsrc'
  have hsrc_x : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x)
      ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x)) := by
    rw [hez]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := x)) _ hsrc_x).contMDiffAt
      ((chartAt ℂ x).open_source.mem_nhds hsrc_x)
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((chartAt ℂ x) ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x) :=
    ContMDiffAt.comp (I' := 𝓘(ℂ)) ((chartAt ℂ x₀) x) h2 h1
  have hda : DifferentiableAt ℂ ((chartAt ℂ x) ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x) :=
    (contMDiffAt_iff_contDiffAt.1 hcomp).differentiableAt (by norm_num)
  have he : ((chartAt ℂ x) ∘ (chartAt ℂ x₀).symm)
      = ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) x₀).symm) := by
    funext z; simp [mfld_simps]
  have hpt : ((chartAt ℂ x₀) x) = ((extChartAt 𝓘(ℝ, ℂ) x₀) x) := by simp [mfld_simps]
  rw [he, hpt] at hda
  exact hda

/-- **Nonvanishing of the holomorphic transition derivative.** On the analytic (`ω`) manifold, for
`x` in the `x₀`-chart, the complex derivative of the chart transition `τ_x = e₀ ∘ eₓ.symm` at `eₓ x`
is nonzero: `τ_x` has the holomorphic local inverse `eₓ ∘ e₀.symm`, so `deriv τ_x · deriv (inverse) = 1`
by the chain rule on `(eₓ ∘ e₀.symm) ∘ τ_x = id` near `eₓ x`, forcing the factor `≠ 0`. -/
theorem deriv_chartTransition_ne_zero (x₀ x : X)
    (hxsrc : x ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).source) :
    deriv ((extChartAt 𝓘(ℝ, ℂ) x₀) ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm) ((extChartAt 𝓘(ℝ, ℂ) x) x) ≠ 0 := by
  set eₓ := extChartAt 𝓘(ℝ, ℂ) x with hex
  set e₀ := extChartAt 𝓘(ℝ, ℂ) x₀ with he₀
  set τ := e₀ ∘ eₓ.symm with hτ
  set σ := eₓ ∘ e₀.symm with hσ
  -- `τ (eₓ x) = e₀ x`.
  have hτpt : τ (eₓ x) = e₀ x := by simp only [hτ, Function.comp_apply, hex, extChartAt_to_inv]
  -- The two transitions are holomorphic at the relevant points.
  have hτdiff : DifferentiableAt ℂ τ (eₓ x) := differentiableAt_chartTransition x₀ x hxsrc
  have hσdiff : DifferentiableAt ℂ σ (e₀ x) := differentiableAt_chartTransition_symm x₀ x hxsrc
  -- `σ ∘ τ = id` on a neighborhood of `eₓ x`: charts are mutual inverses near `x`.
  -- Eventually in `z`: `z ∈ eₓ.target` and `eₓ.symm z ∈ e₀.source`.
  have htgt : ∀ᶠ z in nhds (eₓ x), z ∈ eₓ.target := by
    rw [hex]
    exact (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have hmem : ∀ᶠ z in nhds (eₓ x), eₓ.symm z ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).source := by
    have hcont : ContinuousAt eₓ.symm (eₓ x) := continuousAt_extChartAt_symm x
    refine hcont.preimage_mem_nhds ?_
    rw [hex, extChartAt_to_inv]
    exact (isOpen_extChartAt_source x₀).mem_nhds hxsrc
  have hinv : (σ ∘ τ) =ᶠ[nhds (eₓ x)] id := by
    filter_upwards [htgt, hmem] with z hztgt hzsrc
    simp only [hσ, hτ, Function.comp_apply, id_eq]
    rw [(extChartAt 𝓘(ℝ, ℂ) x₀).left_inv hzsrc, (extChartAt 𝓘(ℝ, ℂ) x).right_inv hztgt]
  -- Chain rule on `σ ∘ τ = id`: the product of derivatives is `1`.
  have hcomp : deriv (σ ∘ τ) (eₓ x) = deriv σ (τ (eₓ x)) * deriv τ (eₓ x) :=
    deriv_comp (eₓ x) (hτpt ▸ hσdiff) hτdiff
  have hone : deriv (σ ∘ τ) (eₓ x) = 1 := by rw [hinv.deriv_eq, deriv_id]
  rw [hone] at hcomp
  intro h0
  rw [h0, mul_zero] at hcomp
  exact one_ne_zero hcomp

/-- **Transition holomorphy at a general overlap point.** The chart transition `e_a ∘ e_b.symm` is
`ℂ`-differentiable at any `w` in `e_b`'s target whose `e_b`-preimage lies in `e_a`'s source (not only
at the chart centre, as in `differentiableAt_chartTransition`). Same mechanism: the two analytic
(`ω`) charts composed, `ContMDiffAt → ContDiffAt ℂ → DifferentiableAt ℂ`. -/
theorem differentiableAt_transition_of_mem (a b : X) {w : ℂ}
    (hwt : w ∈ (chartAt ℂ b).target) (hws : (chartAt ℂ b).symm w ∈ (chartAt ℂ a).source) :
    DifferentiableAt ℂ ((extChartAt 𝓘(ℝ, ℂ) a) ∘ (extChartAt 𝓘(ℝ, ℂ) b).symm) w := by
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ b).symm w :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := b)) _ hwt).contMDiffAt
      ((chartAt ℂ b).open_target.mem_nhds hwt)
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ a) ((chartAt ℂ b).symm w) :=
    ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := a)) _ hws).contMDiffAt
      ((chartAt ℂ a).open_source.mem_nhds hws)
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((chartAt ℂ a) ∘ (chartAt ℂ b).symm) w :=
    ContMDiffAt.comp (I' := 𝓘(ℂ)) w h2 h1
  have hda : DifferentiableAt ℂ ((chartAt ℂ a) ∘ (chartAt ℂ b).symm) w :=
    (contMDiffAt_iff_contDiffAt.1 hcomp).differentiableAt (by norm_num)
  have he : ((chartAt ℂ a) ∘ (chartAt ℂ b).symm)
      = ((extChartAt 𝓘(ℝ, ℂ) a) ∘ (extChartAt 𝓘(ℝ, ℂ) b).symm) := by
    funext z; simp [mfld_simps]
  rwa [he] at hda

/-- **The frame vector as the (forward) inverse-transition derivative** (direct form). For `x` in the
`x₀`-chart, `Sₓ 1 = symmL ℝ (trivAt x₀) x 1` equals `deriv σ_x (e₀ x)` with `σ_x = eₓ ∘ e₀.symm` the
*inverse* chart transition. (Same `symmL = tangentCoordChange = fderivWithin σ_x` chain as
`frameVector_eq_inv_deriv_transition`, stopping at `fderiv σ_x = deriv σ_x • 1` before inverting; the
reciprocal of the `deriv τ_x` form.) Used to read `∂̄h` in another chart without the inverse. -/
theorem frameVector_eq_deriv_transition_symm (x₀ x : X)
    (hxsrc : x ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).source) :
    (Bundle.Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x) (1 : ℂ)
      = deriv ((extChartAt 𝓘(ℝ, ℂ) x) ∘ (extChartAt 𝓘(ℝ, ℂ) x₀).symm) ((extChartAt 𝓘(ℝ, ℂ) x₀) x) := by
  set eₓ := extChartAt 𝓘(ℝ, ℂ) x with hex
  set e₀ := extChartAt 𝓘(ℝ, ℂ) x₀ with he₀
  set σ := eₓ ∘ e₀.symm with hσ
  have hxchart : x ∈ (chartAt ℂ x₀).source := by rwa [extChartAt_source] at hxsrc
  have h1 : Bundle.Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x
      = tangentCoordChange 𝓘(ℝ, ℂ) x₀ x x := TangentBundle.symmL_trivializationAt_eq_core hxchart
  have hσdiff : DifferentiableAt ℂ σ (e₀ x) := differentiableAt_chartTransition_symm x₀ x hxsrc
  have hfd : fderiv ℝ σ (e₀ x) = (deriv σ (e₀ x)) • (1 : ℂ →L[ℝ] ℂ) :=
    hσdiff.hasDerivAt.complexToReal_fderiv.fderiv
  have h2 : tangentCoordChange 𝓘(ℝ, ℂ) x₀ x x = fderiv ℝ σ (e₀ x) := by
    rw [tangentCoordChange_def, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  rw [h1, h2, hfd]
  change (deriv σ (e₀ x)) • ((1 : ℂ →L[ℝ] ℂ) 1) = _
  simp

/-! #### The local primitive at the value-`1` level

`exists_localPrimitive_apply_one` produces, near every `x₀`, a smooth `u` whose intrinsic `∂̄`
Wirtinger scalar `proj01 (mfderiv … u x) 1` matches `g x 1`. It is now PROVEN by reduction to a single
finer sub-kernel, the chart-pullback `(0,1)`-datum `exists_chartPullback_zeroOne_datum` (below): the
planar PDE `DbarLocal.dbar_solvable_locally` (DONE) solves `∂̄f = G` in the `x₀`-chart for that datum
`G`, the global smooth lift `exists_smoothLift_of_chartFun` (DONE) globalizes it to `u`, the chart
bridge `dbar_apply_one_eq_dbarDisk` (DONE) reads `∂̄u` at `x` in its own chart, and the Wirtinger
chain rule `dbarDisk_comp_holo` (DONE) produces the `conj(τ′)` frame factor that cancels exactly
against the one in the datum's transformation law. The *only* remaining analytic content — the
smoothness of the chart-read datum `G` and the `(0,1)`-transformation law — is isolated in
`exists_chartPullback_zeroOne_datum`. -/

/-- The chart-read datum of `g` at the fixed `x₀`-trivialization is a smooth map `X → ℂ` at every
point `y` of the `x₀`-chart source: `x ↦ (g x) (Sₓ 1)`, with `Sₓ = symmL ℝ (trivializationAt ℂ
(TangentSpace 𝓘(ℝ,ℂ)) x₀) x` the `symmL` of the *fixed* `x₀`-trivialization.

Mechanism: by `contMDiffAt_hom_bundle` at `y` (the codomain trivial `ℂ`-bundle has identity
trivialisation), `x ↦ (g x).comp (symmL(trivAt y)(x))` is smooth into `ℂ →L[ℝ] ℂ`. The frame at `y`
and at `x₀` differ by the bundle `coordChangeL` (`x ↦ coordChangeL (trivAt x₀) (trivAt y) x`, smooth
by `contMDiffAt_coordChangeL`), so the value `(g x)(Sₓ 1)` rewrites as
`((g x).comp (symmL(trivAt y)(x))) (coordChangeL (trivAt x₀) (trivAt y) x 1)` near `y`
(`coordChangeL_apply` + `symmL_continuousLinearMapAt`); both factors are smooth, so `ContMDiffAt.clm_apply`
closes it. (No varying chart-at-`x`: `Sₓ` uses only the fixed `x₀`-trivialization; the `y`-frame is an
internal device.) -/
private theorem contMDiffAt_chartRead_datum (g : SmoothCOneForms X) (x₀ y : X)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).source) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun x => (g x) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x) (1 : ℂ))) y := by
  set ex₀ := trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀ with hex₀
  set ey := trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y with hey
  -- (a) `x ↦ (g x).comp (symmL ey x)` is smooth at `y` (hom-bundle reduction in the `y`-frame).
  have h := g.contMDiff_toFun y
  rw [contMDiffAt_hom_bundle] at h
  simp only [ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    Bundle.Trivial.fiberBundle_trivializationAt', ContinuousLinearMap.id_comp, ← hey] at h
  -- (b) `x ↦ coordChangeL ex₀ ey x 1` is smooth at `y` (`coordChangeL` smooth, eval at `1`).
  have hyb : y ∈ ex₀.baseSet ∩ ey.baseSet :=
    ⟨by rw [hex₀, TangentBundle.trivializationAt_baseSet, ← extChartAt_source 𝓘(ℝ, ℂ)]; exact hy,
      by rw [hey, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source ℂ y⟩
  have hcc : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun x => (Bundle.Trivialization.coordChangeL ℝ ex₀ ey x : ℂ →L[ℝ] ℂ) (1 : ℂ)) y :=
    (contMDiffAt_coordChangeL (e := ex₀) (e' := ey) hyb.1 hyb.2).clm_apply contMDiffAt_const
  -- The product, rewritten to the target via the frame identity (valid near `y`).
  have hbase : ∀ᶠ x in nhds y, x ∈ ex₀.baseSet ∩ ey.baseSet :=
    (ex₀.open_baseSet.inter ey.open_baseSet).mem_nhds hyb
  refine (h.2.clm_apply hcc).congr_of_eventuallyEq ?_
  filter_upwards [hbase] with x hx
  -- `((g x).comp (symmL ey x)) (coordChangeL ex₀ ey x 1) = (g x) (symmL ex₀ x 1)`.
  simp only [ContinuousLinearMap.comp_apply, ← hex₀]
  congr 1
  -- `symmL ey x (coordChangeL ex₀ ey x 1) = symmL ex₀ x 1`, via the frame identity.
  simp only [ContinuousLinearEquiv.coe_coe]
  rw [ex₀.coordChangeL_apply ey hx,
    ← ey.continuousLinearMapAt_apply_of_mem (R := ℝ) hx.2 (ex₀.symm x 1),
    ey.symmL_continuousLinearMapAt hx.2]
  rfl

/-- **The frame vector is the inverse transition derivative.** For `x` in the `x₀`-chart source, the
constant `x₀`-frame tangent vector `Sₓ 1 = symmL ℝ (trivAt x₀) x 1` equals `(τ_x′(eₓ x))⁻¹`, the
reciprocal of the holomorphic chart-transition derivative `τ_x = e₀ ∘ eₓ.symm`. (`symmL (trivAt x₀) x`
is the tangent `coordChange (achart x₀) (achart x) x = tangentCoordChange x₀ x x = fderivWithin ℝ
(eₓ ∘ e₀.symm) (range) (e₀ x)`; on the boundaryless model this is `fderiv ℝ σ_x (e₀ x)`, and `σ_x =
eₓ ∘ e₀.symm` is holomorphic so `fderiv ℝ σ_x (e₀ x) = (deriv σ_x (e₀ x)) • 1`; finally `deriv σ_x
(e₀ x) = (deriv τ_x (eₓ x))⁻¹` since `σ_x` is the local inverse of `τ_x`.) -/
private theorem frameVector_eq_inv_deriv_transition (x₀ x : X)
    (hxsrc : x ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).source) :
    (Bundle.Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x) (1 : ℂ)
      = (deriv ((extChartAt 𝓘(ℝ, ℂ) x₀) ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm)
          ((extChartAt 𝓘(ℝ, ℂ) x) x))⁻¹ := by
  set eₓ := extChartAt 𝓘(ℝ, ℂ) x with hex
  set e₀ := extChartAt 𝓘(ℝ, ℂ) x₀ with he₀
  set σ := eₓ ∘ e₀.symm with hσ
  set τ := e₀ ∘ eₓ.symm with hτ
  -- `symmL (trivAt x₀) x = tangentCoordChange x₀ x x = fderivWithin ℝ σ (range) (e₀ x)`.
  have hxchart : x ∈ (chartAt ℂ x₀).source := by rwa [extChartAt_source] at hxsrc
  have h1 : Bundle.Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x
      = tangentCoordChange 𝓘(ℝ, ℂ) x₀ x x := TangentBundle.symmL_trivializationAt_eq_core hxchart
  -- It is the `ℝ`-`fderiv` of the holomorphic inverse transition `σ` at `e₀ x`.
  have hσdiff : DifferentiableAt ℂ σ (e₀ x) := differentiableAt_chartTransition_symm x₀ x hxsrc
  have hfd : fderiv ℝ σ (e₀ x) = (deriv σ (e₀ x)) • (1 : ℂ →L[ℝ] ℂ) :=
    hσdiff.hasDerivAt.complexToReal_fderiv.fderiv
  have h2 : tangentCoordChange 𝓘(ℝ, ℂ) x₀ x x = fderiv ℝ σ (e₀ x) := by
    rw [tangentCoordChange_def, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  -- The inverse-derivative relation `deriv σ (e₀ x) = (deriv τ (eₓ x))⁻¹`.
  have hτpt : τ (eₓ x) = e₀ x := by simp only [hτ, Function.comp_apply, hex, extChartAt_to_inv]
  have hτdiff : DifferentiableAt ℂ τ (eₓ x) := differentiableAt_chartTransition x₀ x hxsrc
  have htgt : ∀ᶠ z in nhds (eₓ x), z ∈ eₓ.target := by
    rw [hex]; exact (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have hmem : ∀ᶠ z in nhds (eₓ x), eₓ.symm z ∈ e₀.source := by
    have hcont : ContinuousAt eₓ.symm (eₓ x) := continuousAt_extChartAt_symm x
    refine hcont.preimage_mem_nhds ?_
    rw [hex, extChartAt_to_inv]; exact (isOpen_extChartAt_source x₀).mem_nhds hxsrc
  have hinv : (σ ∘ τ) =ᶠ[nhds (eₓ x)] id := by
    filter_upwards [htgt, hmem] with z hztgt hzsrc
    simp only [hσ, hτ, Function.comp_apply, id_eq]
    rw [e₀.left_inv hzsrc, eₓ.right_inv hztgt]
  have hcomp : deriv (σ ∘ τ) (eₓ x) = deriv σ (e₀ x) * deriv τ (eₓ x) := by
    rw [deriv_comp (eₓ x) (hτpt ▸ hσdiff) hτdiff, hτpt]
  have hone : deriv (σ ∘ τ) (eₓ x) = 1 := by rw [hinv.deriv_eq, deriv_id]
  have hτne : deriv τ (eₓ x) ≠ 0 := deriv_chartTransition_ne_zero x₀ x hxsrc
  have hinvderiv : deriv σ (e₀ x) = (deriv τ (eₓ x))⁻¹ := by
    rw [hone] at hcomp
    exact (inv_eq_of_mul_eq_one_left hcomp.symm).symm
  -- Assemble: `symmL … 1 = fderiv ℝ σ (e₀ x) 1 = deriv σ (e₀ x) • 1 = (deriv τ (eₓ x))⁻¹`.
  rw [h1, h2, hfd, hinvderiv]
  change (deriv τ (eₓ x))⁻¹ • ((1 : ℂ →L[ℝ] ℂ) 1) = _
  simp

/-- **The `(0,1)`-form `g x` is conjugate-`ℂ`-linear** (since `g ∈ OneFormsZeroOne X`): `(g x) v =
conj v · (g x) 1`. Reduces to `proj01_eq_conj_smul` via `g x = proj01 (β x)` for the representative
`β` with `proj01L β = g`. -/
private theorem oneForm_apply_conjLinear {g : SmoothCOneForms X} (hg : g ∈ OneFormsZeroOne X)
    (x : X) (v : ℂ) : (g x) v = (starRingEnd ℂ) v * (g x) (1 : ℂ) := by
  obtain ⟨β, hβ⟩ := hg
  have hgx : g x = proj01 (β x) := by rw [← hβ]; rfl
  rw [hgx]; exact proj01_eq_conj_smul (β x) v

/-- **(Finer analytic sub-kernel — the chart-pullback `(0,1)`-datum.)** A smooth `(0,1)`-form `g`
read in the `x₀`-chart is a *smooth planar function* `G : ℂ → ℂ` (its Wirtinger / value-`1` datum)
that reproduces the intrinsic value `g x 1` after the holomorphic frame change: on a *neighborhood*
`V` of `x₀`, with `τ_x = e₀ ∘ eₓ.symm` the holomorphic transition,
`conj(τ_x′(eₓ x)) · G(e₀ x) = g x 1`.

LOCALITY (why a neighborhood `V`, not the whole chart source): the datum `G` is the chart-pullback of
`g`; on a non-compact chart-disk it is genuinely *unbounded at the chart boundary*, so the global
"for all `x ∈ e₀.source`" form is FALSE. The honest statement gives the law only near `x₀` (where the
local primitive is built); this is all `exists_localPrimitive_apply_one` consumes.

This is the genuine smooth-section ↔ planar-form dictionary entry that Mathlib lacks: it packages
(i) the smoothness of the chart-read datum `G` and (ii) the `(0,1)`-transformation law (the `conj(τ′)`
frame factor) into the exact form consumed by `exists_localPrimitive_apply_one`. The `conj(τ′)` here
is the *same* factor produced on the `∂̄u` side by the Wirtinger chain rule `dbarDisk_comp_holo`
(PROVEN), so the two cancel and the planar PDE `DbarLocal.dbar_solvable_locally` (DONE) closes the
local primitive. TRUE: it is the standard statement that a `(0,1)`-form pulls back along a chart to a
smooth `(0,1)`-form, whose anti-holomorphic component transforms by `conj` of the transition
derivative (`proj01_eq_conj_smul` gives the conjugate-homogeneity fiberwise; the content is the
*smoothness* of `G` and the chart-derivative bookkeeping `mfderiv` of charts ↔ planar `deriv τ`). -/
theorem exists_chartPullback_zeroOne_datum (g : SmoothCOneForms X)
    (hg : g ∈ OneFormsZeroOne X) (x₀ : X) :
    ∃ (G : ℂ → ℂ) (V : Set X), ContDiff ℝ (⊤ : ℕ∞) G ∧ IsOpen V ∧ x₀ ∈ V ∧
      ∀ x ∈ V, (starRingEnd ℂ) (deriv (extChartAt 𝓘(ℝ, ℂ) x₀ ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm)
            (extChartAt 𝓘(ℝ, ℂ) x x)) * G (extChartAt 𝓘(ℝ, ℂ) x₀ x) = (g x) (1 : ℂ) := by
  classical
  set e₀ := extChartAt 𝓘(ℝ, ℂ) x₀ with he₀
  -- The chart-read datum `Φ x = (g x) (Sₓ 1)` (smooth at each point of `e₀.source`, `contMDiffAt_chartRead_datum`).
  set Φ : X → ℂ := fun x => (g x) ((Bundle.Trivialization.symmL ℝ
    (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x) (1 : ℂ)) with hΦ
  -- `e₀.target` is an open neighborhood of `e₀ x₀`; pick a bump `χ` with `closedBall r ⊆ e₀.target`.
  have htgt_open : IsOpen e₀.target := by rw [he₀]; exact isOpen_extChartAt_target x₀
  have hx₀tgt : e₀ x₀ ∈ e₀.target := by rw [he₀]; exact mem_extChartAt_target x₀
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp htgt_open (e₀ x₀) hx₀tgt
  set χ : ContDiffBump (e₀ x₀) := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hχ
  -- `closedBall (r/2) ⊆ ball r ⊆ e₀.target` (the bump's outer support lies safely inside the chart).
  have hcball_sub : Metric.closedBall (e₀ x₀) (r / 2) ⊆ e₀.target := fun z hz =>
    hr_sub (Metric.closedBall_subset_ball (by linarith) hz)
  -- `Ψ := Φ ∘ e₀.symm` is `ContDiffAt` at every `w ∈ e₀.target` (helper + smooth chart inverse).
  have hΨ : ∀ w ∈ e₀.target, ContDiffAt ℝ (⊤ : ℕ∞) (fun w => Φ (e₀.symm w)) w := by
    intro w hw
    have hsymm_mem : e₀.symm w ∈ e₀.source := by rw [he₀]; exact PartialEquiv.map_target _ hw
    have hsymm : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) e₀.symm e₀.target w :=
      (contMDiffOn_extChartAt_symm x₀) _ hw
    have hΦat : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) Φ (e₀.symm w) :=
      contMDiffAt_chartRead_datum g x₀ (e₀.symm w) hsymm_mem
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun w => Φ (e₀.symm w)) e₀.target w :=
      hΦat.contMDiffWithinAt.comp w hsymm (fun z _ => Set.mem_univ _)
    exact contMDiffAt_iff_contDiffAt.mp (hcomp.contMDiffAt (htgt_open.mem_nhds hw))
  -- The global datum `G := χ • (Φ ∘ e₀.symm)` (smooth everywhere; `= Φ ∘ e₀.symm` near `e₀ x₀`).
  refine ⟨fun w => (χ w : ℝ) • Φ (e₀.symm w),
    e₀.source ∩ e₀ ⁻¹' Metric.ball (e₀ x₀) (r / 4), ?_, ?_, ?_, ?_⟩
  · -- (1) Global smoothness of `G`.
    rw [contDiff_iff_contDiffAt]; intro w
    by_cases hw : w ∈ Metric.closedBall (e₀ x₀) (r / 2)
    · -- Inside `closedBall (r/2) ⊆ e₀.target`: both factors smooth.
      exact (χ.contDiff.contDiffAt).smul (hΨ w (hcball_sub hw))
    · -- Outside: `χ = 0` on the open complement of `closedBall (r/2) ⊇ supp χ`, so `G = 0`.
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      have hcompl : (Metric.closedBall (e₀ x₀) (r / 2))ᶜ ∈ nhds w :=
        (Metric.isClosed_closedBall.isOpen_compl).mem_nhds hw
      filter_upwards [hcompl] with z hz
      have : χ z = 0 := by
        rw [← Function.notMem_support, χ.support_eq]
        exact fun h => hz (Metric.ball_subset_closedBall h)
      rw [this, zero_smul]
  · -- (2) `V` is open.
    rw [he₀]; exact isOpen_extChartAt_preimage' x₀ Metric.isOpen_ball
  · -- (3) `x₀ ∈ V`.
    refine ⟨mem_extChartAt_source x₀, ?_⟩
    simp only [Set.mem_preimage, he₀, Metric.mem_ball, dist_self]; positivity
  · -- (4) The transformation law on `V`.
    rintro x ⟨hxsrc, hxball⟩
    rw [extChartAt_source] at hxsrc
    have hxsrc' : x ∈ e₀.source := by rw [he₀, extChartAt_source]; exact hxsrc
    -- On `V`, `e₀ x ∈ ball (r/2) ⊆ ball rIn`, so `χ (e₀ x) = 1` and `e₀.symm (e₀ x) = x`.
    have hχ1 : (χ (e₀ x) : ℝ) = 1 := by
      apply χ.one_of_mem_closedBall
      simp only [Set.mem_preimage, Metric.mem_ball] at hxball
      exact Metric.ball_subset_closedBall hxball
    have hsymm_pt : e₀.symm (e₀ x) = x := e₀.left_inv hxsrc'
    -- `G (e₀ x) = Φ x = (g x) (Sₓ 1)`.
    show (starRingEnd ℂ) (deriv (e₀ ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm) (extChartAt 𝓘(ℝ, ℂ) x x))
      * ((χ (e₀ x) : ℝ) • Φ (e₀.symm (e₀ x))) = (g x) (1 : ℂ)
    rw [hχ1, one_smul, hsymm_pt, hΦ]
    simp only []
    -- Frame identity + conjugate-linearity: `conj(τ′) · (g x) (Sₓ 1) = (g x) 1`.
    rw [frameVector_eq_inv_deriv_transition x₀ x hxsrc',
      oneForm_apply_conjLinear hg x ((deriv (e₀ ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm)
        (extChartAt 𝓘(ℝ, ℂ) x x))⁻¹)]
    rw [map_inv₀]
    have hne : (starRingEnd ℂ) (deriv (e₀ ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm)
        (extChartAt 𝓘(ℝ, ℂ) x x)) ≠ 0 := by
      rw [map_ne_zero]; exact deriv_chartTransition_ne_zero x₀ x hxsrc'
    field_simp

theorem exists_localPrimitive_apply_one (g : SmoothCOneForms X) (hg : g ∈ OneFormsZeroOne X)
    (x₀ : X) :
    ∃ (V : Set X) (u : SmoothCFunctions X), IsOpen V ∧ x₀ ∈ V ∧
      ∀ x ∈ V, proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) (1 : ℂ) = (g x) (1 : ℂ) := by
  classical
  -- The chart-pullback `(0,1)`-datum `G` (smooth planar function) with its transformation law,
  -- valid on a neighborhood `Vdat` of `x₀` (the law is local — `G` is unbounded at the chart edge).
  obtain ⟨G, Vdat, hGsmooth, hVdatopen, hx₀Vdat, hGlaw⟩ :=
    exists_chartPullback_zeroOne_datum g hg x₀
  -- STEP A: solve the planar `∂̄f = G` on a neighborhood `W` of the chart coordinate `e₀ x₀`.
  obtain ⟨W, f, hWopen, hWmem, hfsmooth, hfsolve⟩ :=
    DbarLocal.dbar_solvable_locally hGsmooth (extChartAt 𝓘(ℝ, ℂ) x₀ x₀)
  -- STEP B: lift `f` to a global smooth `u` agreeing with `f ∘ e₀` near `x₀`.
  obtain ⟨V₀, u, hV₀open, hx₀V₀, hlift⟩ := exists_smoothLift_of_chartFun f hfsmooth x₀
  -- The working neighborhood: inside the datum nbhd `Vdat`, the lift set `V₀`, the chart source
  -- (kept for `differentiableAt_chartTransition`), and the `e₀`-preimage of `W`.
  refine ⟨Vdat ∩ (V₀ ∩ ((extChartAt 𝓘(ℝ, ℂ) x₀).source ∩
      (extChartAt 𝓘(ℝ, ℂ) x₀) ⁻¹' W)), u, ?_, ?_, ?_⟩
  · exact hVdatopen.inter (hV₀open.inter (isOpen_extChartAt_preimage' x₀ hWopen))
  · exact ⟨hx₀Vdat, hx₀V₀, mem_extChartAt_source x₀, by simpa using hWmem⟩
  · rintro x ⟨hxVdat, hxV₀, hxsrc, hxW⟩
    simp only [Set.mem_preimage] at hxW
    -- Read the intrinsic ∂̄ at `x` in `x`'s own chart (the chart bridge).
    rw [dbar_apply_one_eq_dbarDisk u x]
    -- The holomorphic transition `τ = e₀ ∘ eₓ.symm` and its key point value `τ (eₓ x) = e₀ x`.
    set eₓ := extChartAt 𝓘(ℝ, ℂ) x with hex
    set e₀ := extChartAt 𝓘(ℝ, ℂ) x₀ with he₀
    have hτpt : (e₀ ∘ eₓ.symm) (eₓ x) = e₀ x := by
      simp only [Function.comp_apply, hex, extChartAt_to_inv]
    -- Near `eₓ x`, the chart-pullback of `u` equals `f ∘ τ` (lift identity on `V₀`).
    have hmemV₀ : ∀ᶠ z in nhds (eₓ x), eₓ.symm z ∈ V₀ := by
      have hcont : ContinuousAt eₓ.symm (eₓ x) := continuousAt_extChartAt_symm x
      refine hcont.preimage_mem_nhds (hV₀open.mem_nhds ?_)
      rw [hex, extChartAt_to_inv]; exact hxV₀
    have heq : (fun z => u (eₓ.symm z)) =ᶠ[nhds (eₓ x)] (f ∘ (e₀ ∘ eₓ.symm)) := by
      filter_upwards [hmemV₀] with z hz
      simp only [Function.comp_apply]
      exact hlift _ hz
    rw [dbarDisk_congr heq]
    -- Wirtinger chain rule: the `conj(τ′)` frame factor appears.
    rw [dbarDisk_comp_holo f (e₀ ∘ eₓ.symm) (eₓ x)
      (hfsmooth.differentiable (by norm_num) _)
      (differentiableAt_chartTransition x₀ x hxsrc)]
    -- `DbarDisk.dbar f` at `τ (eₓ x) = e₀ x` is `G (e₀ x)` (`f` solves `∂̄f = G` on `W`).
    rw [hτpt, hfsolve (e₀ x) hxW]
    -- Exactly the transformation law for the chart-pullback `(0,1)`-datum (valid on `Vdat`).
    exact hGlaw x hxVdat

/-! ### Step 3 — the cutoff chart-pullback over a chart-disk cover (linear, smooth, compact support)

For the *forward* Dolbeault → Čech operator we must solve `∂̄u_i = g` on the *whole* disk `U_i` of a
`ChartDiskCover`, linearly in `g`. The planar datum fed to the (linear) Cauchy transform is the
**cutoff chart-pullback** `χᵢ · (Φ_g ∘ eᵢ.symm)`: the `(0,1)`-form `g` read in the `center i`-chart
(`Φ_g y = g y (frame 1)`), multiplied by the disk bump `χᵢ` (`= 1` on `U_i`, supported in the chart
target). It is smooth, compactly supported, and `ℝ`-linear in `g` — exactly the input shape of
`cauchyTransform_add` / `cauchyTransform_smul`. The smoothness reuses `contMDiffAt_chartRead_datum`
(the same argument as `exists_chartPullback_zeroOne_datum`'s global-smoothness step). -/

/-- **Chart-holomorphy ⟹ `𝒪`-section (`OmegaD 0`).** A function `F` on an open `V` whose
extension-by-zero `Gext F`, read in each point's own `ℂ`-chart, is *analytic* there, is a holomorphic
section: `F ∈ OmegaD 0 V`. Both halves go through the `Gext` bridge — `IsMeromorphic` via
`Gext_chart_bridge` (analytic ⟹ meromorphic), and `0 ≤ ordU` via `ordU_eq_orderAt_Gext` plus
`AnalyticAt.meromorphicOrderAt_nonneg`. The bridge that turns the planar cocycle holomorphy into a
genuine `cechH1` cocycle. -/
theorem mem_OmegaD_zero_of_gext_analytic {V : TopologicalSpace.Opens X} {F : V → ℂ}
    (hF : ∀ v : V, AnalyticAt ℂ (Gext F ∘ (chartAt (H := ℂ) (v : X)).symm)
      ((chartAt (H := ℂ) (v : X)) (v : X))) :
    F ∈ OmegaD (0 : Divisor X) V := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · obtain ⟨vx, hvx⟩ := v
    obtain ⟨hbase, hev⟩ := Gext_chart_bridge F hvx
    rw [hbase]
    exact ((hF ⟨vx, hvx⟩).meromorphicAt).congr (hev.symm.filter_mono nhdsWithin_le_nhds)
  · obtain ⟨vx, hvx⟩ := v
    rw [ordU_eq_orderAt_Gext F hvx]
    simpa using (hF ⟨vx, hvx⟩).meromorphicOrderAt_nonneg

/-- **Local Cauchy–Riemann.** A function `ℝ`-differentiable at `x` whose planar `∂̄` vanishes there is
`ℂ`-differentiable at `x`. The `DifferentiableAt`-hypothesis (local) form of
`DbarDiskCohomology.differentiableAt_of_dbar_eq_zero`. -/
private theorem differentiableAt_complex_of_dbar_eq_zero {f : ℂ → ℂ} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) (hdb : DbarDisk.dbar f x = 0) : DifferentiableAt ℂ f x := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hf, ?_⟩
  have h2 : (fderiv ℝ f x) 1 + Complex.I * (fderiv ℝ f x) Complex.I = 0 := by
    have := hdb; rw [DbarDisk.dbar] at this; field_simp at this; linear_combination this
  have hD1 : (fderiv ℝ f x) 1 = -(Complex.I * (fderiv ℝ f x) Complex.I) := by linear_combination h2
  rw [hD1, smul_eq_mul, mul_neg, ← mul_assoc, Complex.I_mul_I]; ring

namespace ChartDiskCover

/-- The cutoff bump for disk `i`: `1` on the closed disk `closedBall (eᵢ) (radius i)` (so on `U_i`),
supported in `closedBall (eᵢ) R ⊆` target, with `R` from `exists_bumpOuterRadius`. -/
noncomputable def diskBump (𝔇 : ChartDiskCover X) (i : 𝔇.ι) :
    ContDiffBump (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) (𝔇.center i)) where
  rIn := 𝔇.radius i
  rOut := (𝔇.exists_bumpOuterRadius i).choose
  rIn_pos := 𝔇.radius_pos i
  rIn_lt_rOut := (𝔇.exists_bumpOuterRadius i).choose_spec.1

theorem diskBump_support_subset_target (𝔇 : ChartDiskCover X) (i : 𝔇.ι) :
    Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) (𝔇.center i)) (𝔇.diskBump i).rOut
      ⊆ (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).target :=
  (𝔇.exists_bumpOuterRadius i).choose_spec.2

/-- The **cutoff chart-pullback** of `g` over disk `i`: the planar function
`w ↦ χᵢ(w) · (g (eᵢ.symm w)) (frame 1)`. Smooth, compactly supported, `ℝ`-linear in `g`. -/
noncomputable def cutoffPullback (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g : SmoothCOneForms X) :
    ℂ → ℂ :=
  fun w => ((𝔇.diskBump i) w : ℝ) •
    (g ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm w))
      ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center i))
        ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm w)) (1 : ℂ))

theorem cutoffPullback_add (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g₁ g₂ : SmoothCOneForms X) :
    𝔇.cutoffPullback i (g₁ + g₂) = 𝔇.cutoffPullback i g₁ + 𝔇.cutoffPullback i g₂ := by
  funext w
  simp only [cutoffPullback, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, smul_add]

theorem cutoffPullback_smul (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (c : ℝ) (g : SmoothCOneForms X) :
    𝔇.cutoffPullback i (c • g) = c • 𝔇.cutoffPullback i g := by
  funext w
  simp only [cutoffPullback, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, smul_comm (𝔇.diskBump i w : ℝ) c]

/-- The cutoff chart-pullback is globally smooth (the bump `χᵢ` times the chart-read datum, which is
smooth on the chart target by `contMDiffAt_chartRead_datum`; outside the support `χᵢ = 0`). -/
theorem contDiff_cutoffPullback (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g : SmoothCOneForms X) :
    ContDiff ℝ (⊤ : ℕ∞) (𝔇.cutoffPullback i g) := by
  set x₀ := 𝔇.center i with hx₀
  set e₀ := extChartAt 𝓘(ℝ, ℂ) x₀ with he₀
  set χ := 𝔇.diskBump i with hχ
  set Φ : X → ℂ := fun y => (g y) ((Bundle.Trivialization.symmL ℝ
    (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) y) (1 : ℂ)) with hΦ
  have htgt_open : IsOpen e₀.target := by rw [he₀]; exact isOpen_extChartAt_target x₀
  have hΨ : ∀ w ∈ e₀.target, ContDiffAt ℝ (⊤ : ℕ∞) (fun w => Φ (e₀.symm w)) w := by
    intro w hw
    have hsymm_mem : e₀.symm w ∈ e₀.source := by rw [he₀]; exact PartialEquiv.map_target _ hw
    have hsymm : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) e₀.symm e₀.target w :=
      (contMDiffOn_extChartAt_symm x₀) _ hw
    have hΦat : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) Φ (e₀.symm w) :=
      contMDiffAt_chartRead_datum g x₀ (e₀.symm w) hsymm_mem
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun w => Φ (e₀.symm w)) e₀.target w :=
      hΦat.contMDiffWithinAt.comp w hsymm (fun z _ => Set.mem_univ _)
    exact contMDiffAt_iff_contDiffAt.mp (hcomp.contMDiffAt (htgt_open.mem_nhds hw))
  have hcut : 𝔇.cutoffPullback i g = fun w => (χ w : ℝ) • Φ (e₀.symm w) := rfl
  rw [hcut, contDiff_iff_contDiffAt]; intro w
  by_cases hw : w ∈ Metric.closedBall (e₀ x₀) χ.rOut
  · exact (χ.contDiff.contDiffAt).smul (hΨ w (𝔇.diskBump_support_subset_target i hw))
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    have hcompl : (Metric.closedBall (e₀ x₀) χ.rOut)ᶜ ∈ nhds w :=
      (Metric.isClosed_closedBall.isOpen_compl).mem_nhds hw
    filter_upwards [hcompl] with z hz
    have hz0 : χ z = 0 := by
      rw [← Function.notMem_support, χ.support_eq]
      exact fun h => hz (Metric.ball_subset_closedBall h)
    rw [hz0, zero_smul]

/-- The cutoff chart-pullback is compactly supported (in `closedBall (eᵢ) χᵢ.rOut`, outside which the
bump vanishes). -/
theorem hasCompactSupport_cutoffPullback (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g : SmoothCOneForms X) :
    HasCompactSupport (𝔇.cutoffPullback i g) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) (𝔇.center i)) (𝔇.diskBump i).rOut)
  intro z hz
  show ((𝔇.diskBump i) z : ℝ) • _ = 0
  have hz0 : (𝔇.diskBump i) z = 0 := by
    rw [← Function.notMem_support, (𝔇.diskBump i).support_eq]
    exact fun h => hz (Metric.ball_subset_closedBall h)
  rw [hz0, zero_smul]

/-! ### Step 4a — the planar primitive `cauchyTransform (cutoffPullback)` (linear, solves ∂̄) -/

/-- The **planar primitive** over disk `i`: the Cauchy transform of the cutoff chart-pullback. It is
the explicit `ℝ`-linear witness whose planar `∂̄` is the cutoff pullback everywhere (so equals the
chart-read `g` on `U_i`, where `χᵢ = 1`). -/
noncomputable def planarPrimitive (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g : SmoothCOneForms X) :
    ℂ → ℂ :=
  DbarDisk.cauchyTransform (𝔇.cutoffPullback i g)

theorem contDiff_planarPrimitive (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g : SmoothCOneForms X) :
    ContDiff ℝ (⊤ : ℕ∞) (𝔇.planarPrimitive i g) :=
  DbarDisk.contDiff_cauchyTransform (𝔇.contDiff_cutoffPullback i g)
    (𝔇.hasCompactSupport_cutoffPullback i g)

/-- The planar `∂̄` of the primitive is the cutoff pullback (Cauchy–Pompeiu). -/
theorem dbar_planarPrimitive (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g : SmoothCOneForms X) (z : ℂ) :
    DbarDisk.dbar (𝔇.planarPrimitive i g) z = 𝔇.cutoffPullback i g z := by
  rw [planarPrimitive,
    DbarDisk.dbar_cauchyTransform (𝔇.contDiff_cutoffPullback i g)
      (𝔇.hasCompactSupport_cutoffPullback i g) z,
    DbarDisk.cauchyPompeiu (𝔇.contDiff_cutoffPullback i g)
      (𝔇.hasCompactSupport_cutoffPullback i g) z]

theorem planarPrimitive_add (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g₁ g₂ : SmoothCOneForms X) :
    𝔇.planarPrimitive i (g₁ + g₂) = 𝔇.planarPrimitive i g₁ + 𝔇.planarPrimitive i g₂ := by
  rw [planarPrimitive, 𝔇.cutoffPullback_add i g₁ g₂,
    DbarDisk.cauchyTransform_add
      (𝔇.contDiff_cutoffPullback i g₁).continuous (𝔇.hasCompactSupport_cutoffPullback i g₁)
      (𝔇.contDiff_cutoffPullback i g₂).continuous (𝔇.hasCompactSupport_cutoffPullback i g₂)]
  rfl

theorem planarPrimitive_smul (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (c : ℝ) (g : SmoothCOneForms X) :
    𝔇.planarPrimitive i (c • g) = c • 𝔇.planarPrimitive i g := by
  rw [planarPrimitive, 𝔇.cutoffPullback_smul i c g, DbarDisk.cauchyTransform_smul]
  rfl

/-! ### Step 4b — the linear 0-cochain of disk primitives -/

/-- The disk-`i` primitive read back as a section on `U i`: `x ↦ planarPrimitive i g (eᵢ x)`. The
local `∂̄`-primitive `u_i` of `g` on the disk `U_i`. -/
noncomputable def diskSection (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g : SmoothCOneForms X) :
    𝔇.U i → ℂ :=
  fun x => 𝔇.planarPrimitive i g (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) x.1)

theorem diskSection_add (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (g₁ g₂ : SmoothCOneForms X) :
    𝔇.diskSection i (g₁ + g₂) = 𝔇.diskSection i g₁ + 𝔇.diskSection i g₂ := by
  funext x; simp only [diskSection, 𝔇.planarPrimitive_add, Pi.add_apply]

theorem diskSection_smul (𝔇 : ChartDiskCover X) (i : 𝔇.ι) (c : ℝ) (g : SmoothCOneForms X) :
    𝔇.diskSection i (c • g) = c • 𝔇.diskSection i g := by
  funext x; simp only [diskSection, 𝔇.planarPrimitive_smul, Pi.smul_apply]

/-! ### Step 4c — cross-chart cancellation: the cocycle is holomorphic on overlaps -/

/-- **Cross-chart cancellation (planar form).** On the overlap `U_i ⊓ U_j`, the difference of disk
primitives read in chart `i` — `z ↦ u_j(e_j(e_i⁻¹ z)) − u_i(z)` — has vanishing planar `∂̄` at `e_i x`
for every `x ∈ U_i ∩ U_j`. Mechanism: `∂̄(u_j∘τ) = conj(τ′)·(∂̄u_j ∘ τ)` (Wirtinger chain rule),
`∂̄u_i = cutoffPullback_i`, `∂̄u_j = cutoffPullback_j`; on the disks `χ = 1`, so these are
`g x (frameᵢ 1)` and `g x (frameⱼ 1)`; the `(0,1)` law turns them into `conj(frame)·(g x 1)`, the
frame is the inverse transition derivative, and the transition cocycle `A_j = τ′·A_i` cancels. -/
theorem dbar_planarDiff_eq_zero (𝔇 : ChartDiskCover X) {g : SmoothCOneForms X}
    (hg : g ∈ OneFormsZeroOne X) (i j : 𝔇.ι) {x : X}
    (hxi : x ∈ (𝔇.U i : Set X)) (hxj : x ∈ (𝔇.U j : Set X)) :
    DbarDisk.dbar (fun z => 𝔇.planarPrimitive j g
        ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)) ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm z))
        - 𝔇.planarPrimitive i g z)
      ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)) x) = 0 := by
  set ei := extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) with hei
  set ej := extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) with hej
  set ex := extChartAt 𝓘(ℝ, ℂ) x with hexx
  set z₀ := ei x with hz0
  set τ := ej ∘ ei.symm with hτ
  -- Source memberships and the chart round-trips.
  have hxsi : x ∈ ei.source := 𝔇.subset_chart_source i hxi
  have hxsj : x ∈ ej.source := 𝔇.subset_chart_source j hxj
  have hsymm_i : ei.symm z₀ = x := ei.left_inv hxsi
  have hτz₀ : τ z₀ = ej x := by rw [hτ, Function.comp_apply, hsymm_i]
  have hsymm_j : ej.symm (τ z₀) = x := by rw [hτz₀]; exact ej.left_inv hxsj
  -- chartAt-level facts for the general transition lemma.
  have hx_src_i : x ∈ (chartAt ℂ (𝔇.center i)).source := by
    rw [hei, extChartAt_source] at hxsi; exact hxsi
  have hx_src_j : x ∈ (chartAt ℂ (𝔇.center j)).source := by
    rw [hej, extChartAt_source] at hxsj; exact hxsj
  have hz0_eq : z₀ = (chartAt ℂ (𝔇.center i)) x := by rw [hz0, hei]; simp [mfld_simps]
  have hz0t : z₀ ∈ (chartAt ℂ (𝔇.center i)).target := by
    rw [hz0_eq]; exact (chartAt ℂ (𝔇.center i)).map_source hx_src_i
  have hsymm_chart : (chartAt ℂ (𝔇.center i)).symm z₀ ∈ (chartAt ℂ (𝔇.center j)).source := by
    rw [hz0_eq, (chartAt ℂ (𝔇.center i)).left_inv hx_src_i]; exact hx_src_j
  -- Differentiability of the transition `τ` at `z₀`, and of the primitives.
  have hτdiff : DifferentiableAt ℂ τ z₀ :=
    differentiableAt_transition_of_mem (𝔇.center j) (𝔇.center i) hz0t hsymm_chart
  have hppj_diff : ∀ w, DifferentiableAt ℝ (𝔇.planarPrimitive j g) w := fun w =>
    (𝔇.contDiff_planarPrimitive j g).differentiable (by norm_num) w
  have hppi_diff : ∀ w, DifferentiableAt ℝ (𝔇.planarPrimitive i g) w := fun w =>
    (𝔇.contDiff_planarPrimitive i g).differentiable (by norm_num) w
  -- `∂̄` of the difference splits; the first term via the Wirtinger chain rule.
  have hsub : ∀ (P Q : ℂ → ℂ), DifferentiableAt ℝ P z₀ → DifferentiableAt ℝ Q z₀ →
      DbarDisk.dbar (fun z => P z - Q z) z₀ = DbarDisk.dbar P z₀ - DbarDisk.dbar Q z₀ := by
    intro P Q hP hQ
    show DbarDisk.dbar (P - Q) z₀ = _
    unfold DbarDisk.dbar
    rw [fderiv_sub hP hQ]
    simp only [ContinuousLinearMap.sub_apply]; ring
  have hcomp_eq : (fun z => 𝔇.planarPrimitive j g (ej (ei.symm z)) - 𝔇.planarPrimitive i g z)
      = (fun z => (𝔇.planarPrimitive j g ∘ τ) z - 𝔇.planarPrimitive i g z) := rfl
  rw [hcomp_eq, hsub (𝔇.planarPrimitive j g ∘ τ) (𝔇.planarPrimitive i g)
        ((hppj_diff (τ z₀)).comp z₀ (hτdiff.restrictScalars ℝ)) (hppi_diff z₀),
      dbarDisk_comp_holo (𝔇.planarPrimitive j g) τ z₀ (hppj_diff (τ z₀)) hτdiff,
      𝔇.dbar_planarPrimitive j g (τ z₀), 𝔇.dbar_planarPrimitive i g z₀]
  -- Evaluate the two cutoff pullbacks: on the disks `χ = 1`, leaving `g x (frame 1)`.
  have hballi : ei x ∈ Metric.ball (ei (𝔇.center i)) (𝔇.radius i) := by
    have h := hxi; rw [𝔇.isDisk i] at h; exact h.1
  have hballj : ej x ∈ Metric.ball (ej (𝔇.center j)) (𝔇.radius j) := by
    have h := hxj; rw [𝔇.isDisk j] at h; exact h.1
  have hχi : (𝔇.diskBump i) z₀ = 1 :=
    (𝔇.diskBump i).one_of_mem_closedBall (by rw [hz0]; exact Metric.ball_subset_closedBall hballi)
  have hχj : (𝔇.diskBump j) (τ z₀) = 1 :=
    (𝔇.diskBump j).one_of_mem_closedBall (by rw [hτz₀]; exact Metric.ball_subset_closedBall hballj)
  rw [show 𝔇.cutoffPullback j g (τ z₀) = ((𝔇.diskBump j) (τ z₀) : ℝ) •
      (g (ej.symm (τ z₀))) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center j)) (ej.symm (τ z₀))) (1 : ℂ)) from rfl,
    show 𝔇.cutoffPullback i g z₀ = ((𝔇.diskBump i) z₀ : ℝ) •
      (g (ei.symm z₀)) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center i)) (ei.symm z₀)) (1 : ℂ)) from rfl,
    hχi, hχj, hsymm_i, hsymm_j, one_smul, one_smul,
    frameVector_eq_inv_deriv_transition (𝔇.center i) x hxsi,
    frameVector_eq_inv_deriv_transition (𝔇.center j) x hxsj]
  -- Abbreviate the two inverse transition derivatives; apply the `(0,1)` conjugate-linearity law.
  set Ai := deriv (ei ∘ ex.symm) (ex x) with hAi
  set Aj := deriv (ej ∘ ex.symm) (ex x) with hAj
  rw [oneForm_apply_conjLinear hg x Aj⁻¹, oneForm_apply_conjLinear hg x Ai⁻¹]
  -- The transition cocycle `Aj = (deriv τ z₀) · Ai` (chain rule on `ej∘ex.symm = τ∘(ei∘ex.symm)`).
  have hψdiff : DifferentiableAt ℂ (ei ∘ ex.symm) (ex x) :=
    differentiableAt_chartTransition (𝔇.center i) x hxsi
  have hψpt : (ei ∘ ex.symm) (ex x) = z₀ := by
    rw [Function.comp_apply, hexx, extChartAt_to_inv, hz0]
  have hev : (ej ∘ ex.symm) =ᶠ[nhds (ex x)] (τ ∘ (ei ∘ ex.symm)) := by
    have htgt : ∀ᶠ z in nhds (ex x), z ∈ ex.target := by
      rw [hexx]; exact (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
    have hmem : ∀ᶠ z in nhds (ex x), ex.symm z ∈ ei.source := by
      have hcont : ContinuousAt ex.symm (ex x) := continuousAt_extChartAt_symm x
      refine hcont.preimage_mem_nhds ?_
      rw [hexx, extChartAt_to_inv]; exact (isOpen_extChartAt_source (𝔇.center i)).mem_nhds hxsi
    filter_upwards [htgt, hmem] with z hztgt hzsrc
    simp only [hτ, Function.comp_apply, ei.left_inv hzsrc]
  have hcocycle : Aj = deriv τ z₀ * Ai := by
    rw [hAi, hAj, hev.deriv_eq, deriv_comp (ex x) (hψpt ▸ hτdiff) hψdiff, hψpt]
  -- Nonvanishing: the two frame derivatives are nonzero, hence so is `deriv τ z₀`.
  have hAi0 : Ai ≠ 0 := deriv_chartTransition_ne_zero (𝔇.center i) x hxsi
  have hAj0 : Aj ≠ 0 := deriv_chartTransition_ne_zero (𝔇.center j) x hxsj
  have hτ0 : deriv τ z₀ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hcocycle; exact hAj0 hcocycle
  -- Final algebra: `conj(τ′)·conj(Aj⁻¹) = conj(Ai⁻¹)`, so the two terms cancel.
  rw [hcocycle]
  have hAic : (starRingEnd ℂ) Ai ≠ 0 := by rwa [map_ne_zero]
  have hτc : (starRingEnd ℂ) (deriv τ z₀) ≠ 0 := by rwa [map_ne_zero]
  simp only [map_inv₀, map_mul]
  field_simp
  ring

/-- **The disk primitive solves `∂̄ = g` intrinsically on `U_k`.** For `x ∈ U_k`, the intrinsic
Wirtinger scalar of the disk-primitive *value function* `wₖ = planarPrimitive k g ∘ e_k` equals
`g x 1` — i.e. `∂̄wₖ = g` at `x`. Mechanism (single-chart, mirroring `dbar_planarDiffH_eq_zero`): the
generalized bridge `dbar_apply_one_eq_dbarDisk'` reads `∂̄wₖ` in `x`'s own chart as
`DbarDisk.dbar (planarPrimitive k g ∘ τ')` (`τ' = e_k ∘ eₓ.symm`); the Wirtinger chain rule
`dbarDisk_comp_holo` peels a `conj(deriv τ')` factor; `dbar_planarPrimitive` gives the cutoff pullback
(`χ = 1` on the disk), and `frameVector_eq_deriv_transition_symm` + `oneForm_apply_conjLinear`
introduce a second `conj(deriv σ)` factor (`σ = eₓ ∘ e_k.symm`). The two cancel because `σ ∘ τ' = id`
(`deriv σ · deriv τ' = 1`), leaving exactly `g x 1`. -/
theorem dbar_diskValue_eq_g (𝔇 : ChartDiskCover X) {g : SmoothCOneForms X}
    (hg : g ∈ OneFormsZeroOne X) (k : 𝔇.ι) {x : X} (hxk : x ∈ (𝔇.U k : Set X)) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        (fun y => 𝔇.planarPrimitive k g ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center k)) y)) x) (1 : ℂ)
      = (g x) (1 : ℂ) := by
  set ek := extChartAt 𝓘(ℝ, ℂ) (𝔇.center k) with hek
  set ex := extChartAt 𝓘(ℝ, ℂ) x with hexx
  set wk : X → ℂ := fun y => 𝔇.planarPrimitive k g (ek y) with hwk
  set z₀ := ek x with hz0
  set τ' := ek ∘ ex.symm with hτ'
  set σ := ex ∘ ek.symm with hσ
  have hxsk : x ∈ ek.source := 𝔇.subset_chart_source k hxk
  have hx_src_k : x ∈ (chartAt ℂ (𝔇.center k)).source := by rw [hek, extChartAt_source] at hxsk; exact hxsk
  -- `wₖ` is `MDifferentiableAt x` (`e_k` smooth at `x ∈ source`, `planarPrimitive` is `C^∞`).
  have hekmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ek x :=
    ((contMDiffOn_extChartAt (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := 𝔇.center k) x hx_src_k).contMDiffAt
      ((chartAt ℂ (𝔇.center k)).open_source.mem_nhds hx_src_k)).mdifferentiableAt (by simp)
  have hppmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.planarPrimitive k g) (ek x) :=
    ((𝔇.contDiff_planarPrimitive k g).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hwkmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) wk x := hppmd.comp x hekmd
  -- Read the intrinsic `∂̄` in `x`'s own chart; the pullback is `planarPrimitive k g ∘ τ'`.
  rw [dbar_apply_one_eq_dbarDisk' hwkmd]
  have hcomp : (fun z => wk (ex.symm z)) = (𝔇.planarPrimitive k g) ∘ τ' := by
    funext z; simp only [hwk, hτ', Function.comp_apply]
  rw [hcomp]
  -- The transition `τ'` is holomorphic at `eₓ x`, with `τ' (eₓ x) = z₀`.
  have hτ'pt : τ' (ex x) = z₀ := by
    rw [hτ', Function.comp_apply, hexx, extChartAt_to_inv]
  have hτ'diff : DifferentiableAt ℂ τ' (ex x) := by
    rw [hτ', hexx, hek]; exact differentiableAt_chartTransition (𝔇.center k) x hxsk
  rw [dbarDisk_comp_holo (𝔇.planarPrimitive k g) τ' (ex x)
        ((𝔇.contDiff_planarPrimitive k g).differentiable (by norm_num) _) hτ'diff, hτ'pt,
      𝔇.dbar_planarPrimitive k g z₀]
  -- The cutoff is `1` on the disk; the frame law + `(0,1)`-conjugate-linearity give the second factor.
  have hχk : (𝔇.diskBump k) z₀ = 1 := by
    have h' := hxk; rw [𝔇.isDisk k] at h'
    exact (𝔇.diskBump k).one_of_mem_closedBall (by rw [hz0]; exact Metric.ball_subset_closedBall h'.1)
  have hsymm_k : ek.symm z₀ = x := ek.left_inv hxsk
  rw [show 𝔇.cutoffPullback k g z₀ = ((𝔇.diskBump k) z₀ : ℝ) •
      (g (ek.symm z₀)) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center k)) (ek.symm z₀)) (1 : ℂ)) from rfl,
    hχk, hsymm_k, one_smul, frameVector_eq_deriv_transition_symm (𝔇.center k) x hxsk,
    oneForm_apply_conjLinear hg x (deriv σ z₀)]
  -- `σ ∘ τ' = id` near `eₓ x`, so `deriv σ z₀ · deriv τ' (eₓ x) = 1`.
  have hσdiff : DifferentiableAt ℂ σ z₀ := by
    rw [hσ, hz0, hexx, hek]; exact differentiableAt_chartTransition_symm (𝔇.center k) x hxsk
  have hev : (σ ∘ τ') =ᶠ[nhds (ex x)] id := by
    have hcont : ContinuousAt ex.symm (ex x) := continuousAt_extChartAt_symm x
    have hmem : ∀ᶠ z in nhds (ex x), ex.symm z ∈ ek.source := by
      refine hcont.preimage_mem_nhds ?_
      rw [hexx, extChartAt_to_inv]; exact (isOpen_extChartAt_source (𝔇.center k)).mem_nhds hxsk
    have htgt : ∀ᶠ z in nhds (ex x), z ∈ ex.target := by
      rw [hexx]; exact (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
    filter_upwards [hmem, htgt] with z hzmem hztgt
    simp only [hσ, hτ', Function.comp_apply, id_eq, ek.left_inv hzmem, ex.right_inv hztgt]
  have hone : deriv σ z₀ * deriv τ' (ex x) = 1 := by
    have hd := hev.deriv_eq
    rw [deriv_comp (ex x) (hτ'pt ▸ hσdiff) hτ'diff, hτ'pt] at hd
    simpa using hd
  have hconj : (starRingEnd ℂ) (deriv τ' (ex x)) * (starRingEnd ℂ) (deriv σ z₀) = 1 := by
    rw [← map_mul, mul_comm, hone, map_one]
  rw [← mul_assoc, hconj, one_mul]

/-- The chart-`i` read of the cochain difference is **holomorphic** (`ℂ`-differentiable) at `e_i x`
for `x ∈ U_i ⊓ U_j`: Lemma A `dbar_planarDiff_eq_zero` (`∂̄ = 0`) + local smoothness (the transition
is holomorphic, the primitives are `C^∞`) via local Cauchy–Riemann. -/
theorem differentiableAt_planarDiff (𝔇 : ChartDiskCover X) {g : SmoothCOneForms X}
    (hg : g ∈ OneFormsZeroOne X) (i j : 𝔇.ι) {x : X}
    (hxi : x ∈ (𝔇.U i : Set X)) (hxj : x ∈ (𝔇.U j : Set X)) :
    DifferentiableAt ℂ (fun z => 𝔇.planarPrimitive j g
        ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)) ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm z))
        - 𝔇.planarPrimitive i g z)
      ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)) x) := by
  set ei := extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) with hei
  set ej := extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) with hej
  set z₀ := ei x with hz0
  set τ := ej ∘ ei.symm with hτ
  have hxsi : x ∈ ei.source := 𝔇.subset_chart_source i hxi
  have hxsj : x ∈ ej.source := 𝔇.subset_chart_source j hxj
  have hx_src_i : x ∈ (chartAt ℂ (𝔇.center i)).source := by rw [hei, extChartAt_source] at hxsi; exact hxsi
  have hx_src_j : x ∈ (chartAt ℂ (𝔇.center j)).source := by rw [hej, extChartAt_source] at hxsj; exact hxsj
  have hz0_eq : z₀ = (chartAt ℂ (𝔇.center i)) x := by rw [hz0, hei]; simp [mfld_simps]
  have hz0t : z₀ ∈ (chartAt ℂ (𝔇.center i)).target := by
    rw [hz0_eq]; exact (chartAt ℂ (𝔇.center i)).map_source hx_src_i
  have hsymm_chart : (chartAt ℂ (𝔇.center i)).symm z₀ ∈ (chartAt ℂ (𝔇.center j)).source := by
    rw [hz0_eq, (chartAt ℂ (𝔇.center i)).left_inv hx_src_i]; exact hx_src_j
  have hτdiff : DifferentiableAt ℂ τ z₀ :=
    differentiableAt_transition_of_mem (𝔇.center j) (𝔇.center i) hz0t hsymm_chart
  have hppj : DifferentiableAt ℝ (𝔇.planarPrimitive j g) (τ z₀) :=
    (𝔇.contDiff_planarPrimitive j g).differentiable (by norm_num) (τ z₀)
  have hppi : DifferentiableAt ℝ (𝔇.planarPrimitive i g) z₀ :=
    (𝔇.contDiff_planarPrimitive i g).differentiable (by norm_num) z₀
  have hHr : DifferentiableAt ℝ
      (fun z => 𝔇.planarPrimitive j g (ej (ei.symm z)) - 𝔇.planarPrimitive i g z) z₀ :=
    (hppj.comp z₀ (hτdiff.restrictScalars ℝ)).sub hppi
  exact differentiableAt_complex_of_dbar_eq_zero hHr (𝔇.dbar_planarDiff_eq_zero hg i j hxi hxj)

/-- **Second cancellation (the `∂̄`-image is a coboundary).** For a global potential `h`, the chart-`i`
read of `u_i − h` (with `u_i = planarPrimitive i (∂̄h)`) has vanishing planar `∂̄` at `e_i x`: both are
`∂̄`-primitives of `∂̄h`. Mechanism mirrors Lemma A — `∂̄u_i = cutoffPullback i (∂̄h)`, while
`∂̄(h∘e_i.symm) = conj(deriv σ)·(∂̄h x 1)` via the Wirtinger chain rule + the own-chart bridge
`dbar_apply_one_eq_dbarDisk`; the *direct* frame form `frameVector_eq_deriv_transition_symm` makes the
two equal (no inverse-derivative needed). -/
theorem dbar_planarDiffH_eq_zero (𝔇 : ChartDiskCover X) (h : SmoothCFunctions X) (i : 𝔇.ι) {x : X}
    (hxi : x ∈ (𝔇.U i : Set X)) :
    DbarDisk.dbar (fun z => 𝔇.planarPrimitive i (dbarL h) z
        - h ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm z))
      ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)) x) = 0 := by
  set ei := extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) with hei
  set ex := extChartAt 𝓘(ℝ, ℂ) x with hexx
  set z₀ := ei x with hz0
  set σ := ex ∘ ei.symm with hσ
  have hxsi : x ∈ ei.source := 𝔇.subset_chart_source i hxi
  have hz0tgt : z₀ ∈ ei.target := by rw [hz0]; exact ei.map_source hxsi
  have hsymm_i : ei.symm z₀ = x := ei.left_inv hxsi
  have hσdiff : DifferentiableAt ℂ σ z₀ := by
    rw [hσ, hz0, hei, hexx]; exact differentiableAt_chartTransition_symm (𝔇.center i) x hxsi
  -- `B = h ∘ e_i.symm` is smooth at `z₀`.
  have hBdiff : DifferentiableAt ℝ (fun z => h (ei.symm z)) z₀ := by
    have hsymm : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) ei.symm ei.target z₀ :=
      (contMDiffOn_extChartAt_symm (𝔇.center i)) _ hz0tgt
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun z => h (ei.symm z)) ei.target z₀ :=
      (h.contMDiff (ei.symm z₀)).contMDiffWithinAt.comp z₀ hsymm (fun _ _ => Set.mem_univ _)
    exact (contMDiffAt_iff_contDiffAt.mp
      (hcomp.contMDiffAt ((isOpen_extChartAt_target (𝔇.center i)).mem_nhds hz0tgt))).differentiableAt
      (by norm_num)
  have hsub : DbarDisk.dbar (fun z => 𝔇.planarPrimitive i (dbarL h) z - h (ei.symm z)) z₀
      = DbarDisk.dbar (𝔇.planarPrimitive i (dbarL h)) z₀
        - DbarDisk.dbar (fun z => h (ei.symm z)) z₀ := by
    show DbarDisk.dbar (𝔇.planarPrimitive i (dbarL h) - fun z => h (ei.symm z)) z₀ = _
    unfold DbarDisk.dbar
    rw [fderiv_sub ((𝔇.contDiff_planarPrimitive i (dbarL h)).differentiable (by norm_num) z₀) hBdiff]
    simp only [ContinuousLinearMap.sub_apply]; ring
  -- `∂̄(h∘e_i.symm) = conj(deriv σ)·∂̄h(x)(1)` via chart change + own-chart bridge.
  have hσpt : σ z₀ = ex x := by rw [hσ, Function.comp_apply, hsymm_i]
  have hBxdiff : DifferentiableAt ℝ (fun z => h (ex.symm z)) (σ z₀) := by
    rw [hσpt]
    have hxtgt : ex x ∈ ex.target := by rw [hexx]; exact mem_extChartAt_target x
    have hsymm : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) ex.symm ex.target (ex x) :=
      (contMDiffOn_extChartAt_symm x) _ hxtgt
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun z => h (ex.symm z)) ex.target (ex x) :=
      (h.contMDiff (ex.symm (ex x))).contMDiffWithinAt.comp (ex x) hsymm (fun _ _ => Set.mem_univ _)
    exact (contMDiffAt_iff_contDiffAt.mp
      (hcomp.contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hxtgt))).differentiableAt (by norm_num)
  have hBval : DbarDisk.dbar (fun z => h (ei.symm z)) z₀
      = (starRingEnd ℂ) (deriv σ z₀) * proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑h) x) 1 := by
    have hev : (fun z => h (ei.symm z)) =ᶠ[nhds z₀] ((fun z => h (ex.symm z)) ∘ σ) := by
      have hcont : ContinuousAt ei.symm z₀ :=
        (continuousOn_extChartAt_symm (𝔇.center i)).continuousAt
          ((isOpen_extChartAt_target (𝔇.center i)).mem_nhds hz0tgt)
      have hmem : ∀ᶠ z in nhds z₀, ei.symm z ∈ ex.source := by
        refine hcont.preimage_mem_nhds ?_
        rw [hsymm_i, hexx]; exact (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
      filter_upwards [hmem] with z hz
      show h (ei.symm z) = h (ex.symm (σ z))
      rw [hσ, Function.comp_apply, ex.left_inv hz]
    rw [dbarDisk_congr hev,
      dbarDisk_comp_holo (fun z => h (ex.symm z)) σ z₀ hBxdiff hσdiff, hσpt,
      ← dbar_apply_one_eq_dbarDisk h x]
  rw [hsub, 𝔇.dbar_planarPrimitive i (dbarL h) z₀, hBval,
    show 𝔇.cutoffPullback i (dbarL h) z₀ = ((𝔇.diskBump i) z₀ : ℝ) •
      ((dbarL h) (ei.symm z₀)) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center i)) (ei.symm z₀)) (1 : ℂ)) from rfl]
  have hχi : (𝔇.diskBump i) z₀ = 1 := by
    have h' := hxi; rw [𝔇.isDisk i] at h'
    exact (𝔇.diskBump i).one_of_mem_closedBall (by rw [hz0]; exact Metric.ball_subset_closedBall h'.1)
  have hdbarL : (dbarL h) x (1 : ℂ) = proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑h) x) (1 : ℂ) := rfl
  rw [hχi, hsymm_i, one_smul, frameVector_eq_deriv_transition_symm (𝔇.center i) x hxsi,
    oneForm_apply_conjLinear (dbarL_mem_zeroOne h) x (deriv σ z₀), hdbarL]
  ring

/-- The chart-`i` read of `u_i − h` is holomorphic at `e_i x` (`dbar_planarDiffH_eq_zero` + local
smoothness + local Cauchy–Riemann). The single-chart analogue of `differentiableAt_planarDiff`. -/
theorem differentiableAt_planarDiffH (𝔇 : ChartDiskCover X) (h : SmoothCFunctions X) (i : 𝔇.ι)
    {x : X} (hxi : x ∈ (𝔇.U i : Set X)) :
    DifferentiableAt ℂ (fun z => 𝔇.planarPrimitive i (dbarL h) z
        - h ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm z))
      ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)) x) := by
  set ei := extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) with hei
  set z₀ := ei x with hz0
  have hxsi : x ∈ ei.source := 𝔇.subset_chart_source i hxi
  have hz0tgt : z₀ ∈ ei.target := by rw [hz0]; exact ei.map_source hxsi
  have hBdiff : DifferentiableAt ℝ (fun z => h (ei.symm z)) z₀ := by
    have hsymm : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) ei.symm ei.target z₀ :=
      (contMDiffOn_extChartAt_symm (𝔇.center i)) _ hz0tgt
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun z => h (ei.symm z)) ei.target z₀ :=
      (h.contMDiff (ei.symm z₀)).contMDiffWithinAt.comp z₀ hsymm (fun _ _ => Set.mem_univ _)
    exact (contMDiffAt_iff_contDiffAt.mp
      (hcomp.contMDiffAt ((isOpen_extChartAt_target (𝔇.center i)).mem_nhds hz0tgt))).differentiableAt
      (by norm_num)
  exact differentiableAt_complex_of_dbar_eq_zero
    (((𝔇.contDiff_planarPrimitive i (dbarL h)).differentiable (by norm_num) z₀).sub hBdiff)
    (𝔇.dbar_planarDiffH_eq_zero h i hxi)

/-- `Gext (u_i − h)`, read in each point's own chart, is analytic — single-chart analogue of
`gext_diff_analyticAt` (using `differentiableAt_planarDiffH`). -/
theorem gextH_diff_analyticAt (𝔇 : ChartDiskCover X) (h : SmoothCFunctions X) (i : 𝔇.ι)
    (F : ↥(𝔇.U i) → ℂ)
    (hFeq : ∀ v : ↥(𝔇.U i), F v
      = 𝔇.planarPrimitive i (dbarL h) (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) v.1) - h v.1)
    (w : ↥(𝔇.U i)) :
    AnalyticAt ℂ (Gext F ∘ (chartAt (H := ℂ) (w : X)).symm) ((chartAt (H := ℂ) (w : X)) (w : X)) := by
  obtain ⟨wx, hwx⟩ := w
  refine analyticAt_chart_change (y := 𝔇.center i) ?_ ?_
  · have := 𝔇.subset_chart_source i hwx; rwa [extChartAt_source] at this
  · set ci := chartAt (H := ℂ) (𝔇.center i) with hci
    set Hi : ℂ → ℂ := fun z => 𝔇.planarPrimitive i (dbarL h) z
      - h ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm z) with hHi
    set W : Set ℂ := ci.target ∩ ci.symm ⁻¹' ((𝔇.U i : TopologicalSpace.Opens X) : Set X) with hWdef
    have hwsrc : wx ∈ ci.source := by
      have := 𝔇.subset_chart_source i hwx; rwa [extChartAt_source] at this
    have hWopen : IsOpen W := ci.isOpen_inter_preimage_symm (𝔇.U i).isOpen
    have hmemW : ci wx ∈ W :=
      ⟨ci.map_source hwsrc, by simp only [Set.mem_preimage, ci.left_inv hwsrc]; exact hwx⟩
    have hcoe : ∀ p : X, (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)) p = ci p := fun p => by simp [hci, mfld_simps]
    have hcoesymm : ∀ q : ℂ, (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm q = ci.symm q := fun q => by
      simp [hci, mfld_simps]
    have hHiOn : DifferentiableOn ℂ Hi W := by
      intro z hz
      have hzV : ci.symm z ∈ ((𝔇.U i : TopologicalSpace.Opens X) : Set X) := hz.2
      have hd := 𝔇.differentiableAt_planarDiffH h i hzV
      rw [hcoe (ci.symm z), ci.right_inv hz.1] at hd
      exact hd.differentiableWithinAt
    have hEq : Set.EqOn (Gext F ∘ ci.symm) Hi W := by
      intro z hz
      have hzV : ci.symm z ∈ ((𝔇.U i : TopologicalSpace.Opens X) : Set X) := hz.2
      simp only [Function.comp_apply, Gext_apply_mem F hzV, hFeq, hHi, hcoesymm,
        hcoe (ci.symm z), ci.right_inv hz.1]
    exact (hHiOn.congr hEq).analyticAt (hWopen.mem_nhds hmemW)

/-- The **linear 0-cochain of disk primitives**: `g ↦ (i ↦ [u_i])`, the germ-classes of the local
`∂̄`-primitives. `ℝ`-linear in `g` (via `planarPrimitive` linearity + `toGerm`). Its `cechDelta0` is
the Dolbeault → Čech cocycle. -/
noncomputable def rawCochain (𝔇 : ChartDiskCover X) :
    SmoothCOneForms X →ₗ[ℝ] 𝔇.toFiniteCover.Cochain0 where
  toFun g i := toGerm (𝔇.U i) (𝔇.diskSection i g)
  map_add' g₁ g₂ := by
    funext i
    simp only [Pi.add_apply, 𝔇.diskSection_add]
    exact map_add (toGerm (𝔇.U i)) (𝔇.diskSection i g₁) (𝔇.diskSection i g₂)
  map_smul' c g := by
    funext i
    simp only [RingHom.id_apply, Pi.smul_apply, 𝔇.diskSection_smul]
    exact (toGerm (𝔇.U i)).map_smul_of_tower c (𝔇.diskSection i g)

/-! ### Step 4d — the cocycle lands in `cocycles1 0`, and the operator `dolbeaultToCechCocycle` -/

/-- The cochain difference `F = u_j − u_i` on the overlap `V = U_i ⊓ U_j`, read in *each point's own*
chart via the extension-by-zero `Gext`, is analytic there. Chart-`i` holomorphy
(`differentiableAt_planarDiff`, an open `DifferentiableOn` ⟹ `AnalyticAt`) transported to the point's
own chart by `analyticAt_chart_change`. The hypothesis on `F` is its overlap value. -/
theorem gext_diff_analyticAt (𝔇 : ChartDiskCover X) {g : SmoothCOneForms X}
    (hg : g ∈ OneFormsZeroOne X) (i j : 𝔇.ι) (F : ↥(𝔇.U i ⊓ 𝔇.U j) → ℂ)
    (hFeq : ∀ w : ↥(𝔇.U i ⊓ 𝔇.U j), F w = 𝔇.planarPrimitive j g (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) w.1)
        - 𝔇.planarPrimitive i g (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i) w.1))
    (w : ↥(𝔇.U i ⊓ 𝔇.U j)) :
    AnalyticAt ℂ (Gext F ∘ (chartAt (H := ℂ) (w : X)).symm) ((chartAt (H := ℂ) (w : X)) (w : X)) := by
  obtain ⟨wx, hwx⟩ := w
  refine analyticAt_chart_change (y := 𝔇.center i) ?_ ?_
  · have := 𝔇.subset_chart_source i hwx.1; rwa [extChartAt_source] at this
  · set ci := chartAt (H := ℂ) (𝔇.center i) with hci
    set Hi : ℂ → ℂ := fun z => 𝔇.planarPrimitive j g
        ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)) ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm z))
        - 𝔇.planarPrimitive i g z with hHi
    set W : Set ℂ := ci.target ∩ ci.symm ⁻¹' ((𝔇.U i ⊓ 𝔇.U j : TopologicalSpace.Opens X) : Set X)
      with hWdef
    have hwsrc : wx ∈ ci.source := by
      have := 𝔇.subset_chart_source i hwx.1; rwa [extChartAt_source] at this
    have hWopen : IsOpen W := ci.isOpen_inter_preimage_symm (𝔇.U i ⊓ 𝔇.U j).isOpen
    have hmemW : ci wx ∈ W :=
      ⟨ci.map_source hwsrc, by simp only [Set.mem_preimage, ci.left_inv hwsrc]; exact hwx⟩
    have hcoe : ∀ p : X, (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)) p = ci p := fun p => by
      simp [hci, mfld_simps]
    have hcoesymm : ∀ q : ℂ, (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).symm q = ci.symm q := fun q => by
      simp [hci, mfld_simps]
    have hHiOn : DifferentiableOn ℂ Hi W := by
      intro z hz
      have hzV : ci.symm z ∈ ((𝔇.U i ⊓ 𝔇.U j : TopologicalSpace.Opens X) : Set X) := hz.2
      have hd := 𝔇.differentiableAt_planarDiff hg i j hzV.1 hzV.2
      rw [hcoe (ci.symm z), ci.right_inv hz.1] at hd
      exact hd.differentiableWithinAt
    have hEq : Set.EqOn (Gext F ∘ ci.symm) Hi W := by
      intro z hz
      have hzV : ci.symm z ∈ ((𝔇.U i ⊓ 𝔇.U j : TopologicalSpace.Opens X) : Set X) := hz.2
      simp only [Function.comp_apply, Gext_apply_mem F hzV, hFeq, hHi, hcoesymm,
        hcoe (ci.symm z), ci.right_inv hz.1]
    exact (hHiOn.congr hEq).analyticAt (hWopen.mem_nhds hmemW)

/-- **The cocycle lands in `Z¹(𝒪)`.** `cechDelta0 (rawCochain g)` is a Čech `1`-cocycle of `𝒪`: it is
in `ker cechDelta1` (any germ cochain) and its overlap germs are holomorphic
(`gext_diff_analyticAt` + the `mem_OmegaD_zero_of_gext_analytic` bridge). Needs `g` a `(0,1)`-form
(the conjugate-linearity used by Lemma A). -/
theorem cechDelta0_rawCochain_mem_cocycles1 (𝔇 : ChartDiskCover X) {g : SmoothCOneForms X}
    (hg : g ∈ OneFormsZeroOne X) :
    𝔇.toFiniteCover.cechDelta0 (𝔇.rawCochain g) ∈ 𝔇.toFiniteCover.cocycles1 (0 : Divisor X) := by
  refine Submodule.mem_inf.2 ⟨cechDelta0_mem_ker_cechDelta1 _ _, fun p => ?_⟩
  obtain ⟨i, j⟩ := p
  set F : ↥(𝔇.U i ⊓ 𝔇.U j) → ℂ :=
    𝔇.diskSection j g ∘ openIncl inf_le_right - 𝔇.diskSection i g ∘ openIncl inf_le_left with hFdef
  have hcomp : 𝔇.toFiniteCover.cechDelta0 (𝔇.rawCochain g) (i, j) = toGerm (𝔇.U i ⊓ 𝔇.U j) F := by
    simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    rw [show 𝔇.rawCochain g j = toGerm (𝔇.U j) (𝔇.diskSection j g) from rfl,
      show 𝔇.rawCochain g i = toGerm (𝔇.U i) (𝔇.diskSection i g) from rfl,
      rawRestrictG_coe, rawRestrictG_coe, ← map_sub]
  rw [hcomp]
  refine ⟨F, mem_OmegaD_zero_of_gext_analytic (fun w => 𝔇.gext_diff_analyticAt hg i j F (fun w => ?_) w), rfl⟩
  simp only [hFdef, Pi.sub_apply, Function.comp_apply, openIncl, diskSection]

end ChartDiskCover

/-- **(Analytic sub-kernel.)** Local `∂̄`-solvability on the manifold: any smooth `(0,1)`-form `g`
(in `OneFormsZeroOne X`) is, near every point `x₀`, the `∂̄` of a smooth function `u`. Proven
**completely** from the value-`1` local primitive `exists_localPrimitive_apply_one` (the finer
sub-kernel) via the value-`1`-to-CLM upgrade `dbar_eq_of_apply_one`: the full intrinsic CLM equation
`dbar u x = g x` follows because both sides are `(0,1)`-forms determined by their Wirtinger scalar.
The local primitives `u` it produces are the `u_i` whose differences `u_i − u_j` are the
Dolbeault → Čech cocycle. -/
theorem dbar_solvable_locally_manifold (g : SmoothCOneForms X) (hg : g ∈ OneFormsZeroOne X)
    (x₀ : X) :
    ∃ (V : Set X) (u : SmoothCFunctions X), IsOpen V ∧ x₀ ∈ V ∧ ∀ x ∈ V, (dbar u) x = g x := by
  obtain ⟨V, u, hV, hx₀, hval⟩ := exists_localPrimitive_apply_one g hg x₀
  exact ⟨V, u, hV, hx₀, fun x hx => dbar_eq_of_apply_one hg u x (hval x hx)⟩

/-! ### Dolbeault → Čech: the genuine PDE content, isolated; the quotient assembly, complete

The map `[g] ↦ [{u_i − u_j}]` factors through the Čech cocycle group. We isolate the *only* analytic
content — a **linear** global `∂̄`-solution operator over the (Leray) cover — as the named kernel
`dolbeaultToCechCocycle` (the cochain `{[u_i]}` of germ-classes of local primitives `∂̄u_i = g`,
linear in `g`, whose `cechDelta0` is automatically a holomorphic cocycle), plus its
well-definedness fact `dolbeaultToCechCocycle_dbarImage_le` (the `∂̄`-image maps to a coboundary).
The cohomological assembly — lifting through the two quotients `DolbeaultH01 = A^{0,1}/im ∂̄` and
`cechH1 = Z¹/B¹`, with the `ℂ→ℝ` scalar restriction — is then **complete** (`Submodule.liftQ`).
-/

set_option maxHeartbeats 1000000 in
/-- **(Analytic sub-kernel — the Dolbeault → Čech cocycle operator.)** The `ℝ`-linear map sending a
`(0,1)`-form `g ∈ A^{0,1}` to the Čech `1`-cocycle `{[u_j] − [u_i]} = cechDelta0 {[u_i]} ∈ Z¹(𝔘, 𝒪)`,
where `u_i` solves `∂̄u_i = g` on the (simply-connected / disk) cover set `U_i`.

This packages the *only* PDE content of the Dolbeault → Čech direction: **global** `∂̄`-solvability on
each Leray cover set (`DbarLocal.dbar_solvable_locally` only gives a *point*-neighborhood; the
disk-global solve, via the Cauchy transform, is what is needed) — crucially **linear in `g`** (the
Cauchy-transform solution operator is linear), so the whole assignment is `ℝ`-linear. The output
lands in `cocycles1` because (i) `cechDelta0 c ∈ ker cechDelta1` for *any* germ-class cochain `c`
(`cechDelta0_mem_ker_cechDelta1`, complete), and (ii) on each overlap `U_i ∩ U_j` the difference
`u_j − u_i` is **holomorphic** (`∂̄(u_j − u_i) = g − g = 0`), so `cechDelta0 {[u_i]} ∈ sections1 0`. -/
noncomputable def dolbeaultToCechCocycle (𝔇 : ChartDiskCover X) :
    ↥(OneFormsZeroOne X) →ₗ[ℝ] ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)) :=
  LinearMap.codRestrict ((𝔇.toFiniteCover.cocycles1 0).restrictScalars ℝ)
    ((𝔇.toFiniteCover.cechDelta0.restrictScalars ℝ) ∘ₗ 𝔇.rawCochain ∘ₗ (OneFormsZeroOne X).subtype)
    (fun v => by
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.restrictScalars_mem]
      exact 𝔇.cechDelta0_rawCochain_mem_cocycles1 v.2)

/-- **(Analytic sub-kernel — well-definedness of Dolbeault → Čech.)** A global `∂̄`-image
`g = ∂̄h` is sent to a Čech **coboundary**, hence to `0` in `H¹`: each local primitive difference
`u_i − h` is holomorphic on `U_i` (`∂̄(u_i − h) = g − g = 0`), so `{[u_i − h]} ∈ sections0 0` and
`cechDelta0 {[u_i]} = cechDelta0 {[u_i − h]} ∈ coboundaries1 0` (the global `h` contributes `0` to
`cechDelta0`). This is exactly the statement that `dbarImageInZeroOne X` lies in the kernel of the
composite `A^{0,1} → Z¹ → H¹`, which makes the lift to `DolbeaultH01 = A^{0,1}/im ∂̄` well-defined. -/
theorem dolbeaultToCechCocycle_dbarImage_le (𝔇 : ChartDiskCover X) :
    dbarImageInZeroOne X ≤ LinearMap.ker
      ((Submodule.mkQ ((𝔇.toFiniteCover.coboundaries1 (0 : Divisor X)).submoduleOf
          (𝔇.toFiniteCover.cocycles1 (0 : Divisor X)))).restrictScalars ℝ
        ∘ₗ dolbeaultToCechCocycle 𝔇) := by
  intro w hw
  simp only [dbarImageInZeroOne, Submodule.submoduleOf, Submodule.mem_comap,
    Submodule.subtype_apply] at hw
  obtain ⟨h, hh⟩ := hw
  -- `↑(dolbeaultToCechCocycle 𝔇 w) = cechDelta0 (rawCochain ↑w) = cechDelta0 (rawCochain (∂̄h))`.
  have hval : ((dolbeaultToCechCocycle 𝔇 w : ↥(𝔇.toFiniteCover.cocycles1 0)) :
        𝔇.toFiniteCover.Cochain1)
      = 𝔇.toFiniteCover.cechDelta0 (𝔇.rawCochain (dbarL h)) := by
    show 𝔇.toFiniteCover.cechDelta0 (𝔇.rawCochain (↑w : SmoothCOneForms X))
      = 𝔇.toFiniteCover.cechDelta0 (𝔇.rawCochain (dbarL h))
    rw [hh]
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  rw [hval]
  -- Coboundary witness: `{[u_i]} − {[h|U_i]} ∈ sections0`, and `cechDelta0` of the global `h` is `0`.
  refine ⟨𝔇.rawCochain (dbarL h) - fun k => toGerm (𝔇.U k) (⇑h ∘ Subtype.val), ?_, ?_⟩
  · intro k
    rw [Pi.sub_apply,
      show 𝔇.rawCochain (dbarL h) k = toGerm (𝔇.U k) (𝔇.diskSection k (dbarL h)) from rfl, ← map_sub]
    exact ⟨𝔇.diskSection k (dbarL h) - ⇑h ∘ Subtype.val,
      mem_OmegaD_zero_of_gext_analytic (fun v => 𝔇.gextH_diff_analyticAt h k _
        (fun u => by simp only [Pi.sub_apply, Function.comp_apply, ChartDiskCover.diskSection]) v),
      rfl⟩
  · rw [map_sub]
    have hc0 : 𝔇.toFiniteCover.cechDelta0 (fun k => toGerm (𝔇.U k) (⇑h ∘ Subtype.val)) = 0 := by
      funext p
      obtain ⟨a, b⟩ := p
      simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, LinearMap.proj_apply, rawRestrictG_coe, Pi.zero_apply, sub_eq_zero]
      rfl
    rw [hc0, sub_zero]

/-- **Dolbeault → Čech.** The `ℝ`-linear map `H^{0,1}(X) → H¹(X, 𝒪)`. Assembled **completely** from
the analytic cocycle operator `dolbeaultToCechCocycle` and its well-definedness
`dolbeaultToCechCocycle_dbarImage_le`: project the cocycle to `cechH1 = Z¹/B¹` (`Submodule.mkQ`,
scalar-restricted `ℂ → ℝ`), then lift through the Dolbeault quotient `A^{0,1}/im ∂̄`
(`Submodule.liftQ`, justified by the kernel inclusion). All genuine content lives in the two named
sub-kernels above. -/
noncomputable def dolbeault_to_cech (𝔇 : ChartDiskCover X) :
    DolbeaultH01 X →ₗ[ℝ] 𝔇.toFiniteCover.cechH1 0 :=
  Submodule.liftQ (dbarImageInZeroOne X)
    ((Submodule.mkQ ((𝔇.toFiniteCover.coboundaries1 (0 : Divisor X)).submoduleOf
        (𝔇.toFiniteCover.cocycles1 (0 : Divisor X)))).restrictScalars ℝ ∘ₗ dolbeaultToCechCocycle 𝔇)
    (dolbeaultToCechCocycle_dbarImage_le 𝔇)

end Jacobians.Dolbeault
