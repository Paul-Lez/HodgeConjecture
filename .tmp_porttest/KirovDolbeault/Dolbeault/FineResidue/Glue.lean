/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.ChainRule
import KirovDolbeault.Dolbeault.FineResidue.OneOneCoeff
import KirovDolbeault.Dolbeault.FineResidue.PoUSplit
import KirovDolbeault.Dolbeault.ChartDiskFiniteness
import KirovDolbeault.Dolbeault.DbarOpenDisk

/-!
# R3b — the glue law: `∂̄` of the PoU split is a global `(1,1)` chart-coefficient family

Step 3 of the Forster §17.3 fine-sheaf residue construction (S3 scoping §2.0 step 3, lane R of
`docs/planning/CAMPAIGN_KEYSTONE.md`).  Read the R2 split `σ_j = ∑_k ρ_k·w_{kj}` in chart-`j`
coordinates, `s_j := pouSplit ∘ (chart j).symm` (`splitCoeff`).  Because the telescoping identity
`σ_k − σ_j = w_{jk}` (`pouSplit_telescope`) has **holomorphic** right-hand side, `∂̄` kills it
(`DbarDisk.dbar_eq_zero_of_differentiableAt`), so `∂̄s` is *transition-independent*: by the R3
chain rule `dbar_comp` it obeys, germ-eventually at every overlap point, the `(0,1)` law

  `∂̄s_j = (∂̄s_k ∘ φ) · conj φ′`     (`dbar_splitCoeff_transition`).

Weighted by a holomorphic `dz`-slot family (`IsOneZeroCoeff` — in the residue application, the
chart coefficients of the S1 canonical form `ω₀`), the family

  `t_j := DbarDisk.dbar s_j · g_j`     (`glueCoeff`)

is a global `(1,1)` chart-coefficient family: `glueCoeff_mem_oneOneCoeff : glueCoeff ∈
oneOneCoeff 𝔇` — the R3 headline, the chart-coefficient incarnation of "the `∂̄σ_i` glue to a
global smooth `(1,1)`-form `τ`".

## Where the two halves of R1's `normSq φ′` factor come from (law-shape reconciliation)

`OneOneLawAt`'s factor is `normSq φ′ = φ′ · conj φ′`.  The chain rule supplies **only
`conj φ′`**, and on the landed R2 interface — where the overlap family `w` is **scalar**-valued
on `X` with the plain additive `IsOverlapCocycle` (the Mittag–Leffler `w i j = m_j − m_i`
shape) — no more is provable for `∂̄s` alone: the telescope forces `s_k∘φ − s_j` to be
holomorphic, which pins the transformation law of `(∂̄s_j)_j` to the `(0,1)` factor `conj φ′`.
The slot-free claim "`(DbarDisk.dbar s_j)_j ∈ oneOneCoeff 𝔇`" is therefore **false** for
nontrivial data (a nonzero `(0,1)` family cannot also satisfy the `(1,1)` law unless `φ′ ≡ 1`).
R1's law was **not** adjusted.  Instead, per the R3 handoff note, the second `φ′` enters through
the **holomorphic change of the `dz`-slot**: on scalar overlap data the `dz`-slot is carried by
an explicit input — a holomorphic `(1,0)` chart-coefficient family `g` with the overlap law
`g_j = (g_k ∘ φ) · φ′` (`OneZeroLawAt`), i.e. exactly the coefficient family of a global
holomorphic 1-form.  Then

  `t_j = (∂̄s_k ∘ φ)·conj φ′ · (g_k ∘ φ)·φ′ = (t_k ∘ φ) · normSq φ′`,

reassembling R1's factor on the nose (`Complex.mul_conj`).  `t_j` is the chart coefficient of
`τ = ∂̄(σ^{scalar}·ω₀)` — the Forster `(1,1)` density that R4 integrates against the **pinned**
R0 normalization `resNormalization = −π⁻¹` (`SignTest.lean`; cite, do not re-derive).

## Application note (recorded for R4/R6, also in `docs/planning/R_LANE_PROGRESS.log`)

For `K = div ω₀ ≠ 0` (genus ≥ 2), the scalar overlap data of a `Z¹(𝒪_K)`-cocycle has poles at
`K`-points, so `HolomorphicOnOverlaps` requires the chart-disk cover to be refined so that each
of the finitely many `K`-points lies in a *single* cover set (then every `w k j` with `k ≠ j` is
holomorphic on its overlap, and at a `K`-point of `U_j` only the `k = j` term of `σ_j` survives,
which the cocycle diagonal `w j j = 0` kills).  At genus 1, `K = 0` and no refinement is needed.

## Main declarations

* `splitCoeff 𝔇 w j` — the chart-`j` read `pouSplit 𝔇 w j ∘ (chartAt ℂ (𝔇.center j)).symm`.
* `HolomorphicOnOverlaps` — the overlap functions are holomorphic in chart coordinates.
* `dbar_splitCoeff_transition` — the `(0,1)` transition law for `∂̄(splitCoeff)`.
* `OneZeroLawAt` / `IsOneZeroCoeff` — holomorphic `(1,0)` chart-coefficient families (the
  `dz`-slot; inhabited by `0`, and in application by the chart coefficients of `ω₀`).
* `glueCoeff` / `glueCoeff_mem_oneOneCoeff` — the R3 headline.
-/

open Complex Filter
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### The chart-read split and its smoothness -/

/-- The **chart-`j` read of the PoU split**: `s_j := (pouSplit 𝔇 w j) ∘ (chart j).symm : ℂ → ℂ`,
the planar `(1,0)`-direction split coefficient `s_j(z) = ∑_k ρ̃_k(z)·w̃_{kj}(z)` of the S3
scoping §2.2.  A global stand-in function; meaningful on the chart-`j` image of `U j`. -/
noncomputable def splitCoeff (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ)
    (j : 𝔇.toFiniteCover.ι) : ℂ → ℂ :=
  fun z => pouSplit 𝔇 w j ((chartAt ℂ (𝔇.center j)).symm z)

@[simp] theorem splitCoeff_apply (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ)
    (j : 𝔇.toFiniteCover.ι) (z : ℂ) :
    splitCoeff 𝔇 w j z = pouSplit 𝔇 w j ((chartAt ℂ (𝔇.center j)).symm z) := rfl

/-- **Planar smoothness of the chart-read split** at the chart image of its own cover set:
`contMDiffAt_pouSplit` composed with the (real-)smooth chart inverse, converted to `ContDiffAt`
through the `RealManifold` bridge. -/
theorem contDiffAt_splitCoeff {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    (hw : SmoothOnOverlaps 𝔇 w) (j : 𝔇.toFiniteCover.ι) {x : X}
    (hx : x ∈ (𝔇.U j : Set X)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (splitCoeff 𝔇 w j) (chartMap 𝔇 j x) := by
  have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hx
  have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
    (chartAt ℂ (𝔇.center j)).map_source hxsrc
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartAt ℂ (𝔇.center j)).symm
      (chartMap 𝔇 j x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := 𝔇.center j) _ hzt).contMDiffAt
      ((chartAt ℂ (𝔇.center j)).open_target.mem_nhds hzt)
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
    (chartAt ℂ (𝔇.center j)).left_inv hxsrc
  have hσ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (pouSplit 𝔇 w j)
      ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
    rw [hli]
    exact contMDiffAt_pouSplit 𝔇 hw j hx
  exact contMDiffAt_iff_contDiffAt.1 (hσ.comp (chartMap 𝔇 j x) hsymm)

/-! ### Holomorphy of the overlap data in chart coordinates -/

/-- An overlap family `w` is **holomorphic on overlaps** when each `w i j`, read in the chart of
its *first* index, is `ℂ`-differentiable at the chart image of every overlap point.  (By
`transitionMap_analyticAt` this is equivalent to holomorphy in any cover chart containing the
point; the first-index chart is the one the telescope consumes.)  This is the hypothesis that
makes `∂̄` of the split transition-independent — and, per the module docstring, for
`Z¹(𝒪_K)`-data at `K ≠ 0` it asks the cover to separate the `K`-points from the overlaps. -/
def HolomorphicOnOverlaps (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ) : Prop :=
  ∀ i j, ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X),
    DifferentiableAt ℂ (fun z => w i j ((chartAt ℂ (𝔇.center i)).symm z)) (chartMap 𝔇 i x)

/-! ### The telescope in chart coordinates and the `(0,1)` transition law -/

/-- **The telescope, read in chart-`j` coordinates**: near the chart-`j` coordinate of an
overlap point of `U j ⊓ U k`, the chart-`k` read of the split, relocated through the transition
`φ_{jk}`, is the chart-`j` read shifted by the overlap function:

  `s_k ∘ φ_{jk} = s_j + w_{jk} ∘ (chart j).symm`  (germ-eventually).

Pure plumbing on `pouSplit_telescope` (R2): the chart inverse is continuous, so nearby planar
points stay in the overlap, where the telescope applies pointwise. -/
theorem splitCoeff_transition_eventuallyEq
    {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ} (hcoc : IsOverlapCocycle 𝔇 w)
    {j k : 𝔇.toFiniteCover.ι} {x : X} (hx : x ∈ (𝔇.U j ⊓ 𝔇.U k : Opens X)) :
    (fun z => splitCoeff 𝔇 w k (transitionMap 𝔇 j k z))
      =ᶠ[𝓝 (chartMap 𝔇 j x)] fun z =>
        splitCoeff 𝔇 w j z + w j k ((chartAt ℂ (𝔇.center j)).symm z) := by
  have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hx.1
  have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
    (chartAt ℂ (𝔇.center j)).map_source hxsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
    (chartAt ℂ (𝔇.center j)).symm.continuousAt
      (by rwa [(chartAt ℂ (𝔇.center j)).symm_source])
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
    (chartAt ℂ (𝔇.center j)).left_inv hxsrc
  have hov : ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X)
      ∈ 𝓝 ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
    rw [hli]
    exact (𝔇.U j ⊓ 𝔇.U k : Opens X).isOpen.mem_nhds hx
  filter_upwards [hcont.preimage_mem_nhds hov] with z hz
  have hzk : (chartAt ℂ (𝔇.center j)).symm z ∈ (chartAt ℂ (𝔇.center k)).source :=
    mem_chartSource_of_mem_U 𝔇 hz.2
  have h1 : splitCoeff 𝔇 w k (transitionMap 𝔇 j k z)
      = pouSplit 𝔇 w k ((chartAt ℂ (𝔇.center j)).symm z) := by
    show pouSplit 𝔇 w k ((chartAt ℂ (𝔇.center k)).symm
        ((chartAt ℂ (𝔇.center k)) ((chartAt ℂ (𝔇.center j)).symm z))) = _
    rw [(chartAt ℂ (𝔇.center k)).left_inv hzk]
  have h2 := pouSplit_telescope 𝔇 hcoc (i := j) (j := k) hz
  rw [h1, splitCoeff_apply]
  linear_combination h2

/-- **The `(0,1)` transition law for `∂̄` of the chart-read split** — "`∂̄s` is
transition-independent": germ-eventually at the chart-`j` coordinate of every overlap point,

  `∂̄s_j = (∂̄s_k ∘ φ_{jk}) · conj φ′_{jk}`.

Proof: by the chart-read telescope, `s_k ∘ φ = s_j + ŵ` with `ŵ = w_{jk} ∘ (chart j).symm`
holomorphic (`HolomorphicOnOverlaps`), so `∂̄ŵ = 0` (`dbar_eq_zero_of_differentiableAt`) and
`∂̄(s_k ∘ φ) = ∂̄s_j`; the chain rule `dbar_comp` converts the left side.  This is the maximal
law for the slot-free family — the `(1,1)` headline below adds the `dz`-slot factor. -/
theorem dbar_splitCoeff_transition {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    (hw : SmoothOnOverlaps 𝔇 w) (hcoc : IsOverlapCocycle 𝔇 w)
    (hhol : HolomorphicOnOverlaps 𝔇 w) {j k : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U j ⊓ 𝔇.U k : Opens X)) :
    ∀ᶠ z in 𝓝 (chartMap 𝔇 j x),
      DbarDisk.dbar (splitCoeff 𝔇 w j) z
        = DbarDisk.dbar (splitCoeff 𝔇 w k) (transitionMap 𝔇 j k z)
            * (starRingEnd ℂ) (deriv (transitionMap 𝔇 j k) z) := by
  have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hx.1
  have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
    (chartAt ℂ (𝔇.center j)).map_source hxsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
    (chartAt ℂ (𝔇.center j)).symm.continuousAt
      (by rwa [(chartAt ℂ (𝔇.center j)).symm_source])
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
    (chartAt ℂ (𝔇.center j)).left_inv hxsrc
  have hov : ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X)
      ∈ 𝓝 ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
    rw [hli]
    exact (𝔇.U j ⊓ 𝔇.U k : Opens X).isOpen.mem_nhds hx
  filter_upwards [(splitCoeff_transition_eventuallyEq 𝔇 hcoc hx).eventuallyEq_nhds,
    (transitionMap_analyticAt 𝔇 hx.1 hx.2).eventually_analyticAt,
    hcont.preimage_mem_nhds hov,
    (chartAt ℂ (𝔇.center j)).open_target.mem_nhds hzt] with z hz_ev hz_an hz_mem hz_tgt
  -- The planar point `z` is the chart-`j` coordinate of the overlap point `(chart j).symm z`.
  have hcmj : chartMap 𝔇 j ((chartAt ℂ (𝔇.center j)).symm z) = z :=
    (chartAt ℂ (𝔇.center j)).right_inv hz_tgt
  have hsj : ContDiffAt ℝ (⊤ : ℕ∞) (splitCoeff 𝔇 w j) z := by
    have h := contDiffAt_splitCoeff 𝔇 hw j hz_mem.1
    rwa [hcmj] at h
  have hcmk : chartMap 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z) = transitionMap 𝔇 j k z := by
    rw [← transitionMap_chartMap 𝔇 (k := k) hz_mem.1, hcmj]
  have hsk : ContDiffAt ℝ (⊤ : ℕ∞) (splitCoeff 𝔇 w k) (transitionMap 𝔇 j k z) := by
    have h := contDiffAt_splitCoeff 𝔇 hw k hz_mem.2
    rwa [hcmk] at h
  have hŵ : DifferentiableAt ℂ
      (fun ζ => w j k ((chartAt ℂ (𝔇.center j)).symm ζ)) z := by
    have h := hhol j k _ hz_mem
    rwa [hcmj] at h
  -- Chain rule on the relocated read, then kill the holomorphic telescope term.
  have hd4 := dbar_comp (f := splitCoeff 𝔇 w k) (φ := transitionMap 𝔇 j k)
    (hsk.differentiableAt (by simp)) hz_an.differentiableAt
  rw [Function.comp_def] at hd4
  have hd1 : DbarDisk.dbar (fun ζ => splitCoeff 𝔇 w k (transitionMap 𝔇 j k ζ)) z
      = DbarDisk.dbar (fun ζ => splitCoeff 𝔇 w j ζ
          + w j k ((chartAt ℂ (𝔇.center j)).symm ζ)) z := by
    simp only [DbarDisk.dbar, hz_ev.fderiv_eq]
  have hd2 : DbarDisk.dbar (fun ζ => splitCoeff 𝔇 w j ζ
          + w j k ((chartAt ℂ (𝔇.center j)).symm ζ)) z
      = DbarDisk.dbar (splitCoeff 𝔇 w j) z
        + DbarDisk.dbar (fun ζ => w j k ((chartAt ℂ (𝔇.center j)).symm ζ)) z :=
    DbarOpenDisk.dbar_add (hsj.differentiableAt (by simp)) (hŵ.restrictScalars ℝ)
  have hd3 : DbarDisk.dbar (fun ζ => w j k ((chartAt ℂ (𝔇.center j)).symm ζ)) z = 0 :=
    DbarDisk.dbar_eq_zero_of_differentiableAt hŵ
  rw [← hd4, hd1, hd2, hd3, add_zero]

/-! ### Holomorphic `(1,0)` slot families -/

/-- The **`(1,0)` chart-coefficient overlap law at an overlap point `x`, up to germ**:

  `g_j(z) = g_k(φ_{jk} z) · φ′_{jk}(z)`  for `z` near `chartMap 𝔇 j x`

— the transformation law of the chart coefficients of a holomorphic 1-form (the `dz`-slot).
Companion of R1's `(1,1)` law `OneOneLawAt` (factor `normSq φ′ = φ′·conj φ′`) and of the `(0,1)`
law of `dbar_splitCoeff_transition` (factor `conj φ′`). -/
def OneZeroLawAt (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (j k : 𝔇.toFiniteCover.ι) (x : X) : Prop :=
  ∀ᶠ z in 𝓝 (chartMap 𝔇 j x),
    g j z = g k (transitionMap 𝔇 j k z) * deriv (transitionMap 𝔇 j k) z

/-- A **holomorphic `(1,0)` chart-coefficient family** for the chart-disk cover: one planar
function per cover index, holomorphic at the chart image of its own cover set, satisfying the
germ-eventual `φ′` overlap law at every overlap point.  This is the curve-level stand-in for
"chart coefficients of a global holomorphic 1-form" — in the residue application, of the S1
canonical form `ω₀` (`0` is a trivial inhabitant; the `ω₀`-witness is a later lane-R rung). -/
def IsOneZeroCoeff (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) : Prop :=
  (∀ j, ∀ x ∈ (𝔇.U j : Set X), AnalyticAt ℂ (g j) (chartMap 𝔇 j x)) ∧
    ∀ j k, ∀ x ∈ (𝔇.U j ⊓ 𝔇.U k : Opens X), OneZeroLawAt 𝔇 g j k x

/-! ### The R3 headline -/

/-- The **glued `(1,1)` coefficient family** of a PoU split and a `dz`-slot family:

  `t_j := ∂̄s_j · g_j`,  `s_j = splitCoeff 𝔇 w j`.

For `w` the scalar overlap data of an `Ω = 𝒪_K·ω₀` Čech cocycle and `g` the chart coefficients
of `ω₀`, this is the chart-coefficient presentation of Forster's global `(1,1)`-form
`τ = ∂̄σ_i` — the integrand of the R4 residue functional (against `resNormalization`, R0). -/
noncomputable def glueCoeff (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) : 𝔇.toFiniteCover.ι → ℂ → ℂ :=
  fun j z => DbarDisk.dbar (splitCoeff 𝔇 w j) z * g j z

@[simp] theorem glueCoeff_apply (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (j : 𝔇.toFiniteCover.ι) (z : ℂ) :
    glueCoeff 𝔇 w g j z = DbarDisk.dbar (splitCoeff 𝔇 w j) z * g j z := rfl

/-- **R3 headline — the glue law.**  For a smooth holomorphic overlap cocycle `w` and a
holomorphic `(1,0)` slot family `g`, the family `t_j = ∂̄(splitCoeff 𝔇 w j) · g_j` is a global
`(1,1)` chart-coefficient family:

  `glueCoeff 𝔇 w g ∈ oneOneCoeff 𝔇`.

The `(1,1)` overlap factor `normSq φ′` assembles as `conj φ′` (chain rule, via
`dbar_splitCoeff_transition`) times `φ′` (the `dz`-slot law `OneZeroLawAt`), by
`Complex.mul_conj`.  This is "the `∂̄σ_i` agree on overlaps and glue to a global smooth
`(1,1)`-form `τ`" of Forster §17.3, in the bundle-free representation of R1. -/
theorem glueCoeff_mem_oneOneCoeff {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hw : SmoothOnOverlaps 𝔇 w)
    (hcoc : IsOverlapCocycle 𝔇 w) (hhol : HolomorphicOnOverlaps 𝔇 w)
    (hg : IsOneZeroCoeff 𝔇 g) :
    glueCoeff 𝔇 w g ∈ oneOneCoeff 𝔇 := by
  rw [mem_oneOneCoeff]
  refine ⟨fun j x hx => ?_, fun j k x hx => ?_⟩
  · -- Smoothness: `∂̄s_j` is `C^∞` at the chart image (`contDiffAt_dbar_chartDisk`), `g_j`
    -- is analytic.
    exact (ChartDiskCover.contDiffAt_dbar_chartDisk (contDiffAt_splitCoeff 𝔇 hw j hx)).mul
      (((hg.1 j x hx).restrictScalars (𝕜 := ℝ)).contDiffAt)
  · -- The `(1,1)` law: `(0,1)` factor `conj φ′` times `dz`-slot factor `φ′`.
    unfold OneOneLawAt
    filter_upwards [dbar_splitCoeff_transition 𝔇 hw hcoc hhol hx, hg.2 j k x hx]
      with z h1 h2
    have hns : ((normSq (deriv (transitionMap 𝔇 j k) z) : ℝ) : ℂ)
        = deriv (transitionMap 𝔇 j k) z
            * (starRingEnd ℂ) (deriv (transitionMap 𝔇 j k) z) :=
      (Complex.mul_conj _).symm
    simp only [glueCoeff_apply]
    rw [h1, h2, hns]
    ring

end Jacobians.Dolbeault.FineResidue
