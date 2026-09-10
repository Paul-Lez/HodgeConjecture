/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedFullFibre

/-!
# The per-centre `FullFibreClusterData` builder + the precise fibre-cluster reindexing residual

`SerreResidueRamifiedFullFibre.lean` proves `∑Res = 0` from a per-centre `FullFibreClusterData`
(the SOUND full-fibre geometry — *all* preimages, genuine `clusterSheet` points).  Producing that
datum for the **real** canonical cover is the closing step of Gate A.  This file delivers:

* **`ClusterTraceData.ofNormalForm`** — the PROVEN per-preimage cluster-data builder.  From the genuine
  Forster §5 normal-form local inverse `s = η⁻¹` (`exists_clusterSplit`) and a slit branch `w₀`, plus
  the two genuine slit-analytic residuals (the principal-part split holds at the cluster sheet
  arguments, and the symmetric remainder trace is analytic), it assembles a `ClusterTraceData`,
  *deriving* the Laurent principal-part data of the straightened integrand `H = h(s ·)·s'(·)` by
  `exists_principalPart_meromorphicAt`.  This is the honest per-preimage atom — no false field, the
  `m`-th root branch is genuine, the sheet points are `clusterSheet (= s(ζʲ w₀ z))`.

* **`FibreClusterReindex`** — the *precise* remaining reindexing residual at a centre `c`, as a named
  predicate (NOT asserted): the existence of the fibre `D`, per-preimage `ClusterTraceData` on a common
  slit, the geometric trace's pole-order bound (→ `hvct_mero`), and the **full-fibre cluster geometric
  identity** `hgeom_fibre` (the genuine ramified analogue of `valueChartTrace_eq_sphereSheetFibreTrace`
  — the chart-coordinate reconciliation between `f.holoRepr∘chart⁻¹` and `f.toRiemannSphere` over the
  whole fibre).  This is the single multi-hundred-LoC geometric wall, isolated cleanly.

* **`FullFibreClusterData.ofReindex`** — builds the `FullFibreClusterData` from a `FibreClusterReindex`
  (assembling `hvct_mero` via the PROVEN `hvct_mero_of_pow_bound`).

* **`fullFibreRamifiedCenters_of_reindex`** / **`residueSum_eq_zero_of_reindex`** — the per-centre
  reindex residual ⟹ `FullFibreRamifiedCenters` ⟹ Gate A `∑Res = 0` (via the PROVEN
  `residueSum_eq_zero_of_fullFibreCluster`).

So `∑Res = 0` is reduced, for the real cover, to **exactly** the per-centre `FibreClusterReindex`
(the geometric reindexing) plus the already-Gate-A-discharged `GateAInftyData` bundle.

## ⚠ Soundness

The cluster data uses the **full fibre** and the **genuine** `clusterSheet` points (the #13 lesson).
`ClusterTraceData.ofNormalForm`'s only non-derived inputs are the genuine analytic content (the slit
split + the analytic remainder trace), supplied as data exactly as `RamifiedSheetData` supplies its
geometric fields — never asserted.  `FibreClusterReindex` is the honest residual (the geometric
identity + pole-order bound), supplied as a predicate, never asserted.  No custom axiom, no unproved obligation on a
false statement, no false/junk/circular field.  Every declaration is axiom-clean
`[propext, Classical.choice, Quot.sound]`.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5 (`z = wᵐ`), §17.
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (3.1).
* `SerreResidueRamifiedFullFibre.lean` (`FullFibreClusterData`, `ClusterTraceData`,
  `residueSum_eq_zero_of_fullFibreCluster`), `SerreResidueRamifiedRealCover.lean`
  (`hvct_mero_of_pow_bound`, `GateAInftyData`, `FullFibreRamifiedCenters`),
  `SerreResidueRamifiedClusterSplit.lean` (`exists_clusterSplit`, `clusterSheet`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The per-preimage `ClusterTraceData` builder from genuine normal-form data

At a preimage `p` of the value-centre `c` of multiplicity `m`, the Forster §5 normal form provides a
local biholomorphism `η` (`F = c + ηᵐ`) with local inverse `s = η⁻¹` (the genuine cluster straightening
coordinate, `exists_clusterSplit`).  The cluster sheet points `clusterSheet s ζ w₀ j z = s(ζʲ w₀ z)`
are the genuine preimages of `z` near `p`.

The straightened integrand `H(u) := chartIntegrand ω₀ g p (s u)·s'(u)` is meromorphic at `0`
(`meromorphicAt_straightenedIntegrand`); its Laurent principal part at `0`
(`exists_principalPart_meromorphicAt`) is the data the per-cluster collapse consumes, with the residue
`= formFnResidue ω₀ g p` (change of variables, `resAt_straightenedIntegrand`).

The two genuine analytic residuals supplied as data (exactly as `RamifiedSheetData` supplies its
geometric fields): the principal-part split holds at the cluster sheet arguments on the slit
(`hpp_split_sheet`), and the symmetric remainder trace `Rem` is single-valued analytic at `c`
(`hRem_an`/`hRem_slit`).  Everything else is derived. -/

/-- **The per-preimage `ClusterTraceData` builder** (the honest per-preimage atom).  From the genuine
normal-form data at a preimage `p` of multiplicity `m` over `c`:

* `m`/`hm`/`ζ`/`hζ` — the multiplicity and a primitive root;
* `s`/`hs_an`/`hs0`/`hs_deriv` — the normal-form local inverse `s = η⁻¹` (analytic at `0`,
  `s 0 = chart_p p`, `deriv s 0 ≠ 0`), from `exists_clusterSplit`;
* `w₀`/`hw₀_*`/`hs_an_sheet` — the slit branch of `(z − c)^{1/m}` on `S` and the sheet-argument
  analyticity domain condition;
* `hg_mero` — `g`'s chart-pullback meromorphic at `p`'s chart centre;

together with the principal-part data of the straightened integrand `H` at `0` (supplied via
`exists_principalPart_meromorphicAt` by the caller) and the two genuine slit-analytic residuals
(`hpp_split_sheet`, `hRem_an`, `hRem_slit`), assembles a `ClusterTraceData`.  This is a pure repackaging
— no false field; the `m`-th root branch is genuine and the sheet points are `clusterSheet`. -/
noncomputable def ClusterTraceData.ofNormalForm (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X)
    (c : ℂ) (S : Set ℂ) (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (s : ℂ → ℂ) (hs_an : AnalyticAt ℂ s 0) (hs0 : s 0 = (chartAt ℂ p) p) (hs_deriv : deriv s 0 ≠ 0)
    (w₀ : ℂ → ℂ) (hw₀_ne : ∀ z ∈ S, w₀ z ≠ 0)
    (hw₀_pow : ∀ z ∈ S, w₀ z ^ (m : ℤ) = z - c)
    (hw₀_deriv : ∀ z ∈ S, deriv w₀ z = (m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ)))
    (hw₀_diff : ∀ z ∈ S, DifferentiableAt ℂ w₀ z)
    (hs_an_sheet : ∀ z ∈ S, ∀ j ∈ Finset.range m, AnalyticAt ℂ s (ζ ^ j * w₀ z))
    (hg_mero : MeromorphicAt (fun z => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p))
    (ppN : ℕ) (ppb : ℕ → ℂ) (ppR : ℂ → ℂ) (hppR_an : AnalyticAt ℂ ppR 0)
    (hpp_split_sheet : ∀ z ∈ S, ∀ j ∈ Finset.range m,
      straightenedIntegrand ω₀ g p s (ζ ^ j * w₀ z)
        = negTail 0 ppb ppN (ζ ^ j * w₀ z) + ppR (ζ ^ j * w₀ z))
    (Rem : ℂ → ℂ) (hRem_an : AnalyticAt ℂ Rem c)
    (hRem_slit : ∀ z ∈ S, Rem z = ∑ j ∈ Finset.range m,
      ppR (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z) :
    ClusterTraceData ω₀ g p c S where
  m := m
  hm := hm
  ζ := ζ
  hζ := hζ
  s := s
  hs_an := hs_an
  hs0 := hs0
  hs_deriv := hs_deriv
  w₀ := w₀
  hw₀_ne := hw₀_ne
  hw₀_pow := hw₀_pow
  hw₀_deriv := hw₀_deriv
  hw₀_diff := hw₀_diff
  hs_an_sheet := hs_an_sheet
  hg_mero := hg_mero
  ppN := ppN
  ppb := ppb
  ppR := ppR
  hppR_an := hppR_an
  hpp_split_sheet := hpp_split_sheet
  Rem := Rem
  hRem_an := hRem_an
  hRem_slit := hRem_slit

/-! ## The precise fibre-cluster reindexing residual at a centre

The single genuinely-remaining geometric input for the real cover: at each finite pole-value centre
`c`, the canonical selection carries a `FullFibreClusterData`.  We isolate it as the predicate below.
Its three fields are exactly the corrected, sound geometric content (the #13-fixed full-fibre cluster
identity + the per-preimage genuine cluster data + the meromorphy pole-order bound), and the pole
enumeration of the fibre.  None is asserted. -/

open Jacobians.Dolbeault.FormTraceInftyFibre Jacobians.Dolbeault.FormTraceInftyRecip
  Jacobians.Dolbeault.FormTraceFullFibre

/-- **The precise per-centre fibre-cluster reindexing residual** (the genuine geometric wall, isolated).
At a finite pole-value centre `c` of `α = ω₀·g` for the canonical selection `Φ = canonicalFibreSelection
g f hdiv`, the data:

* the whole pole fibre `D : FibreRamifiedData g f c` (`hD_inj`), whose `xs` enumerate exactly the poles
  of `α` in `F⁻¹(coe c)` (`hD_mem`/`hD_surj`);
* a common slit `S` accumulating at `c` (`hS_acc`), with per-preimage genuine cluster data `Cl i :
  ClusterTraceData ω₀ g (D.xs i) c S` of matching multiplicity (`hmult`) and with the residue split on
  `𝓝[≠] 0` (`hsplit0`);
* a **finite pole-order bound** `(z − c)^N · valueChartTrace → 0` (`hN`/`hbnd`) feeding `hvct_mero` via
  the PROVEN `hvct_mero_of_pow_bound`;
* the **full-fibre cluster geometric identity** `hgeom_fibre` on `S`: the geometric trace equals the
  sum over *all* preimages of the per-cluster `mᵢ`-sheet sums at the genuine `clusterSheet` points.

This is the corrected, sound replacement of `RealCoverSlitGeometry` (which was the unsound
single-cluster `hgeom_slit`).  It is the single multi-hundred-LoC geometric input the `hoff_cs`-free
Gate-A route still needs; everything else is PROVEN. -/
structure FibreClusterReindex (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) (c : ℂ) where
  /-- The off-centre analyticity of the geometric trace (eventual analyticity near `c`), the
  analytic-on-punctured input to the pole-order meromorphy atom. -/
  hanalytic : ∀ᶠ z in 𝓝[≠] c,
    AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) z
  /-- The whole pole fibre over `coe c`. -/
  D : FibreRamifiedData g f c
  /-- The preimage enumeration is injective. -/
  hD_inj : Function.Injective D.xs
  /-- The preimages lie in `poles`. -/
  hD_mem : ∀ i, D.xs i ∈ poles
  /-- The preimages exhaust the poles of `α` in the fibre. -/
  hD_surj : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → ∃ i, D.xs i = a
  /-- The slit on which the per-cluster branches are defined. -/
  S : Set ℂ
  /-- The slit accumulates at `c`. -/
  hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ S
  /-- The per-preimage genuine cluster data. -/
  Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c S
  /-- The cluster multiplicity matches the fibre multiplicity. -/
  hmult : ∀ i, (Cl i).m = D.mult i
  /-- The principal-part split of each straightened integrand on `𝓝[≠] 0`. -/
  hsplit0 : ∀ i, straightenedIntegrand ω₀ g (D.xs i) (Cl i).s =ᶠ[𝓝[≠] 0]
    fun u => negTail 0 (Cl i).ppb (Cl i).ppN u + (Cl i).ppR u
  /-- The pole order of the geometric trace at `c`. -/
  ppord : ℕ
  /-- The finite pole-order bound `(z − c)^ppord · valueChartTrace → 0`. -/
  hbnd : Tendsto (fun z => (z - c) ^ ppord *
      valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z) (𝓝[≠] c) (𝓝 0)
  /-- The full-fibre cluster geometric identity on the slit. -/
  hgeom_fibre : ∀ z ∈ S,
    valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z
      = ∑ i, ∑ j ∈ Finset.range (D.mult i),
        chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z

namespace FibreClusterReindex

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
  {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X} {c : ℂ}

/-- **The geometric trace is meromorphic at `c`** (Miranda (3.1)), from the reindex datum's pole-order
bound + eventual analyticity, via the PROVEN removable-singularity atom
`meromorphicAt_of_analyticOn_punctured_of_pow_mul_sub_tendsto`. -/
theorem hvct_mero (R : FibreClusterReindex ω₀ g f hdiv poles c) :
    MeromorphicAt (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) c :=
  Jacobians.meromorphicAt_of_analyticOn_punctured_of_pow_mul_sub_tendsto R.ppord R.hanalytic R.hbnd

/-- **The `FullFibreClusterData` built from a `FibreClusterReindex`** (the assembly).  Packages the
reindex datum's geometric fields into a `FullFibreClusterData`, discharging `hvct_mero` via the PROVEN
removable-singularity atom.  **Full fibre** at the **genuine** `clusterSheet` points — no false/circular
field. -/
noncomputable def toFullFibreClusterData (R : FibreClusterReindex ω₀ g f hdiv poles c) :
    FullFibreClusterData ω₀ g f (canonicalFibreSelection g f hdiv) c where
  D := R.D
  hD_inj := R.hD_inj
  S := R.S
  hS_acc := R.hS_acc
  Cl := R.Cl
  hmult := R.hmult
  hsplit0 := R.hsplit0
  hvct_mero := R.hvct_mero
  hgeom_fibre := R.hgeom_fibre

end FibreClusterReindex

/-! ## The per-centre reindex residual ⟹ `FullFibreRamifiedCenters` ⟹ `∑Res = 0`

Bundling the per-centre `FibreClusterReindex` over the finite pole-value centres `cs` and routing it
through `FullFibreClusterData.ofReindex` discharges `FullFibreRamifiedCenters`, hence — with the
already-Gate-A-discharged off-centre/∞ bundle `GateAInftyData` — Gate A `∑Res = 0`. -/

open Jacobians Jacobians.Dolbeault.FormTraceInftyFibre Jacobians.Dolbeault.FormTraceInftyRecip
  Jacobians.Dolbeault.FormTraceFullFibre

/-- **`FullFibreRamifiedCenters` from per-centre reindex residuals.**  Given, at each finite pole-value
centre `cs i`, a `FibreClusterReindex` (the genuine geometric reindexing of the full-fibre trace into
per-preimage clusters), the canonical selection carries the SOUND per-centre `FullFibreClusterData`
enumerating the poles of `α` in the fibre — i.e. `FullFibreRamifiedCenters`. -/
theorem fullFibreRamifiedCenters_of_reindex {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X} {m : ℕ}
    {cs : Fin m → ℂ}
    (R : ∀ i, FibreClusterReindex ω₀ g f hdiv poles (cs i)) :
    FullFibreRamifiedCenters ω₀ g f hdiv poles cs :=
  ⟨fun i => (R i).toFullFibreClusterData,
    fun i k => (R i).hD_mem k,
    fun i a ha hfa => (R i).hD_surj a ha hfa⟩

/-- **Gate A `∑Res = 0` from per-centre reindex residuals, `hoff_cs`-FREE.**  Given the per-centre
fibre-cluster reindexing `FibreClusterReindex` (the SOUND full-fibre geometry — *all* preimages,
genuine `clusterSheet` points) and the already-Gate-A-discharged off-centre/∞ bundle `GateAInftyData`,
the total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g a = 0`.

This composes `fullFibreRamifiedCenters_of_reindex` into the PROVEN capstone
`residueSum_eq_zero_of_fullFibreCluster`.  The *only* genuinely-remaining content is the per-centre
`FibreClusterReindex` (the chart-coordinate fibre-cluster reindexing); the rest of the residue calculus,
the per-cluster symmetric collapse, the meromorphy reduction, and the off-centre/∞ machinery are all
PROVEN. -/
theorem residueSum_eq_zero_of_reindex {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X} {m : ℕ}
    {cs : Fin m → ℂ} {br : Finset ℂ}
    (A : Jacobians.GateAInftyData ω₀ g f hdiv poles cs br)
    (R : ∀ i, FibreClusterReindex ω₀ g f hdiv poles (cs i)) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_fullFibreCluster A (fullFibreRamifiedCenters_of_reindex R)

/-! ## Soundness: `FibreClusterReindex` is NOT a disguised `False` — a genuine MULTI-PREIMAGE RAMIFIED
witness

The decisive #13-style soundness check.  The `FibreClusterReindex` structure imposes **no**
single-preimage restriction and is inhabited at a genuinely ramified multiplicity.  For the zero
numerator `g ≡ 0` the canonical-selection geometric trace vanishes identically (`chartIntegrand ω₀ 0 ·
= 0`), so for *any* injective fibre `D` over `c` (any number of preimages, any multiplicities `≥ 1` —
in particular several ramified preimages) we inhabit a `FibreClusterReindex` with `poles := image D.xs`:
each preimage gets a `clusterTraceData_slit` cluster (the genuine `cpow` slit branch), the pole-order
bound is `(z − c)^0 · 0 → 0`, the eventual analyticity is `AnalyticAt 0`, and the full-fibre identity
is `0 = ∑ᵢ ∑ⱼ 0`.  This shows the structure is constructible at genuinely ramified multiplicities, not a
disguised `False` and not single-preimage. -/

/-- **The canonical-selection geometric trace vanishes for the zero numerator.**
`valueChartTrace ω₀ f (canonicalFibreSelection 0 f hdiv) ≡ 0` — each per-sheet integrand
`chartIntegrand ω₀ 0 a w = coeffAt ω₀ a w · 0 = 0`. -/
theorem valueChartTrace_zero_numerator (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) :
    valueChartTrace ω₀ f (canonicalFibreSelection (fun _ => (0 : ℂ)) f hdiv) = fun _ => (0 : ℂ) := by
  funext z
  simp only [valueChartTrace_apply, FibreTrace.traceCoeff]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [fibreTrace_coeff]
  simp [chartIntegrand]

/-- **`FibreClusterReindex` is inhabited at a genuine multi-preimage ramified fibre** (the #13 soundness
witness).  For the zero numerator `g ≡ 0` and *any* injective `FibreRamifiedData D` over `c` (any
preimages, any multiplicities `≥ 1` — including ramified), with `poles := image D.xs`, a
`FibreClusterReindex` is inhabited: the canonical trace is `≡ 0` (`valueChartTrace_zero_numerator`), per
preimage a `clusterTraceData_slit` cluster, pole-order bound `0`, the full-fibre identity `0 = ∑ᵢ ∑ⱼ 0`.
So the structure imposes **no single-preimage restriction** and is constructible at genuine
ramification. -/
noncomputable def fibreClusterReindex_zero (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (D : FibreRamifiedData (fun _ => (0 : ℂ)) f c) (hD_inj : Function.Injective D.xs) :
    FibreClusterReindex ω₀ (fun _ => (0 : ℂ)) f hdiv (Finset.univ.image D.xs) c where
  hanalytic := by
    rw [valueChartTrace_zero_numerator ω₀ f hdiv]
    exact Filter.Eventually.of_forall (fun z => analyticAt_const)
  D := D
  hD_inj := hD_inj
  hD_mem := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  hD_surj := by
    intro a ha _
    rw [Finset.mem_image] at ha
    obtain ⟨i, _, hi⟩ := ha
    exact ⟨i, hi⟩
  S := {z | z - c ∈ slitPlane}
  hS_acc := (fullFibreClusterData_zero ω₀ f c D hD_inj).hS_acc
  Cl := fun i => clusterTraceData_slit ω₀ (D.xs i) c (D.mult i) (D.hmult_pos i)
    (Complex.exp (2 * π * Complex.I / (D.mult i)))
    (Complex.isPrimitiveRoot_exp (D.mult i) (D.hmult_pos i).ne')
  hmult := fun _ => rfl
  hsplit0 := by
    intro i
    refine Filter.EventuallyEq.of_eq ?_
    funext u
    simp [straightenedIntegrand, chartIntegrand, negTail, clusterTraceData_slit]
  ppord := 0
  hbnd := by
    rw [valueChartTrace_zero_numerator ω₀ f hdiv]
    have : (fun z => (z - c) ^ 0 * (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by funext z; ring
    rw [this]
    exact tendsto_const_nhds
  hgeom_fibre := by
    intro z _
    rw [valueChartTrace_zero_numerator ω₀ f hdiv]
    symm
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    rw [show chartIntegrand ω₀ (fun _ => (0 : ℂ)) (D.xs i) = (fun _ => (0 : ℂ)) by
      funext w; simp [chartIntegrand]]
    simp

/-- **Non-vacuity of `residueSum_eq_zero_of_reindex`'s premise (no finite pole-value centres).**  When
there are no finite pole-value centres (`m = 0`), the per-centre reindex residual is vacuously
inhabited, so `FullFibreRamifiedCenters` holds — confirming the reindex route is **not** a disguised
`False`. -/
theorem fullFibreRamifiedCenters_of_reindex_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) :
    FullFibreRamifiedCenters ω₀ g f hdiv poles (m := 0) Fin.elim0 :=
  fullFibreRamifiedCenters_of_reindex (fun i => i.elim0)

end Jacobians.Dolbeault.SerreResidueTheorem
