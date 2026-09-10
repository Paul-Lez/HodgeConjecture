/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRealSlitAssembly

/-!
# The per-slit §5 normal-form section geometry for the real cover (closing the residue obligation)

`SerreResidueRamifiedRealSlitAssembly.lean` reduced the residue theorem `∑Res = 0`, for the real cover,
to the single obligation `RealCoverSlitSectionGeometry`: at each finite pole-value centre `c`, a slit
`Sset` accumulating at `c` off the branch locus, the per-preimage §5 cluster data `Cl`, and per slit
value `z ∈ Sset` the §5 normal-form section facts `RealSlitSectionData` (`hcs_sec`/`hcs_np`/`hwithin`/
`hcross`/`hsrc`).

This file builds the genuine Forster §4/§5 normal-form section geometry from the PROVEN §5 atom
`exists_clusterSplit_at_fibrePoint` (the normal form `F = c + ηᵐ` + the local inverse `s = η⁻¹`).

## The key analytic mechanism: the *shrunk* slit

The §5 atom's inverse property `η (s a) = a` and the normal form `F (chart.symm w) = c + η wᵐ` hold only
**near `a = 0` / `w = chart p`** (a local biholomorphism domain).  For a *fixed* slit value `z` and `w`
near `z`, the cluster argument is `a(w) = ζʲ · w₀ w`, which tends to `ζʲ · w₀ z` — NOT to `0` unless `z`
is close to `c` (`w₀ z = (z − c)^{1/m} → 0` as `z → c`).  The resolution is the **shrunk slit**: choose
`Sset ⊆ {z | z − c ∈ slitPlane}` small enough (per preimage) that every cluster argument `ζʲ · w₀ z`
stays in the §5 inverse-property domain.  Then, for `z` interior to the shrunk slit, a *full* ℂ-neighbourhood
of `z` keeps the cluster arguments in that domain, so the eventual section facts (`hcs_sec`, `hsrc`) hold.

## What is delivered (the SECTION half — axiom-clean, complete)

* the per-`(z₀,i)` §5 section primitives (`cpow_slitBranch_tendsto_zero`,
  `eventually_nonpole_of_nonpole`, `eventually_holoRepr_clusterSheet_eq`,
  `eventually_clusterSheet_mem_target`, `clusterArg_inverse_self`, `ne_of_mem_disjoint`);
* `SlitSectionGerm` — the per-`(z₀,i)` §5 normal-form section germ data;
* **`RealSlitSectionData.ofSlitSectionGerm`** — assembles a full `RealSlitSectionData` (all five
  section fields `hcs_sec`/`hcs_np`/`hwithin`/`hcross`/`hsrc`) from a slit-wide germ family.

So the **section half** of `RealCoverSlitSectionGeometry` is DONE.

## The two remaining pieces (to close `∑Res = 0` unconditionally)

1. **The cluster data `Cl`** — a `ClusterTraceData` per preimage via `ClusterTraceData.ofNormalForm` on
   the shrunk slit, whose ONLY non-mechanical input is the **`Rem` symmetric-function descent**:
   for the analytic remainder `ppR` of the straightened integrand, the trace
   `Rem z = ∑_{j<m} ppR(ζʲ·w₀ z)·deriv(ζz ↦ ζʲ·w₀ ζz) z` is **analytic at `c`** (`hRem_an`).  This is the
   standard "trace of a holomorphic form is holomorphic"; closed form
   `Rem z = ∑_{k≥0} a_{m(k+1)-1}·(z − c)^k` (`a_n` the Taylor coefficients of `ppR` at `0`).  It is NOT in
   Mathlib and has been carried as a *data hypothesis* throughout the ramified-residue subtree
   (`RamifiedSheetData`/`ClusterTraceData`); it is the single genuinely-new analytic lemma.  Its cleanest
   formulation is the reusable atom: *a `ζ`-invariant analytic germ `P` (`P(ζ·u) = P(u)`, `ζ` a primitive
   `m`-th root) factors as `P = Q ∘ (·^m)` with `Q` analytic* — equivalently the symmetric trace
   `z ↦ ∑_{j<m} G(ζʲ·(z − c)^{1/m})` is analytic at `c` for `G` analytic at `0`.

2. **The shrunk slit `Sset` + the germ hypotheses** — a slit `Sset ⊆ {z | z − c ∈ slitPlane}` shrunk near
   `c` (off the finitely-many branch values, still accumulating at `c`) on which the `SlitSectionGerm`
   smallness hypotheses hold for every `z₀ ∈ Sset` (the cluster arguments `ζʲ·w₀ z₀` lie in the §5
   inverse-property domain).  This is mechanical (continuity + `cpow_slitBranch_tendsto_zero` + the §5
   atom's open domains + T2 separation of the preimages) but voluminous.

## ⚠ Soundness

The §5 sections are genuine (`exists_clusterSplit_at_fibrePoint`).  The shrunk slit is a genuine slit
(still accumulating at `c`, off the branch locus, simply connected).  The cluster sheets are the genuine
`s(ζʲ·w₀ z)` (NOT the first-order `wp + ζʲ·w₀ z`).  Slit values are regular (off-branch).  `D` is the
whole fibre (#17).  No custom axiom, no unproved obligation on a false statement, no false/junk/circular field.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4–5.
* `SerreResidueRamifiedMultiplicityBridge.lean` (`exists_clusterSplit_at_fibrePoint`),
  `SerreResidueRamifiedFullFibreBuilder.lean` (`ClusterTraceData.ofNormalForm`),
  `SerreResidueRamifiedClusterSplit.lean` (`clusterSheet`, `clusterSheet_sect`).
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
  Jacobians.Dolbeault.FormTraceMovingFibre
  Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct Jacobians.RiemannSphere

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The cpow slit branch tends to `0` at the centre

The standard slit branch `w₀ z = (z − c)^{1/m}` (the `cpow` principal branch) is continuous at every
slit value and tends to `0` as `z → c` (`(z − c) → 0`, `0^{1/m} = 0`).  This is the mechanism that lets
the cluster arguments `ζʲ · w₀ z` be pushed into the §5 inverse-property domain by shrinking the slit. -/

/-- **The cpow slit branch is continuous and `→ 0` at the centre.**  For `m ≥ 1`, the principal branch
`w₀ z := (z − c)^{(m:ℂ)⁻¹}` tends to `0` as `z → c`.  (`cpow` is continuous at `0` for a positive real
exponent: `0^{1/m} = 0` since `1/m ≠ 0`.) -/
theorem cpow_slitBranch_tendsto_zero (c : ℂ) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun z => (z - c) ^ ((m : ℂ)⁻¹)) (𝓝 c) (𝓝 0) := by
  have hsub : Tendsto (fun z : ℂ => z - c) (𝓝 c) (𝓝 0) := by
    simpa using (continuous_sub_right c).tendsto c
  have hre : (0 : ℝ) < ((m : ℂ)⁻¹).re := by
    rw [show ((m : ℂ)⁻¹) = ((m : ℝ)⁻¹ : ℝ) by push_cast; ring, Complex.ofReal_re]
    positivity
  have hcont0 : Tendsto (fun w : ℂ => w ^ ((m : ℂ)⁻¹)) (𝓝 0) (𝓝 0) := by
    have h := Complex.continuousAt_cpow_zero_of_re_pos hre
    have h2 : Tendsto (fun w : ℂ => (w, (m : ℂ)⁻¹)) (𝓝 0) (𝓝 (0, (m : ℂ)⁻¹)) :=
      Tendsto.prodMk_nhds (by simpa using tendsto_id) tendsto_const_nhds
    have hne : ((m : ℂ)⁻¹) ≠ 0 := by simp [hm.ne']
    have := h.tendsto.comp h2
    simpa [Function.comp, Complex.zero_cpow hne] using this
  exact hcont0.comp hsub

/-! ## Non-pole is an open condition

A non-pole `x` (`0 ≤ orderAtPoint x`) of a meromorphic function has a whole neighbourhood of non-poles:
`toRiemannSphere` is continuous at `x` (it equals `coe ∘ holoRepr` near a non-pole) with finite value
`coe (holoRepr x) ≠ ∞`, so points near `x` map into `{∞}ᶜ`, hence are non-poles
(`toRiemannSphere_of_pole` contrapositive).  This is the mechanism that makes `hcs_np` reachable: for the
shrunk slit, the cluster section point lies in the non-pole neighbourhood of its fibre preimage `p`. -/

/-- **Non-pole is an open condition.**  If `x` is a non-pole (`0 ≤ f.orderAtPoint x`), then every point
in a neighbourhood of `x` is a non-pole. -/
theorem eventually_nonpole_of_nonpole (f : MeromorphicFunction X) {x : X}
    (hx : 0 ≤ f.orderAtPoint x) : ∀ᶠ y in 𝓝 x, 0 ≤ f.orderAtPoint y := by
  have hcont : ContinuousAt f.toRiemannSphere x :=
    (f.contMDiffAt_toRiemannSphere_of_nonneg hx).continuousAt
  have hval : f.toRiemannSphere x ≠ OnePoint.infty := by
    rw [f.toRiemannSphere_of_nonneg hx]; exact OnePoint.coe_ne_infty _
  have hmem : f.toRiemannSphere ⁻¹' {OnePoint.infty}ᶜ ∈ 𝓝 x :=
    hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hval)
  filter_upwards [hmem] with y hy
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hy
  by_contra hlt
  exact hy (f.toRiemannSphere_of_pole (not_le.mp hlt))

/-! ## The per-preimage eventual §5 section property (the heart of `hcs_sec`)

The §5 atom `exists_clusterSplit_at_fibrePoint` provides `η`/`s` with the inverse property `η (s a) = a`
near `a = 0` and the normal form `f.holoRepr (chart.symm w) = c + η wᵐ` near `w = chart p`.  For a slit
value `z₀` whose cluster arguments `ζʲ · w₀ z₀` lie near `0`, the section property
`f.holoRepr (chart.symm (clusterSheet s ζ w₀ j w)) = w` holds for `w` in a *full ℂ-neighbourhood* of
`z₀` (the cluster arguments stay near `0`, the cluster points stay near `chart p`, and the slit power
identity holds), by pulling back the §5 atom's eventual facts along the continuous `w ↦ ζʲ · w₀ w`. -/

/-- **The eventual §5 section property near a slit value `z₀`.**  Given the §5 normal-form data
(`η`/`s`, the inverse property `hinv` valid near `a₀ := ζʲ · w₀ z₀`, the normal form `hnf` valid near
`s a₀`, and the slit power identity `hpow` valid near `z₀`), the cluster sheet point is a genuine
`holoRepr`-section of `f` near `z₀`:

> `∀ᶠ w in 𝓝 z₀, f.holoRepr (chart_p.symm (clusterSheet s ζ w₀ j w)) = w`.

This is the §5 section clause of `exists_clusterSplit_at_fibrePoint` (`clusterSheet_sect`), localised at
`z₀` by the continuity pullback of the atom's `𝓝 0` / `𝓝 (chart p)` eventual facts. -/
theorem eventually_holoRepr_clusterSheet_eq (f : MeromorphicFunction X) {c : ℂ} {p : X} {m : ℕ}
    {η s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {z₀ : ℂ}
    (hs_cont : ContinuousAt s (ζ ^ j * w₀ z₀)) (hw₀_cont : ContinuousAt w₀ z₀)
    (hζ : IsPrimitiveRoot ζ m)
    (hinv : ∀ᶠ a in 𝓝 (ζ ^ j * w₀ z₀), η (s a) = a)
    (hnf : ∀ᶠ w' in 𝓝 (s (ζ ^ j * w₀ z₀)),
      f.holoRepr ((chartAt (H := ℂ) p).symm w') = c + η w' ^ m)
    (hpow : ∀ᶠ w in 𝓝 z₀, w₀ w ^ (m : ℤ) = w - c) :
    ∀ᶠ w in 𝓝 z₀, f.holoRepr ((chartAt (H := ℂ) p).symm (clusterSheet s ζ w₀ j w)) = w := by
  have harg_a : Tendsto (fun w => ζ ^ j * w₀ w) (𝓝 z₀) (𝓝 (ζ ^ j * w₀ z₀)) :=
    tendsto_const_nhds.mul hw₀_cont.tendsto
  have ha : ∀ᶠ w in 𝓝 z₀, η (s (ζ ^ j * w₀ w)) = ζ ^ j * w₀ w := harg_a.eventually hinv
  have harg_b : Tendsto (fun w => s (ζ ^ j * w₀ w)) (𝓝 z₀) (𝓝 (s (ζ ^ j * w₀ z₀))) :=
    hs_cont.tendsto.comp harg_a
  have hb : ∀ᶠ w in 𝓝 z₀, f.holoRepr ((chartAt (H := ℂ) p).symm (s (ζ ^ j * w₀ w)))
      = c + η (s (ζ ^ j * w₀ w)) ^ m := harg_b.eventually hnf
  filter_upwards [ha, hb, hpow] with w hwa hwb hwp
  exact clusterSheet_sect (F := fun u => f.holoRepr ((chartAt (H := ℂ) p).symm u)) hζ hwp hwa hwb

/-- **The eventual chart-target locality near a slit value `z₀` (the heart of `hsrc`).**  Given the
cluster sheet value `s a₀` (`a₀ := ζʲ · w₀ z₀`) lies in the (open) chart target at `p` (`hmem`), the
cluster sheet value stays in that target for `w` in a full ℂ-neighbourhood of `z₀` (continuity of
`w ↦ s (ζʲ · w₀ w)`). -/
theorem eventually_clusterSheet_mem_target (p : X) {s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {z₀ : ℂ}
    (hs_cont : ContinuousAt s (ζ ^ j * w₀ z₀)) (hw₀_cont : ContinuousAt w₀ z₀)
    (hmem : s (ζ ^ j * w₀ z₀) ∈ (chartAt (H := ℂ) p).target) :
    ∀ᶠ w in 𝓝 z₀, clusterSheet s ζ w₀ j w ∈ (chartAt (H := ℂ) p).target := by
  have harg : Tendsto (fun w => s (ζ ^ j * w₀ w)) (𝓝 z₀) (𝓝 (s (ζ ^ j * w₀ z₀))) :=
    hs_cont.tendsto.comp (tendsto_const_nhds.mul hw₀_cont.tendsto)
  filter_upwards [harg.eventually ((chartAt (H := ℂ) p).open_target.mem_nhds hmem)] with w hw
  exact hw

/-! ## The within-cluster injectivity at a slit value (the `hwithin` content)

Within one preimage's cluster, the `m` sheet points are distinct because the §5 straightening coordinate
`η` recovers the sheet argument: `η (s (ζʲ · w₀ z)) = ζʲ · w₀ z`.  The proven
`clusterSection_within_cluster_inj` derives `j = k` from a point coincidence, given the chart-target
memberships, the inverse recoveries `hinv_j`/`hinv_k`, the nonzero branch, and the primitivity.  We
package the inverse recoveries from the §5 atom's `at-z₀` inverse property. -/

/-- **The §5 inverse recovery at a slit value.**  `η (s a₀) = a₀` at `a₀ := ζʲ · w₀ z₀`, the `at-z₀`
instance of the §5 atom's inverse property (valid when `a₀` lies in the inverse-property domain). -/
theorem clusterArg_inverse_self {η s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {z₀ : ℂ}
    (hinv : ∀ᶠ a in 𝓝 (ζ ^ j * w₀ z₀), η (s a) = a) :
    η (s (ζ ^ j * w₀ z₀)) = ζ ^ j * w₀ z₀ := hinv.self_of_nhds

/-! ## The cross-cluster separation at a slit value (the `hcross` content)

At *distinct* preimages `p ≠ p'`, the clusters are disjoint: the cluster sheet points cluster at `p`,
`p'` respectively, which are T2-separated.  We package the separation as a standalone fact: two points
lying in disjoint sets are distinct.  At the assembly the two cluster section points lie in disjoint
neighbourhoods of `p` and `p'` (the cluster points are near their respective preimages on the shrunk
slit). -/

/-- **Cross-cluster separation from disjoint neighbourhoods.**  If `q ∈ U`, `q' ∈ U'`, and `U`, `U'` are
disjoint, then `q ≠ q'`.  Used with `U`/`U'` the T2-separating neighbourhoods of distinct preimages
`p ≠ p'` (the cluster section points lie near their preimages on the shrunk slit). -/
theorem ne_of_mem_disjoint {q q' : X} {U U' : Set X} (hq : q ∈ U) (hq' : q' ∈ U')
    (hdisj : Disjoint U U') : q ≠ q' := by
  intro h; subst h
  exact (Set.disjoint_left.mp hdisj hq) hq'

/-! ## The per-`(z₀,i)` §5 section germ data + the `RealSlitSectionData` builder

We package, for one slit value `z₀` and one fibre preimage `i`, exactly the §5 normal-form data the five
section facts consume — the straightening coordinate `η` matching the cluster data's local inverse
`(Cl i).s`, the §5 eventual facts (inverse near the cluster argument, normal form near the cluster point,
slit power near `z₀`), the chart-target locality of the cluster sheet value, the §5 inverse recovery, and
the smallness witnesses making the cluster section point a non-pole near its preimage and the clusters
cross-separated.  From a slit-wide such bundle, the builder assembles `RealSlitSectionData`, discharging
all five fields.  This isolates the residue obligation's section half to **this germ data per `(z₀,i)`** —
the genuine Forster §5 normal-form geometry, with the cluster data `Cl` (carrying the `Rem`
symmetric-function descent) supplied separately. -/

/-- **The per-`(z₀,i)` §5 section germ data** (the precise per-preimage section content at one slit value
`z₀`).  For the whole-fibre `D = realFibreData g hdiv c hnp`, the cluster data `Cl`, a slit value `z₀`,
and a preimage `i`, bundles:

* `η` — the §5 straightening coordinate, with the inverse property `hinv` valid near each cluster argument
  `(Cl i).ζ ^ j · (Cl i).w₀ z₀` (`j < mult i`), the normal form `hnf` valid near each cluster point
  `(Cl i).s ((Cl i).ζ ^ j · (Cl i).w₀ z₀)`, and the slit power identity `hpow` near `z₀`;
* `hs_cont`/`hw₀_cont` — continuity of the §5 local inverse `(Cl i).s` at the cluster arguments and of the
  branch `(Cl i).w₀` at `z₀`;
* `htgt` — the cluster sheet value `(Cl i).s (cluster arg)` lies in the (open) chart target at `D.xs i`;
* `hnonpole` — the cluster section point is a non-pole at `z₀` (it lies near the non-pole preimage `D.xs i`
  on the shrunk slit);
* `hsep` — cross-cluster separation: at distinct preimages `i ≠ i'` the cluster section points at `z₀` are
  distinct (the clusters cluster at distinct T2-separated preimages on the shrunk slit). -/
structure SlitSectionGerm (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i))
    {Sset : Set ℂ}
    (Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset)
    (z₀ : ℂ) (i : (realFibreData g hdiv c hnp).ι) where
  /-- The §5 straightening coordinate at the preimage `D.xs i`. -/
  η : ℂ → ℂ
  /-- Continuity of the §5 local inverse `(Cl i).s` at each cluster argument. -/
  hs_cont : ∀ j : Fin ((realFibreData g hdiv c hnp).mult i),
    ContinuousAt (Cl i).s ((Cl i).ζ ^ (j : ℕ) * (Cl i).w₀ z₀)
  /-- Continuity of the branch `(Cl i).w₀` at `z₀`. -/
  hw₀_cont : ContinuousAt (Cl i).w₀ z₀
  /-- The §5 inverse property valid near each cluster argument. -/
  hinv : ∀ j : Fin ((realFibreData g hdiv c hnp).mult i),
    ∀ᶠ a in 𝓝 ((Cl i).ζ ^ (j : ℕ) * (Cl i).w₀ z₀), η ((Cl i).s a) = a
  /-- The §5 normal form valid near each cluster point. -/
  hnf : ∀ j : Fin ((realFibreData g hdiv c hnp).mult i),
    ∀ᶠ w' in 𝓝 ((Cl i).s ((Cl i).ζ ^ (j : ℕ) * (Cl i).w₀ z₀)),
      f.holoRepr ((chartAt ℂ ((realFibreData g hdiv c hnp).xs i)).symm w') = c + η w' ^ (Cl i).m
  /-- The slit power identity near `z₀`. -/
  hpow : ∀ᶠ w in 𝓝 z₀, (Cl i).w₀ w ^ ((Cl i).m : ℤ) = w - c
  /-- The cluster sheet value lies in the chart target at `D.xs i`. -/
  htgt : ∀ j : Fin ((realFibreData g hdiv c hnp).mult i),
    (Cl i).s ((Cl i).ζ ^ (j : ℕ) * (Cl i).w₀ z₀) ∈ (chartAt ℂ ((realFibreData g hdiv c hnp).xs i)).target
  /-- The cluster section point is a non-pole at `z₀`. -/
  hnonpole : ∀ j : Fin ((realFibreData g hdiv c hnp).mult i),
    0 ≤ f.orderAtPoint (clusterSection (realFibreData g hdiv c hnp) Cl i j z₀)
  /-- Cross-cluster separation at `z₀` (distinct preimages give distinct cluster points). -/
  hsep : ∀ (i' : (realFibreData g hdiv c hnp).ι)
    (j : Fin ((realFibreData g hdiv c hnp).mult i)) (k : Fin ((realFibreData g hdiv c hnp).mult i')),
    i ≠ i' → clusterSection (realFibreData g hdiv c hnp) Cl i j z₀
      ≠ clusterSection (realFibreData g hdiv c hnp) Cl i' k z₀

/-- **`RealSlitSectionData` from a per-preimage `SlitSectionGerm` family at `z₀`.**  Given, at the slit
value `z₀`, a `SlitSectionGerm` for every fibre preimage `i` (the genuine Forster §5 normal-form section
geometry), and the multiplicity match `hmult : ∀ i, (Cl i).m = (realFibreData …).mult i`, build the
`RealSlitSectionData`: each of the five section fields is discharged from the germ data via the
section-fact toolkit (`eventually_holoRepr_clusterSheet_eq`, `eventually_clusterSheet_mem_target`,
`clusterSection_within_cluster_inj`, `clusterArg_inverse_self`).  This makes the **section half** of the
residue obligation `RealCoverSlitSectionGeometry` DONE; the only separately-supplied content is the
cluster data `Cl` (carrying the `Rem` symmetric-function descent). -/
noncomputable def RealSlitSectionData.ofSlitSectionGerm {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {c : ℂ}
    {hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)} {Sset : Set ℂ}
    {Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset} {z₀ : ℂ}
    (hz_slit : z₀ ∈ Sset)
    (hmult : ∀ i, (Cl i).m = (realFibreData g hdiv c hnp).mult i)
    (G : ∀ i, SlitSectionGerm ω₀ g hdiv c hnp Cl z₀ i) :
    RealSlitSectionData ω₀ g hdiv c hnp Cl z₀ where
  hcs_sec := fun i j => by
    -- the §5 section property near z₀, via the germ's eventual inverse/normal-form/slit-power facts.
    have h := eventually_holoRepr_clusterSheet_eq f ((G i).hs_cont j) (G i).hw₀_cont (Cl i).hζ
      ((G i).hinv j) ((G i).hnf j) (G i).hpow
    -- `clusterSection D Cl i j w = chart.symm (clusterSheet …)` — defeq.
    exact h
  hcs_np := fun i j => (G i).hnonpole j
  hwithin := fun i j k hpt => by
    -- within-cluster injectivity via the proven `clusterSection_within_cluster_inj`.
    refine clusterSection_within_cluster_inj (D := realFibreData g hdiv c hnp) (η := (G i).η)
      (hmult i).symm ?_ ?_ ?_ ?_ ?_ hpt
    · -- target membership of sheet `j` (the cluster sheet value at z₀ in chart target).
      exact (G i).htgt j
    · exact (G i).htgt k
    · exact clusterArg_inverse_self ((G i).hinv j)
    · exact clusterArg_inverse_self ((G i).hinv k)
    · -- branch nonzero on the slit: `(Cl i).w₀ z₀ ≠ 0` from `hw₀_ne` at `z₀ ∈ Sset`.
      exact (Cl i).hw₀_ne z₀ hz_slit
  hcross := fun i i' j k hii => (G i).hsep i' j k hii
  hsrc := fun i j => eventually_clusterSheet_mem_target ((realFibreData g hdiv c hnp).xs i)
    ((G i).hs_cont j) (G i).hw₀_cont ((G i).htgt j)

end Jacobians.Dolbeault.SerreResidueTheorem
