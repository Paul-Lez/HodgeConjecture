/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRemDescent

/-!
# Closing the residue theorem `∑Res = 0` unconditionally — the §5 slit-geometry assembly (Gate-A)

`SerreResidueRamifiedRealSlitSection.lean` proved the **section half** of the residue obligation
(`RealSlitSectionData.ofSlitSectionGerm`): from a per-`(z₀,i)` `SlitSectionGerm` family it assembles a
`RealSlitSectionData` (all five §5 section fields).  `SerreResidueRamifiedRemDescent.lean` proved the
**cluster data** half (`exists_clusterTraceData_descent_at_fibrePoint`): a `ClusterTraceData` with the
`Rem` symmetric-function descent supplied (no longer a data hypothesis), plus the *shrunk slit*
mechanism (`exists_descentSlit`, `eventually_cpowBranch_mem`).
`SerreResidueRamifiedRealSlitAssembly.lean` reduced the residue theorem `∑Res = 0` to the single
obligation `RealCoverSlitSectionGeometry` (per centre: a `RealCenterSlitSectionData`).

This file performs the final assembly: it BUILDS `RealCoverSlitSectionGeometry` for the canonical real
cover, hence closes `∑Res = 0` **unconditionally** via
`residueTheorem_of_realCoverSlitSectionGeometry`.

## The geometric heart: cluster sections converge to their preimages

The cluster section point is `clusterSection D Cl i j z = chart_{p}.symm (s (ζʲ·w₀ z))` (`p = D.xs i`).
As `z → c`, `w₀ z → 0` (`cpow_slitBranch_tendsto_zero`), so `ζʲ·w₀ z → 0`, so the §5 local inverse
`s (ζʲ·w₀ z) → s 0 = chart_p p`, hence `chart_p.symm (s (ζʲ·w₀ z)) → chart_p.symm (chart_p p) = p`.
Thus the cluster section point **converges to the preimage `p`** as `z → c`.  Two consequences,
isolating the hardest §5 section fields:

* `hnonpole` — `p` is a non-pole and non-poles are an open condition
  (`eventually_nonpole_of_nonpole`), so the cluster section point is a non-pole for `z` near `c`;
* `hsep` — at distinct preimages `p ≠ p'` (T2-separated), the cluster section points lie in disjoint
  neighbourhoods of `p`, `p'` for `z` near `c`, hence are distinct (`ne_of_mem_disjoint`).

## ⚠ Soundness

The §5 sections are genuine (`exists_clusterSplit_at_fibrePoint`).  The shrunk slit is a genuine slit
(still accumulating at `c`, off the branch locus).  The cluster sheets are the genuine `s(ζʲ·w₀ z)`.
Slit values regular (off-branch).  `D` = the whole fibre (#17).  The `Rem` descent is the genuine
symmetric sum.  `hanalytic`/`hbnd` are the proven canonical-selection machinery
(`hreg_canonical_at_goodValue_sound` / `hbnd_canonical_sound_full`), `pp` from
`exists_principalPart_meromorphicAt`, `hmult = rfl`.  No custom axiom, no unproved obligation on a false statement, no
false/junk/circular field.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4–5, §17.3.
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3.
* `SerreResidueRamifiedRealSlitSection.lean` (`RealSlitSectionData.ofSlitSectionGerm`, `SlitSectionGerm`,
  `eventually_nonpole_of_nonpole`, `cpow_slitBranch_tendsto_zero`),
  `SerreResidueRamifiedRemDescent.lean` (`exists_clusterTraceData_descent_at_fibrePoint`,
  `exists_descentSlit`, `eventually_cpowBranch_mem`),
  `SerreResidueRamifiedRealSlitAssembly.lean` (`RealCenterSlitSectionData`,
  `RealCoverSlitSectionGeometry`, `residueTheorem_of_realCoverSlitSectionGeometry`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.SymmetricDescent
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart
  Jacobians.Dolbeault.FormTraceMovingFibre
  Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct Jacobians.RiemannSphere

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The cluster section converges to its preimage as `z → c`

The geometric heart of `hnonpole`/`hsep`: for the §5 local inverse `s` (analytic at `0`, `s 0 = chart p`),
the cpow slit branch `w₀ z = (z − c)^{1/m}` (`→ 0`), and any sheet index `j`, the cluster section point
`chart_p.symm (s (ζʲ·w₀ z))` tends to `p` as `z → c`. -/

/-- **The cluster section point tends to its preimage `p` as `z → c`.**  For the §5 local inverse `s`
(continuous at `0` with `s 0 = chart_p p`) and the `cpow` slit branch `w₀ z = (z − c)^{1/m}` (`m ≥ 1`),
the cluster section point `chart_p.symm (s (ζʲ · w₀ z))` tends to `p` as `z → c` (within any filter
`≤ 𝓝 c`).  Mechanism: `w₀ z → 0` (`cpow_slitBranch_tendsto_zero`), `s` continuous so
`s (ζʲ·w₀ z) → s 0 = chart_p p`, and `chart_p.symm` continuous at `chart_p p` with
`chart_p.symm (chart_p p) = p`. -/
theorem clusterSectionPoint_tendsto_preimage (p : X) {s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {c : ℂ} {m : ℕ}
    (hm : 0 < m) (hs_cont : ContinuousAt s 0) (hs0 : s 0 = (chartAt ℂ p) p)
    (hw₀_eq : w₀ =ᶠ[𝓝 c] fun z => (z - c) ^ ((m : ℂ)⁻¹)) :
    Tendsto (fun z => (chartAt ℂ p).symm (s (ζ ^ j * w₀ z))) (𝓝 c) (𝓝 p) := by
  -- `w₀ z → 0`.
  have hw₀0 : Tendsto w₀ (𝓝 c) (𝓝 0) :=
    (cpow_slitBranch_tendsto_zero c hm).congr' hw₀_eq.symm
  -- `ζʲ · w₀ z → 0`.
  have harg : Tendsto (fun z => ζ ^ j * w₀ z) (𝓝 c) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ζ ^ j)).mul hw₀0
  -- `s (ζʲ·w₀ z) → s 0 = chart_p p`.
  have hs : Tendsto (fun z => s (ζ ^ j * w₀ z)) (𝓝 c) (𝓝 ((chartAt ℂ p) p)) := by
    rw [← hs0]; exact hs_cont.tendsto.comp harg
  -- `chart_p.symm` continuous at `chart_p p`, with `chart_p.symm (chart_p p) = p`.
  have hsymm : ContinuousAt (chartAt ℂ p).symm ((chartAt ℂ p) p) := by
    have htgt : (chartAt ℂ p) p ∈ (chartAt ℂ p).target :=
      (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    exact (chartAt ℂ p).continuousAt_symm htgt
  have hsymm_p : (chartAt ℂ p).symm ((chartAt ℂ p) p) = p :=
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hcomp := (hsymm.tendsto).comp hs
  rw [hsymm_p] at hcomp
  exact hcomp

/-- **The cluster section point is a non-pole near `c` (the `hnonpole` content, eventual form).**  At a
non-pole preimage `p` of `f`, with the §5 local inverse `s` (continuous at `0`, `s 0 = chart_p p`) and the
`cpow` slit branch `w₀`, the cluster section point `chart_p.symm (s (ζʲ·w₀ z))` is a non-pole of `f` for
`z` in a neighbourhood of `c` (it tends to the non-pole `p`, and non-poles are open). -/
theorem eventually_clusterSectionPoint_nonpole (f : MeromorphicFunction X) {p : X}
    (hp_np : 0 ≤ f.orderAtPoint p) {s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {c : ℂ} {m : ℕ}
    (hm : 0 < m) (hs_cont : ContinuousAt s 0) (hs0 : s 0 = (chartAt ℂ p) p)
    (hw₀_eq : w₀ =ᶠ[𝓝 c] fun z => (z - c) ^ ((m : ℂ)⁻¹)) :
    ∀ᶠ z in 𝓝 c, 0 ≤ f.orderAtPoint ((chartAt ℂ p).symm (s (ζ ^ j * w₀ z))) := by
  have htend := clusterSectionPoint_tendsto_preimage p hm hs_cont hs0 hw₀_eq (ζ := ζ) (j := j)
  exact htend.eventually (eventually_nonpole_of_nonpole f hp_np)

/-! ## A reusable "transport a `𝓝 0` fact to an open `𝓝 c` set along the cpow branch" helper

`exists_descentSlit` transported one *equation* along the cpow branch.  Here we extract the underlying
device as a reusable open-set producer: for any property `P` holding on a `𝓝 0` neighbourhood, there is
an open `V ∋ c` on which `P` holds at the cpow branch for all `z ∈ V`.  Used to build the common shrunk
slit serving all the eventual §5 facts (inverse, normal form, analyticity, pp-split, non-pole) at once. -/

/-- **An open `𝓝 c` set on which a `𝓝 0` property holds along the cpow branch.**  For any property `P`
holding eventually in `𝓝 0`, there is an open `V ∋ c` with `P ((z − c)^{1/m})` for every `z ∈ V`. -/
theorem exists_open_cpowBranch_mem (c : ℂ) {m : ℕ} (hm : 0 < m) {P : ℂ → Prop}
    (hP : ∀ᶠ u in 𝓝 (0 : ℂ), P u) :
    ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧ ∀ z ∈ V, P ((z - c) ^ ((m : ℂ)⁻¹)) := by
  have hev := eventually_cpowBranch_mem c hm hP
  rw [Filter.eventually_iff, _root_.mem_nhds_iff] at hev
  obtain ⟨V, hVsub, hVopen, hcV⟩ := hev
  exact ⟨V, hVopen, hcV, fun z hz => hVsub hz⟩

/-- **An open `𝓝 c` set on which a property of `z` holds (from an eventual `𝓝 c` fact).**  Unpacks an
`∀ᶠ z in 𝓝 c, P z` into an open `V ∋ c` with `P` on it. -/
theorem exists_open_of_eventually_nhds (c : ℂ) {P : ℂ → Prop} (hP : ∀ᶠ z in 𝓝 c, P z) :
    ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧ ∀ z ∈ V, P z := by
  rw [Filter.eventually_iff, _root_.mem_nhds_iff] at hP
  obtain ⟨V, hVsub, hVopen, hcV⟩ := hP
  exact ⟨V, hVopen, hcV, fun z hz => hVsub hz⟩

/-! ## Transporting a punctured `𝓝[≠] 0` property along the cpow branch (the `hpp_split_sheet` device)

The principal-part split holds on a *punctured* neighbourhood `𝓝[≠] 0` of the straightening coordinate.
Pulled back along the cpow branch `z ↦ ζʲ · (z − c)^{1/m}` restricted to the slit `{z | z − c ∈ slitPlane}`
(where the branch is nonzero, `ζʲ ≠ 0`, and `→ 0`), the split holds at the sheet argument for every slit
value near `c`. -/

/-- **The cpow sheet argument maps the slit-at-`c` filter into `𝓝[≠] 0`.**  For `m ≥ 1`, `ζ` a primitive
`m`-th root, and the slit `slit := {z | z − c ∈ slitPlane}`, the map `z ↦ ζʲ · (z − c)^{1/m}` carries
`𝓝[slit] c` into `𝓝[≠] 0`: it tends to `0` (cpow branch), and on the slit the value is nonzero
(`slitPlane_ne_zero` + `ζʲ ≠ 0`). -/
theorem cpowSheetArg_tendsto_punctured (c : ℂ) {m : ℕ} (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (j : ℕ) :
    Tendsto (fun z => ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) (𝓝[{z : ℂ | z - c ∈ slitPlane}] c) (𝓝[≠] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · -- tends to 0
    have h0 : Tendsto (fun z => (z - c) ^ ((m : ℂ)⁻¹))
        (𝓝[{z : ℂ | z - c ∈ slitPlane}] c) (𝓝 0) :=
      (cpow_slitBranch_tendsto_zero c hm).mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := ζ ^ j)).mul h0
  · -- eventually nonzero on the slit
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hζne : ζ ^ j ≠ 0 := pow_ne_zero _ (hζ.ne_zero hm.ne')
    have hw₀ne : (z - c) ^ ((m : ℂ)⁻¹) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero hz))
    exact mul_ne_zero hζne hw₀ne

/-- **Transport of a `𝓝[≠] 0` property to an open `𝓝 c` set along the cpow sheet argument.**  For `P`
holding eventually in `𝓝[≠] 0`, there is an open `V ∋ c` such that, for every slit value `z ∈ V`
(`z − c ∈ slitPlane`), `P (ζʲ · (z − c)^{1/m})` holds.  This supplies the `hpp_split_sheet` punctured-
split hypothesis on the shrunk slit `V ∩ slit`. -/
theorem exists_open_cpowSheetArg_punctured (c : ℂ) {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (j : ℕ) {P : ℂ → Prop} (hP : ∀ᶠ u in 𝓝[≠] (0 : ℂ), P u) :
    ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧
      ∀ z ∈ V, z - c ∈ slitPlane → P (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) := by
  have hev : ∀ᶠ z in 𝓝[{z : ℂ | z - c ∈ slitPlane}] c, P (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) :=
    (cpowSheetArg_tendsto_punctured c hm hζ j).eventually hP
  rw [eventually_nhdsWithin_iff, Filter.eventually_iff, _root_.mem_nhds_iff] at hev
  obtain ⟨V, hVsub, hVopen, hcV⟩ := hev
  exact ⟨V, hVopen, hcV, fun z hz hslit => hVsub hz hslit⟩

/-! ## The `s`-composed cpow branch lands near `chart p` (the `hnf`/`htgt` device)

For the §5 local inverse `s` (continuous at `0`, `s 0 = chart_p p`), the composed map
`z ↦ s (ζʲ · (z − c)^{1/m})` tends to `chart_p p` as `z → c`.  So `s (sheet arg)` lands in any given open
neighbourhood of `chart_p p` for `z` near `c` — supplying the normal-form domain (`hnf`) and the chart-
target membership (`htgt`) on the shrunk slit. -/

/-- **The `s`-composed cpow sheet argument tends to `chart_p p`.**  For `m ≥ 1`, `s` continuous at `0`
with `s 0 = chart_p p`, the map `z ↦ s (ζʲ · (z − c)^{1/m})` tends to `chart_p p` as `z → c`. -/
theorem sComp_cpowSheetArg_tendsto (p : X) {s : ℂ → ℂ} {ζ : ℂ} {j : ℕ} (c : ℂ) {m : ℕ}
    (hm : 0 < m) (hs_cont : ContinuousAt s 0) (hs0 : s 0 = (chartAt ℂ p) p) :
    Tendsto (fun z => s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))) (𝓝 c) (𝓝 ((chartAt ℂ p) p)) := by
  have harg : Tendsto (fun z => ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) (𝓝 c) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ζ ^ j)).mul (cpow_slitBranch_tendsto_zero c hm)
  rw [← hs0]; exact hs_cont.tendsto.comp harg

/-! ## The per-preimage §5 datum on a shrunk-slit neighbourhood

We bundle, for one non-pole fibre preimage `p = D.xs i` of multiplicity `m = (localDeg f (coe c) p).toNat`,
all the *slit-independent* §5 / principal-part / descent data (the §5 atom's straightening `η`/local
inverse `s`, the Laurent principal part `ppN`/`ppb`/`ppR`, the descent germ `G`) together with one open
neighbourhood `V ∋ c` on which every per-slit-value fact needed downstream holds at the `cpow` sheet
arguments.  This is the per-preimage extraction; the centre-level assembly intersects the `V`'s over the
finite fibre and reads off both the cluster data `Cl i` and the §5 section germs. -/

/-- **The per-preimage §5 datum on a shrunk-slit nbhd `V`** (the slit-independent §5/pp/descent package).
For a non-pole fibre preimage `p` of multiplicity `m` (`ζ` a primitive `m`-th root), bundles the §5 atom
(`η`/`s` with inverse `hinv0` near `0` and normal form `hnf0` near `chart_p p`), the Laurent principal
part (`ppN`/`ppb`/`ppR`/`hppR_an`/`hsplit0`), the descent germ (`G`/`hG`), and an open `V ∋ c` on which —
for `z ∈ V` off-slit-restricted — the cpow sheet arguments satisfy: `s`-analyticity (`hVs_an`), the
principal-part split (`hVpp_split`), the descent identity (`hVsmall`), the inverse-property domain
membership (`hVinv_mem`), the normal-form domain membership (`hVnf_mem`), and the chart-target membership
(`hVtgt`). -/
structure Fibre5Datum (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (f : MeromorphicFunction X) (c : ℂ) (p : X) (m : ℕ) where
  /-- `m ≥ 1`. -/
  hm : 0 < m
  /-- A primitive `m`-th root. -/
  ζ : ℂ
  /-- `ζ` is primitive. -/
  hζ : IsPrimitiveRoot ζ m
  /-- The §5 straightening coordinate. -/
  η : ℂ → ℂ
  /-- The §5 local inverse `s = η⁻¹`. -/
  s : ℂ → ℂ
  /-- `s` analytic at `0`. -/
  hs_an : AnalyticAt ℂ s 0
  /-- `s 0 = chart_p p`. -/
  hs0 : s 0 = (chartAt ℂ p) p
  /-- `deriv s 0 ≠ 0`. -/
  hs_deriv : deriv s 0 ≠ 0
  /-- The §5 inverse property near `0`. -/
  hinv0 : ∀ᶠ a in 𝓝 (0 : ℂ), η (s a) = a
  /-- The §5 normal form near `chart_p p`. -/
  hnf0 : ∀ᶠ w in 𝓝 ((chartAt ℂ p) p), f.holoRepr ((chartAt ℂ p).symm w) = c + η w ^ m
  /-- Laurent principal-part degree. -/
  ppN : ℕ
  /-- Laurent principal-part coefficients. -/
  ppb : ℕ → ℂ
  /-- Analytic remainder. -/
  ppR : ℂ → ℂ
  /-- The remainder is analytic at `0`. -/
  hppR_an : AnalyticAt ℂ ppR 0
  /-- The principal-part split on `𝓝[≠] 0`. -/
  hsplit0 : straightenedIntegrand ω₀ g.toFun p s =ᶠ[𝓝[≠] 0]
    fun u => negTail 0 ppb ppN u + ppR u
  /-- The descent germ. -/
  G : ℂ → ℂ
  /-- The descent germ is analytic at `0`. -/
  hG : AnalyticAt ℂ G 0
  /-- The shrunk-slit neighbourhood. -/
  V : Set ℂ
  /-- `V` is open. -/
  hVopen : IsOpen V
  /-- `c ∈ V`. -/
  hcV : c ∈ V
  /-- `s` is analytic at each cpow sheet argument on `V ∩ slit`. -/
  hVs_an : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    AnalyticAt ℂ s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))
  /-- The principal-part split holds at each cpow sheet argument on `V ∩ slit`. -/
  hVpp_split : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    straightenedIntegrand ω₀ g.toFun p s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))
      = negTail 0 ppb ppN (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) + ppR (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))
  /-- The descent identity holds at the cpow branch on `V ∩ slit`. -/
  hVsmall : ∀ z ∈ V, z - c ∈ slitPlane →
    (∑ j ∈ Finset.range m, ppR (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) * ζ ^ j)
      = m * ((z - c) ^ ((m : ℂ)⁻¹)) ^ (m - 1) * G (((z - c) ^ ((m : ℂ)⁻¹)) ^ m)
  /-- The cpow sheet argument lands in the inverse-property domain on `V ∩ slit`. -/
  hVinv_mem : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    ∀ᶠ a in 𝓝 (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)), η (s a) = a
  /-- The `s`-composed cpow sheet argument lands in the normal-form domain on `V ∩ slit`. -/
  hVnf_mem : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    ∀ᶠ w in 𝓝 (s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))),
      f.holoRepr ((chartAt ℂ p).symm w) = c + η w ^ m
  /-- The `s`-composed cpow sheet argument lands in the chart target on `V ∩ slit`. -/
  hVtgt : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) ∈ (chartAt ℂ p).target

/-- **The per-preimage §5 datum exists at a non-pole fibre preimage.**  At a non-pole fibre preimage `p`
over `coe c` of a non-constant cover `f` (`f.div ≠ 0`), of genuine multiplicity
`m = (localDeg f (coe c) p).toNat`, with `ζ` a primitive `m`-th root, the `Fibre5Datum` is constructed
from: the Forster §5 normal form (`exists_clusterSplit_at_fibrePoint`); the Laurent principal part of the
straightened integrand (`exists_principalPart_meromorphicAt`); the symmetric-function descent germ
(`analyticAt_weightedSymSum_descent`); and an open `V ∋ c` (the finite intersection of the per-fact
shrunk-slit neighbourhoods, via `exists_open_cpowBranch_mem` / `exists_open_cpowSheetArg_punctured` /
`exists_open_of_eventually_nhds`). -/
theorem exists_fibre5Datum (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ} {p : X}
    (hp_fib : f.toRiemannSphere p = ((c : ℂ) : RiemannSphere)) (hp_np : 0 ≤ f.orderAtPoint p)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (localDeg f ((c : ℂ) : RiemannSphere) p).toNat) :
    Nonempty (Fibre5Datum ω₀ g f c p (localDeg f ((c : ℂ) : RiemannSphere) p).toNat) := by
  classical
  set m := (localDeg f ((c : ℂ) : RiemannSphere) p).toNat with hm_def
  have hm : 0 < m := (Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1
  -- The §5 atom.
  obtain ⟨η, s, hη_an, hη0, hηderiv, hnf0, hs_an, hs0, hs_deriv, hinv0, _hsect⟩ :=
    exists_clusterSplit_at_fibrePoint f hdiv hp_fib hp_np hζ
  -- The principal part of the straightened integrand at `0`.
  have hg_mero : MeromorphicAt (fun z => g.toFun ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) := by
    simpa [Function.comp] using g.meromorphic p
  have hH_mero : MeromorphicAt (straightenedIntegrand ω₀ g.toFun p s) 0 :=
    meromorphicAt_straightenedIntegrand ω₀ g.toFun p hs_an hs0 hg_mero
  obtain ⟨ppN, ppb, ppR, hppR_an, hsplit0⟩ := exists_principalPart_meromorphicAt hH_mero
  -- The descent germ from the analytic remainder.
  obtain ⟨G, hG, hGev⟩ := analyticAt_weightedSymSum_descent hppR_an hm hζ
  -- `a ↦ ζʲ·a` fixes `0` (the scaling that pushes a `𝓝 0` fact onto the cpow sheet argument).
  have harg0 : ∀ j : ℕ, Tendsto (fun a : ℂ => ζ ^ j * a) (𝓝 0) (𝓝 0) := fun j => by
    have : Continuous (fun a : ℂ => ζ ^ j * a) := continuous_const.mul continuous_id
    simpa using this.tendsto' 0 0 (by simp)
  -- The open neighbourhoods for the six per-slit-value facts.
  -- (1) `s`-analyticity at sheet args (𝓝 0 fact, per `j`).
  have hVs_an_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane → AnalyticAt ℂ s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) := by
    intro j
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_cpowBranch_mem c (m := m) hm
      (P := fun a => AnalyticAt ℂ s (ζ ^ j * a))
      ((harg0 j).eventually hs_an.eventually_analyticAt)
    exact ⟨V, hVo, hcV, fun z hz hslit => hV z hz⟩
  -- (2) principal-part split at sheet args (𝓝[≠] 0 fact, per `j`).
  have hVpp_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane →
        straightenedIntegrand ω₀ g.toFun p s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))
          = negTail 0 ppb ppN (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) + ppR (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) :=
    fun j => exists_open_cpowSheetArg_punctured c hm hζ j hsplit0
  -- (3) descent identity at branch (𝓝 0 fact, single).
  have hVsmall_ex : ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧
      ∀ z ∈ V, z - c ∈ slitPlane →
        (∑ j ∈ Finset.range m, ppR (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) * ζ ^ j)
          = m * ((z - c) ^ ((m : ℂ)⁻¹)) ^ (m - 1) * G (((z - c) ^ ((m : ℂ)⁻¹)) ^ m) := by
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_cpowBranch_mem c hm hGev
    exact ⟨V, hVo, hcV, fun z hz _ => hV z hz⟩
  -- (4) inverse-property domain membership (𝓝 0 fact, per `j`).
  have hVinv_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane →
        ∀ᶠ a in 𝓝 (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)), η (s a) = a := by
    intro j
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_cpowBranch_mem c (m := m) hm
      (P := fun w => ∀ᶠ a in 𝓝 (ζ ^ j * w), η (s a) = a)
      ((harg0 j).eventually hinv0.eventually_nhds)
    exact ⟨V, hVo, hcV, fun z hz hslit => hV z hz⟩
  -- (5) normal-form domain membership (continuity fact, per `j`).
  have hVnf_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane →
        ∀ᶠ w in 𝓝 (s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))),
          f.holoRepr ((chartAt ℂ p).symm w) = c + η w ^ m := by
    intro j
    have htend := sComp_cpowSheetArg_tendsto p (s := s) (ζ := ζ) (j := j) c hm hs_an.continuousAt hs0
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_of_eventually_nhds c (htend.eventually hnf0.eventually_nhds)
    exact ⟨V, hVo, hcV, fun z hz hslit => hV z hz⟩
  -- (6) chart-target membership (continuity fact, per `j`).
  have hVtgt_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane →
        s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) ∈ (chartAt ℂ p).target := by
    intro j
    have htend := sComp_cpowSheetArg_tendsto p (s := s) (ζ := ζ) (j := j) c hm hs_an.continuousAt hs0
    have htgt0 : (chartAt ℂ p).target ∈ 𝓝 ((chartAt ℂ p) p) :=
      (chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_of_eventually_nhds c (htend.eventually htgt0)
    exact ⟨V, hVo, hcV, fun z hz hslit => hV z hz⟩
  -- Choose the per-`j` neighbourhoods and intersect everything (finite: `j ∈ range m`).
  choose Vsa hVsa_o hVsa_c hVsa using hVs_an_j
  choose Vpp hVpp_o hVpp_c hVpp using hVpp_j
  obtain ⟨Vsm, hVsm_o, hVsm_c, hVsm⟩ := hVsmall_ex
  choose Vinv hVinv_o hVinv_c hVinv using hVinv_j
  choose Vnf hVnf_o hVnf_c hVnf using hVnf_j
  choose Vtg hVtg_o hVtg_c hVtg using hVtgt_j
  -- The common open neighbourhood.
  set V : Set ℂ := Vsm ∩ (⋂ j ∈ Finset.range m, (Vsa j ∩ Vpp j ∩ Vinv j ∩ Vnf j ∩ Vtg j)) with hV_def
  have hVopen : IsOpen V := by
    refine hVsm_o.inter ?_
    refine isOpen_biInter_finset (fun j _ => ?_)
    exact (((hVsa_o j).inter (hVpp_o j)).inter (hVinv_o j)).inter (hVnf_o j) |>.inter (hVtg_o j)
  have hcV : c ∈ V := by
    refine ⟨hVsm_c, ?_⟩
    rw [Set.mem_iInter₂]
    exact fun j _ => ⟨⟨⟨⟨hVsa_c j, hVpp_c j⟩, hVinv_c j⟩, hVnf_c j⟩, hVtg_c j⟩
  -- Extract per-`j` membership from `V`.
  have hVmem : ∀ z ∈ V, ∀ j ∈ Finset.range m,
      z ∈ Vsa j ∧ z ∈ Vpp j ∧ z ∈ Vinv j ∧ z ∈ Vnf j ∧ z ∈ Vtg j := by
    intro z hz j hj
    have h := (Set.mem_iInter₂.mp hz.2) j hj
    exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  exact ⟨{
    hm := hm
    ζ := ζ
    hζ := hζ
    η := η
    s := s
    hs_an := hs_an
    hs0 := hs0
    hs_deriv := hs_deriv
    hinv0 := hinv0
    hnf0 := hnf0
    ppN := ppN
    ppb := ppb
    ppR := ppR
    hppR_an := hppR_an
    hsplit0 := hsplit0
    G := G
    hG := hG
    V := V
    hVopen := hVopen
    hcV := hcV
    hVs_an := fun z hz hslit j hj => hVsa j z (hVmem z hz j hj).1 hslit
    hVpp_split := fun z hz hslit j hj => hVpp j z (hVmem z hz j hj).2.1 hslit
    hVsmall := fun z hz hslit => hVsm z hz.1 hslit
    hVinv_mem := fun z hz hslit j hj => hVinv j z (hVmem z hz j hj).2.2.1 hslit
    hVnf_mem := fun z hz hslit j hj => hVnf j z (hVmem z hz j hj).2.2.2.1 hslit
    hVtgt := fun z hz hslit j hj => hVtg j z (hVmem z hz j hj).2.2.2.2 hslit }⟩

/-! ## Cross-cluster separation on a centre neighbourhood (the `hsep`/`hcross` content)

At distinct fibre preimages `p ≠ p'` (T2-separated since `realFibreData.xs` is injective), the cluster
section points converge to `p`, `p'` respectively as `z → c`
(`clusterSectionPoint_tendsto_preimage`), so they lie in disjoint neighbourhoods of `p`, `p'` — hence are
distinct — for `z` in a centre neighbourhood.  We produce one open `Vsep ∋ c` serving every pair
(finitely many, over the finite fibre). -/

/-- **Cross-cluster separation on a centre neighbourhood.**  For the whole-fibre data
`D = realFibreData g hdiv c hnp`, a per-preimage cluster family `Cl` whose local inverse `(Cl i).s` is
continuous at `0` with `(Cl i).s 0 = chart_{D.xs i} (D.xs i)` and whose branch `(Cl i).w₀` is the `cpow`
branch near `c`, there is an open `Vsep ∋ c` such that for every `z ∈ Vsep` and distinct preimages
`i ≠ i'`, the cluster section points are distinct:

> `clusterSection D Cl i j z ≠ clusterSection D Cl i' k z`.

Mechanism: the cluster section points tend to the distinct T2-separated preimages `D.xs i`, `D.xs i'`,
so they eventually lie in disjoint neighbourhoods. -/
theorem exists_open_clusterSection_separated {ω₀ : HolomorphicOneForms X} {g : MeromorphicFunction X}
    {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {c : ℂ}
    {hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)} {Sset : Set ℂ}
    (Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset)
    (hs_cont : ∀ i, ContinuousAt (Cl i).s 0)
    (hs0 : ∀ i, (Cl i).s 0 = (chartAt ℂ ((realFibreData g hdiv c hnp).xs i))
      ((realFibreData g hdiv c hnp).xs i))
    (hw₀_eq : ∀ i, (Cl i).w₀ =ᶠ[𝓝 c] fun z => (z - c) ^ (((Cl i).m : ℂ)⁻¹)) :
    ∃ Vsep : Set ℂ, IsOpen Vsep ∧ c ∈ Vsep ∧
      ∀ z ∈ Vsep, ∀ (i i' : (realFibreData g hdiv c hnp).ι)
        (j : Fin ((realFibreData g hdiv c hnp).mult i)) (k : Fin ((realFibreData g hdiv c hnp).mult i')),
        i ≠ i' → clusterSection (realFibreData g hdiv c hnp) Cl i j z
          ≠ clusterSection (realFibreData g hdiv c hnp) Cl i' k z := by
  classical
  -- The cluster section point tends to its preimage `D.xs i`, for every `i`, `j`.
  have htend : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
      Tendsto (fun z => clusterSection (realFibreData g hdiv c hnp) Cl i j z) (𝓝 c)
        (𝓝 ((realFibreData g hdiv c hnp).xs i)) := by
    intro i j
    exact clusterSectionPoint_tendsto_preimage (c := c) (m := (Cl i).m)
      ((realFibreData g hdiv c hnp).xs i) (Cl i).hm (hs_cont i) (hs0 i) (hw₀_eq i)
      (ζ := (Cl i).ζ) (j := (j : ℕ))
  -- For each ordered pair `(i, i')` with `i ≠ i'`, an open nbhd of `c` separating their clusters.
  have hpair : ∀ (i i' : (realFibreData g hdiv c hnp).ι), i ≠ i' → ∃ W : Set ℂ, IsOpen W ∧ c ∈ W ∧
      ∀ z ∈ W, ∀ (j : Fin ((realFibreData g hdiv c hnp).mult i))
        (k : Fin ((realFibreData g hdiv c hnp).mult i')),
        clusterSection (realFibreData g hdiv c hnp) Cl i j z
          ≠ clusterSection (realFibreData g hdiv c hnp) Cl i' k z := by
    intro i i' hii
    have hne : (realFibreData g hdiv c hnp).xs i ≠ (realFibreData g hdiv c hnp).xs i' :=
      fun h => hii (realFibreData_inj g hdiv c hnp h)
    obtain ⟨U, U', hUo, hU'o, hxU, hxU', hdisj⟩ := t2_separation hne
    -- Each cluster section point at `i` eventually lands in `U`; at `i'` in `U'`.
    have hev : ∀ᶠ z in 𝓝 c,
        (∀ j : Fin ((realFibreData g hdiv c hnp).mult i),
          clusterSection (realFibreData g hdiv c hnp) Cl i j z ∈ U) ∧
        (∀ k : Fin ((realFibreData g hdiv c hnp).mult i'),
          clusterSection (realFibreData g hdiv c hnp) Cl i' k z ∈ U') := by
      rw [eventually_and]
      exact ⟨eventually_all.2 (fun j => (htend i j).eventually (hUo.mem_nhds hxU)),
        eventually_all.2 (fun k => (htend i' k).eventually (hU'o.mem_nhds hxU'))⟩
    obtain ⟨W, hWo, hcW, hW⟩ := exists_open_of_eventually_nhds c hev
    exact ⟨W, hWo, hcW, fun z hz j k =>
      ne_of_mem_disjoint ((hW z hz).1 j) ((hW z hz).2 k) hdisj⟩
  -- Choose a separating nbhd for each ordered pair and intersect over the finite index square.
  choose! W hWo hcW hW using hpair
  refine ⟨⋂ i : (realFibreData g hdiv c hnp).ι, ⋂ i' : (realFibreData g hdiv c hnp).ι,
      (if h : i ≠ i' then W i i' else Set.univ), ?_, ?_, ?_⟩
  · refine isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun i' => ?_))
    by_cases h : i ≠ i'
    · rw [dif_pos h]; exact hWo i i' h
    · rw [dif_neg h]; exact isOpen_univ
  · rw [Set.mem_iInter]
    intro i; rw [Set.mem_iInter]; intro i'
    by_cases h : i ≠ i'
    · rw [dif_pos h]; exact hcW i i' h
    · rw [dif_neg h]; exact Set.mem_univ _
  · intro z hz i i' j k hii
    have hmem : z ∈ W i i' := by
      have h2 := (Set.mem_iInter.mp ((Set.mem_iInter.mp hz) i)) i'
      rwa [dif_pos hii] at h2
    exact hW i i' hii z hmem j k

/-! ## The cluster data `Cl` from a `Fibre5Datum` on a shrunk slit

From a `Fibre5Datum` (the §5 atom + Laurent principal part + descent germ) and any slit `Sset` inside its
neighbourhood `V` (and inside the standard slit), build the concrete `ClusterTraceData` with `s := FD.s`,
`w₀ := (cpow branch)`, `ζ := FD.ζ`, the residue split from `FD.hsplit0`, and `Rem := FD.G(· − c)`
supplied by the symmetric-function descent (`exists_ramifiedTrace_descent`).  The fields are set
explicitly (not via `Nonempty`), so `(toClusterTraceData …).s`/`.w₀`/`.ζ`/`.m` are definitionally the
`Fibre5Datum`'s — the matching the §5 section germs and the separation lemma require. -/

/-- **The concrete `ClusterTraceData` from a `Fibre5Datum` on a shrunk slit.**  For `Sset` inside both
`FD.V` and the standard slit (`hsub`), the `Fibre5Datum`'s data assembles a `ClusterTraceData ω₀ g.toFun p
c Sset` via `ClusterTraceData.ofNormalForm`: the slit branch `w₀ = (· − c)^{1/m}` and its calculus from
`clusterTraceData_slit`, the §5 atom `FD.s`, the principal part `FD.ppN`/`FD.ppb`/`FD.ppR`, the per-slit
analyticity/split (`FD.hVs_an`/`FD.hVpp_split`), and `Rem := FD.G(· − c)` from the descent
(`exists_ramifiedTrace_descent`, its slit identity matching `ofNormalForm`'s `wp = 0` shape). -/
noncomputable def Fibre5Datum.toClusterTraceData {ω₀ : HolomorphicOneForms X} {g : MeromorphicFunction X}
    {f : MeromorphicFunction X} {c : ℂ} {p : X} {m : ℕ} (FD : Fibre5Datum ω₀ g f c p m)
    (Sset : Set ℂ) (hsub : ∀ z ∈ Sset, z ∈ FD.V ∧ z - c ∈ slitPlane) :
    ClusterTraceData ω₀ g.toFun p c Sset :=
  ClusterTraceData.ofNormalForm ω₀ g.toFun p c Sset m FD.hm FD.ζ FD.hζ
    FD.s FD.hs_an FD.hs0 FD.hs_deriv
    (clusterTraceData_slit ω₀ p c m FD.hm FD.ζ FD.hζ).w₀
    (fun z hz => (clusterTraceData_slit ω₀ p c m FD.hm FD.ζ FD.hζ).hw₀_ne z (hsub z hz).2)
    (fun z hz => (clusterTraceData_slit ω₀ p c m FD.hm FD.ζ FD.hζ).hw₀_pow z (hsub z hz).2)
    (fun z hz => (clusterTraceData_slit ω₀ p c m FD.hm FD.ζ FD.hζ).hw₀_deriv z (hsub z hz).2)
    (fun z hz => (clusterTraceData_slit ω₀ p c m FD.hm FD.ζ FD.hζ).hw₀_diff z (hsub z hz).2)
    (fun z hz j hj => FD.hVs_an z (hsub z hz).1 (hsub z hz).2 j hj)
    (by simpa [Function.comp] using g.meromorphic p) FD.ppN FD.ppb FD.ppR FD.hppR_an
    (fun z hz j hj => FD.hVpp_split z (hsub z hz).1 (hsub z hz).2 j hj)
    (fun z => FD.G (z - c)) (FD.hG.comp_of_eq (by fun_prop) (by ring))
    (fun z hz => by
      have h := (Jacobians.SymmetricDescent.ramifiedTrace_slit_eq FD.ppR 0 c FD.hm FD.ζ
        (clusterTraceData_slit ω₀ p c m FD.hm FD.ζ FD.hζ).w₀ FD.G
        ((clusterTraceData_slit ω₀ p c m FD.hm FD.ζ FD.hζ).hw₀_ne z (hsub z hz).2)
        ((clusterTraceData_slit ω₀ p c m FD.hm FD.ζ FD.hζ).hw₀_pow z (hsub z hz).2)
        ((clusterTraceData_slit ω₀ p c m FD.hm FD.ζ FD.hζ).hw₀_deriv z (hsub z hz).2)
        (by simpa using FD.hVsmall z (hsub z hz).1 (hsub z hz).2)).symm
      simpa only [zero_add] using h)

@[simp] theorem Fibre5Datum.toClusterTraceData_s {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {c : ℂ} {p : X} {m : ℕ}
    (FD : Fibre5Datum ω₀ g f c p m) (Sset : Set ℂ)
    (hsub : ∀ z ∈ Sset, z ∈ FD.V ∧ z - c ∈ slitPlane) :
    (FD.toClusterTraceData Sset hsub).s = FD.s := rfl

@[simp] theorem Fibre5Datum.toClusterTraceData_w₀ {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {c : ℂ} {p : X} {m : ℕ}
    (FD : Fibre5Datum ω₀ g f c p m) (Sset : Set ℂ)
    (hsub : ∀ z ∈ Sset, z ∈ FD.V ∧ z - c ∈ slitPlane) :
    (FD.toClusterTraceData Sset hsub).w₀ = fun z => (z - c) ^ ((m : ℂ)⁻¹) := rfl

@[simp] theorem Fibre5Datum.toClusterTraceData_ζ {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {c : ℂ} {p : X} {m : ℕ}
    (FD : Fibre5Datum ω₀ g f c p m) (Sset : Set ℂ)
    (hsub : ∀ z ∈ Sset, z ∈ FD.V ∧ z - c ∈ slitPlane) :
    (FD.toClusterTraceData Sset hsub).ζ = FD.ζ := rfl

@[simp] theorem Fibre5Datum.toClusterTraceData_m {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {c : ℂ} {p : X} {m : ℕ}
    (FD : Fibre5Datum ω₀ g f c p m) (Sset : Set ℂ)
    (hsub : ∀ z ∈ Sset, z ∈ FD.V ∧ z - c ∈ slitPlane) :
    (FD.toClusterTraceData Sset hsub).m = m := rfl

/-! ## The §5 power identity on a neighbourhood (the `hpow` field)

The cpow `m`-th-root identity `((z − c)^{1/m})^m = z − c` holds on the open slit `{z | z − c ∈ slitPlane}`,
hence on a whole neighbourhood of any interior slit value `z₀` (the slit is open, `slitPlane` open). -/

/-- **The cpow power identity holds on a neighbourhood of an interior slit value.**  For `m ≥ 1` and
`z₀ − c ∈ slitPlane`, the identity `((z − c)^{1/m})^{(m:ℤ)} = z − c` holds for `z` in a neighbourhood of
`z₀` (the slit is open). -/
theorem eventually_cpow_pow_eq (c : ℂ) {m : ℕ} (hm : 0 < m) {z₀ : ℂ} (hz₀ : z₀ - c ∈ slitPlane) :
    ∀ᶠ z in 𝓝 z₀, ((z - c) ^ ((m : ℂ)⁻¹)) ^ (m : ℤ) = z - c := by
  have hopen : ∀ᶠ z in 𝓝 z₀, z - c ∈ slitPlane := by
    have hcont : ContinuousAt (fun z : ℂ => z - c) z₀ := (continuous_sub_right c).continuousAt
    exact hcont.eventually (Complex.isOpen_slitPlane.mem_nhds hz₀)
  filter_upwards [hopen] with z _
  rw [zpow_natCast]; exact Complex.cpow_nat_inv_pow _ hm.ne'

/-! ## The §5 section germ from a per-preimage `Fibre5Datum` family

Assemble the per-`(z₀,i)` `SlitSectionGerm` from the per-preimage `Fibre5Datum` family, the cluster data
`Cl i := (FD i).toClusterTraceData …`, a slit value `z₀ ∈ Sset`, and the two centre-level facts
(`hnonpole`/`hsep`).  Each germ field reads off the corresponding `Fibre5Datum` `V`-fact (`hVinv_mem`,
`hVnf_mem`, `hVtgt`, `hVs_an`), the cpow calculus (`hw₀_cont`, `hpow`), and the centre-level data. -/

/-- **The §5 section germ from a `Fibre5Datum` family.**  For the whole-fibre `D = realFibreData g hdiv c
hnp`, the per-preimage data `FD i : Fibre5Datum ω₀ g f c (D.xs i) (D.mult i)`, the cluster family
`Cl i = (FD i).toClusterTraceData Sset (hsub i)`, a slit value `z₀ ∈ Sset`, and the centre-level
non-pole (`hnonpole`) / separation (`hsep`) facts at `z₀`, build a `SlitSectionGerm`.  Discharges the
eight germ fields from the `Fibre5Datum` `V`-facts, the cpow calculus, and the two centre-level data. -/
noncomputable def slitSectionGerm_of_fibre5 {ω₀ : HolomorphicOneForms X} {g : MeromorphicFunction X}
    {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {c : ℂ}
    {hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)} {Sset : Set ℂ}
    (FD : ∀ i, Fibre5Datum ω₀ g f c ((realFibreData g hdiv c hnp).xs i)
      ((realFibreData g hdiv c hnp).mult i))
    (hsub : ∀ i, ∀ z ∈ Sset, z ∈ (FD i).V ∧ z - c ∈ slitPlane)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Sset) (i : (realFibreData g hdiv c hnp).ι)
    (hnonpole : ∀ (i : (realFibreData g hdiv c hnp).ι)
      (j : Fin ((realFibreData g hdiv c hnp).mult i)),
      0 ≤ f.orderAtPoint (clusterSection (realFibreData g hdiv c hnp)
        (fun i => (FD i).toClusterTraceData Sset (hsub i)) i j z₀))
    (hsep : ∀ (i i' : (realFibreData g hdiv c hnp).ι)
      (j : Fin ((realFibreData g hdiv c hnp).mult i)) (k : Fin ((realFibreData g hdiv c hnp).mult i')),
      i ≠ i' → clusterSection (realFibreData g hdiv c hnp)
          (fun i => (FD i).toClusterTraceData Sset (hsub i)) i j z₀
        ≠ clusterSection (realFibreData g hdiv c hnp)
          (fun i => (FD i).toClusterTraceData Sset (hsub i)) i' k z₀) :
    SlitSectionGerm ω₀ g hdiv c hnp (fun i => (FD i).toClusterTraceData Sset (hsub i)) z₀ i where
  η := (FD i).η
  hs_cont := fun j => ((FD i).hVs_an z₀ (hsub i z₀ hz₀).1 (hsub i z₀ hz₀).2 (j : ℕ)
    (Finset.mem_range.2 j.isLt)).continuousAt
  hw₀_cont := ((clusterTraceData_slit ω₀ ((realFibreData g hdiv c hnp).xs i) c
    ((realFibreData g hdiv c hnp).mult i) (FD i).hm (FD i).ζ (FD i).hζ).hw₀_diff z₀
    (hsub i z₀ hz₀).2).continuousAt
  hinv := fun j => (FD i).hVinv_mem z₀ (hsub i z₀ hz₀).1 (hsub i z₀ hz₀).2 (j : ℕ)
    (Finset.mem_range.2 j.isLt)
  hnf := fun j => (FD i).hVnf_mem z₀ (hsub i z₀ hz₀).1 (hsub i z₀ hz₀).2 (j : ℕ)
    (Finset.mem_range.2 j.isLt)
  hpow := eventually_cpow_pow_eq c (FD i).hm (hsub i z₀ hz₀).2
  htgt := fun j => (FD i).hVtgt z₀ (hsub i z₀ hz₀).1 (hsub i z₀ hz₀).2 (j : ℕ)
    (Finset.mem_range.2 j.isLt)
  hnonpole := fun j => hnonpole i j
  hsep := fun i' j k hii => hsep i i' j k hii

/-! ## The cluster section points are non-poles on a centre neighbourhood (the `hnonpole` content)

Each cluster section point tends to its preimage `D.xs i` (a non-pole at a finite value-centre), so it is
a non-pole for `z` in a centre neighbourhood (non-poles are open).  We produce one open `Vnp ∋ c` serving
every preimage/sheet (finitely many). -/

/-- **The cluster section points are non-poles on a centre neighbourhood.**  For the whole-fibre data
`D = realFibreData g hdiv c hnp` (every preimage a non-pole) and a per-preimage cluster family `Cl` with
`(Cl i).s` continuous at `0` (`(Cl i).s 0 = chart_{D.xs i}`) and `(Cl i).w₀` the `cpow` branch near `c`,
there is an open `Vnp ∋ c` such that for every `z ∈ Vnp`, preimage `i`, and sheet `j`, the cluster section
point is a non-pole:

> `0 ≤ f.orderAtPoint (clusterSection D Cl i j z)`. -/
theorem exists_open_clusterSection_nonpole {ω₀ : HolomorphicOneForms X} {g : MeromorphicFunction X}
    {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {c : ℂ}
    {hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)} {Sset : Set ℂ}
    (Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset)
    (hs_cont : ∀ i, ContinuousAt (Cl i).s 0)
    (hs0 : ∀ i, (Cl i).s 0 = (chartAt ℂ ((realFibreData g hdiv c hnp).xs i))
      ((realFibreData g hdiv c hnp).xs i))
    (hw₀_eq : ∀ i, (Cl i).w₀ =ᶠ[𝓝 c] fun z => (z - c) ^ (((Cl i).m : ℂ)⁻¹)) :
    ∃ Vnp : Set ℂ, IsOpen Vnp ∧ c ∈ Vnp ∧
      ∀ z ∈ Vnp, ∀ (i : (realFibreData g hdiv c hnp).ι)
        (j : Fin ((realFibreData g hdiv c hnp).mult i)),
        0 ≤ f.orderAtPoint (clusterSection (realFibreData g hdiv c hnp) Cl i j z) := by
  classical
  -- For each preimage `i` and sheet `j`, the cluster section point is eventually a non-pole.
  have hev_ij : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
      ∀ᶠ z in 𝓝 c, 0 ≤ f.orderAtPoint (clusterSection (realFibreData g hdiv c hnp) Cl i j z) := by
    intro i j
    -- `D.xs i = fullFibreEnum f hdiv c i` is a non-pole.
    have hp_np : 0 ≤ f.orderAtPoint ((realFibreData g hdiv c hnp).xs i) := by
      rw [realFibreData_xs]; exact hnp i
    exact eventually_clusterSectionPoint_nonpole f hp_np (c := c) (m := (Cl i).m) (ζ := (Cl i).ζ)
      (j := (j : ℕ)) (Cl i).hm (hs_cont i) (hs0 i) (hw₀_eq i)
  -- Intersect over the finite index `Σ i, Fin (D.mult i)`.
  have hev : ∀ᶠ z in 𝓝 c, ∀ (p : Σ i : (realFibreData g hdiv c hnp).ι,
      Fin ((realFibreData g hdiv c hnp).mult i)),
      0 ≤ f.orderAtPoint (clusterSection (realFibreData g hdiv c hnp) Cl p.1 p.2 z) := by
    rw [eventually_all]
    rintro ⟨i, j⟩; exact hev_ij i j
  obtain ⟨Vnp, hVo, hcV, hV⟩ := exists_open_of_eventually_nhds c hev
  exact ⟨Vnp, hVo, hcV, fun z hz i j => hV z hz ⟨i, j⟩⟩

/-! ## The shrunk slit accumulates at `c` off the branch locus

The shrunk slit `(open V ∋ c) ∩ {z | z − c ∈ slitPlane} \ (finite bad set)` still accumulates at `c`: the
standard slit accumulates at `c` (`slitPlane_shift_accumulates`); intersecting with an open `V ∋ c`
preserves the accumulation (`V ∈ 𝓝 c`); and removing a finite set does not destroy a cluster point. -/

/-- **The shrunk slit accumulates at `c`.**  For an open `V ∋ c` and a finite set `bad`, the shrunk slit
`V ∩ {z | z − c ∈ slitPlane} \ bad` accumulates at `c` (frequently in `𝓝[≠] c`). -/
theorem shrunkSlit_accumulates (c : ℂ) {V : Set ℂ} (hVopen : IsOpen V) (hcV : c ∈ V)
    (bad : Finset ℂ) :
    ∃ᶠ z in 𝓝[≠] c, z ∈ (V ∩ {z : ℂ | z - c ∈ slitPlane}) \ (bad : Set ℂ) := by
  -- The standard slit accumulates at `c`.
  have hslit : ∃ᶠ z in 𝓝[≠] c, z ∈ {z : ℂ | z - c ∈ slitPlane} := slitPlane_shift_accumulates c
  -- `V ∈ 𝓝 c`, and removing the finite `bad` keeps the cluster point: `(bad \ {c})ᶜ ∈ 𝓝 c`.
  have hVnhds : ∀ᶠ z in 𝓝[≠] c, z ∈ V :=
    Filter.eventually_iff.2 (nhdsWithin_le_nhds (hVopen.mem_nhds hcV))
  have hbad : ∀ᶠ z in 𝓝[≠] c, z ∈ ((bad : Set ℂ) \ {c})ᶜ :=
    Filter.eventually_iff.2 (nhdsWithin_le_nhds
      ((bad.finite_toSet.diff).isClosed.compl_mem_nhds (by simp)))
  -- Combine: frequently on the slit, and in `V`, off `bad`.
  refine (hslit.and_eventually (hVnhds.and hbad)).mono ?_
  rintro z ⟨hzslit, hzV, hzbad⟩
  have hzc : z ≠ c := fun h => Complex.slitPlane_ne_zero hzslit (by rw [h, sub_self])
  refine ⟨⟨hzV, hzslit⟩, fun hzbad' => hzbad ⟨hzbad', fun h => hzc ?_⟩⟩
  rw [Set.mem_singleton_iff] at h; exact h

/-! ## The pole-order bound from the cluster identity (the Miranda-(3.1) meromorphy)

The geometric trace `valueChartTrace`, analytic on a punctured neighbourhood of the pole-value centre `c`,
agrees on the slit `Sset` with the single-valued meromorphic cluster sum `T = ∑ᵢ (Clᵢ).clusterTrace`.  By
the analytic identity theorem on the (preconnected) punctured ball, this agreement spreads to the whole
punctured neighbourhood, so `valueChartTrace =ᶠ[𝓝[≠] c] T` is meromorphic at `c` with a finite pole order
— Miranda *Algebraic Curves and Riemann Surfaces* §VIII.3 (3.1). -/

/-- **The punctured ball in `ℂ` is connected.**  For `r > 0`, `ball c r \ {c}` is connected (it is the
continuous image of the connected product `Ioo 0 r ×ˢ sphere 0 1` under `(ρ, u) ↦ c + ρ • u`, the polar
parametrisation; `sphere 0 1` is connected since `ℂ` has real rank `2`). -/
theorem isConnected_punctured_ball (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConnected (Metric.ball c r \ {c}) := by
  have hrank : (1 : ℕ) < Module.rank ℝ ℂ := by
    rw [show Module.rank ℝ ℂ = 2 from Complex.rank_real_complex]; exact_mod_cast one_lt_two
  have hsphere : IsConnected (Metric.sphere (0 : ℂ) 1) := isConnected_sphere hrank 0 (by norm_num)
  have hprod : IsConnected ((Set.Ioo (0 : ℝ) r) ×ˢ (Metric.sphere (0 : ℂ) 1)) :=
    (isConnected_Ioo hr).prod hsphere
  have hcont : Continuous (fun p : ℝ × ℂ => c + (p.1 : ℂ) • p.2) := by fun_prop
  have himg := hprod.image _ hcont.continuousOn
  convert himg using 1
  ext z
  simp only [Set.mem_diff, Metric.mem_ball, Set.mem_singleton_iff, Set.mem_image, Set.mem_prod,
    Set.mem_Ioo, mem_sphere_zero_iff_norm, Complex.dist_eq, Prod.exists]
  constructor
  · rintro ⟨hzr, hzc⟩
    have hne : z - c ≠ 0 := sub_ne_zero.mpr hzc
    have hnpos : 0 < ‖z - c‖ := norm_pos_iff.mpr hne
    have hnne : ((‖z - c‖ : ℝ) : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt hnpos
    refine ⟨‖z - c‖, (z - c) / (‖z - c‖ : ℂ), ⟨⟨hnpos, hzr⟩, ?_⟩, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hnpos.le, div_self (ne_of_gt hnpos)]
    · rw [smul_eq_mul, mul_div_cancel₀ _ hnne, add_sub_cancel]
  · rintro ⟨ρ, u, ⟨⟨hρ0, hρr⟩, hu⟩, hz⟩
    subst hz
    refine ⟨?_, ?_⟩
    · rw [add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ0.le, hu,
        mul_one]; exact hρr
    · rw [add_eq_left]; intro h
      rw [smul_eq_zero] at h
      rcases h with h | h
      · rw [Complex.ofReal_eq_zero] at h; exact (ne_of_gt hρ0) h
      · rw [h, norm_zero] at hu; exact one_ne_zero hu.symm

/-- **Meromorphy at `c` from analyticity on a punctured nbhd + open agreement with a meromorphic germ.**
If `F` is analytic on a punctured neighbourhood of `c`, `T` is meromorphic at `c`, `O` is an open set with
`c ∈ closure O` and `c ∉ O`, and `F = T` on `O`, then `F =ᶠ[𝓝[≠] c] T`.  Proof: shrink to a punctured
ball `ball c r \ {c}` (preconnected, both `F` and `T` analytic on it) and seed the analytic identity
theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) from a point `z₀ ∈ O ∩ ball c r` (which
exists since `c ∈ closure O`): `F = T` on `O ∋ z₀` (open) gives the frequently-equality at `z₀`, so
`F = T` on the whole punctured ball, hence `=ᶠ[𝓝[≠] c]`. -/
theorem eventuallyEq_of_analyticOn_punctured_eqOn_open {F T : ℂ → ℂ} {c : ℂ}
    (hF_an : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ F z) (hT : MeromorphicAt T c)
    {O : Set ℂ} (hO_open : IsOpen O) (hcO : c ∈ closure O) (hcnO : c ∉ O)
    (hFT : ∀ z ∈ O, F z = T z) :
    F =ᶠ[𝓝[≠] c] T := by
  classical
  -- `T` is analytic on a punctured nbhd of `c`.
  have hT_an : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ T z := hT.eventually_analyticAt
  -- A common open nbhd `U ∋ c` (minus `c`) where both are analytic.
  rw [eventually_nhdsWithin_iff] at hF_an hT_an
  obtain ⟨UF, hUF_sub, hUF_open, hcUF⟩ := _root_.mem_nhds_iff.1 hF_an
  obtain ⟨UT, hUT_sub, hUT_open, hcUT⟩ := _root_.mem_nhds_iff.1 hT_an
  -- A ball `ball c r ⊆ UF ∩ UT`.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hUF_open.inter hUT_open) c ⟨hcUF, hcUT⟩
  -- Both `F` and `T` are `AnalyticOnNhd` on the punctured ball `ball c r \ {c}`.
  have hFan_ball : AnalyticOnNhd ℂ F (Metric.ball c r \ {c}) := by
    intro z hz
    exact hUF_sub (hball hz.1).1 (by simpa using hz.2)
  have hTan_ball : AnalyticOnNhd ℂ T (Metric.ball c r \ {c}) := by
    intro z hz
    exact hUT_sub (hball hz.1).2 (by simpa using hz.2)
  -- A point `z₀ ∈ ball c r ∩ O` (exists since `c ∈ closure O` and `ball c r ∈ 𝓝 c`).
  have hmeet : (Metric.ball c r ∩ O).Nonempty :=
    _root_.mem_closure_iff.1 hcO _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨z₀, hz₀ball, hz₀O⟩ := hmeet
  have hz₀c : z₀ ≠ c := fun h => hcnO (h ▸ hz₀O)
  have hz₀_mem : z₀ ∈ Metric.ball c r \ {c} := ⟨hz₀ball, by simpa using hz₀c⟩
  -- `F = T` frequently near `z₀` (on the open `O ∋ z₀`).
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, F z = T z := by
    have hOnhds : ∀ᶠ z in 𝓝[≠] z₀, z ∈ O :=
      Filter.eventually_iff.2 (nhdsWithin_le_nhds (hO_open.mem_nhds hz₀O))
    exact hOnhds.frequently.mono (fun z hz => hFT z hz)
  -- The analytic identity theorem on the preconnected punctured ball.
  have hEqOn : Set.EqOn F T (Metric.ball c r \ {c}) :=
    hFan_ball.eqOn_of_preconnected_of_frequently_eq hTan_ball
      (isConnected_punctured_ball c hr).isPreconnected hz₀_mem hfreq
  -- Read off the punctured-neighbourhood germ equality.
  have hball_nhds : Metric.ball c r \ {c} ∈ 𝓝[≠] c := by
    rw [mem_nhdsWithin]
    exact ⟨Metric.ball c r, Metric.isOpen_ball, Metric.mem_ball_self hr, by
      intro z hz; exact ⟨hz.1, by simpa using hz.2⟩⟩
  filter_upwards [hball_nhds] with z hz using hEqOn hz

/-- **A meromorphic germ has a finite pole-order bound.**  If `T` is meromorphic at `c`, then for some
`N : ℕ`, `(z − c)^N · T → 0` as `z → c`.  (Write `T =ᶠ[𝓝[≠] c] (z − c)^n • g` with `g` analytic; take
`N` large enough that `N + n ≥ 1`, so `(z − c)^N · T =ᶠ (z − c)^{N+n} · g → 0`.) -/
theorem exists_pow_bound_of_meromorphicAt {T : ℂ → ℂ} {c : ℂ} (hT : MeromorphicAt T c) :
    ∃ N : ℕ, Tendsto (fun z => (z - c) ^ N * T z) (𝓝[≠] c) (𝓝 0) := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt] at hT
  obtain ⟨n, g, hg_an, hg_eq⟩ := hT
  -- Choose `N` with `(N : ℤ) + n ≥ 1`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℤ) ≤ (N : ℤ) + n := by
    by_cases hn : 0 ≤ n
    · exact ⟨1, by omega⟩
    · exact ⟨(1 - n).toNat, by omega⟩
  refine ⟨N, ?_⟩
  -- `(z − c)^{N + n} · g → 0` since the exponent is `≥ 1` (so `(z − c)^{…} → 0`) and `g` is bounded.
  have hexp : Tendsto (fun z => (z - c) ^ ((N : ℤ) + n)) (𝓝[≠] c) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => z - c) (𝓝[≠] c) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun z : ℂ => z - c) (𝓝 c) (𝓝 0) := by
          simpa using (continuous_sub_right c).tendsto c
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa [sub_ne_zero] using hz
    have h2 : Tendsto (fun w : ℂ => w ^ ((N : ℤ) + n)) (𝓝[≠] 0) (𝓝 0) := by
      have hpow : Tendsto (fun w : ℂ => w ^ (((N : ℤ) + n).toNat)) (𝓝 0) (𝓝 0) := by
        have hpos : 0 < ((N : ℤ) + n).toNat := by omega
        simpa using (continuous_pow ((N : ℤ) + n).toNat).tendsto' 0 0 (by simp [hpos.ne'])
      refine (hpow.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [← zpow_natCast w, Int.toNat_of_nonneg (by omega)]
    have := h2.comp h1
    simpa [Function.comp] using this
  have hg_cont : Tendsto g (𝓝[≠] c) (𝓝 (g c)) :=
    hg_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htend1 : Tendsto (fun z => (z - c) ^ ((N : ℤ) + n) * g z) (𝓝[≠] c) (𝓝 0) := by
    have := hexp.mul hg_cont; simpa using this
  refine htend1.congr' ?_
  filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hzc
  have hzc' : z - c ≠ 0 := sub_ne_zero.mpr hzc
  rw [hz, smul_eq_mul, ← mul_assoc, ← zpow_natCast (z - c) N, ← zpow_add₀ hzc']

/-! ## The per-centre §5-section datum, modulo the pole-order bound

We assemble the full `RealCenterSlitSectionData` at a finite pole-value centre `c = A.cs idx` of an
adapted cover, taking the finite pole-order bound `(ppord, hbnd)` as input.  Every other field is
discharged: the per-preimage `Fibre5Datum` family (`exists_fibre5Datum`), the shrunk slit (the finite
intersection of the per-preimage neighbourhoods + the non-pole/separation neighbourhoods, off the branch
values, accumulating at `c`), the cluster data (`Fibre5Datum.toClusterTraceData`), the §5 section facts
(`slitSectionGerm_of_fibre5` → `RealSlitSectionData.ofSlitSectionGerm`), the sphere sheet systems
(`exists_sphereSheetSystem`), and the off-centre analyticity (`eventually_analyticAt_of_hreg`).  This
isolates the residue obligation to **exactly** the pole-order bound `hbnd`. -/

/-- **The per-centre §5-section datum from an adapted cover (UNCONDITIONAL).**  At every finite
pole-value centre `c = A.cs idx`, the bundled `RealCenterSlitSectionData` holds.  Every field — including
the Miranda-(3.1) finite pole-order bound — is constructed from the proven §5/descent/regular-value
machinery: the per-preimage `Fibre5Datum` family, the shrunk slit, the cluster data, the §5 section facts,
the sphere sheet systems, the off-centre analyticity, and the pole-order bound (the geometric trace agrees
on the slit with the single-valued meromorphic cluster sum `T = ∑ᵢ (Clᵢ).clusterTrace`; the analytic
identity theorem on the punctured ball globalises this to `valueChartTrace =ᶠ[𝓝[≠] c] T`, meromorphic,
giving the finite pole-order bound). -/
noncomputable def realCenterSlitSectionData_of_adaptedFRamified {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles) (idx : Fin A.m) :
    RealCenterSlitSectionData ω₀ g A.hdiv (A.cs idx) := by
  classical
  set f := A.f with hf_def
  set hdiv := A.hdiv with hdiv_def
  set c := A.cs idx with hc_def
  -- Every fibre preimage over `coe c` is a non-pole (finite value-centre).
  have hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i) := fun i => realFibre_nonpole hdiv c i
  -- The per-preimage §5 data family.
  have hFD : ∀ i, Nonempty (Fibre5Datum ω₀ g f c ((realFibreData g hdiv c hnp).xs i)
      ((realFibreData g hdiv c hnp).mult i)) := by
    intro i
    have hfib : f.toRiemannSphere ((realFibreData g hdiv c hnp).xs i) = ((c : ℂ) : RiemannSphere) := by
      rw [realFibreData_xs]; exact fullFibreEnum_mem f hdiv c i
    have hnpi : 0 ≤ f.orderAtPoint ((realFibreData g hdiv c hnp).xs i) := by
      rw [realFibreData_xs]; exact hnp i
    have hroot : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I /
        (localDeg f ((c : ℂ) : RiemannSphere) (fullFibreEnum f hdiv c i)).toNat))
        (localDeg f ((c : ℂ) : RiemannSphere) (fullFibreEnum f hdiv c i)).toNat :=
      Complex.isPrimitiveRoot_exp _ (realFibre_mult_pos hdiv (fullFibreEnum_mem f hdiv c i) (hnp i)).ne'
    have h := exists_fibre5Datum ω₀ g hdiv hfib hnpi (by rw [realFibreData_xs] at hfib ⊢; exact hroot)
    rw [realFibreData_mult]; exact h
  -- Choose a per-preimage §5 datum.
  set FD : ∀ i, Fibre5Datum ω₀ g f c ((realFibreData g hdiv c hnp).xs i)
    ((realFibreData g hdiv c hnp).mult i) := fun i => (hFD i).some with hFD_def
  -- The provisional slit (no `Vnp`/`Vsep` yet).
  set Sprov : Set ℂ := ((⋂ i, (FD i).V) ∩ {z : ℂ | z - c ∈ slitPlane}) \ (branchValues f hdiv : Set ℂ)
    with hSprov_def
  have hSprov_sub : ∀ i, ∀ z ∈ Sprov, z ∈ (FD i).V ∧ z - c ∈ slitPlane := by
    intro i z hz
    exact ⟨(Set.mem_iInter.mp hz.1.1) i, hz.1.2⟩
  -- The provisional cluster family.
  set Clprov : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sprov :=
    fun i => (FD i).toClusterTraceData Sprov (hSprov_sub i) with hClprov_def
  -- The §5-data continuity facts (slit-independent), for the non-pole / separation neighbourhoods.
  have hs_cont : ∀ i, ContinuousAt (Clprov i).s 0 := fun i => (FD i).hs_an.continuousAt
  have hs0 : ∀ i, (Clprov i).s 0 = (chartAt ℂ ((realFibreData g hdiv c hnp).xs i))
      ((realFibreData g hdiv c hnp).xs i) := fun i => (FD i).hs0
  have hw₀_eq : ∀ i, (Clprov i).w₀ =ᶠ[𝓝 c] fun z => (z - c) ^ (((Clprov i).m : ℂ)⁻¹) :=
    fun i => Filter.Eventually.of_forall (fun z => rfl)
  -- The non-pole and separation neighbourhoods (chosen by `.choose` since the goal is data).
  set Vnp : Set ℂ := (exists_open_clusterSection_nonpole Clprov hs_cont hs0 hw₀_eq).choose
    with hVnp_def
  obtain ⟨hVnp_o, hVnp_c, hVnp⟩ :=
    (exists_open_clusterSection_nonpole Clprov hs_cont hs0 hw₀_eq).choose_spec
  set Vsep : Set ℂ := (exists_open_clusterSection_separated Clprov hs_cont hs0 hw₀_eq).choose
    with hVsep_def
  obtain ⟨hVsep_o, hVsep_c, hVsep⟩ :=
    (exists_open_clusterSection_separated Clprov hs_cont hs0 hw₀_eq).choose_spec
  -- The final shrunk slit.
  set Sset : Set ℂ := (((⋂ i, (FD i).V) ∩ Vnp ∩ Vsep) ∩ {z : ℂ | z - c ∈ slitPlane})
    \ (branchValues f hdiv : Set ℂ) with hSset_def
  have hSset_sub : ∀ i, ∀ z ∈ Sset, z ∈ (FD i).V ∧ z - c ∈ slitPlane := by
    intro i z hz
    exact ⟨(Set.mem_iInter.mp hz.1.1.1.1) i, hz.1.2⟩
  have hSset_subprov : Sset ⊆ Sprov := by
    intro z hz
    exact ⟨⟨hz.1.1.1.1, hz.1.2⟩, hz.2⟩
  have hSset_Vnp : ∀ z ∈ Sset, z ∈ Vnp := fun z hz => hz.1.1.1.2
  have hSset_Vsep : ∀ z ∈ Sset, z ∈ Vsep := fun z hz => hz.1.1.2
  have hSset_offBranch : ∀ z ∈ Sset, (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere := by
    intro z hz
    exact coe_notMem_branchLocus_of_notMem_branchValues f hdiv (fun h => hz.2 h)
  -- The final cluster family (on `Sset`).
  set Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset :=
    fun i => (FD i).toClusterTraceData Sset (hSset_sub i) with hCl_def
  -- `hanalytic` from the off-centre analyticity of the canonical selection.
  have hanalytic : ∀ᶠ z in 𝓝[≠] c,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv)) z :=
    eventually_analyticAt_of_hreg (gateAInftyData_of_adaptedFRamified A).hreg
  -- `hSset` is open and `c ∈ closure Sset`, `c ∉ Sset` (the slit is open off `c`).
  have hSset_open : IsOpen Sset := by
    refine IsOpen.sdiff ?_ (branchValues f hdiv).finite_toSet.isClosed
    exact (((isOpen_iInter_of_finite (fun i => (FD i).hVopen)).inter hVnp_o).inter hVsep_o).inter
      (Complex.isOpen_slitPlane.preimage (continuous_sub_right c))
  have hcnSset : c ∉ Sset := by
    intro h
    exact Complex.slitPlane_ne_zero h.1.2 (sub_self c)
  have hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ Sset := by
    have hVopen : IsOpen ((⋂ i, (FD i).V) ∩ Vnp ∩ Vsep) :=
      ((isOpen_iInter_of_finite (fun i => (FD i).hVopen)).inter hVnp_o).inter hVsep_o
    have hcV : c ∈ (⋂ i, (FD i).V) ∩ Vnp ∩ Vsep :=
      ⟨⟨Set.mem_iInter.2 (fun i => (FD i).hcV), hVnp_c⟩, hVsep_c⟩
    exact shrunkSlit_accumulates c hVopen hcV (branchValues f hdiv)
  have hcSset : c ∈ closure Sset := by
    rw [mem_closure_iff_frequently]; exact hS_acc.filter_mono nhdsWithin_le_nhds
  -- `hSsys`: a sphere sheet system at each off-branch slit value.
  set hSsys : ∀ z ∈ Sset, Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)) :=
    fun z hz => (exists_sphereSheetSystem f (exists_orderAtPoint_ne_zero f hdiv)
      (hSset_offBranch z hz)).some with hSsys_def
  -- `hsec`: the §5 section facts at each slit value, via the section germ family.
  have hsec : ∀ z ∈ Sset, RealSlitSectionData ω₀ g hdiv c hnp Cl z := by
    intro z₀ hz₀
    refine RealSlitSectionData.ofSlitSectionGerm (Cl := Cl) hz₀ (fun i => rfl) (fun i => ?_)
    refine slitSectionGerm_of_fibre5 FD hSset_sub hz₀ i ?_ ?_
    · intro i' j
      exact hVnp z₀ (hSset_Vnp z₀ hz₀) i' j
    · intro i' i'' j k hii
      exact hVsep z₀ (hSset_Vsep z₀ hz₀) i' i'' j k hii
  -- The per-slit-value `FibreClusterTopology` (the conservation-of-number geometry).
  have htop : ∀ z ∈ Sset, FibreClusterTopology (canonicalFibreSelection g.toFun f hdiv)
      (realFibreData g hdiv c hnp) Cl z := fun z hz =>
    ((hsec z hz).toClusterSplitData (hSset_offBranch z hz) hz (fun i => rfl)
      (hSsys z hz)).toFibreClusterTopology
  -- The single-valued meromorphic cluster sum `T`.
  set T : ℂ → ℂ := fun z => ∑ i, (Cl i).clusterTrace z with hT_def
  have hT_mero : MeromorphicAt T c :=
    MeromorphicAt.fun_sum (fun i _ => (Cl i).meromorphicAt_clusterTrace)
  -- The geometric identity `valueChartTrace = T` on the slit.
  have hident : ∀ z ∈ Sset,
      valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv) z = T z := by
    intro z hz
    rw [valueChartTrace_eq_clusterSum_of_clusterReindexData
      (ClusterReindexData.ofFibreClusterTopology (htop z hz))]
    exact Finset.sum_congr rfl (fun i _ => (Cl i).clusterSum_eq_clusterTrace_slit hz)
  -- The pole-order bound, via the punctured-ball identity theorem + the cluster sum's meromorphy.
  have hvct_eq : valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv) =ᶠ[𝓝[≠] c] T :=
    eventuallyEq_of_analyticOn_punctured_eqOn_open hanalytic hT_mero hSset_open hcSset hcnSset hident
  have hvct_mero : MeromorphicAt
      (valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv)) c := hT_mero.congr hvct_eq.symm
  have hbnd_ex := exists_pow_bound_of_meromorphicAt hvct_mero
  exact
    { hnp := hnp
      hanalytic := hanalytic
      Sset := Sset
      hS_acc := hS_acc
      hSset_offBranch := hSset_offBranch
      hSsys := hSsys
      Cl := Cl
      hmult := fun i => rfl
      hsplit0 := fun i => (FD i).hsplit0
      ppord := hbnd_ex.choose
      hbnd := hbnd_ex.choose_spec
      hsec := hsec }

/-! ## The UNCONDITIONAL residue theorem `∑Res = 0` (the §5-section route, closed)

`realCenterSlitSectionData_of_adaptedFRamified` builds the per-centre §5-section datum at every finite
pole-value centre with NO remaining hypothesis — including the Miranda-(3.1) pole-order bound, derived
from the cluster identity + the punctured-ball identity theorem.  So `RealCoverSlitSectionGeometry` holds
unconditionally, and the 1-form residue theorem `∑Res = 0` closes. -/

/-- **`RealCoverSlitSectionGeometry` holds unconditionally.**  At every adapted cover `A` and finite
pole-value centre `A.cs i`, the bundled §5-section datum is built by
`realCenterSlitSectionData_of_adaptedFRamified`. -/
noncomputable def realCoverSlitSectionGeometry {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} :
    RealCoverSlitSectionGeometry ω₀ g poles :=
  fun A i => realCenterSlitSectionData_of_adaptedFRamified A i

/-- **The 1-form residue theorem `∑Res = 0` for `α = ω₀·g` (UNCONDITIONAL).**  For a genuine meromorphic
numerator `g` and any finite `poles` containing the poles of `α = ω₀·g` (off which `g` is analytic), the
total residue vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`.

This is the SOUND well-definedness content underlying the global `Res : H¹(X,Ω) → ℂ` (Forster 17.3) →
§17.5.  The entire §5 normal-form slit geometry — the cluster sections, the symmetric-function descent,
the conservation-of-number topology, the regular-value primitives, the off-centre/∞ machinery, the
genericity (`existsAdaptedFRamified`), AND the Miranda-(3.1) pole-order bound (via the cluster identity +
the punctured-ball analytic identity theorem) — is PROVEN.  No remaining hypothesis. -/
theorem residueTheorem_unconditional (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X)
    (hpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 :=
  residueTheorem_of_realCoverSlitSectionGeometry ω₀ g poles hpoles realCoverSlitSectionGeometry

end Jacobians.Dolbeault.SerreResidueTheorem
