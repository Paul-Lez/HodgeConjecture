/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueDirectGenus0Germ
import KirovDolbeault.Dolbeault.FormTraceRegularValueDatum

/-!
# Gate A `∑Res = 0` — discharging the finite full-fibre moving coherence `Cfull` (§VIII.3)

`Jacobians.Dolbeault.SerreResidueTheorem.residueTheorem_ofCanonicalSimpleInfty_genus0_germ`
(`SerreResidueDirectGenus0Germ.lean`) reduced Gate A `∑Res = 0` (kirovGenus `0`, simple `∞`-poles, canonical
full-fibre selection) to *exactly*:

* the per-finite-centre full-fibre moving coherence `Cfull i : MovingCoherenceDatum ω₀ g f Φ (cs i)`
  (with `hCfull_inj`/`hCfull_image`/`hnonpole_an`), and
* the off-centre analyticity `hreg`/`hbnd` + the `∞`-coherence `hcoh_full`,

plus the discrete genericity bookkeeping (`hgood`/`hsimpleInf`/`hmeroInf`/`hcenters_cs`).

This file **discharges the `Cfull` field-group** (the genuine §VIII.3 *moving sphere-fibre sum* content
at each finite pole-centre) from the symmetric-invariance lever, given a per-centre **genericity**
hypothesis (`coe (cs i)` off the branch locus, the standard adapted-cover condition) and the
regular-value `g`-meromorphy near each centre.  Concretely: at a pole-value `coe (cs i)` off the branch
locus, the sphere sheet system `exists_sphereSheetSystem` supplies the moving sheets sweeping the full
fibre, and `MovingCoherenceDatum.ofSphereSheetSystemCanon` (the symmetric lever,
`FormTraceRegularValueDatum`) reconstructs the per-`b'` index bijection *pointwise* from the
labeling-independent fact that the canonical selection `Φ b'` enumerates the *same fibre set* as the
sheets — its `hdiag` (value-trace = moving sphere-fibre sum) is a germ-equality on `𝓝 (cs i)`, never
evaluating at the singularity.

**Soundness:** this is NOT a disguise of `∑Res = 0`.  The `hdiag` field is a *local* germ-equality
derived from the local sheet-system definition (the trace is the symmetric sum over the sheets of the
fibre — Miranda §VIII.3); it never references the residue cancellation.  The per-centre off-branch
genericity is a geometric input (a generic separating cover), not a residue identity.  The literal
junk-value defect (`hcont_int`) was already eliminated upstream by germ-Cauchy; `Cfull`'s germ-equality
holds on a *full* neighbourhood but is consumed only punctured/germ-wise downstream, so no junk-value
evaluation occurs.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `movingCoherenceDatum_canonical` — the full-fibre `MovingCoherenceDatum` for the canonical selection at
  an off-branch pole-value, with the reference fibre the sphere-sheet fibre (`.D.xs k = S.sheet k
  (coe (cs i))`), built via `MovingCoherenceDatum.ofSphereSheetSystemCanon`.
* `residueTheorem_ofCanonicalSimpleInfty_genus0_germ_Cfull` — the capstone with the `Cfull` field-group
  **discharged**: Gate A `∑Res = 0` from the per-centre off-branch genericity + regular `g`-data +
  `hreg`/`hbnd` + `hcoh_full` (no `Cfull`, no `hCfull_inj`/`hCfull_image`/`hnonpole_an` supplied).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace `Tr`; single-valued by
  symmetry; the trace = symmetric moving fibre-sum near each value).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §17.
* `Jacobians/Dolbeault/FormTraceRegularValueDatum.lean` (the symmetric lever
  `MovingCoherenceDatum.ofSphereSheetSystemCanon`).
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

/-! ## The full-fibre moving coherence datum for the canonical selection

At a finite value `coe c` off the branch locus, `exists_sphereSheetSystem` supplies a `LocalSheetSystem
S` of the compact sphere map `F = f.toRiemannSphere`, whose sheets sweep the full fibre.  The canonical
full-fibre selection `Φ = canonicalFibreSelection g f hdiv` enumerates that same fibre as a set near `c`
(`canonicalFibreSelection_hΦrangeReg`/`hΦinjReg`, given the regular-value `g`-meromorphy), so the
symmetric-invariance lever `MovingCoherenceDatum.ofSphereSheetSystemCanon` produces the moving coherence
datum — its `hdiag` (value-trace = moving sphere-fibre sum) reconstructed pointwise with no labeling. -/

/-- **The full-fibre moving coherence datum for the canonical selection at an off-branch value.**  At a
finite value `c` with `coe c` off the branch locus of `F = f.toRiemannSphere`, given the regular-value
`g`-meromorphy `hgmero` (`g`'s chart-pullback meromorphic at every full-fibre point, eventually near
`c`) and the at-`c` `g`-meromorphy `hmero_c` (for the reference sheet-fibre `hmero`), the canonical
full-fibre selection has a `MovingCoherenceDatum` at `c` whose reference fibre is the sphere-sheet fibre
(`.D.xs k = S.sheet k (coe c)`).  The deep §VIII.3 content — the diagonal identity value-trace = moving
sphere-fibre sum — is discharged by the symmetric lever (`ofSphereSheetSystemCanon`); the off-branch
regularity `hderiv` is intrinsic (`sheet_holoRepr_deriv_ne_zero`), and the sheet injectivity/chart-source
data is intrinsic to any `LocalSheetSystem`. -/
noncomputable def movingCoherenceDatum_canonical (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    (hoff : (((c : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((c : ℂ) : RiemannSphere)))
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))) (S.sheet i (((c : ℂ) : RiemannSphere)))))
    (hgmero : ∀ᶠ b' in 𝓝 c, ∀ i,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i))) :
    MovingCoherenceDatum ω₀ g f (canonicalFibreSelection g f hdiv) c :=
  MovingCoherenceDatum.ofSphereSheetSystemCanon S
    (fun i => sheet_holoRepr_deriv_ne_zero f hdiv hoff (S.sheet_section i _ S.mem_V))
    hmero
    (canonicalFibreSelection_hΦinjReg g f hdiv hoff hgmero)
    (canonicalFibreSelection_hΦrangeReg g f hdiv hoff hgmero)
    (by
      -- Sheet injectivity near `c` (intrinsic to `S`): `S.sheet_inj` over the open `S.V`.
      have hVnhds : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' S.V) ∈ 𝓝 c :=
        (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds (S.isOpen_V.mem_nhds S.mem_V)
      filter_upwards [hVnhds] with b' hb'
      exact S.sheet_inj (((b' : ℂ) : RiemannSphere)) hb')
    (by
      -- Sheet chart-source membership near `c` (intrinsic to `S`): continuity of each sheet at `c`.
      have hev : ∀ i : Fin S.n, ∀ᶠ b' in 𝓝 c, S.sheet i (((b' : ℂ) : RiemannSphere)) ∈
          (chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))).source := by
        intro i
        have hcont : ContinuousAt (S.holoReprSheet i) c :=
          (S.holoReprSheet_contMDiffAt i).continuousAt
        have hsrc : (chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))).source ∈
            𝓝 (S.sheet i (((c : ℂ) : RiemannSphere))) :=
          (chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))).open_source.mem_nhds
            (mem_chart_source ℂ _)
        have := hcont.preimage_mem_nhds (show
          (chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))).source ∈ 𝓝 (S.holoReprSheet i c) from hsrc)
        filter_upwards [this] with b' hb' using hb'
      rw [eventually_all]; exact hev)

/-- The reference fibre of `movingCoherenceDatum_canonical` enumerates the sphere sheets:
`.D.xs k = S.sheet k (coe c)`. -/
@[simp] theorem movingCoherenceDatum_canonical_D_xs (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    (hoff : (((c : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((c : ℂ) : RiemannSphere)))
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))) (S.sheet i (((c : ℂ) : RiemannSphere)))))
    (hgmero : ∀ᶠ b' in 𝓝 c, ∀ i,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i)))
    (k : Fin S.n) :
    (movingCoherenceDatum_canonical (g := g) (ω₀ := ω₀) hdiv hoff S hmero hgmero).D.xs k
      = S.sheet k (((c : ℂ) : RiemannSphere)) := rfl

/-! ### The combinatorial fields `hCfull_inj` / `hCfull_image` for `movingCoherenceDatum_canonical`

The reference fibre `.D.xs k = S.sheet k (coe c)` enumerates the **full** fibre `F⁻¹(coe c)` (the sheets
sweep the fibre, `sheetValues_range_eq_fibre`); it is injective (`S.sheet_inj` at the base).  At a good
value `c`, the canonical selection *also* enumerates that fibre (`canonicalFibreSelection_xs_range`), so
the two `Finset.univ.image`s agree — both equal `(F⁻¹(coe c))` as a finite set. -/

/-- **Set-range equality lifts to `Finset.univ.image` equality** for maps from a `Fintype`. -/
theorem image_univ_eq_of_range_eq {ι κ Y : Type*} [Fintype ι] [Fintype κ] [DecidableEq Y]
    {p : ι → Y} {q : κ → Y} (h : Set.range p = Set.range q) :
    Finset.univ.image p = Finset.univ.image q := by
  apply Finset.coe_injective
  rw [Finset.coe_image, Finset.coe_image, Finset.coe_univ, Finset.coe_univ,
    Set.image_univ, Set.image_univ, h]

/-- **`hCfull_inj` for `movingCoherenceDatum_canonical`.**  The reference sheet fibre `.D.xs k =
S.sheet k (coe c)` is injective: the sheets are injective in the index at the base (`S.sheet_inj` over
`S.V ∋ coe c`). -/
theorem movingCoherenceDatum_canonical_D_inj (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    (hoff : (((c : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((c : ℂ) : RiemannSphere)))
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))) (S.sheet i (((c : ℂ) : RiemannSphere)))))
    (hgmero : ∀ᶠ b' in 𝓝 c, ∀ i,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i))) :
    Function.Injective
      (movingCoherenceDatum_canonical (g := g) (ω₀ := ω₀) hdiv hoff S hmero hgmero).D.xs := by
  intro k k' hkk'
  exact S.sheet_inj (((c : ℂ) : RiemannSphere)) S.mem_V hkk'

/-- **`hCfull_image` for `movingCoherenceDatum_canonical`.**  The reference sheet fibre and the canonical
full-fibre selection at `c` have the same `Finset.univ.image`: both enumerate the full fibre `F⁻¹(coe c)`
(the sheets sweep it; the canonical selection is the full fibre at the good value `c`). -/
theorem movingCoherenceDatum_canonical_D_image (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    (hoff : (((c : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((c : ℂ) : RiemannSphere)))
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet i (((c : ℂ) : RiemannSphere)))) (S.sheet i (((c : ℂ) : RiemannSphere)))))
    (hgmero : ∀ᶠ b' in 𝓝 c, ∀ i,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i)))
    (hc_good : GoodValue g f hdiv c) :
    Finset.univ.image
        (movingCoherenceDatum_canonical (g := g) (ω₀ := ω₀) hdiv hoff S hmero hgmero).D.xs
      = Finset.univ.image (canonicalFibreSelection g f hdiv c).xs := by
  apply image_univ_eq_of_range_eq
  -- Both ranges equal the full fibre `F⁻¹(coe c)`.
  rw [canonicalFibreSelection_xs_range g f hdiv hc_good]
  -- The sheet-fibre range: `.D.xs k = S.sheet k (coe c)`, range = fibre by `sheetValues_range_eq_fibre`.
  have hrange : Set.range
      (movingCoherenceDatum_canonical (g := g) (ω₀ := ω₀) hdiv hoff S hmero hgmero).D.xs
      = Set.range (fun k => S.sheet k (((c : ℂ) : RiemannSphere))) := rfl
  rw [hrange, sheetValues_range_eq_fibre S S.mem_V]

/-! ## The `Cfull`-discharged kirovGenus-`0` capstone

Wiring `movingCoherenceDatum_canonical` (+ its combinatorial fields) into
`residueTheorem_ofCanonicalSimpleInfty_genus0_germ`, the per-centre full-fibre moving coherence `Cfull`
is **discharged** from the per-centre genericity (off-branch pole-values + good values), the regular-value
`g`-meromorphy near/at each centre, and the global "`g` is holomorphic off the poles of `α`"
(`hg_an_offpoles`).  Gate A `∑Res = 0` then rests on the off-centre analyticity `hreg`/`hbnd`, the
`∞`-coherence `hcoh_full`, and the discrete genericity bookkeeping — *no* `Cfull`/`hCfull_*`/`hnonpole_an`
supplied. -/

/-- **Gate A `∑Res = 0` (kirovGenus `0`, simple `∞`-poles, canonical selection) with the finite full-fibre
moving coherence `Cfull` DISCHARGED.**  The per-centre `Cfull i` is built internally by
`movingCoherenceDatum_canonical` from:

* `hoff_cs i` — the pole-value `cs i` is off the branch locus (the standard adapted-cover genericity);
* `hc_good i` — `cs i` is a good value (off-branch + `g`-meromorphic at the full fibre over `cs i`);
* `hgmero i` — the regular-value `g`-meromorphy near `cs i` (eventually at the full fibre points);
* `hg_an_offpoles` — `g`'s chart-pullback is analytic at every non-pole (the meaning of `α = ω₀·g`
  having poles exactly `poles`).

The deep §VIII.3 diagonal identity (value-trace = moving sphere-fibre sum) is discharged by the symmetric
lever inside `movingCoherenceDatum_canonical`.  Gate A then rests on `hreg`/`hbnd` (off-centre analyticity)
and `hcoh_full` (the `∞`-coherence), plus the discrete genericity. -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0_germ_Cfull (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hoff_cs : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hc_good : ∀ i, GoodValue g f hdiv (cs i))
    (hgmero : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∀ j,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_offpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
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
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 := by
  classical
  -- Per-centre sphere sheet system at the off-branch pole-value `coe (cs i)`.
  set S : ∀ i, Jacobians.LocalSheetSystem f.toRiemannSphere (((cs i : ℂ) : RiemannSphere)) :=
    fun i => (exists_sphereSheetSystem f (exists_orderAtPoint_ne_zero f hdiv) (hoff_cs i)).some
    with hS
  -- The reference-sheet-fibre `g`-meromorphy at `coe (cs i)` (from the good value `hc_good i`: the
  -- canonical full fibre is the sphere fibre, so the sheet points are full-fibre points).
  have hmeroS : ∀ i, ∀ k, MeromorphicAt
      (fun z => g ((chartAt ℂ ((S i).sheet k (((cs i : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ ((S i).sheet k (((cs i : ℂ) : RiemannSphere))))
        ((S i).sheet k (((cs i : ℂ) : RiemannSphere)))) := by
    intro i k
    -- The sheet point lies in the fibre `F⁻¹(coe cs_i)` = range of the canonical selection (good value);
    -- the canonical selection's fibre points are `fullFibreEnum`, where `g`'s pullback is meromorphic.
    have hfib : (S i).sheet k (((cs i : ℂ) : RiemannSphere)) ∈
        f.toRiemannSphere ⁻¹' {(((cs i : ℂ) : RiemannSphere))} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact (S i).sheet_section k _ (S i).mem_V
    rw [← canonicalFibreSelection_xs_range g f hdiv (hc_good i),
      canonicalFibreSelection_eq_ofFullFibre g f hdiv (hc_good i)] at hfib
    obtain ⟨j, hj⟩ := hfib
    -- `hj : (ofFullFibre …).xs j = S.sheet k (coe cs_i)`, i.e. `fullFibreEnum f hdiv (cs i) j = …`.
    have hpt : (S i).sheet k (((cs i : ℂ) : RiemannSphere)) = fullFibreEnum f hdiv (cs i) j := hj.symm
    rw [hpt]
    exact (hc_good i).2 j
  -- Assemble the per-centre full-fibre moving coherence datum.
  set Cfull : ∀ i, MovingCoherenceDatum ω₀ g f (canonicalFibreSelection g f hdiv) (cs i) :=
    fun i => movingCoherenceDatum_canonical hdiv (hoff_cs i) (S i) (hmeroS i) (hgmero i) with hCfull
  refine residueTheorem_ofCanonicalSimpleInfty_genus0_germ hdiv hgood m cs ρ hcs_ball hcs_inj br
    hcenters_cs Cfull
    (fun i => movingCoherenceDatum_canonical_D_inj hdiv (hoff_cs i) (S i) (hmeroS i) (hgmero i))
    (fun i => movingCoherenceDatum_canonical_D_image hdiv (hoff_cs i) (S i) (hmeroS i) (hgmero i)
      (hc_good i))
    (fun i k hk => hg_an_offpoles _ hk)
    hsimpleInf hmeroInf hnonpole_inf_an hreg hbnd hcoh_full

/-! ## The `∞`-coherence in its cleanest (unpatched) form

The patched `∞`-coherence `hcoh_full` differs from the unpatched geometric `∞`-coherence
`recipCoeff (valueChartTrace …) =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF …)` only at the finitely-many
branch values, which escape to `∞` under `ζ ↦ ζ⁻¹` (`recipCoeff_valueChartTracePatched_eventuallyEq`).
So the genuine `∞`-residual is the **unpatched** geometric `∞`-coherence — the §VIII.3
`∞`-single-valuedness "the trace = the moving `∞`-fibre sum near `∞`, read in the reciprocal chart" —
which we expose as the cleaner input below.  This is *not* a disguise of `∑Res = 0`: it is the moving
fibre-sum identity at `∞` (the reciprocal-chart analogue of `MovingCoherenceDatum.coherent`), never
referencing the residue cancellation. -/

/-- **Gate A `∑Res = 0` (kirovGenus `0`, simple `∞`-poles, canonical selection) with `Cfull` discharged and
the `∞`-coherence taken in its cleanest *unpatched* geometric form.**  Identical to
`residueTheorem_ofCanonicalSimpleInfty_genus0_germ_Cfull` except the patched `∞`-coherence `hcoh_full` is
replaced by the **unpatched geometric `∞`-coherence** `hcoh_geom`:

> `recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full)`,

the genuine §VIII.3 `∞`-single-valuedness (the trace germ-equals the fixed `∞`-fibre moving sum along the
shared reciprocal-chart sheets near `∞`).  The patched form is recovered via
`recipCoeff_valueChartTracePatched_eventuallyEq` (the patch escapes to `∞`).  This is the smallest honest
`∞`-residual remaining after `Cfull` is discharged. -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0_germ_Cfull_geomInfty
    (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hoff_cs : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hc_good : ∀ i, GoodValue g f hdiv (cs i))
    (hgmero : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∀ j,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_offpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
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
    (hcoh_geom : recipCoeff (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv))
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofCanonicalSimpleInfty_genus0_germ_Cfull hdiv hgood m cs ρ hcs_ball hcs_inj br
    hcenters_cs hoff_cs hc_good hgmero hg_an_offpoles hsimpleInf hmeroInf hnonpole_inf_an hreg hbnd
    -- Patch the `∞`-coherence: `recipCoeff (patched) =ᶠ recipCoeff (raw) =ᶠ recipCoeff (inftyMovingSumNF)`.
    ((recipCoeff_valueChartTracePatched_eventuallyEq ω₀ f
      (canonicalFibreSelection g f hdiv) br).trans hcoh_geom)

/-! ## Discharging the off-centre analyticity `hreg`

At a value `w` off the centres `cs` and off the branch values, `coe w` is off the branch locus *and*
not a pole-value (`hcenters_cs` + `w ∉ image cs` + `coe` injectivity), so every full-fibre point over
`coe w` is a regular **non-pole** of `α`.  The canonical selection then has a `MovingCoherenceDatum` at
`w` (`movingCoherenceDatum_canonical`) whose fixed-fibre points are non-poles, so
`analyticAt_valueChartTrace_of_movingDatum` (the self-coherence ⟹ analyticity bridge) gives `hreg` at
`w` from the global "`g` holomorphic off the poles" `hg_an_offpoles`.  This eliminates `hreg` for
`br ⊇ branchValues f`. -/

/-- **A fibre point at a non-pole-value is not a pole of `α`.**  If `coe w` is finite, `w ∉ image cs`,
and `hcenters_cs` identifies the finite pole-values with `image cs`, then any `p` with `F p = coe w` is
**not** in `poles`: otherwise `coe w = F p ∈ (poles.image F).erase ∞ = (image cs).image coe`, forcing
`w = cs i` (`coe` injective) — contradicting `w ∉ image cs`. -/
theorem notMem_poles_of_fibrePoint_offCentres {m : ℕ} {cs : Fin m → ℂ}
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    {w : ℂ} (hw : w ∉ Finset.univ.image cs) {p : X}
    (hp : f.toRiemannSphere p = (((w : ℂ) : RiemannSphere))) : p ∉ poles := by
  classical
  intro hpole
  -- `coe w = F p ∈ poles.image F`, and `coe w ≠ ∞`, so `coe w ∈ (poles.image F).erase ∞`.
  have hmem : (((w : ℂ) : RiemannSphere)) ∈ (poles.image f.toRiemannSphere).erase OnePoint.infty := by
    rw [Finset.mem_erase]
    exact ⟨OnePoint.coe_ne_infty w, by
      rw [Finset.mem_image]; exact ⟨p, hpole, hp⟩⟩
  rw [← hcenters_cs, Finset.mem_image] at hmem
  obtain ⟨c, hc_mem, hc_eq⟩ := hmem
  -- `coe c = coe w ⟹ c = w`, and `c ∈ image cs`, so `w ∈ image cs` — contradiction.
  have : c = w := OnePoint.coe_injective hc_eq
  rw [this] at hc_mem
  exact hw hc_mem

/-- **`hreg` discharged for the canonical selection.**  At every value `w` off `image cs ∪ br` with
`br ⊇ branchValues f`, `valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)` is `AnalyticAt`.  `coe w`
is off the branch locus (`br ⊇ branchValues`) so `w` is a good value (with the regular-value `g`-data
`hgood_reg`); the canonical selection has a `MovingCoherenceDatum` at `w` whose fixed fibre points are
non-poles (`notMem_poles_of_fibrePoint_offCentres`), so `analyticAt_valueChartTrace_of_movingDatum`
applies with `hg_an_offpoles`. -/
theorem hreg_canonical_of_offBranch (hdiv : (f.div : Divisor X) ≠ 0) {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} (hbr : branchValues f hdiv ⊆ br)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_offpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) :
    ∀ w ∉ Finset.univ.image cs ∪ br,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) w := by
  classical
  intro w hw
  have hwcs : w ∉ Finset.univ.image cs := fun h => hw (Finset.mem_union_left _ h)
  have hwbr : w ∉ br := fun h => hw (Finset.mem_union_right _ h)
  have hoff : (((w : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere :=
    coe_notMem_branchLocus_of_notMem_branchValues f hdiv (fun h => hwbr (hbr h))
  -- The sphere sheet system at `coe w` (off-branch) and the moving coherence datum.
  set S : Jacobians.LocalSheetSystem f.toRiemannSphere (((w : ℂ) : RiemannSphere)) :=
    (exists_sphereSheetSystem f (exists_orderAtPoint_ne_zero f hdiv) hoff).some with hS
  -- The reference sheet-fibre `g`-meromorphy at `coe w` (good value ⟹ full fibre = sphere fibre).
  have hmeroS : ∀ k, MeromorphicAt
      (fun z => g ((chartAt ℂ (S.sheet k (((w : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet k (((w : ℂ) : RiemannSphere)))) (S.sheet k (((w : ℂ) : RiemannSphere)))) := by
    intro k
    have hfib : S.sheet k (((w : ℂ) : RiemannSphere)) ∈
        f.toRiemannSphere ⁻¹' {(((w : ℂ) : RiemannSphere))} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]; exact S.sheet_section k _ S.mem_V
    rw [← canonicalFibreSelection_xs_range g f hdiv (hgood_reg w hw),
      canonicalFibreSelection_eq_ofFullFibre g f hdiv (hgood_reg w hw)] at hfib
    obtain ⟨j, hj⟩ := hfib
    have hpt : S.sheet k (((w : ℂ) : RiemannSphere)) = fullFibreEnum f hdiv w j := hj.symm
    rw [hpt]; exact (hgood_reg w hw).2 j
  set C : MovingCoherenceDatum ω₀ g f (canonicalFibreSelection g f hdiv) w :=
    movingCoherenceDatum_canonical hdiv hoff S hmeroS (hgmero_reg w hw) with hC
  -- The fixed fibre points `C.D.xs k` lie in the full fibre `F⁻¹(coe w)` (its range equals the canonical
  -- range, which is the fibre at the good value `w`), hence are non-poles (non-pole-value `w`); so `g` is
  -- analytic there by `hg_an_offpoles`.
  refine analyticAt_valueChartTrace_of_movingDatum C (fun k => ?_)
  -- `C.D.xs k` lies in the canonical range = full fibre `F⁻¹(coe w)` (via the proven image-equality).
  have himg : Finset.univ.image C.D.xs
      = Finset.univ.image (canonicalFibreSelection g f hdiv w).xs := by
    rw [hC]
    exact movingCoherenceDatum_canonical_D_image (ω₀ := ω₀) hdiv hoff S hmeroS
      (hgmero_reg w hw) (hgood_reg w hw)
  have hmemImg : C.D.xs k ∈ Finset.univ.image (canonicalFibreSelection g f hdiv w).xs := by
    rw [← himg]; exact Finset.mem_image_of_mem C.D.xs (Finset.mem_univ k)
  rw [Finset.mem_image] at hmemImg
  obtain ⟨j, _, hj⟩ := hmemImg
  have hfib : f.toRiemannSphere (C.D.xs k) = (((w : ℂ) : RiemannSphere)) := by
    rw [← hj]
    have : (canonicalFibreSelection g f hdiv w).xs j ∈
        Set.range (canonicalFibreSelection g f hdiv w).xs := ⟨j, rfl⟩
    rw [canonicalFibreSelection_xs_range g f hdiv (hgood_reg w hw)] at this
    rwa [Set.mem_preimage, Set.mem_singleton_iff] at this
  exact hg_an_offpoles _ (notMem_poles_of_fibrePoint_offCentres hcenters_cs hwcs hfib)

/-! ## The kirovGenus-`0` capstone with both `Cfull` and `hreg` discharged

Combining `movingCoherenceDatum_canonical` (the per-centre `Cfull`) with `hreg_canonical_of_offBranch`
(the off-centre analyticity `hreg`), Gate A `∑Res = 0` rests on:

* the per-centre genericity (off-branch pole-values `hoff_cs`, good values `hc_good`, near-centre
  `g`-meromorphy `hgmero`);
* the regular-value genericity (every value off `cs ∪ br` is a good value `hgood_reg` with near-value
  `g`-meromorphy `hgmero_reg`), with `br ⊇ branchValues f` (the branch-patch covers the branch values);
* `hg_an_offpoles` (`g` holomorphic off the poles);
* the branch-value boundedness `hbnd` (the one remaining analytic input besides `∞`); and
* the `∞`-coherence `hcoh_geom` (the unpatched §VIII.3 `∞`-single-valuedness).

The finite full-fibre moving coherence `Cfull` and the off-centre analyticity `hreg` are **discharged**. -/

/-- **Gate A `∑Res = 0` (kirovGenus `0`, simple `∞`-poles, canonical selection) with `Cfull` AND `hreg`
discharged.**  The most-reduced sound form: only the genericity bookkeeping, the branch-value boundedness
`hbnd`, and the `∞`-coherence `hcoh_geom` remain.  The per-centre full-fibre moving coherence `Cfull` is
built by `movingCoherenceDatum_canonical`; the off-centre analyticity `hreg` is discharged by
`hreg_canonical_of_offBranch`.  Both rest on the symmetric-invariance lever (Miranda §VIII.3, no
labeling). -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg
    (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ) (hbr : branchValues f hdiv ⊆ br)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hoff_cs : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hc_good : ∀ i, GoodValue g f hdiv (cs i))
    (hgmero : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∀ j,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_offpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
        (𝓝[≠] b₀) (𝓝 0))
    (hcoh_geom : recipCoeff (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv))
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofCanonicalSimpleInfty_genus0_germ_Cfull_geomInfty hdiv hgood m cs ρ hcs_ball hcs_inj
    br hcenters_cs hoff_cs hc_good hgmero hg_an_offpoles hsimpleInf hmeroInf hnonpole_inf_an
    (hreg_canonical_of_offBranch hdiv hbr hcenters_cs hgood_reg hgmero_reg hg_an_offpoles) hbnd
    hcoh_geom

end Jacobians.Dolbeault.SerreResidueTheorem
