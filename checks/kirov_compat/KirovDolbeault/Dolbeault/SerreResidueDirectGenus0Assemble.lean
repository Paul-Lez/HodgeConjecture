/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueDirectGenus0
import KirovDolbeault.Dolbeault.SerreResidueDirectAssemble

/-!
# Gate A `∑Res = 0` for an adapted cover, residual-#5 group discharged (Miranda §VIII.3 genericity)

`Jacobians.Dolbeault.SerreResidueTheorem.directTraceGeometry_ofCanonicalSimpleInfty`
(`SerreResidueDirectAssemble.lean`) reduces Gate A's genericity for an adapted cover to a precise list
of residuals, **including** the kirovGenus-`0` `∞`-vanishing field-group `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq`
(residual #5).  That group was, before `SerreResidueDirectGenus0.lean`, discharged only for the empty
pole case (and, as that file shows, the field `hR₀0 : R₀ 0 = 0` is *circular* with the residue theorem
when read through the global `T = L.R`).

This file mirrors the adapted-cover assembly but routes through the residual-#5-**discharged** residue
theorem `residueTheorem_of_directGeometry_genus0` (`SerreResidueDirectGenus0.lean`), so the resulting
capstones yield Gate A `∑Res = 0` **without** the `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` hypotheses.  The proven
combinatorial field-groups (pole sub-fibre `poleSubfibre`, `∞`-pole sub-enumeration `poleSubEnum`, the
finite-pole-value enumeration, the full `∞`-fibre from simple poles, and the canonical-selection
`Φ`-enumeration) are reused verbatim from `SerreResidueDirectAssemble.lean`.

Because the `DirectTraceGeometry` *structure* still carries the `R₀`/`hR₀_*` fields, a residual-#5-free
constructor cannot return the structure; it returns the residue theorem `∑Res = 0` directly — the
honest "drops these from the hypothesis list" form.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `residueTheorem_ofAdapted_genus0` — Gate A `∑Res = 0` for a general adapted cover (general `Φ`), with
  the kirovGenus-`0` `∞`-vanishing field-group dropped.
* `residueTheorem_ofAdaptedSimpleInfty_genus0` — the simple-`∞` specialization (the full `∞`-fibre
  constructed from simple poles).
* `residueTheorem_ofCanonicalSimpleInfty_genus0` — the most-wired capstone: the canonical full-fibre
  selection + simple `∞`-poles, so the `Φ`-enumeration is discharged from the single pole-value-goodness
  genericity `hgood`.  Gate A `∑Res = 0` rests on *exactly* the per-centre full-fibre coherence `Cfull`,
  the off-centre analyticity `hreg`/`hbnd`, the **finite** junk-freeness `hcont_int`, and the
  `∞`-coherence `hcoh_full` — the kirovGenus-`0` `∞`-vanishing is **gone**.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3.
* `SerreResidueDirectGenus0.lean` (the Cauchy-at-`∞` discharge of residual #5).
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

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ## The general adapted-cover capstone (residual-#5 group dropped)

Identical proven field-groups to `directTraceGeometry_ofAdapted`, but routed through
`residueTheorem_of_directGeometry_genus0`, so `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` are **not** inputs. -/

/-- **Gate A `∑Res = 0` from an adapted cover, residual-#5 group discharged.**  Mirrors the proven
field-groups of `directTraceGeometry_ofAdapted` (pole sub-fibre `D := poleSubfibre ∘ Φ`, the `∞`-pole
sub-enumeration, the matching `hpole_image`/`hpole_image_inf`, the centre bookkeeping) and feeds them to
`residueTheorem_of_directGeometry_genus0`.  The kirovGenus-`0` `∞`-vanishing field-group is **gone**; the
remaining analytic inputs are `hreg`/`hbnd` (off-centre analyticity), the **finite** junk-freeness
`hcont_int`, and the `∞`-coherence `hcoh_full`. -/
theorem residueTheorem_ofAdapted_genus0
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
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full)) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_of_directGeometry_genus0 Φ m cs ρ hcs_ball hcs_inj br hreg hbnd Cfull
    -- pole-only fibre `D := poleSubfibre ∘ Φ` (proven combinatorics from `SerreResidueDirectAssemble`).
    (fun p => poleSubfibre poles (Φ p))
    (fun p => poleSubfibre_xs_injective poles (Φ p) (hΦ_inj p))
    (fun p i => poleSubfibre_xs_mem poles (Φ p) (hΦ_mem p) i)
    (fun p a ha hfa => by
      obtain ⟨i, rfl⟩ := hΦ_surj p a ha hfa
      exact ⟨⟨i, ha⟩, rfl⟩)
    hcenters_cs hCfull_inj
    (fun i => by rw [hCfull_image i]; exact poleSubfibre_hpole_image poles (Φ (cs i)))
    hnonpole_an hcont_int Dinf_full hcoh_full hfullInf_inj
    -- `∞`-pole sub-enumeration `xsInf_po := Dinf_full.xs ∘ Subtype.val`.
    (ιInfP := {k // Dinf_full.xs k ∈ poles}) (fun k => Dinf_full.xs k.1)
    (poleSubEnum_injective poles Dinf_full.xs hfullInf_inj)
    (fun k => poleSubEnum_mem poles Dinf_full.xs hinf_mem k)
    (fun a ha hfa => poleSubEnum_surj poles Dinf_full.xs hinf_surj a ha hfa)
    (poleSubEnum_hpole_image poles Dinf_full.xs)
    hnonpole_inf_an

/-- **Gate A `∑Res = 0` from an adapted cover with simple `∞`-poles, residual-#5 group discharged.**  The
simple-`∞` specialization of `residueTheorem_ofAdapted_genus0`: the full `∞`-fibre `Dinf_full` is
constructed as `inftyFibreDataNF_full` (enumerating all `f`-poles, each simple), discharging the four
`∞`-fibre-data inputs from `hsimpleInf`/`hmeroInf`.  No kirovGenus-`0` `∞`-vanishing. -/
theorem residueTheorem_ofAdaptedSimpleInfty_genus0
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
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofAdapted_genus0 Φ hΦ_inj hΦ_mem hΦ_surj m cs ρ hcs_ball hcs_inj br hcenters_cs
    Cfull hCfull_inj hCfull_image hnonpole_an
    (inftyFibreDataNF_full g f hsimpleInf hmeroInf)
    (inftyFibreEnum_injective f)
    (fun k => inftyFibreEnum_mem f k)
    (fun _a _ha hfa => inftyFibreEnum_surj f hfa)
    hnonpole_inf_an hreg hbnd hcont_int hcoh_full

/-! ## The canonical-selection capstone (residual-#5 group dropped)

The most-wired form: `Φ := canonicalFibreSelection g f hdiv` (the three `Φ`-enumeration inputs from the
single pole-value-goodness genericity `hgood`), simple `∞`-poles.  Mirrors
`residueTheorem_of_canonicalAdapted` but with the kirovGenus-`0` `∞`-vanishing field-group **removed** — the
honest standing of Gate A after this discharge. -/

/-- **Gate A `∑Res = 0` from the canonical selection with simple `∞`-poles, residual-#5 group
discharged.**  The capstone: with the canonical full-fibre selection (so the `Φ`-enumeration inputs come
from the single pole-value-goodness `hgood`) and simple `∞`-poles, the residue theorem `∑_{a ∈ poles}
formFnResidue ω₀ g a = 0` holds modulo *only* the per-centre full-fibre coherence `Cfull`, the
off-centre analyticity `hreg`/`hbnd`, the **finite** junk-freeness `hcont_int`, and the `∞`-coherence
`hcoh_full`.  The kirovGenus-`0` `∞`-vanishing `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` is **discharged internally**
(Cauchy at `∞` for the entire remainder + `hcoh_full`), so it is no longer a hypothesis. -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0 (hdiv : (f.div : Divisor X) ≠ 0)
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
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br - L.R)
          =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a,
        ContinuousAt (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br - L.R) p)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofAdaptedSimpleInfty_genus0 (canonicalFibreSelection g f hdiv)
    (canonicalFibreSelection_hΦ_inj f hdiv)
    (canonicalFibreSelection_hΦ_mem f hdiv)
    (canonicalFibreSelection_hΦ_surj f hdiv hgood)
    m cs ρ hcs_ball hcs_inj br hcenters_cs Cfull hCfull_inj hCfull_image hnonpole_an
    hsimpleInf hmeroInf hnonpole_inf_an hreg hbnd hcont_int hcoh_full

end Jacobians.Dolbeault.SerreResidueTheorem
