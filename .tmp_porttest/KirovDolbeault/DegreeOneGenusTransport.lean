/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Provenance: port-side reconstruction of the biholomorphic genus transport from
the parent repository's `Jacobians/RiemannSurface/DegreeOneGenusZero.lean`
(`inverse_contMDiff_of_bijective_order_one` → `degreeOne_genus_zero`,
lines 388–451, axiom-clean). Re-proved here against the port's own machinery
(`degreeOne_bijective`, the discharge lemma
`deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood`, and the manifold IFT
`exists_holo_localInverse`) because the port package cannot import the parent
package (circular Lake dependency).
-/
import KirovDolbeault.DegreeOneSphere
import KirovDolbeault.ManifoldIFT
import KirovDolbeault.HolomorphicForms
import KirovDolbeault.Discharge.Manifold.RegularValueExistsRegUnconditional

/-!
# Degree one ⟹ genus zero: the biholomorphic genus transport

This file closes the genus-0 conclusion of the single-simple-pole chain
**keystone-free and de-Rham-free** (Abel-wall piece A3 of
`docs/planning/ABEL_WALL_GAP_ANALYSIS.md`, ported per its §4 item 1):

> a meromorphic function with a single simple pole makes `X` biholomorphic to
> `ℂℙ¹`, and a biholomorphism transports holomorphic 1-forms, so
> `kirovGenus X = kirovGenus ℂℙ¹ = 0`.

Compare `genus_zero_of_nonempty_homeo_sphere` (`KirovDolbeault.DegreeOneSphere`),
which reaches the same conclusion from a **bare homeomorphism** `X ≃ₜ S²` and
therefore must route through the de Rham wall `HasHolomorphicPrimitives X`
(a homeomorphism carries no complex structure, so the pullback transport is
unavailable there). Here the hypothesis is analytic, the transport applies, and
no de Rham input is needed.

## Main results

* `Jacobians.bijective_inverse_contMDiff` — a non-constant bijective `C^ω` map
  between compact connected Riemann surfaces has `C^ω` inverse.
* `Jacobians.kirovGenus_eq_of_biholo` — mutually inverse `C^ω` maps give
  `kirovGenus X = kirovGenus Y` (pullback of forms is a linear equivalence).
* `Jacobians.genus_zero_of_singleSimplePole` — a single simple pole forces
  `kirovGenus X = 0`.

## Route notes (vs the parent repository's proof)

The parent proof derives inverse holomorphy from "local mapping order 1
everywhere", extracted from its weighted-fiber-conservation machinery, which
has no port analog. Port-side the same fact is cheaper: global injectivity
gives local injectivity at every point, the discharge bridge
`deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood` converts that to a
non-vanishing chart-pullback derivative, and `exists_holo_localInverse`
(manifold IFT) produces a local `C^ω` section that must agree with the global
set-theoretic inverse by injectivity.

## References

* Forster, *Lectures on Riemann Surfaces*, §§4–5, §10.
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. II §4, Ch. IV §1.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Bijective ⟹ biholomorphic.** A non-constant bijective `C^ω` map between
compact connected Riemann surfaces has a `C^ω` (holomorphic) inverse.

At each `y : Y` with `x := F⁻¹ y`: global injectivity makes `F` locally
injective at `x`, so the chart-pullback derivative is nonzero
(`deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood`), so the manifold IFT
(`exists_holo_localInverse`) gives a `C^ω` local section `g` of `F` near `y`;
`g` agrees with the set-theoretic inverse near `y` by injectivity, so the
inverse is `C^ω` at `y`. -/
theorem bijective_inverse_contMDiff
    (F : X → Y) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hnc : ¬ IsConstantMap F) (hbij : Function.Bijective F) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((Equiv.ofBijective F hbij).symm : Y → X) := by
  intro y
  set e := Equiv.ofBijective F hbij with he
  set x : X := e.symm y with hx
  have hFx : F x = y := e.apply_symm_apply y
  -- Global injectivity ⟹ local injectivity at `x`.
  have hinj : ∃ U ∈ 𝓝 x, Set.InjOn F U :=
    ⟨Set.univ, Filter.univ_mem, fun a _ b _ hab => hbij.1 hab⟩
  -- Hence the chart-pullback derivative at `x` is nonzero.
  have hderiv : deriv ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 :=
    Jacobians.Discharge.ContMDiff.Degree.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood
      hF hnc x hinj
  -- Manifold IFT: a `C^ω` local section `g` of `F` on an open `V ∋ F x = y`.
  obtain ⟨g, V, hVopen, hFxV, _hgFx, hsec, hgsmooth⟩ :=
    exists_holo_localInverse F hF x hderiv
  have hyV : y ∈ V := hFx ▸ hFxV
  have hgAt : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g y :=
    hgsmooth.contMDiffAt (hVopen.mem_nhds hyV)
  -- `g` agrees with the set-theoretic inverse on `V` (injectivity).
  have heq : (e.symm : Y → X) =ᶠ[𝓝 y] g := by
    filter_upwards [hVopen.mem_nhds hyV] with y' hy'
    refine hbij.1 ?_
    calc F (e.symm y') = y' := e.apply_symm_apply y'
      _ = F (g y') := (hsec y' hy').symm
  exact hgAt.congr_of_eventuallyEq heq

/-- **Genus transport along a biholomorphism.** Mutually inverse `C^ω` maps
`F : X → Y`, `G : Y → X` make `pullbackForm F` a linear equivalence
`Ω(Y) ≃ₗ[ℂ] Ω(X)` (inverse `pullbackForm G`, via `pullbackForm_id` /
`pullbackForm_comp`), so the genera agree. -/
theorem kirovGenus_eq_of_biholo
    (F : X → Y) (G : Y → X)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hG : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω G)
    (hGF : G ∘ F = id) (hFG : F ∘ G = id) :
    kirovGenus X = kirovGenus Y := by
  have hFG_smooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (F ∘ G) := by rw [hFG]; exact contMDiff_id
  have hGF_smooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (G ∘ F) := by rw [hGF]; exact contMDiff_id
  -- `pullbackForm` of either round-trip is the identity (proof irrelevance in
  -- the bundled smoothness argument).
  have keyY : ∀ h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (F ∘ G),
      pullbackForm (F ∘ G) h =
        (LinearMap.id : HolomorphicOneForms Y →ₗ[ℂ] HolomorphicOneForms Y) := by
    rw [hFG]
    intro h
    exact pullbackForm_id
  have keyX : ∀ h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (G ∘ F),
      pullbackForm (G ∘ F) h =
        (LinearMap.id : HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms X) := by
    rw [hGF]
    intro h
    exact pullbackForm_id
  have h1 : (pullbackForm G hG).comp (pullbackForm F hF) = LinearMap.id :=
    (pullbackForm_comp G hG F hF hFG_smooth).symm.trans (keyY hFG_smooth)
  have h2 : (pullbackForm F hF).comp (pullbackForm G hG) = LinearMap.id :=
    (pullbackForm_comp F hF G hG hGF_smooth).symm.trans (keyX hGF_smooth)
  show Module.finrank ℂ (HolomorphicOneForms X) = Module.finrank ℂ (HolomorphicOneForms Y)
  exact (LinearEquiv.ofLinear (pullbackForm F hF) (pullbackForm G hG) h2 h1).finrank_eq.symm

/-- **Single simple pole ⟹ genus zero** (keystone- and de-Rham-free).

`F := f.toSphere P` is holomorphic, non-constant and of degree one
(`KirovDolbeault.DegreeOneSphere` Steps 1–2), hence bijective
(`degreeOne_bijective`) with holomorphic inverse
(`bijective_inverse_contMDiff`); transporting holomorphic 1-forms along this
biholomorphism (`kirovGenus_eq_of_biholo`) gives
`kirovGenus X = kirovGenus ℂℙ¹ = 0` (`RiemannSphere.genus_eq_zero`).

This is the genus-obstruction half (A2+A3) of the Abel wall
(`abelJacobi_twoPoint_ne_zero`, `KirovDolbeault.Abel`): together with the
`div f = (P) − (Q) ⟹ HasSingleSimplePole` bookkeeping (A1) it yields
"`(P) − (Q)` principal with `P ≠ Q` contradicts `0 < kirovGenus X`" without
touching `HasHolomorphicPrimitives`. -/
theorem genus_zero_of_singleSimplePole
    (f : MeromorphicFunction X) {P : X} (hP : f.HasSingleSimplePole P) :
    kirovGenus X = 0 := by
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P) := f.contMDiff_toSphere hP
  have hnc : ¬ IsConstantMap (f.toSphere P) := f.toSphere_not_isConstant hP
  have hdeg : degreeFiber (f.toSphere P) hF = 1 := f.degreeFiber_toSphere_eq_one hP hF
  have hbij : Function.Bijective (f.toSphere P) :=
    degreeOne_bijective (f.toSphere P) hF hnc hdeg
  set e := Equiv.ofBijective (f.toSphere P) hbij with he
  have hsymm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (e.symm : RiemannSphere → X) :=
    bijective_inverse_contMDiff (f.toSphere P) hF hnc hbij
  have hGF : (e.symm : RiemannSphere → X) ∘ (f.toSphere P) = id :=
    funext fun x => e.symm_apply_apply x
  have hFG : (f.toSphere P) ∘ (e.symm : RiemannSphere → X) = id :=
    funext fun y => e.apply_symm_apply y
  have htrans : kirovGenus X = kirovGenus RiemannSphere :=
    kirovGenus_eq_of_biholo (f.toSphere P) (e.symm : RiemannSphere → X) hF hsymm hGF hFG
  rw [htrans]
  exact RiemannSphere.genus_eq_zero

end Jacobians
