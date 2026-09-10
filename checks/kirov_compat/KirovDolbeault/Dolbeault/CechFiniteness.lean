/-
  Dolbeault ladder — `H¹(X, 𝒪_D)` finiteness (Forster 14.9), the de-risked finiteness tree.

  Plan: the cochain restriction
  between the cover and a relatively-compact shrinking is a COMPACT operator (Montel), so by the
  Schwartz finiteness lemma (`SchwartzFiniteness.finiteDimensional_quotient_range_add_compact`,
  Forster 14.8 — DONE) the Čech `H¹` is finite-dimensional. The Montel input reuses the repo's
  *plain-function* disk lemmas (`Montel/Compactness.lean`); this file starts from the de-bundled
  compact-restriction ATOM (validated by a spike), then builds the cochain sup-norm representation
  and the wiring.

  STATUS: the compact-restriction atom is proven here; the cochain-rep + Leray + comparison layers
  that discharge `DolbeaultLadder.finiteDimensional_cechH1` are scaffolded as explicit obligations below.
-/
import KirovDolbeault.Montel.Compactness
import KirovDolbeault.Dolbeault.SchwartzFiniteness

open Metric Topology BoundedContinuousFunction
open Jacobians.Montel

namespace Jacobians.Dolbeault.CechFiniteness

/-! ### The de-bundled compact-restriction atom (Montel core for cochains)

A sup-`M`-bounded family of functions holomorphic on an open `U ⊆ ℂ`, restricted to a compact convex
`K ⋐ U`, is relatively compact in `K →ᵇ ℂ`. This is the plain-function analogue of the repo's
bundle-level `isCompact_closure_image_inner_bcf`, and it is *simpler* (no `localRep`/cotangent
bookkeeping). It is the engine that makes the cochain restriction a compact operator. -/

theorem isCompact_closure_restrict_bddHolo
    {U K : Set ℂ} (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U)
    (hKconv : Convex ℝ K) {M : ℝ} (hMnn : 0 ≤ M)
    {S : Type*} (g : S → ℂ → ℂ)
    (hg_an : ∀ s, AnalyticOn ℂ (g s) U) (hg_bd : ∀ s, ∀ z ∈ U, ‖g s z‖ ≤ M)
    (hg_cont : ∀ s, ContinuousOn (g s) U) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
    IsCompact (closure (Set.range (fun s : S =>
      mkOfCompact ⟨K.restrict (g s), ((hg_cont s).mono hKU).restrict⟩))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
  apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M) (isCompact_closedBall _ _)
  · -- bounded: every value lies in `closedBall 0 M`
    rintro f y ⟨s, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, mkOfCompact_apply]
    exact hg_bd s y.1 (hKU y.2)
  · -- equicontinuous: plain-function repo lemma + subtype transfer (mirrors the bundle atom)
    classical
    set F_bcf : S → (K →ᵇ ℂ) :=
      fun s => mkOfCompact ⟨K.restrict (g s), ((hg_cont s).mono hKU).restrict⟩ with hFbcf
    have hequi_on : UniformEquicontinuousOn g K :=
      uniformEquicontinuousOn_of_bounded_analyticOn hU hKcpt hKU hKconv hMnn hg_an hg_bd
    have hFbcf_fn : Equicontinuous (fun s : S => (⇑(F_bcf s) : K → ℂ)) :=
      (equicontinuous_restrict_iff g).mpr hequi_on.equicontinuousOn
    let u : ↥(Set.range F_bcf) → S := fun x => Classical.choose x.2
    have hu_spec : ∀ x : ↥(Set.range F_bcf), F_bcf (u x) = x.val :=
      fun x => Classical.choose_spec x.2
    have hcomp : (fun x : ↥(Set.range F_bcf) => (⇑x.val : K → ℂ)) =
        (fun s : S => (⇑(F_bcf s) : K → ℂ)) ∘ u := by
      funext x y; simp only [Function.comp]; rw [hu_spec x]
    have hrange : Equicontinuous (fun x : ↥(Set.range F_bcf) => (⇑x.val : K → ℂ)) := by
      rw [hcomp]; exact hFbcf_fn.comp u
    exact hrange

/-! ### Roadmap — from the atom to `DolbeaultLadder.finiteDimensional_cechH1`

The two hardest, most-uncertain pieces are now DONE and axiom-clean: the abstract Schwartz finiteness
lemma (`SchwartzFiniteness.finiteDimensional_quotient_range_add_compact`, Forster 14.8) and the
de-bundled compact-restriction atom above (the Montel core). The remaining layers are templated
assembly:

* **STEP 1 (rep).** The sup-norm Banach space `BddHol U` of bounded holomorphic functions on an open
  `U ⊆ ℂ` (a closed `ℂ`-subspace of `bcf`, complete; closedness via the repo's
  `analyticOn_of_tendstoLocallyUniformlyOn`), and the restriction CLM `BddHol U → (K →ᵇ ℂ)` for
  `K ⋐ U` compact. It is an `IsCompactOperator` via the atom
  (`isCompactOperator_iff_isCompact_closure_image_closedBall` + `isCompact_closure_restrict_bddHolo`).

* **STEP 2 (cochain).** Assemble the cochain Banach spaces `C^q` over the repo's chart-disk cover +
  its shrinking (`Montel/Cover.lean`: `coverOpen ⊇ chartOpen ⊇ innerChartOpen`); the cochain
  restriction `C^q(𝔘) → C^q(𝔙)` is compact (finite product of the disk restrictions of STEP 1).

* **STEP 3 (Schwartz + Leray).** Feed the Leray two-cover map into
  `finiteDimensional_quotient_range_add_compact`: the restriction `Z¹(𝔘) → Z¹(𝔙)` is compact and the
  induced map on `H¹` is a surjection (chart-disks are Leray, `H¹(disk,𝒪)=0` from the proven G1
  `DbarDisk`), giving `H¹(𝔙, 𝒪)` finite-dimensional.

* **STEP 4 (comparison).** The germ-class `cechH1` (CechComplex) equals the sup-norm-rep `H¹` in
  dimension (they differ only by codiscrete junk, which does not change `H¹` — the same
  codiscrete↔𝓝[≠] bridge proven in `CechH0`), discharging `finiteDimensional_cechH1` for `D = 0`,
  then general `D` by the `D`-twist.
-/

end Jacobians.Dolbeault.CechFiniteness
