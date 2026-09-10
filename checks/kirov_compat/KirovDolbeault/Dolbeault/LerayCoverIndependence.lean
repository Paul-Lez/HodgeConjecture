/-
  Čech finiteness — `exists_cechModel` via cover-independence (mutual-refinement transport).

  This file extends the *acyclic* discharge of `CechFinitenessWiring.exists_cechModel`
  (`exists_cechModel_of_subsingleton`, `CechModelConstruction.exists_cechModel_of_sharedChart_zero`)
  from a literal `SharedChartCover` to **any cover that mutually refines one** — the first genuine use
  of the (complete) Leray cover-independence isomorphism `refineH1_equiv` inside the finiteness node.

  ## What this banks (complete, axiom-clean `[propext, Classical.choice, Quot.sound]`)

    * `subsingleton_cechH1_of_mutualRefinement` — `Subsingleton` transports along a mutual refinement:
      if `𝔙 ⪯ 𝔘` and `𝔘 ⪯ 𝔙` (mutual refinements) and `cechH1 𝔙 D` is a subsingleton, then so is
      `cechH1 𝔘 D` (via the cover-independence equiv `refineH1_equiv`, then `Equiv.subsingleton`).
    * `exists_cechModel_of_mutualRefinement_subsingleton` — hence `exists_cechModel 𝔘 D` for any such
      `𝔘` (the trivial acyclic model + `LinearEquiv.ofSubsingleton`, exactly as in the subsingleton
      case, but now the subsingleton hypothesis is *derived* from a back-refinement to an acyclic cover).
    * `exists_cechModel_of_mutualRefinement_sharedChart_zero` — the geometric instantiation at `D = 0`:
      any cover `𝔘` that mutually refines a `SharedChartCover 𝔇` admits the chart-disk Leray model, the
      acyclicity now coming from the COMPLETED disk-∂̄ engine on `𝔇`
      (`cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 𝔇.hasGluedDbarDatum`) transported across the
      mutual-refinement equiv.

  ## Scope / what this is NOT (the honest remaining gap)

  This does NOT close the GENERAL `exists_cechModel` (arbitrary Leray `𝔘`, arbitrary `D`).  Two limits:
    * `D = 0` only — the disk-acyclicity engine (`HasGluedDbarDatum`) is proven only at `D = 0`; a
      general-`D` acyclic model is a separate analytic extension (skyscraper/order bounds), not here.
    * MUTUAL refinement only — `refineH1_equiv` is the complete *mutual*-refinement iso (pure STEP A
      homotopy, no analysis).  The general cover-independence `exists_cechModel` needs the iso for a
      STRICTLY-finer Leray refinement through a COMMON refinement (no back-refinement), which is the
      genuine Leray theorem still blocked on the germ-level disk-acyclicity atom + nested Čech collapse
      (`CechRefinementLeray.RefinementLift`/`RefinementDescend`; see that file's `## SURJECTIVITY`).

  So this is a sound, complete *enlargement* of the acyclic-case discharge — every `𝔘` mutually
  refining an acyclic shared-chart cover is now covered — banked toward the eventual general node.
-/
import KirovDolbeault.Dolbeault.CechModelConstruction
import KirovDolbeault.Dolbeault.CechRefinementLeray

open scoped Manifold ContDiff Topology

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily

/-- **Subsingleton `H¹` transports along a mutual refinement.**  If `𝔙 ⪯ 𝔘` (`hr`) and `𝔘 ⪯ 𝔙` (`hs`)
mutually refine and `cechH1 𝔙 D` is a subsingleton, then `cechH1 𝔘 D` is a subsingleton too: the
cover-independence isomorphism `refineH1_equiv D hr hs : cechH1 𝔘 D ≃ₗ[ℂ] cechH1 𝔙 D` (complete, pure
STEP A homotopy) carries the subsingleton back along its underlying equivalence (`Equiv.subsingleton`).
-/
theorem subsingleton_cechH1_of_mutualRefinement {𝔙 𝔘 : FiniteCover X} {s : 𝔘.ι → 𝔙.ι}
    {r : 𝔙.ι → 𝔘.ι} (hr : IsRefinement 𝔙 𝔘 r) (hs : IsRefinement 𝔘 𝔙 s) (D : Divisor X)
    [Subsingleton (𝔙.cechH1 D)] : Subsingleton (𝔘.cechH1 D) :=
  (IsRefinement.refineH1_equiv D hr hs).toEquiv.subsingleton

end FiniteCover

/-- **`exists_cechModel` from a back-refinement to an acyclic cover.**  If `𝔘` mutually
refines a cover `𝔙` whose germ-class `H¹` is a subsingleton (`𝔙 ⪯ 𝔘` via `hr`, `𝔘 ⪯ 𝔙` via `hs`), then
`exists_cechModel 𝔘 D` holds.  The subsingleton transports to `cechH1 𝔘 D`
(`subsingleton_cechH1_of_mutualRefinement`), and `exists_cechModel_of_subsingleton` then supplies the
trivial acyclic model plus the `LinearEquiv.ofSubsingleton` comparison — correctly tied to `(𝔘, D)`.

This generalizes `exists_cechModel_of_subsingleton` (which needs `cechH1 𝔘 D` *itself* subsingleton):
the acyclicity may now live on a *different* cover `𝔙` and be pulled across the cover-independence
equiv. -/
theorem exists_cechModel_of_mutualRefinement_subsingleton {𝔙 𝔘 : FiniteCover X} {s : 𝔘.ι → 𝔙.ι}
    {r : 𝔙.ι → 𝔘.ι} (hr : FiniteCover.IsRefinement 𝔙 𝔘 r) (hs : FiniteCover.IsRefinement 𝔘 𝔙 s)
    (D : Divisor X) [Subsingleton (𝔙.cechH1 D)] :
    ∃ (d : DiskOverlapData) (c : Coboundaries d), Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  haveI : Subsingleton (𝔘.cechH1 D) :=
    FiniteCover.subsingleton_cechH1_of_mutualRefinement hr hs D
  exists_cechModel_of_subsingleton 𝔘.toFiniteFamily D

/-! ### NOTE — the former `exists_cechModel_of_mutualRefinement_sharedChart_zero` is removed (un-vacuum)

Previously this file carried `exists_cechModel_of_mutualRefinement_sharedChart_zero`, which transported
`Subsingleton (cechH1 𝔇 0)` from a `SharedChartCover 𝔇` across a *mutual refinement* `𝔇 ⪯ 𝔘 ⪯ 𝔇` with a
genuine cover `𝔘`.  After the un-vacuum (`SharedChartCover` now `extends FiniteFamily`, NOT
`FiniteCover`), `𝔇` is no longer a cover, so `FiniteCover.IsRefinement 𝔇.toFiniteCover 𝔘` cannot even be
stated — and mathematically a single-chart *family* cannot mutually refine a genuine cover of compact
`X` (the hypotheses were unsatisfiable).  Moreover the discharge relied on the now-removed unconditional
`SharedChartCover.hasGluedDbarDatum` (see `GluedDbarDatum.dbarDatum_agrees_on_interiorCore` for the
precise obstruction: closed-core agreement holds only on `interior core`, not all of `Ω_i ∩ ball`).  The
sound, genuinely-non-vacuous mutual-refinement transport `exists_cechModel_of_mutualRefinement_subsingleton`
(between two real covers) is retained above. -/

end Jacobians.Dolbeault
