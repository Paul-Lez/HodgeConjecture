/-
  Dolbeault ladder — the skyscraper long exact sequence on a chart-disk-adapted cover (the
  *discharged* form of `CohomologicalRR.exists_skyscraperLES`).

  ## What this file banks (the chart-disk case, axiom-clean)

  `CohomologicalRR.exists_skyscraperLES 𝔘 hL D P` is left as a single honest named obligation upstream because
  it is stated for an arbitrary *Leray* cover, and the genuine skyscraper assembly
  (`SkyscraperAssembly.skyscraperLES_of_chartDisk`) needs *geometric* hypotheses that a generic Leray
  cover does not satisfy (a chart-disk cover-set `∋ P` whose chart source is the whole set, `D`
  supported on it only at `P`, and a singleton star at `P`).  That assembly lives **downstream** of
  `CohomologicalRR` (it uses the `SkyscraperLES` structure and the `h0Incl`/`Skyscraper`/`h1Map`
  arrows), so it cannot be threaded back into `exists_skyscraperLES` without an import cycle.

  This file is that downstream wiring.  It supplies the skyscraper LES **from the explicit chart-disk
  hypotheses**, with the two finiteness inputs now fully discharged:

    * `H¹(𝒪_D)`, `H¹(𝒪_{D+P})` finiteness — `finiteDimensional_cechH1_general`
      (Forster §16 skyscraper reduction; now axiom-clean, the stale `SkyscraperAssembly` comment
      predates that);
    * `H⁰(𝒪_{D+P})` finiteness — the new `CohomologicalH0Finiteness.finiteDimensional_globalSections`
      *instance* (Gap 1; Forster compactness), so no instance hypothesis is needed any more.

  The deliverable

      `exists_skyscraperLES_of_chartDisk` :
        chart-disk hypotheses on `(𝔘, D, P)` ⟹ `Nonempty (SkyscraperLES 𝔘 D P)`

  is fully PROVEN and **axiom-clean** `[propext, Classical.choice, Quot.sound]`.  It is exactly
  `CohomologicalRR.exists_skyscraperLES` with its genuine geometric prerequisites made explicit.

  ## The remaining gap to the GENERAL `exists_skyscraperLES` (the honest diagnosis)

  ⚠ The `hstar` (singleton-star) hypothesis here — `P ∈ U j → j = i` — **cannot hold at every point**
  on a finite cover of a *compact connected* `X` (it would force the cover sets pairwise disjoint,
  disconnecting `X`, or be the single set `U = X`, impossible for a chart-disk cover of compact `X`).
  Since the χ-induction needs the LES for *every* support point `P`, and overlap points always exist,
  **this banked chart-disk LES is unconsumable as-is** — it does NOT discharge `exists_skyscraperLES`
  on `chartDiskCover` (or any fixed cover).  The earlier framing ("a standard but unbuilt adapted
  singleton-star shrinking") asked for a cover that does not exist; see the corrected diagnosis on
  `CohomologicalRR.exists_skyscraperLES`.

  Closing the unconditional `exists_skyscraperLES` therefore needs **one of**:
    (A) a *multi-vertex / full-simplex-star* skyscraper LES on the chart-disk cover for GENERAL `(D, P)`
        — replacing all three of `hWsrc`/`hDsupp`/`hstar`.  Its keystone missing primitive is the
        general-`D` local realization (Mittag–Leffler on a disk): `coeffGermLin` surjective via the
        explicit *product* witness in the cover-set's CENTER chart,
        `a·(z−φP)^{−(D P)−1}·∏_{Q∈ supp D∩U i, Q≠P}(z−φQ)^{−(D Q)}` (forced poles/zeros at the other
        support points; `meromorphicOrderAt_prod` for the orders), coupled with the full-simplex
        cochain cone-contraction for `H¹(Q) = 0`;
    (B) `h¹` cover-independence among Leray covers (the strictly-finer `refineH1` surjectivity,
        `CechRefinementLeray`'s `## SURJECTIVITY`, NOT the global `IsDiskAcyclic`), to switch to a
        `P`-adapted cover per jump.

  Both are genuine, currently-unbanked, substantial work, so the general `exists_skyscraperLES` stays
  the single honest named obligation.  This file's chart-disk LES removes the *snake / exactness / finiteness*
  content from that obligation but, because of the unsatisfiable `hstar`, does not itself wire to the
  headline.
-/
import KirovDolbeault.Dolbeault.SkyscraperAssembly
import KirovDolbeault.Dolbeault.CohomologicalH0Finiteness

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily

/-- **The skyscraper long exact sequence from the explicit chart-disk hypotheses — fully PROVEN,
axiom-clean.**  Given a cover-set `U i ∋ P` whose `↥(U i)`-chart source covers all of `U i`
(`hWsrc`), with `D` supported on `U i` only at `P` (`hDsupp`) and a singleton star at `P`
(`hstar`), the skyscraper LES `SkyscraperLES 𝔘 D P` exists.

This is `CohomologicalRR.exists_skyscraperLES` with its genuine geometric prerequisites made explicit:
it runs `SkyscraperAssembly.skyscraperLES_of_chartDisk` (the snake/connecting map, exactness,
surjectivity, `H⁰(Q) ≅ ℂ`, `H¹(Q) = 0`).  The two finiteness inputs are now discharged with **no**
hypothesis: `H¹` by `finiteDimensional_cechH1_general` (axiom-clean) and `H⁰(𝒪_{D+P})` by the
`finiteDimensional_globalSections` instance (Gap 1). -/
theorem exists_skyscraperLES_of_chartDisk (𝔘 : FiniteCover X) (D : Divisor X) (P : X) {i : 𝔘.ι}
    (hP : P ∈ 𝔘.U i)
    (hWsrc : ∀ Q : 𝔘.U i, Q ∈ (chartAt (H := ℂ) (⟨P, hP⟩ : 𝔘.U i)).source)
    (hDsupp : ∀ Q : 𝔘.U i, Q ≠ ⟨P, hP⟩ → D Q.1 = 0)
    (hstar : ∀ j, P ∈ 𝔘.U j → j = i) :
    Nonempty (SkyscraperLES 𝔘 D P) :=
  ⟨𝔘.skyscraperLES_of_chartDisk D P hP hWsrc hDsupp hstar⟩

end FiniteCover

end Jacobians.Dolbeault
