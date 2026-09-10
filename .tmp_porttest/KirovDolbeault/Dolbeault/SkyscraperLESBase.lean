/-
  Dolbeault ladder — the **base layer** of the skyscraper long exact sequence.

  This small file holds exactly the order-bookkeeping arrows and the `SkyscraperLES` structure that
  BOTH directions of the skyscraper construction need:

  * the consumer side — `CohomologicalRR`'s χ-induction (`chi_jump_of_LES`, `cohomological_riemannRoch`)
    runs the six-term alternating-sum crank on a `SkyscraperLES`;
  * the producer side — the downstream snake/realization assembly (`SkyscraperArrow` →
    `SkyscraperSnake` → `SkyscraperAssembly` → `CohomologicalRRChartDisk`) BUILDS a `SkyscraperLES`,
    and references `Skyscraper`/`h0Incl`/`h1Map`.

  Putting `SkyscraperLES` (+ `h0Incl`, `Skyscraper`, `h1Map`, and the degreewise order-weakening
  inclusions) here breaks the import cycle that previously forced `exists_skyscraperLES` to be a bare
  an unproved obligation in `CohomologicalRR` disconnected from the proven assembly: now `CohomologicalRR` can sit
  *downstream* of the assembly and discharge `exists_skyscraperLES` from a `LocalRealizationData`
  (the single genuine local-realization + acyclicity obligation). Same cycle-break pattern as the
  `exists_cechModel` refactor.

  Everything here is pure order/quotient bookkeeping (no analytic content), complete and axiom-clean.
-/
import KirovDolbeault.Dolbeault.CechH0

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Classical

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily

/-! ### Structural inclusion `𝒪_D ↪ 𝒪_{D+P}` (provable, no analytic content)

Adding the effective point divisor `P` only *weakens* the order bound (`D ≤ D + P` pointwise), so a
section of `𝒪_D` is a section of `𝒪_{D+P}`; this gives a degreewise inclusion of the section
submodules and hence of the global-section and cochain spaces. These facts are pure order
bookkeeping — the genuinely-hard analytic/homological data (skyscraper quotient, connecting map) is
isolated separately in `SkyscraperLES`. -/

/-- Pointwise monotonicity of the divisor under adding an effective point: `D x ≤ (D + P) x`. -/
theorem divisor_le_add_single (D : Divisor X) (P x : X) :
    (D : Divisor X) x ≤ (D + Finsupp.single P 1 : Divisor X) x := by
  rw [Finsupp.add_apply, Finsupp.single_apply]; split <;> omega

/-- The order bound for `𝒪_D` implies that for `𝒪_{D+P}` (the bound `−(D+P) ≤ −D` weakens). -/
theorem mem_OmegaD_add_single {D : Divisor X} {P : X} {U : Opens X} {f : U → ℂ}
    (hf : f ∈ OmegaD D U) : f ∈ OmegaD (D + Finsupp.single P 1) U := by
  refine ⟨hf.1, fun u => le_trans ?_ (hf.2 u)⟩
  exact_mod_cast neg_le_neg (divisor_le_add_single D P u.1)

/-- Germ-class sections inherit the inclusion `𝒪_D(U) ⊆ 𝒪_{D+P}(U)`. -/
theorem OmegaDGerm_le_add_single (D : Divisor X) (P : X) (U : Opens X) :
    OmegaDGerm D U ≤ OmegaDGerm (D + Finsupp.single P 1) U := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, mem_OmegaD_add_single hg, rfl⟩

/-- The `𝒪_D` 0-sections are contained in the `𝒪_{D+P}` 0-sections. -/
theorem sections0_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.sections0 D ≤ 𝔘.sections0 (D + Finsupp.single P 1) :=
  fun _ hf i => OmegaDGerm_le_add_single D P (𝔘.U i) (hf i)

/-- The global `𝒪_D`-sections are contained in the global `𝒪_{D+P}`-sections (same `ker δ⁰`, weaker
sheaf condition). This is the underlying map of the long-exact-sequence arrow `H⁰(D) → H⁰(D+P)`. -/
theorem globalSections_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.globalSections D ≤ 𝔘.globalSections (D + Finsupp.single P 1) :=
  inf_le_inf_left _ (𝔘.sections0_le_add_single D P)

/-! ### The skyscraper space and the `H⁰`-inclusion arrow (provable, no analytic content) -/

/-- The canonical H⁰-inclusion `H⁰(𝒪_D) ↪ H⁰(𝒪_{D+P})` (the order bound weakens, `f₁` of the LES). -/
noncomputable def h0Incl (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    ↥(𝔘.globalSections D) →ₗ[ℂ] ↥(𝔘.globalSections (D + Finsupp.single P 1)) :=
  Submodule.inclusion (𝔘.globalSections_le_add_single D P)

theorem h0Incl_injective (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    Function.Injective (𝔘.h0Incl D P) :=
  Submodule.inclusion_injective _

/-- The **skyscraper space** `ℂ_P` at `P`: the genuine **1-dimensional** stalk of the skyscraper
sheaf `𝒪_{D+P}/𝒪_D` (the order-`(−D(P)−1)` principal-part coefficient at `P`), realised as `ℂ`.

NOTE (soundness fix, 2026-06-02): the *previous* definition `H⁰(𝒪_{D+P}) ⧸ range f₁` (the H⁰-cokernel)
was WRONG — at a base point of `|D+P|` the cokernel is `0`-dimensional, so the `skyDim : finrank = 1`
field made `exists_skyscraperLES` **provably false**. The genuine middle term of the cohomology LES of
`0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` is `H⁰(X, ℂ_P) = ℂ` (always 1-dim); the coefficient arrow
`f₂ : H⁰(𝒪_{D+P}) → ℂ_P` is **not** surjective in general (its image *is* the cokernel), so it now
lives — together with the exactness `range f₁ = ker f₂` — as honest data in `SkyscraperLES`. -/
abbrev Skyscraper (_𝔘 : FiniteCover X) (_D : Divisor X) (_P : X) : Type := ℂ

/-! ### The inclusion-induced arrow `f₄ : H¹(𝒪_D) → H¹(𝒪_{D+P})` (provable, no analytic content) -/

/-- The `𝒪_D` 1-sections are contained in the `𝒪_{D+P}` 1-sections (order weakening). -/
theorem sections1_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.sections1 D ≤ 𝔘.sections1 (D + Finsupp.single P 1) :=
  fun _ hf p => OmegaDGerm_le_add_single D P _ (hf p)

/-- The `𝒪_D` 1-cocycles are contained in the `𝒪_{D+P}` 1-cocycles (same `ker δ¹`, weaker sheaf). -/
theorem cocycles1_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.cocycles1 D ≤ 𝔘.cocycles1 (D + Finsupp.single P 1) :=
  inf_le_inf_left _ (𝔘.sections1_le_add_single D P)

/-- The `𝒪_D` 1-coboundaries are contained in the `𝒪_{D+P}` 1-coboundaries (`δ⁰` of more sections). -/
theorem coboundaries1_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.coboundaries1 D ≤ 𝔘.coboundaries1 (D + Finsupp.single P 1) :=
  Submodule.map_mono (𝔘.sections0_le_add_single D P)

/-- The 1-cocycle inclusion `Z¹(𝒪_D) ↪ Z¹(𝒪_{D+P})`. -/
noncomputable def cocyclesIncl (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    ↥(𝔘.cocycles1 D) →ₗ[ℂ] ↥(𝔘.cocycles1 (D + Finsupp.single P 1)) :=
  Submodule.inclusion (𝔘.cocycles1_le_add_single D P)

/-- **The inclusion-induced arrow `f₄ : H¹(𝒪_D) → H¹(𝒪_{D+P})`** (PROVEN). The cocycle inclusion
sends `𝒪_D`-coboundaries to `𝒪_{D+P}`-coboundaries, so it descends to the `H¹` quotients
(`Submodule.mapQ`). -/
noncomputable def h1Map (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.cechH1 D →ₗ[ℂ] 𝔘.cechH1 (D + Finsupp.single P 1) := by
  refine Submodule.mapQ _ _ (𝔘.cocyclesIncl D P) ?_
  rintro ⟨c, _⟩ hcob
  exact 𝔘.coboundaries1_le_add_single D P hcob

/-! ### Subcomplex backbone facts (complete; the algebraic skeleton of the skyscraper snake lemma) -/

/-- **`δ⁰` preserves the sections subcomplex.** The Čech coboundary of `𝒪_D`-0-sections is an
`𝒪_D`-1-section: each component `(δ⁰f)_{ij} = f_j|_{ij} − f_i|_{ij}` is a difference of restrictions of
`𝒪_D`-germs, hence an `𝒪_D`-germ on the overlap (`rawRestrictG_omegaDGerm`). Equivalently
`B¹(𝒪_D) ⊆ C¹(𝒪_D)`. -/
theorem cechDelta0_sections (𝔘 : FiniteCover X) (D : Divisor X) :
    Submodule.map 𝔘.cechDelta0 (𝔘.sections0 D) ≤ 𝔘.sections1 D := by
  rintro _ ⟨f, hf, rfl⟩ p
  simp only [cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  exact sub_mem (rawRestrictG_omegaDGerm inf_le_right (hf p.2))
    (rawRestrictG_omegaDGerm inf_le_left (hf p.1))

/-- **`B¹ ⊆ Z¹`** (coboundaries are cocycles). A `1`-coboundary `δ⁰f` lies in `ker δ¹` (since
`δ¹ ∘ δ⁰ = 0`, `cechDelta1_comp_cechDelta0`) and is an `𝒪_D`-`1`-section (`cechDelta0_sections`), so it
is an `𝒪_D` `1`-cocycle. This is the containment that makes `H¹ = Z¹/B¹` (`cechH1`) the genuine
cohomology, and that lets the snake-lemma connecting map land a lifted coboundary in `Z¹(𝒪_D)`. -/
theorem coboundaries1_le_cocycles1 (𝔘 : FiniteCover X) (D : Divisor X) :
    𝔘.coboundaries1 D ≤ 𝔘.cocycles1 D := by
  rw [coboundaries1, cocycles1, le_inf_iff]
  refine ⟨?_, 𝔘.cechDelta0_sections D⟩
  rw [Submodule.map_le_iff_le_comap]
  intro f _
  rw [Submodule.mem_comap, LinearMap.mem_ker, ← LinearMap.comp_apply, cechDelta1_comp_cechDelta0,
    LinearMap.zero_apply]

/-! ### The skyscraper long exact sequence structure (the genuine homological/analytic kernel)

The single-point χ-jump comes from the **skyscraper short exact sequence** of `𝒪_D`-modules
`0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` (`ℂ_P` = the 1-dimensional skyscraper at `P`). Its **long exact
sequence** in Čech cohomology is
`0 → H⁰(𝒪_D) →[f₁] H⁰(𝒪_{D+P}) →[f₂] ℂ_P →[f₃] H¹(𝒪_D) →[f₄] H¹(𝒪_{D+P}) → 0`,
the skyscraper having `H^{≥1} = 0`.

`SkyscraperLES` bundles the data NOT already proven above. The first arrow `f₁` (`h0Incl`) and the last
arrow `f₄` (`h1Map`, the inclusion-induced map) are PROVEN; the inclusion `f₁` is injective
(`h0Incl_injective`). The genuinely-hard content isolated here is the coefficient arrow `f₂ = h0ToSky`
with `exact₁₂`, the snake-lemma connecting map `f₃` with exactness (`exact₂`, `exact₃`, `surj₄`), and
finiteness of the cohomology groups (Forster 14.9). -/
structure SkyscraperLES (𝔘 : FiniteCover X) (D : Divisor X) (P : X) where
  /-- **The skyscraper coefficient arrow** `f₂ : H⁰(𝒪_{D+P}) → ℂ_P` — the order-`(−D(P)−1)`
  principal-part coefficient at `P`. **Not** surjective in general (its image is the H⁰-cokernel,
  which is `0` exactly when `P` is a base point of `|D+P|`). -/
  h0ToSky : ↥(𝔘.globalSections (D + Finsupp.single P 1)) →ₗ[ℂ] 𝔘.Skyscraper D P
  /-- Exactness at `H⁰(𝒪_{D+P})`: `range f₁ = ker f₂` — a section lies in `𝒪_D` iff its
  order-`(−D(P)−1)` coefficient vanishes. -/
  exact₁₂ : Function.Exact (𝔘.h0Incl D P) h0ToSky
  /-- The connecting homomorphism `ℂ_P → H¹(𝒪_D)` (snake lemma of the SES of cochain complexes). -/
  f₃ : 𝔘.Skyscraper D P →ₗ[ℂ] 𝔘.cechH1 D
  /-- Exactness at `ℂ_P`: `range f₂ = ker f₃`. (Snake lemma.) -/
  exact₂ : Function.Exact h0ToSky f₃
  /-- Exactness at `H¹(𝒪_D)`: `range f₃ = ker f₄` (with `f₄ = h1Map`). (Snake lemma.) -/
  exact₃ : Function.Exact f₃ (𝔘.h1Map D P)
  /-- The last arrow `f₄ = h1Map : H¹(𝒪_D) → H¹(𝒪_{D+P})` is surjective (the skyscraper has
  `H^{≥1} = 0`, so the LES terminates with `→ 0`). -/
  surj₄ : Function.Surjective (𝔘.h1Map D P)
  /-- `H¹(𝒪_D)` is finite-dimensional (Forster 14.9; `finiteDimensional_cechH1`). -/
  [finH1D : FiniteDimensional ℂ (𝔘.cechH1 D)]
  /-- `H¹(𝒪_{D+P})` is finite-dimensional (Forster 14.9; `finiteDimensional_cechH1`). -/
  [finH1DP : FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1))]
  /-- `H⁰(𝒪_{D+P})` is finite-dimensional (Forster compactness `l(D+P) < ∞`). Now an *instance*
  globally (`CohomologicalH0Finiteness.finiteDimensional_globalSections`, Gap 1), so a `SkyscraperLES`
  carries no genuine finiteness obligation here; kept as a field so the structure is self-contained.
  `H⁰(𝒪_D)` finiteness is *derived* (it injects into this one, `h0Incl_injective`). -/
  [finH0DP : FiniteDimensional ℂ ↥(𝔘.globalSections (D + Finsupp.single P 1))]

attribute [instance] SkyscraperLES.finH1D SkyscraperLES.finH1DP SkyscraperLES.finH0DP

/-- `H⁰(𝒪_D)` is finite-dimensional, *derived* from `H⁰(𝒪_{D+P})` finiteness via the injective
inclusion `h0Incl` (`FiniteDimensional.of_injective`). Not assumed. -/
instance (priority := 100) SkyscraperLES.finH0D {𝔘 : FiniteCover X} {D : Divisor X} {P : X}
    (S : SkyscraperLES 𝔘 D P) : FiniteDimensional ℂ ↥(𝔘.globalSections D) :=
  haveI := S.finH0DP
  FiniteDimensional.of_injective (𝔘.h0Incl D P) (𝔘.h0Incl_injective D P)

end FiniteCover

end Jacobians.Dolbeault
