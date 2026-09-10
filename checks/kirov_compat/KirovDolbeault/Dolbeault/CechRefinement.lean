/-
  Dolbeault ladder — the Čech **refinement map** between finite covers (cover-comparison scaffold).

  ## Why this file exists (the `exists_cechModel` / `cechH1` cover-independence gap)

  The finiteness node `CechFinitenessWiring.exists_cechModel` must, for an ARBITRARY Leray cover
  `𝔘`, produce a sup-norm Montel model `c` with `𝔘.cechH1 D ≃ₗ[ℂ] c.supH1`.  The committed geometry
  (`CechModelGeometry.chartCoverOverlapData`) builds that model only from `Montel`'s SPECIFIC chart
  cover `chartCover`.  Likewise the Čech↔Dolbeault comparison
  (`DolbeaultComparisonEquiv.comparison_linearEquiv`) is proven only for a SPECIFIC `ChartDiskCover 𝔇`.
  So bridging "model built from a specific cover" to "the arbitrary Leray `𝔘` in the statement"
  requires **`cechH1` to be independent of the (Leray) cover** — equivalently, a chain of refinement
  isomorphisms `cechH1 𝔘 D ≅ cechH1 (common refinement) D ≅ cechH1 chartCover D`.

  Mathlib has **no** Čech-cohomology refinement / nerve / Leray theorem (greenfield; see the recon
  verdict in the steering report).  This file builds the part of that bridge that is *pure restriction
  algebra* and therefore fully complete:

    * `IsRefinement 𝔙 𝔘 r` — `r : 𝔙.ι → 𝔘.ι` is a refinement-index map (`𝔙.U j ≤ 𝔘.U (r j)`).
    * the induced **reindex+restrict** cochain maps `refineC0/refineC1/refineC2 : Cochain^k 𝔘 → 𝔙`
      (germ restriction `rawRestrictG` along `𝔙.U j ≤ 𝔘.U (r j)`, reindexed by `r`);
    * their **commutation with the Čech differentials** `cechDelta0/cechDelta1` (the chain-map
      property — pure `rawRestrictG_comp` bookkeeping);
    * preservation of the `𝒪_D` section subspaces (`sections0/sections1`), the cocycles, and the
      coboundaries; hence the induced **`refineH1 : cechH1 𝔘 D →ₗ[ℂ] cechH1 𝔙 D`**.

  The induced map is genuine reusable progress: the eventual cover-independence proof
  (`cechH1 𝔘 ≅ cechH1 𝔙` for two Leray covers) is exactly the statement that this `refineH1` is a
  bijection, proved by the standard chain-homotopy-between-two-refinement-maps argument.  See the
  `## PLAN` block at the bottom for the precise route and the greenfield gaps.

  No gaps in this file.  Everything not yet closed is written prose in the PLAN block,
  never a gap tactic.
-/
import KirovDolbeault.Dolbeault.CechComplex

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily

/-! ### Refinement of finite covers -/

/-- `r : 𝔙.ι → 𝔘.ι` exhibits `𝔙` as a **refinement** of `𝔘`: each refining set `𝔙.U j` is contained
in the chosen larger set `𝔘.U (r j)`.  This is exactly the data that induces a restriction map of
Čech cochains `Cochain^k 𝔘 → Cochain^k 𝔙` (reindex by `r`, restrict along `𝔙.U j ≤ 𝔘.U (r j)`).
(`𝔙` being a cover is recorded in `𝔙.covers`; the refinement datum only needs the per-index
containment.) -/
def IsRefinement (𝔙 𝔘 : FiniteCover X) (r : 𝔙.ι → 𝔘.ι) : Prop :=
  ∀ j : 𝔙.ι, 𝔙.U j ≤ 𝔘.U (r j)

namespace IsRefinement

variable {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}

/-- On a pairwise overlap, the refining overlap sits inside the reindexed coarse overlap:
`𝔙.U a ⊓ 𝔙.U b ≤ 𝔘.U (r a) ⊓ 𝔘.U (r b)`. -/
theorem pair_le (h : IsRefinement 𝔙 𝔘 r) (a b : 𝔙.ι) :
    𝔙.U a ⊓ 𝔙.U b ≤ 𝔘.U (r a) ⊓ 𝔘.U (r b) :=
  inf_le_inf (h a) (h b)

/-- On a triple overlap, the refining overlap sits inside the reindexed coarse triple overlap. -/
theorem triple_le (h : IsRefinement 𝔙 𝔘 r) (a b c : 𝔙.ι) :
    𝔙.U a ⊓ 𝔙.U b ⊓ 𝔙.U c ≤ 𝔘.U (r a) ⊓ 𝔘.U (r b) ⊓ 𝔘.U (r c) :=
  inf_le_inf (inf_le_inf (h a) (h b)) (h c)

end IsRefinement

/-! ### The reindex+restrict cochain maps `Cochain^k 𝔘 → Cochain^k 𝔙`

For a refinement `r : 𝔙.ι → 𝔘.ι` (`h : IsRefinement 𝔙 𝔘 r`), a `k`-cochain on the coarse cover `𝔘`
restricts to one on the fine cover `𝔙` by: index the fine `k`-simplex `(j₀,…,j_k)`, pull out the
coarse cochain on `(r j₀,…,r j_k)`, and germ-restrict it along the overlap containment.  These are
`ℂ`-linear (`rawRestrictG` is linear; reindexing/`proj` is linear). -/

namespace IsRefinement

variable {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι} (h : IsRefinement 𝔙 𝔘 r)

/-- Refinement on 0-cochains: `(refineC0 c)_j = c_{r j} |_{𝔙.U j}`. -/
noncomputable def refineC0 : 𝔘.Cochain0 →ₗ[ℂ] 𝔙.Cochain0 :=
  LinearMap.pi fun j => rawRestrictG (h j) ∘ₗ LinearMap.proj (r j)

@[simp] theorem refineC0_apply (c : 𝔘.Cochain0) (j : 𝔙.ι) :
    h.refineC0 c j = rawRestrictG (h j) (c (r j)) := by
  simp only [refineC0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- Refinement on 1-cochains: `(refineC1 g)_{ab} = g_{(r a)(r b)} |_{𝔙.U a ⊓ 𝔙.U b}`. -/
noncomputable def refineC1 : 𝔘.Cochain1 →ₗ[ℂ] 𝔙.Cochain1 :=
  LinearMap.pi fun p => rawRestrictG (h.pair_le p.1 p.2) ∘ₗ LinearMap.proj (r p.1, r p.2)

@[simp] theorem refineC1_apply (g : 𝔘.Cochain1) (p : 𝔙.ι × 𝔙.ι) :
    h.refineC1 g p = rawRestrictG (h.pair_le p.1 p.2) (g (r p.1, r p.2)) := by
  simp only [refineC1, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- Refinement on 2-cochains. -/
noncomputable def refineC2 : 𝔘.Cochain2 →ₗ[ℂ] 𝔙.Cochain2 :=
  LinearMap.pi fun t =>
    rawRestrictG (h.triple_le t.1 t.2.1 t.2.2) ∘ₗ LinearMap.proj (r t.1, r t.2.1, r t.2.2)

@[simp] theorem refineC2_apply (g : 𝔘.Cochain2) (t : 𝔙.ι × 𝔙.ι × 𝔙.ι) :
    h.refineC2 g t = rawRestrictG (h.triple_le t.1 t.2.1 t.2.2) (g (r t.1, r t.2.1, r t.2.2)) := by
  simp only [refineC2, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-! ### The chain-map property — refinement commutes with the Čech differential

This is the genuinely reusable algebraic content (the eventual cover-independence proof needs that the
refinement maps are chain maps, so that they descend to cohomology).  Both directions collapse nested
germ restrictions via `rawRestrictG_comp_apply` — `δ⁰` of a restriction equals the restriction of `δ⁰`
on the smaller overlap. -/

/-- **`δ⁰` is natural for refinement.** `δ⁰_𝔙 ∘ refineC0 = refineC1 ∘ δ⁰_𝔘`: refining then taking the
fine coboundary equals taking the coarse coboundary then refining.  Componentwise on `(a,b)` both
sides are `c_{r b}|_{𝔙ab} − c_{r a}|_{𝔙ab}` (nested restrictions collapse). -/
theorem refineC1_comp_cechDelta0 :
    𝔙.cechDelta0 ∘ₗ h.refineC0 = h.refineC1 ∘ₗ 𝔘.cechDelta0 := by
  refine LinearMap.ext fun c => ?_
  funext p
  obtain ⟨a, b⟩ := p
  simp only [LinearMap.comp_apply, cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, refineC0_apply, refineC1_apply, map_sub,
    rawRestrictG_comp_apply]

/-- **`δ¹` is natural for refinement.** `δ¹_𝔙 ∘ refineC1 = refineC2 ∘ δ¹_𝔘`.  Componentwise on the
triple `(a,b,c)` both sides are the alternating sum `g_{(rb)(rc)} − g_{(ra)(rc)} + g_{(ra)(rb)}`,
each germ-restricted to `𝔙.U a ⊓ 𝔙.U b ⊓ 𝔙.U c` (nested restrictions collapse). -/
theorem refineC2_comp_cechDelta1 :
    𝔙.cechDelta1 ∘ₗ h.refineC1 = h.refineC2 ∘ₗ 𝔘.cechDelta1 := by
  refine LinearMap.ext fun g => ?_
  funext t
  obtain ⟨a, b, c⟩ := t
  simp only [LinearMap.comp_apply, cechDelta1, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply, refineC1_apply, refineC2_apply,
    map_sub, map_add, rawRestrictG_comp_apply]

/-! ### Refinement preserves the `𝒪_D` structure (sections, cocycles, coboundaries)

Germ restriction preserves `𝒪_D`-membership (`rawRestrictG_omegaDGerm`), so the reindex+restrict
maps carry `𝒪_D`-sections to `𝒪_D`-sections; together with the chain-map property this gives the
induced map on `cechH1`. -/

variable (D : Divisor X)

/-- Refinement maps `𝒪_D` 0-sections to `𝒪_D` 0-sections. -/
theorem refineC0_mem_sections0 {c : 𝔘.Cochain0} (hc : c ∈ 𝔘.sections0 D) :
    h.refineC0 c ∈ 𝔙.sections0 D := fun j => by
  rw [h.refineC0_apply]; exact rawRestrictG_omegaDGerm (h j) (hc (r j))

/-- Refinement maps `𝒪_D` 1-sections to `𝒪_D` 1-sections. -/
theorem refineC1_mem_sections1 {g : 𝔘.Cochain1} (hg : g ∈ 𝔘.sections1 D) :
    h.refineC1 g ∈ 𝔙.sections1 D := fun p => by
  rw [h.refineC1_apply]; exact rawRestrictG_omegaDGerm (h.pair_le p.1 p.2) (hg (r p.1, r p.2))

/-- Refinement maps `𝒪_D` 1-cocycles to `𝒪_D` 1-cocycles (`refineC1` sends `ker δ¹_𝔘` into
`ker δ¹_𝔙` by the chain-map property, and preserves the `𝒪_D` sections). -/
theorem refineC1_mem_cocycles1 {g : 𝔘.Cochain1} (hg : g ∈ 𝔘.cocycles1 D) :
    h.refineC1 g ∈ 𝔙.cocycles1 D := by
  obtain ⟨hker, hsec⟩ := hg
  refine ⟨?_, h.refineC1_mem_sections1 D hsec⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hker ⊢
  rw [← LinearMap.comp_apply, h.refineC2_comp_cechDelta1, LinearMap.comp_apply, hker, map_zero]

/-- Refinement maps `𝒪_D` 1-coboundaries to `𝒪_D` 1-coboundaries (a coboundary `δ⁰_𝔘 c` with `c` an
`𝒪_D` 0-section refines to `δ⁰_𝔙 (refineC0 c)` via the chain-map property, with `refineC0 c` again an
`𝒪_D` 0-section). -/
theorem refineC1_mem_coboundaries1 {g : 𝔘.Cochain1} (hg : g ∈ 𝔘.coboundaries1 D) :
    h.refineC1 g ∈ 𝔙.coboundaries1 D := by
  obtain ⟨c, hc, rfl⟩ := hg
  refine ⟨h.refineC0 c, h.refineC0_mem_sections0 D hc, ?_⟩
  rw [← LinearMap.comp_apply, h.refineC1_comp_cechDelta0, LinearMap.comp_apply]

/-! ### The induced map on `cechH1`

The cocycle-level reindex+restrict map (`refineC1` restricted to cocycles) carries coboundaries to
coboundaries, so it descends to the `H¹ = Z¹/B¹` quotients (`Submodule.mapQ`).  This is the comparison
arrow `cechH1 𝔘 → cechH1 𝔙` that the eventual cover-independence proof shows is an isomorphism for two
Leray covers (see the PLAN block). -/

/-- The **cocycle-level refinement map** `Z¹(𝔘, 𝒪_D) →ₗ[ℂ] Z¹(𝔙, 𝒪_D)`: `refineC1` corestricted to
the cocycle subspaces (using `refineC1_mem_cocycles1`). -/
noncomputable def refineZ1 :
    ↥(𝔘.cocycles1 D) →ₗ[ℂ] ↥(𝔙.cocycles1 D) :=
  (h.refineC1.domRestrict (𝔘.cocycles1 D)).codRestrict (𝔙.cocycles1 D)
    fun g => h.refineC1_mem_cocycles1 D g.2

@[simp] theorem refineZ1_coe (g : ↥(𝔘.cocycles1 D)) :
    (h.refineZ1 D g : 𝔙.Cochain1) = h.refineC1 (g : 𝔘.Cochain1) := rfl

/-- **The induced map on Čech `H¹`** `cechH1 𝔘 D →ₗ[ℂ] cechH1 𝔙 D` (`refineH1`).  The cocycle-level
refinement `refineZ1` sends `𝒪_D`-coboundaries on `𝔘` to `𝒪_D`-coboundaries on `𝔙`
(`refineC1_mem_coboundaries1`), so it descends to the `H¹ = Z¹/B¹` quotients (`Submodule.mapQ`).  This
is the comparison arrow the eventual Leray cover-independence isomorphism is built on — the standard
chain-homotopy argument shows it is a bijection when both covers are Leray (PLAN block below). -/
noncomputable def refineH1 : 𝔘.cechH1 D →ₗ[ℂ] 𝔙.cechH1 D := by
  refine Submodule.mapQ _ _ (h.refineZ1 D) ?_
  rintro ⟨g, _⟩ hcob
  -- `hcob : g ∈ coboundaries1 𝔘 D`; need `refineC1 g ∈ coboundaries1 𝔙 D`.
  exact h.refineC1_mem_coboundaries1 D hcob

@[simp] theorem refineH1_mk (g : ↥(𝔘.cocycles1 D)) :
    h.refineH1 D (Submodule.Quotient.mk g) = Submodule.Quotient.mk (h.refineZ1 D g) :=
  rfl

end IsRefinement

/-! ### Functoriality of refinement (identity + composition)

The eventual cover-independence isomorphism is the statement that, for two Leray covers with mutual
refinement maps, the two composites are the identity on `H¹`.  Proving "is the identity" needs the
identity-refinement and composition laws.  These are pure restriction algebra (`rawRestrictG_comp`)
and complete. -/

namespace IsRefinement

variable {𝔚 𝔙 𝔘 : FiniteCover X}

/-- The identity is a refinement of a cover by itself (`𝔘.U i ≤ 𝔘.U (id i)`). -/
theorem id (𝔘 : FiniteCover X) : IsRefinement 𝔘 𝔘 id := fun _ => le_rfl

/-- A composite of refinement-index maps `s : 𝔚.ι → 𝔙.ι`, `r : 𝔙.ι → 𝔘.ι` is a refinement-index map
`𝔚 → 𝔘` via `r ∘ s`. -/
theorem comp {s : 𝔚.ι → 𝔙.ι} {r : 𝔙.ι → 𝔘.ι}
    (hs : IsRefinement 𝔚 𝔙 s) (hr : IsRefinement 𝔙 𝔘 r) :
    IsRefinement 𝔚 𝔘 (r ∘ s) :=
  fun k => (hs k).trans (hr (s k))

/-- **Refinement on 1-cochains is functorial.** Refining `𝔚 → 𝔘` directly (via `r ∘ s`) equals
refining `𝔘 → 𝔙` then `𝔙 → 𝔚` (nested germ restrictions collapse, `rawRestrictG_comp_apply`).  This
composition law is what the eventual cover-independence argument uses to compare the two composites of
a pair of mutual refinement maps. -/
theorem refineC1_comp {s : 𝔚.ι → 𝔙.ι} {r : 𝔙.ι → 𝔘.ι}
    (hs : IsRefinement 𝔚 𝔙 s) (hr : IsRefinement 𝔙 𝔘 r) :
    (hs.comp hr).refineC1 = hs.refineC1 ∘ₗ hr.refineC1 := by
  refine LinearMap.ext fun g => ?_
  funext p
  obtain ⟨a, b⟩ := p
  simp only [LinearMap.comp_apply, refineC1_apply, Function.comp_apply, rawRestrictG_comp_apply]
  rfl

/-- **Refinement on 0-cochains is functorial** (the degree-0 analogue of `refineC1_comp`). -/
theorem refineC0_comp {s : 𝔚.ι → 𝔙.ι} {r : 𝔙.ι → 𝔘.ι}
    (hs : IsRefinement 𝔚 𝔙 s) (hr : IsRefinement 𝔙 𝔘 r) :
    (hs.comp hr).refineC0 = hs.refineC0 ∘ₗ hr.refineC0 := by
  refine LinearMap.ext fun c => ?_
  funext k
  simp only [LinearMap.comp_apply, refineC0_apply, Function.comp_apply, rawRestrictG_comp_apply]
  rfl

end IsRefinement

end FiniteCover

/-! ## PLAN — `cechH1` Leray cover-independence (the greenfield route)

What is BUILT here (complete, axiom-clean): for any refinement `r : 𝔙.ι → 𝔘.ι`
(`IsRefinement 𝔙 𝔘 r`), the reindex+restrict chain map `refineC0/refineC1/refineC2`, its commutation
with `cechDelta0/cechDelta1` (`refineC1_comp_cechDelta0`, `refineC2_comp_cechDelta1`), preservation of
`sections/cocycles/coboundaries`, the induced `refineH1 : cechH1 𝔘 D →ₗ[ℂ] cechH1 𝔙 D`, and
functoriality (`comp`, `refineC0_comp`, `refineC1_comp`).

What remains (the greenfield gaps — written here, NOT as gap tactics):

GOAL.  For two Leray covers `𝔘, 𝔙` of the compact Riemann surface `X`, `refineH1` is a `ℂ`-linear
ISOMORPHISM, so `cechH1 𝔘 D ≃ₗ[ℂ] cechH1 𝔙 D`.  (Then `exists_cechModel` for an arbitrary Leray `𝔘`
is obtained by chaining: `cechH1 𝔘 D ≅ cechH1 𝔚 D ≅ cechH1 chartCover D ≅ supH1`, where `𝔚` is a
common refinement and the last `≅` is the committed `CechModelGeometry` model.)

STANDARD PROOF (Forster §12-13 / Leray, the chain-homotopy-free route — actually the *two-refinement-
maps + chain homotopy* route, which avoids spectral sequences):

STEP A — homotopy-independence of the refinement map.  Two different index maps `r, r' : 𝔙.ι → 𝔘.ι`
(both refinements) induce the SAME map on `H¹`.  Proof: build an explicit cochain homotopy
`k : Cochain1 𝔘 → Cochain0 𝔙` with `refineC1 r − refineC1 r' = cechDelta0_𝔙 ∘ k + k' ∘ cechDelta1_𝔘`
(the usual prism/alternating-sum operator, e.g. `(k g)_j = g_{(r j)(r' j)} |_{𝔙.U j}`).  This is PURE
restriction algebra and is the natural next complete increment in THIS file (it needs only
`rawRestrictG_comp` and `δ`-bookkeeping; the only subtlety is that `g_{(r j)(r' j)}` is defined on
`𝔘.U (r j) ⊓ 𝔘.U (r' j)`, which contains `𝔙.U j` since both `r,r'` are refinements — so the
restriction is well-typed).  ⇒ `refineH1` depends only on the PAIR `(𝔙, 𝔘)`, not on `r`.

STEP B — `refineH1` is an iso when `𝔙 ⪯ 𝔘` are BOTH Leray and `𝔙` refines `𝔘`.  Here is the ONE
genuinely-analytic gap.  Two equivalent formulations:
  (B1) Direct (Leray ⟹ refinement-iso): because every overlap of a Leray cover is `H¹`-acyclic
       (`H¹(U_{i₀…i_k}, 𝒪) = 0`), the Čech-to-Čech refinement is a quasi-isomorphism.  In Forster
       this is Lemma 12.8 / Thm 12.9 (Leray's theorem): the double complex `Č^•(𝔙, Č^•(𝔘, 𝒪))` has
       both filtrations degenerating, giving `H¹(𝔙) ≅ H¹(total) ≅ H¹(𝔘)`.
  (B2) Avoid the double complex: prove that BOTH Leray covers compute the same SHEAF cohomology
       `H¹(X, 𝒪_D)` and that `refineH1` is compatible with the comparison maps `Ȟ¹(𝔘) → H¹(X)`,
       `Ȟ¹(𝔙) → H¹(X)`; the comparison maps are isos for Leray covers (Forster Thm 12.9), so
       `refineH1` is too.

REPO-AVAILABLE PIECES for STEP B:
  * the overlap-acyclicity input.  On a Leray cover the relevant `H¹(overlap, 𝒪) = 0` is exactly the
    disk-`H¹=0` engine already proven: `DbarDiskCohomology.dbar_solvable_ball` /
    `dbar_holo_splitting_ball` (full-disk ∂̄-solvability) — the SAME atom `exists_cechModel`'s `leray`
    field consumes.  The `IsLeray` predicate (`CechComplex.FiniteFamily.IsLeray`) bundles
    simple-connectedness of the cover sets + connectedness of pairwise overlaps, the Forster §12
    hypothesis.
  * the chain-map + descent machinery: this file (`refineH1` + the chain-map lemmas) and the
    `Submodule.mapQ`/quotient API.
  * STEP A's homotopy: constructible here (see above).

GREENFIELD GAPS (absent from Mathlib — confirmed by recon; the real work for STEP B):
  * No Čech double complex / Leray spectral sequence, and no "acyclic cover ⟹ Čech = derived"
    theorem.  `CategoryTheory.Sites.SheafCohomology.Cech.cechComplexFunctor` is the abstract
    cosimplicial/Ext Čech complex with NO refinement comparison and NO acyclicity theorem;
    `MayerVietoris` is only the 2-set LES; `ShrinkingLemma.PartialRefinement` / `precise_refinement`
    are SET-level cover refinement with no cohomology.  So STEP B must be built by hand.
  * Cheapest hand-built route (recommended): the explicit "refinement-of-a-refinement" zig-zag for a
    cover and a relatively-compact shrinking of itself, using disk-acyclicity to lift a `𝔙`-cocycle to
    a `𝔘`-cocycle modulo coboundary (the surjectivity half) and STEP A's homotopy for injectivity —
    i.e. the same shape as `CechFinitenessWiring.Coboundaries.leray`, but stated as an iso of the two
    germ-class `cechH1`s rather than a sup-norm surjectivity.  Estimated ~several hundred LoC, all on
    top of the proven disk atom; no further analysis beyond `dbar_solvable_ball`.

SIDESTEP ASSESSMENT (is refinement REQUIRED, or can the model be built from `𝔘` directly?).
  Examined every consumer of `cechH1` / `finiteDimensional_cechH1`:
    * `CohomologicalRR` (`cohomological_riemannRoch`, `chi_*`, `exists_skyscraperLES`),
      `DolbeaultLadder` (`arithmeticGenus_eq_genus`, `serre_h1_eq`, `riemannRoch_equality_of_ladder`),
      and `SkyscraperSnake` all take an ARBITRARY `𝔘 : FiniteCover X` with `hL : 𝔘.IsLeray` — they do
      NOT receive a `ChartDiskCover` or `Montel.chartCover`.
    * conversely `CechModelGeometry.chartCoverOverlapData` (the model geometry) and
      `DolbeaultComparisonEquiv.comparison_linearEquiv` (the Dolbeault↔Čech iso) are proven ONLY for
      the specific `chartCover` / a specific `ChartDiskCover 𝔇`.
  Hence the model is built from a specific cover while the statement quantifies over an arbitrary
  Leray cover, and there is NO `exists_chartDiskCover` / Leray-cover-existence lemma wiring them.
  ⇒ Cover-independence (this `refineH1` being an iso) is GENUINELY REQUIRED to discharge
  `exists_cechModel` as stated; it cannot be sidestepped by "build the model from `𝔘` directly",
  because `𝔘` is an arbitrary Leray cover with no chart-disk structure, whereas the disk-acyclicity
  model construction fundamentally needs chart-disk sets (`ChartDiskCover.isDisk`, so `∂̄` is solvable
  on each whole cover set via the planar disk solve).
  PARTIAL SIDESTEP (a cheaper restatement, if acceptable):  one could instead RESTATE the downstream
  ladder leaves to quantify over a `ChartDiskCover` (or to take the existence of a single Leray
  chart-disk cover as a hypothesis), since RR's headline `exists_riemannRoch_divisor` only needs SOME
  cover.  That removes the *arbitrary*-`𝔘` cover-independence obligation but still requires
  `cechH1 chartDiskCover 0 ≅ DolbeaultH01` (have it) and the model on that one cover — i.e. it trades
  full cover-independence for "one good cover exists", which is the lighter obligation.  Whether to
  take that restatement is a Lean-architecture decision for the owner (the soundness-audit memo flags
  the free-cover leaves already).  Either way `refineH1` + STEP A are reusable.
-/

end Jacobians.Dolbeault
