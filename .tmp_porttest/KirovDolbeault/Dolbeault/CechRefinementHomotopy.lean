/-
  Dolbeault ladder — **homotopy-independence of the Čech refinement map** (STEP A of the `cechH1`
  Leray cover-independence route; see the `## PLAN` block of `CechRefinement.lean`).

  Two refinement-index maps `r, r' : 𝔙.ι → 𝔘.ι` for the SAME pair of covers `(𝔙, 𝔘)` induce the same
  map on Čech `H¹`: `refineH1 hr D = refineH1 hr' D`.  This is the standard chain-homotopy argument,
  here for the length-2 complex `C⁰ →[δ⁰] C¹ →[δ¹] C²`.

  ## The prism (simplicial) homotopy

  For the two "vertex maps" `r#, r'#` we build the simplicial prism operator `K : C^q → C^{q-1}`,
    `(K g)_{j₀…j_{q-1}} = Σ_{i} (-1)ⁱ  g_{r j₀,…,r jᵢ, r' jᵢ,…,r' j_{q-1}} |_{𝔙-overlap}` ,
  in the two degrees we need:

    * `prismK0 : Cochain¹ 𝔘 → Cochain⁰ 𝔙`, `(prismK0 g)_j     = g_{(r j, r' j)} |_{𝔙.U j}`;
    * `prismK1 : Cochain² 𝔘 → Cochain¹ 𝔙`, `(prismK1 h)_{a b}  = h_{(r a, r' a, r' b)}
                                                                 − h_{(r a, r b, r' b)} |_{𝔙.U a ⊓ 𝔙.U b}`.

  These are well-typed because `𝔙.U j ≤ 𝔘.U (r j) ⊓ 𝔘.U (r' j)` (`le_inf (hr j) (hr' j)`) — the
  germ `g_{(r j, r' j)}` lives on the coarse overlap, which contains the fine set.

  The **prism identity** (pure `rawRestrictG_comp` + alternating-sum `abel` bookkeeping):

      refineC1 hr' − refineC1 hr  =  cechDelta0 𝔙 ∘ prismK0  +  prismK1 ∘ cechDelta1 𝔘 .

  On a **cocycle** `g` (`cechDelta1 𝔘 g = 0`) the second summand vanishes, so the difference of the two
  refinements is the coboundary `δ⁰_𝔙 (prismK0 g)`; moreover `prismK0 g` is an `𝒪_D` 0-section when `g`
  is an `𝒪_D` 1-cocycle, so this is a genuine `coboundaries1 𝔙 D`.  Descending through the
  `H¹ = Z¹/B¹` quotient (`Submodule.Quotient.eq`) gives `refineH1 hr = refineH1 hr'`.

  No gaps in this file.  See the `## STEP B` note at the bottom for what the *analytic* Leray gap
  still needs.
-/
import KirovDolbeault.Dolbeault.CechRefinement

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily
namespace IsRefinement

variable {𝔙 𝔘 : FiniteCover X} {r r' : 𝔙.ι → 𝔘.ι}

/-! ### The prism homotopy operators -/

/-- The fine set `𝔙.U j` sits inside the coarse `(r,r')`-overlap `𝔘.U (r j) ⊓ 𝔘.U (r' j)` (both
`r, r'` are refinements). The well-typedness witness for `prismK0`. -/
theorem le_pair (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r') (j : 𝔙.ι) :
    𝔙.U j ≤ 𝔘.U (r j) ⊓ 𝔘.U (r' j) :=
  le_inf (hr j) (hr' j)

/-- `prismK0 : Cochain¹ 𝔘 →ₗ[ℂ] Cochain⁰ 𝔙`, `(prismK0 g)_j = g_{(r j, r' j)} |_{𝔙.U j}`.
The degree-1 piece of the simplicial prism homotopy between the two vertex maps `r#, r'#`. -/
noncomputable def prismK0 (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r') :
    𝔘.Cochain1 →ₗ[ℂ] 𝔙.Cochain0 :=
  LinearMap.pi fun j => rawRestrictG (le_pair hr hr' j) ∘ₗ LinearMap.proj (r j, r' j)

@[simp] theorem prismK0_apply (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r')
    (g : 𝔘.Cochain1) (j : 𝔙.ι) :
    prismK0 hr hr' g j = rawRestrictG (le_pair hr hr' j) (g (r j, r' j)) := by
  simp only [prismK0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- For `prismK1` on the pair `(a,b)` we restrict the coarse triple germs `h_{(r a, r' a, r' b)}` and
`h_{(r a, r b, r' b)}` from their triple overlaps down to `𝔙.U a ⊓ 𝔙.U b`. The two containment
witnesses: -/
theorem tripleA_le (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r') (a b : 𝔙.ι) :
    𝔙.U a ⊓ 𝔙.U b ≤ 𝔘.U (r a) ⊓ 𝔘.U (r' a) ⊓ 𝔘.U (r' b) :=
  le_inf (le_inf (inf_le_left.trans (hr a)) (inf_le_left.trans (hr' a)))
    (inf_le_right.trans (hr' b))

theorem tripleB_le (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r') (a b : 𝔙.ι) :
    𝔙.U a ⊓ 𝔙.U b ≤ 𝔘.U (r a) ⊓ 𝔘.U (r b) ⊓ 𝔘.U (r' b) :=
  le_inf (le_inf (inf_le_left.trans (hr a)) (inf_le_right.trans (hr b)))
    (inf_le_right.trans (hr' b))

/-- `prismK1 : Cochain² 𝔘 →ₗ[ℂ] Cochain¹ 𝔙`,
`(prismK1 h)_{a b} = h_{(r a, r' a, r' b)} − h_{(r a, r b, r' b)} |_{𝔙.U a ⊓ 𝔙.U b}`.
The degree-2 piece of the simplicial prism homotopy. -/
noncomputable def prismK1 (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r') :
    𝔘.Cochain2 →ₗ[ℂ] 𝔙.Cochain1 :=
  LinearMap.pi fun p =>
    rawRestrictG (tripleA_le hr hr' p.1 p.2) ∘ₗ LinearMap.proj (r p.1, r' p.1, r' p.2)
      - rawRestrictG (tripleB_le hr hr' p.1 p.2) ∘ₗ LinearMap.proj (r p.1, r p.2, r' p.2)

@[simp] theorem prismK1_apply (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r')
    (h : 𝔘.Cochain2) (p : 𝔙.ι × 𝔙.ι) :
    prismK1 hr hr' h p =
      rawRestrictG (tripleA_le hr hr' p.1 p.2) (h (r p.1, r' p.1, r' p.2))
        - rawRestrictG (tripleB_le hr hr' p.1 p.2) (h (r p.1, r p.2, r' p.2)) := by
  simp only [prismK1, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

/-! ### The prism (chain-homotopy) identity -/

/-- **The prism identity.** The two refinement maps differ by a chain homotopy:
`refineC1 hr' − refineC1 hr = δ⁰_𝔙 ∘ prismK0 + prismK1 ∘ δ¹_𝔘`.  Componentwise on the fine pair
`(a,b)` (everything germ-restricted to `𝔙.U a ⊓ 𝔙.U b`, nested restrictions collapsed by
`rawRestrictG_comp_apply`) both sides equal `g_{(r' a)(r' b)} − g_{(r a)(r b)}`; the six prism terms
cancel by `abel`. This is the algebraic heart of homotopy-independence. -/
theorem refineC1_sub_eq_homotopy (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r') :
    hr'.refineC1 - hr.refineC1
      = 𝔙.cechDelta0 ∘ₗ prismK0 hr hr' + prismK1 hr hr' ∘ₗ 𝔘.cechDelta1 := by
  refine LinearMap.ext fun g => ?_
  funext p
  obtain ⟨a, b⟩ := p
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, refineC1_apply,
    cechDelta0, cechDelta1, LinearMap.pi_apply, LinearMap.proj_apply, prismK0_apply, prismK1_apply,
    Pi.add_apply, Pi.sub_apply, map_sub, map_add, rawRestrictG_comp_apply]
  abel

/-! ### Descent to `H¹`: the two refinement maps agree -/

variable (D : Divisor X)

/-- The prism homotopy `prismK0` maps `𝒪_D` 1-sections to `𝒪_D` 0-sections: each component
`(prismK0 g)_j = g_{(r j, r' j)} |_{𝔙.U j}` is a germ restriction of an `𝒪_D` germ
(`rawRestrictG_omegaDGerm`). -/
theorem prismK0_mem_sections0 (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r')
    {g : 𝔘.Cochain1} (hg : g ∈ 𝔘.sections1 D) : prismK0 hr hr' g ∈ 𝔙.sections0 D := fun j => by
  rw [prismK0_apply]
  exact rawRestrictG_omegaDGerm (le_pair hr hr' j) (hg (r j, r' j))

/-- **Homotopy step at the cocycle level.** For an `𝒪_D` 1-cocycle `g`, the difference of the two
refinements `refineC1 hr' g − refineC1 hr g` is an `𝒪_D` coboundary `δ⁰_𝔙 (prismK0 g)`: the prism
identity gives `refineC1 hr' g − refineC1 hr g = δ⁰_𝔙 (prismK0 g) + prismK1 (δ¹_𝔘 g)`, and `δ¹_𝔘 g = 0`
since `g` is a cocycle, while `prismK0 g` is an `𝒪_D` 0-section. -/
theorem refineC1_sub_mem_coboundaries1 (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r')
    {g : 𝔘.Cochain1} (hg : g ∈ 𝔘.cocycles1 D) :
    hr'.refineC1 g - hr.refineC1 g ∈ 𝔙.coboundaries1 D := by
  obtain ⟨hker, hsec⟩ := hg
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hker
  refine ⟨prismK0 hr hr' g, prismK0_mem_sections0 D hr hr' hsec, ?_⟩
  have hid := LinearMap.congr_fun (refineC1_sub_eq_homotopy hr hr') g
  rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    hker, map_zero, add_zero] at hid
  exact hid.symm

/-- **Homotopy-independence of the Čech refinement map.** Any two refinement-index maps `r, r'` for
the same pair of covers induce the SAME map on Čech `H¹`: `refineH1 hr D = refineH1 hr' D`.  The
difference of the two cocycle-level refinements is a coboundary (`refineC1_sub_mem_coboundaries1`), so
the induced classes in `H¹ = Z¹/B¹` coincide (`Submodule.Quotient.eq`); the maps then agree on every
generator `Submodule.Quotient.mk g`. -/
theorem refineH1_eq (hr : IsRefinement 𝔙 𝔘 r) (hr' : IsRefinement 𝔙 𝔘 r') :
    hr.refineH1 D = hr'.refineH1 D := by
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | _ g =>
    rw [refineH1_mk, refineH1_mk, Submodule.Quotient.eq]
    -- `refineZ1 hr g − refineZ1 hr' g ∈ (coboundaries1 𝔙 D).submoduleOf (cocycles1 𝔙 D)`;
    -- membership in `submoduleOf` is (definitionally) membership of the coe in `coboundaries1 𝔙 D`,
    -- and the coe of `refineZ1 _ g` is `refineC1 _ g` (`refineZ1_coe`).
    exact refineC1_sub_mem_coboundaries1 D hr' hr g.2

end IsRefinement
end FiniteCover

/-! ## STEP B — what the Leray cover-independence iso still needs (the analytic gap)

This file discharges **STEP A** of the `CechRefinement.lean` PLAN: `refineH1` depends only on the pair
`(𝔙, 𝔘)`, not on the chosen index map `r` (`IsRefinement.refineH1_eq`).  The chain-homotopy operators
`prismK0`, `prismK1` and the prism identity `refineC1_sub_eq_homotopy` are reusable.

What STEP A buys for STEP B: with index-independence, for two covers admitting *mutual* refinements
`𝔙 ⪯ 𝔘` and `𝔘 ⪯ 𝔙` the two composites `refineH1 ∘ refineH1` are forced to be the identity *as soon as
each round trip is shown to be the canonical self-refinement map* — because any two refinement index
maps (in particular the round-trip `r ∘ s` and the identity `id`) induce the same `H¹` map, and
`(IsRefinement.id 𝔘).refineH1 = LinearMap.id` (a one-liner from `refineC1` of `id` being the identity).
So the remaining content is purely to exhibit, for two *Leray* covers, a common refinement and the
surjectivity half.

GENUINELY-ANALYTIC GAP that remains (absent from Mathlib; NOT addressed here):
  * `refineH1` is an ISOMORPHISM when `𝔙 ⪯ 𝔘` are both Leray.  Injectivity is the homotopy argument
    (STEP A, here) plus the round-trip identity; SURJECTIVITY needs the disk/overlap-acyclicity input
    `H¹(overlap, 𝒪) = 0` — the proven ∂̄-solvability atom `DbarDiskCohomology.dbar_solvable_ball` — to
    lift a `𝔙`-cocycle to a `𝔘`-cocycle modulo coboundary (the same shape as
    `CechFinitenessWiring.Coboundaries.leray`, restated as an iso of the germ-class `cechH1`s).
  * Then `cechH1 𝔘 D ≃ₗ[ℂ] cechH1 𝔙 D` for two Leray covers; chaining through a common refinement and
    the committed `CechModelGeometry` chart-cover model discharges `exists_cechModel` for an arbitrary
    Leray `𝔘`.
  * Recon (see `CechRefinement.lean` PLAN) confirms Mathlib has NO Čech refinement/Leray/acyclic-cover
    theorem, so STEP B is hand-built greenfield (~several hundred LoC on top of the disk atom; no
    further analysis beyond `dbar_solvable_ball`).
-/

end Jacobians.Dolbeault
