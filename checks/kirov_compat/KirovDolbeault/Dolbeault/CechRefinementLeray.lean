/-
  Dolbeault ladder — **STEP B of the Čech Leray cover-independence**: `refineH1` is a `ℂ`-linear
  isomorphism for two Leray covers (the crux of `CechFinitenessWiring.exists_cechModel`).

  Builds on STEP A (`CechRefinementHomotopy.refineH1_eq`, homotopy/index-independence of the
  refinement map) and the refinement chain-map machinery (`CechRefinement`).  See the `## PLAN` block
  of `CechRefinement.lean` for the full route.

  ## What is proven here (complete, axiom-clean `[propext, Classical.choice, Quot.sound]`)

    * **Round-trip / functoriality on `H¹`** (pure restriction algebra + STEP A):
        - `refineC1_id`  — the identity refinement is the identity on 1-cochains;
        - `refineH1_id`  — `(IsRefinement.id 𝔘).refineH1 D = LinearMap.id`;
        - `refineH1_comp` — `(hs.comp hr).refineH1 D = hs.refineH1 D ∘ₗ hr.refineH1 D` (functoriality,
          using `refineC1_comp` + descent through the quotient).
    * **Injectivity from a back-refinement** (STEP A + functoriality, complete):
        - `refineH1_leftInverse` — a back-refinement `𝔘 ⪯ 𝔙` gives `refineH1 hs` as an explicit LEFT
          INVERSE of `refineH1 hr` (`(hs.comp hr).refineH1 = id` by STEP A, since `r∘s : 𝔘 → 𝔘` is a
          self-refinement, equal on `H¹` to the identity refinement);
        - `refineH1_injective` — hence `refineH1 hr` is injective.
    * **The mutual-refinement isomorphism** (complete, NO analytic input):
        - `refineH1_equiv` — for covers `𝔙, 𝔘` with MUTUAL refinements `𝔙 ⪯ 𝔘` and `𝔘 ⪯ 𝔙`, both
          round-trips are self-refinements (= identity on `H¹` by STEP A), so `refineH1 hr` is a
          `ℂ`-linear bijection `cechH1 𝔘 D ≃ₗ[ℂ] cechH1 𝔙 D`.  This is the cover-independence
          isomorphism whenever the two covers mutually refine (in particular it does NOT need
          disk-acyclicity).

  ## What is the genuine analytic GAP (the surjectivity of a *strictly finer* Leray refinement)

  The `exists_cechModel` chaining goes through a COMMON refinement `𝔚 ⪯ 𝔘`, `𝔚 ⪯ 𝔙`, where `𝔚` is
  strictly finer and there is NO back-refinement `𝔘 ⪯ 𝔚`.  For such a strictly-finer Leray refinement
  the down-map `refineH1 (𝔚 ⪯ 𝔘)` being an iso needs the disk/overlap-acyclicity input
  `H¹(U_i ∩ U_j, 𝒪) = 0` (the proven `DbarDiskCohomology.dbar_solvable_ball` /
  `dbar_holo_splitting_ball`).  This file isolates that gap as the named predicate
  `RefinementSurjective` and proves the conditional upgrade `refineH1_equiv_of_surjective` (injectivity
  is unconditional via STEP A's `refineH1_leftInverse` only when a back-refinement exists — for the
  strictly-finer case injectivity ALSO needs the acyclicity, see the `## SURJECTIVITY` note).  The
  unconditional gap-free deliverable is the mutual-refinement equiv `refineH1_equiv`.

  No gaps in this file; everything not yet mechanized is written prose, not a tactic gap.
-/
import KirovDolbeault.Dolbeault.CechRefinementHomotopy
import KirovDolbeault.Dolbeault.CechDiskAcyclic

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily
namespace IsRefinement

variable {𝔚 𝔙 𝔘 : FiniteCover X}

/-! ### Round-trip / functoriality on `H¹` -/

/-- Germ restriction is independent of the particular proof of the open containment. -/
theorem rawRestrictG_congr_le {U V : Opens X} (h h' : V ≤ U) (f : MGerm U) :
    rawRestrictG h f = rawRestrictG h' f := by
  have hh : h = h' := Subsingleton.elim h h'
  subst hh
  rfl

/-- **The identity refinement is the identity on 1-cochains.**  `(IsRefinement.id 𝔘).refineC1 = id`:
on each pair `p` the value is `rawRestrictG le_rfl (g (id p.1, id p.2)) = g p`. -/
theorem refineC1_id (𝔘 : FiniteCover X) :
    (IsRefinement.id 𝔘).refineC1 = LinearMap.id := by
  refine LinearMap.ext fun g => ?_
  funext p
  rw [refineC1_apply, LinearMap.id_apply]
  -- `r = id`: `g (id p.1, id p.2) = g p` (defeq) and the restriction is along `U p ≤ U p`.
  rw [show g (_root_.id p.1, _root_.id p.2) = g p from rfl]
  induction g p using Filter.Germ.inductionOn with | _ f => rfl

variable (D : Divisor X)

/-- **The identity refinement is the identity on cocycles** `Z¹(𝔘) → Z¹(𝔘)`.  Follows from
`refineC1_id` since `refineZ1` corestricts `refineC1` and the cocycle-coe is injective. -/
theorem refineZ1_id (𝔘 : FiniteCover X) (g : ↥(𝔘.cocycles1 D)) :
    (IsRefinement.id 𝔘).refineZ1 D g = g := by
  apply Subtype.ext
  rw [refineZ1_coe, refineC1_id, LinearMap.id_apply]

/-- **`refineH1` of the identity refinement is the identity on `H¹`** (`refineH1_id`). -/
theorem refineH1_id (𝔘 : FiniteCover X) :
    (IsRefinement.id 𝔘).refineH1 D = LinearMap.id := by
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | _ g => rw [refineH1_mk, refineZ1_id, LinearMap.id_apply]

/-- **`refineZ1` is functorial on cocycles.**  `(hs.comp hr).refineZ1 = hs.refineZ1 ∘ hr.refineZ1`
(the cocycle-level form of `refineC1_comp`; corestricting both sides + cocycle-coe injectivity). -/
theorem refineZ1_comp {s : 𝔚.ι → 𝔙.ι} {r : 𝔙.ι → 𝔘.ι}
    (hs : IsRefinement 𝔚 𝔙 s) (hr : IsRefinement 𝔙 𝔘 r) (g : ↥(𝔘.cocycles1 D)) :
    (hs.comp hr).refineZ1 D g = hs.refineZ1 D (hr.refineZ1 D g) := by
  apply Subtype.ext
  rw [refineZ1_coe, refineZ1_coe, refineZ1_coe, refineC1_comp hs hr, LinearMap.comp_apply]

/-- **`refineH1` is functorial on `H¹`** `(hs.comp hr).refineH1 = hs.refineH1 ∘ₗ hr.refineH1`
(`refineH1_comp`).  Descends `refineZ1_comp` through the `H¹ = Z¹/B¹` quotient. -/
theorem refineH1_comp {s : 𝔚.ι → 𝔙.ι} {r : 𝔙.ι → 𝔘.ι}
    (hs : IsRefinement 𝔚 𝔙 s) (hr : IsRefinement 𝔙 𝔘 r) :
    (hs.comp hr).refineH1 D = hs.refineH1 D ∘ₗ hr.refineH1 D := by
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | _ g =>
    rw [refineH1_mk, LinearMap.comp_apply, refineH1_mk, refineH1_mk, refineZ1_comp]

/-! ### Injectivity of `refineH1` from a back-refinement (STEP A + functoriality)

The standard Leray injectivity, in the complete *mutual-refinement* form: if `𝔙 ⪯ 𝔘` (via `r`) AND
`𝔘 ⪯ 𝔙` (via `s`), then the round-trip `r ∘ s : 𝔘.ι → 𝔘.ι` is a self-refinement of `𝔘`, so by STEP A
(homotopy/index-independence, `refineH1_eq`) it induces the SAME `H¹` map as the identity refinement,
namely `LinearMap.id`.  Functoriality (`refineH1_comp`) then exhibits `refineH1 hs` as an explicit
LEFT INVERSE of `refineH1 hr`, giving injectivity.  No analytic input. -/

/-- **A back-refinement gives a left inverse on `H¹`.**  If `𝔙 ⪯ 𝔘` (`hr`) and `𝔘 ⪯ 𝔙` (`hs`) then
`hs.refineH1 D ∘ₗ hr.refineH1 D = LinearMap.id`: the round-trip `r ∘ s` is a self-refinement of `𝔘`,
equal on `H¹` to the identity refinement by STEP A (`refineH1_eq`), and functorial by `refineH1_comp`.
-/
theorem refineH1_comp_eq_id {s : 𝔘.ι → 𝔙.ι} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hs : IsRefinement 𝔘 𝔙 s) :
    hs.refineH1 D ∘ₗ hr.refineH1 D = LinearMap.id := by
  rw [← refineH1_comp D hs hr, refineH1_eq D (hs.comp hr) (IsRefinement.id 𝔘), refineH1_id]

/-- **Injectivity of `refineH1` from a back-refinement.**  When `𝔙 ⪯ 𝔘` (`hr`) admits a
back-refinement `𝔘 ⪯ 𝔙` (`hs`), `hr.refineH1 D` is injective (left inverse `hs.refineH1 D`). -/
theorem refineH1_injective {s : 𝔘.ι → 𝔙.ι} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hs : IsRefinement 𝔘 𝔙 s) :
    Function.Injective (hr.refineH1 D) := by
  have hLI : Function.LeftInverse (hs.refineH1 D) (hr.refineH1 D) := fun q => by
    have := LinearMap.congr_fun (refineH1_comp_eq_id D hr hs) q
    simpa using this
  exact hLI.injective

/-! ### The mutual-refinement isomorphism (complete, no analytic input) -/

/-- **Cover-independence isomorphism for mutually-refining covers.**  If `𝔙, 𝔘` admit MUTUAL
refinements `𝔙 ⪯ 𝔘` (`hr`) and `𝔘 ⪯ 𝔙` (`hs`), then `refineH1 hr` is a `ℂ`-linear ISOMORPHISM
`cechH1 𝔘 D ≃ₗ[ℂ] cechH1 𝔙 D`, with inverse `refineH1 hs`.  Both round-trips `r∘s : 𝔘 → 𝔘` and
`s∘r : 𝔙 → 𝔙` are self-refinements, hence equal on `H¹` to the identity by STEP A
(`refineH1_comp_eq_id`); so the two maps are mutually inverse.  Entirely complete — it does NOT need
disk-acyclicity (the analytic input is only required when one cover STRICTLY refines the other with no
back-refinement; see the `## SURJECTIVITY` note at the bottom). -/
noncomputable def refineH1_equiv {s : 𝔘.ι → 𝔙.ι} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hs : IsRefinement 𝔘 𝔙 s) :
    𝔘.cechH1 D ≃ₗ[ℂ] 𝔙.cechH1 D :=
  LinearEquiv.ofLinear (hr.refineH1 D) (hs.refineH1 D)
    (by rw [← refineH1_comp D hr hs, refineH1_eq D (hr.comp hs) (IsRefinement.id 𝔙), refineH1_id])
    (refineH1_comp_eq_id D hr hs)

@[simp] theorem refineH1_equiv_apply {s : 𝔘.ι → 𝔙.ι} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hs : IsRefinement 𝔘 𝔙 s) (q : 𝔘.cechH1 D) :
    refineH1_equiv D hr hs q = hr.refineH1 D q := rfl

/-! ### The Leray analytic conditions for a STRICTLY-finer refinement (honest predicates)

The mutual-refinement equiv above covers the case where the two covers refine each other.  The
`exists_cechModel` chaining instead needs the case `𝔙 ⪯ 𝔘` with `𝔙` STRICTLY finer (a common
refinement), where there is NO back-refinement `𝔘 ⪯ 𝔙`.  For that case `refineH1 hr` being an iso is
the genuine Leray theorem, and the analytic content is isolated into the two cocycle-level predicates
below — both stated in the SAME "lift mod coboundary" shape as `CechFinitenessWiring.Coboundaries.leray`.
The conditional upgrades (`refineH1_surjective_of_lift`, `refineH1_injective_of_descend`,
`refineH1_equiv_of_leray`) are then complete; the honest analytic obligation is to PRODUCE these
predicates from disk/overlap-acyclicity (the `## SURJECTIVITY` plan at the bottom). -/

variable {r : 𝔙.ι → 𝔘.ι}

/-- The local family obtained by restricting the fine cover `𝔙` to the coarse overlap
`𝔘.U i ∩ 𝔘.U j`.  Its sets are `{𝔙.U a ∩ 𝔘.U i ∩ 𝔘.U j}_a`, the family that appears in the standard
Leray lift proof on a fixed coarse overlap. -/
def overlapFamily (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) : FiniteFamily X :=
  𝔙.toFiniteFamily.restrictToOpen (𝔘.U i ⊓ 𝔘.U j)

@[simp] theorem overlapFamily_U (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) (a : 𝔙.ι) :
    (overlapFamily 𝔙 𝔘 i j).U a = 𝔙.U a ⊓ (𝔘.U i ⊓ 𝔘.U j) :=
  rfl

/-- The restricted fine family covers the chosen coarse overlap. -/
theorem overlapFamily_covers (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) :
    (overlapFamily 𝔙 𝔘 i j).CoversOpen (𝔘.U i ⊓ 𝔘.U j) :=
  FiniteFamily.restrictToOpen_covers_of_cover 𝔙 (𝔘.U i ⊓ 𝔘.U j)

/-- Each member of the overlap family lies in its fine cover set. -/
theorem overlapFamily_le_fine (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) (a : 𝔙.ι) :
    (overlapFamily 𝔙 𝔘 i j).U a ≤ 𝔙.U a :=
  FiniteFamily.restrictToOpen_le_left 𝔙.toFiniteFamily (𝔘.U i ⊓ 𝔘.U j) a

/-- Each member of the overlap family lies in the chosen coarse overlap. -/
theorem overlapFamily_le_coarseOverlap (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) (a : 𝔙.ι) :
    (overlapFamily 𝔙 𝔘 i j).U a ≤ 𝔘.U i ⊓ 𝔘.U j :=
  FiniteFamily.restrictToOpen_le_right 𝔙.toFiniteFamily (𝔘.U i ⊓ 𝔘.U j) a

/-- The pairwise overlap of the restricted overlap family sits inside the original fine pairwise
overlap. -/
theorem overlapFamily_pair_le_finePair (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) (a b : 𝔙.ι) :
    (overlapFamily 𝔙 𝔘 i j).U a ⊓ (overlapFamily 𝔙 𝔘 i j).U b ≤
      𝔙.U a ⊓ 𝔙.U b :=
  inf_le_inf (overlapFamily_le_fine 𝔙 𝔘 i j a) (overlapFamily_le_fine 𝔙 𝔘 i j b)

/-- The triple overlap of the restricted overlap family sits inside the original fine triple
overlap. -/
theorem overlapFamily_triple_le_fineTriple (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι)
    (a b c : 𝔙.ι) :
    (overlapFamily 𝔙 𝔘 i j).U a ⊓ (overlapFamily 𝔙 𝔘 i j).U b ⊓
        (overlapFamily 𝔙 𝔘 i j).U c ≤
      𝔙.U a ⊓ 𝔙.U b ⊓ 𝔙.U c :=
  inf_le_inf
    (inf_le_inf (overlapFamily_le_fine 𝔙 𝔘 i j a) (overlapFamily_le_fine 𝔙 𝔘 i j b))
    (overlapFamily_le_fine 𝔙 𝔘 i j c)

/-- Restrict a fine-cover `0`-cochain to the local family over a fixed coarse overlap. -/
noncomputable def overlapRestrictC0 (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) :
    𝔙.Cochain0 →ₗ[ℂ] (overlapFamily 𝔙 𝔘 i j).Cochain0 :=
  LinearMap.pi fun a =>
    rawRestrictG (overlapFamily_le_fine 𝔙 𝔘 i j a) ∘ₗ LinearMap.proj a

@[simp] theorem overlapRestrictC0_apply (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι)
    (g : 𝔙.Cochain0) (a : 𝔙.ι) :
    overlapRestrictC0 𝔙 𝔘 i j g a =
      rawRestrictG (overlapFamily_le_fine 𝔙 𝔘 i j a) (g a) := by
  change rawRestrictG (overlapFamily_le_fine 𝔙 𝔘 i j a) (g a) =
    rawRestrictG (overlapFamily_le_fine 𝔙 𝔘 i j a) (g a)
  rfl

/-- Restrict a fine-cover `1`-cochain to the local family over a fixed coarse overlap. -/
noncomputable def overlapRestrictC1 (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) :
    𝔙.Cochain1 →ₗ[ℂ] (overlapFamily 𝔙 𝔘 i j).Cochain1 :=
  LinearMap.pi fun p =>
    rawRestrictG (overlapFamily_pair_le_finePair 𝔙 𝔘 i j p.1 p.2) ∘ₗ LinearMap.proj p

@[simp] theorem overlapRestrictC1_apply (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι)
    (g : 𝔙.Cochain1) (p : 𝔙.ι × 𝔙.ι) :
    overlapRestrictC1 𝔙 𝔘 i j g p =
      rawRestrictG (overlapFamily_pair_le_finePair 𝔙 𝔘 i j p.1 p.2) (g p) := by
  change rawRestrictG (overlapFamily_pair_le_finePair 𝔙 𝔘 i j p.1 p.2) (g p) =
    rawRestrictG (overlapFamily_pair_le_finePair 𝔙 𝔘 i j p.1 p.2) (g p)
  rfl

/-- Restrict a fine-cover `2`-cochain to the local family over a fixed coarse overlap. -/
noncomputable def overlapRestrictC2 (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) :
    𝔙.Cochain2 →ₗ[ℂ] (overlapFamily 𝔙 𝔘 i j).Cochain2 :=
  LinearMap.pi fun t =>
    rawRestrictG (overlapFamily_triple_le_fineTriple 𝔙 𝔘 i j t.1 t.2.1 t.2.2) ∘ₗ
      LinearMap.proj t

@[simp] theorem overlapRestrictC2_apply (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι)
    (g : 𝔙.Cochain2) (t : 𝔙.ι × 𝔙.ι × 𝔙.ι) :
    overlapRestrictC2 𝔙 𝔘 i j g t =
      rawRestrictG (overlapFamily_triple_le_fineTriple 𝔙 𝔘 i j t.1 t.2.1 t.2.2) (g t) := by
  change rawRestrictG (overlapFamily_triple_le_fineTriple 𝔙 𝔘 i j t.1 t.2.1 t.2.2) (g t) =
    rawRestrictG (overlapFamily_triple_le_fineTriple 𝔙 𝔘 i j t.1 t.2.1 t.2.2) (g t)
  rfl

/-- Restriction to a coarse-overlap family commutes with the Čech `δ⁰`. -/
theorem overlapRestrictC1_comp_cechDelta0 (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) :
    (overlapFamily 𝔙 𝔘 i j).cechDelta0 ∘ₗ overlapRestrictC0 𝔙 𝔘 i j =
      overlapRestrictC1 𝔙 𝔘 i j ∘ₗ 𝔙.cechDelta0 := by
  refine LinearMap.ext fun g => ?_
  funext p
  obtain ⟨a, b⟩ := p
  simp only [LinearMap.comp_apply, FiniteFamily.cechDelta0, LinearMap.pi_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply, overlapRestrictC0_apply,
    overlapRestrictC1_apply, map_sub, FiniteFamily.rawRestrictG_comp_apply]

/-- Restriction to a coarse-overlap family commutes with the Čech `δ¹`. -/
theorem overlapRestrictC2_comp_cechDelta1 (𝔙 𝔘 : FiniteCover X) (i j : 𝔘.ι) :
    (overlapFamily 𝔙 𝔘 i j).cechDelta1 ∘ₗ overlapRestrictC1 𝔙 𝔘 i j =
      overlapRestrictC2 𝔙 𝔘 i j ∘ₗ 𝔙.cechDelta1 := by
  refine LinearMap.ext fun g => ?_
  funext t
  obtain ⟨a, b, c⟩ := t
  simp only [LinearMap.comp_apply, FiniteFamily.cechDelta1, LinearMap.pi_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    overlapRestrictC1_apply, overlapRestrictC2_apply, map_sub, map_add,
    FiniteFamily.rawRestrictG_comp_apply]
  congr 1

/-- Restricting a fine-cover `𝒪_D` `0`-section to a coarse-overlap family gives an `𝒪_D`
`0`-section on that local family. -/
theorem overlapRestrictC0_mem_sections0 (𝔙 𝔘 : FiniteCover X) (D : Divisor X) (i j : 𝔘.ι)
    {g : 𝔙.Cochain0} (hg : g ∈ 𝔙.sections0 D) :
    overlapRestrictC0 𝔙 𝔘 i j g ∈ (overlapFamily 𝔙 𝔘 i j).sections0 D := fun a => by
  rw [overlapRestrictC0_apply]
  exact rawRestrictG_omegaDGerm (overlapFamily_le_fine 𝔙 𝔘 i j a) (hg a)

/-- Restricting a fine-cover `𝒪_D` `1`-section to a coarse-overlap family gives an `𝒪_D`
`1`-section on that local family. -/
theorem overlapRestrictC1_mem_sections1 (𝔙 𝔘 : FiniteCover X) (D : Divisor X) (i j : 𝔘.ι)
    {g : 𝔙.Cochain1} (hg : g ∈ 𝔙.sections1 D) :
    overlapRestrictC1 𝔙 𝔘 i j g ∈ (overlapFamily 𝔙 𝔘 i j).sections1 D := fun p => by
  rw [overlapRestrictC1_apply]
  exact rawRestrictG_omegaDGerm (overlapFamily_pair_le_finePair 𝔙 𝔘 i j p.1 p.2) (hg p)

/-- Restricting a fine-cover cocycle to a coarse-overlap family gives a cocycle on the local
restricted family.  This is the first algebraic step in the Leray lift proof. -/
theorem overlapRestrictC1_mem_cocycles1 (𝔙 𝔘 : FiniteCover X) (D : Divisor X) (i j : 𝔘.ι)
    {g : 𝔙.Cochain1} (hg : g ∈ 𝔙.cocycles1 D) :
    overlapRestrictC1 𝔙 𝔘 i j g ∈ (overlapFamily 𝔙 𝔘 i j).cocycles1 D := by
  obtain ⟨hker, hsec⟩ := hg
  refine ⟨?_, overlapRestrictC1_mem_sections1 𝔙 𝔘 D i j hsec⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hker ⊢
  rw [← LinearMap.comp_apply, overlapRestrictC2_comp_cechDelta1, LinearMap.comp_apply, hker,
    map_zero]

/-- Restricting a fine-cover coboundary to a coarse-overlap family gives a local coboundary. -/
theorem overlapRestrictC1_mem_coboundaries1 (𝔙 𝔘 : FiniteCover X) (D : Divisor X) (i j : 𝔘.ι)
    {g : 𝔙.Cochain1} (hg : g ∈ 𝔙.coboundaries1 D) :
    overlapRestrictC1 𝔙 𝔘 i j g ∈ (overlapFamily 𝔙 𝔘 i j).coboundaries1 D := by
  obtain ⟨c, hc, rfl⟩ := hg
  refine ⟨overlapRestrictC0 𝔙 𝔘 i j c, overlapRestrictC0_mem_sections0 𝔙 𝔘 D i j hc, ?_⟩
  rw [← LinearMap.comp_apply, overlapRestrictC1_comp_cechDelta0, LinearMap.comp_apply]

/-- The exact local acyclicity target for the Leray lift proof: for every coarse overlap
`𝔘.U i ∩ 𝔘.U j`, the fine family restricted to that overlap is function-level disk-acyclic.  This is
the formal version of the attack-plan atom "a cocycle on a restricted chart-disk overlap family is a
coboundary". -/
def OverlapFunctionDiskAcyclic (𝔙 𝔘 : FiniteCover X) (D : Divisor X) : Prop :=
  ∀ i j : 𝔘.ι, FunctionDiskAcyclic (overlapFamily 𝔙 𝔘 i j) D

/-- Germ-level version of `OverlapFunctionDiskAcyclic`. -/
def OverlapIsDiskAcyclic (𝔙 𝔘 : FiniteCover X) (D : Divisor X) : Prop :=
  ∀ i j : 𝔘.ι, IsDiskAcyclic (overlapFamily 𝔙 𝔘 i j) D

/-- Function-level overlap acyclicity gives germ-level overlap acyclicity. -/
theorem overlapIsDiskAcyclic_of_funcLevel (𝔙 𝔘 : FiniteCover X) (D : Divisor X)
    (h : OverlapFunctionDiskAcyclic 𝔙 𝔘 D) : OverlapIsDiskAcyclic 𝔙 𝔘 D :=
  fun i j => isDiskAcyclic_of_funcLevel (overlapFamily 𝔙 𝔘 i j) D (h i j)

/-- A fine-cover cocycle becomes a local coboundary on every restricted coarse-overlap family once
the overlap families are germ-level disk-acyclic. -/
theorem overlapCoboundary_of_overlapIsDiskAcyclic (𝔙 𝔘 : FiniteCover X) (D : Divisor X)
    (h : OverlapIsDiskAcyclic 𝔙 𝔘 D) (i j : 𝔘.ι) (t : ↥(𝔙.cocycles1 D)) :
    overlapRestrictC1 𝔙 𝔘 i j (t : 𝔙.Cochain1) ∈
      (overlapFamily 𝔙 𝔘 i j).coboundaries1 D :=
  h i j _ (overlapRestrictC1_mem_cocycles1 𝔙 𝔘 D i j t.2)

/-- Function-level overlap acyclicity supplies explicit local holomorphic primitives for the
restriction of any fine-cover cocycle to each coarse overlap. -/
theorem exists_overlapPrimitive_of_overlapFunctionDiskAcyclic (𝔙 𝔘 : FiniteCover X) (D : Divisor X)
    (h : OverlapFunctionDiskAcyclic 𝔙 𝔘 D) (i j : 𝔘.ι) (t : ↥(𝔙.cocycles1 D)) :
    ∃ η : Π a, (overlapFamily 𝔙 𝔘 i j).U a → ℂ,
      (∀ a, η a ∈ OmegaD D ((overlapFamily 𝔙 𝔘 i j).U a)) ∧
        (overlapFamily 𝔙 𝔘 i j).cechDelta0
            (fun a => toGerm ((overlapFamily 𝔙 𝔘 i j).U a) (η a)) =
          overlapRestrictC1 𝔙 𝔘 i j (t : 𝔙.Cochain1) :=
  h i j (overlapRestrictC1 𝔙 𝔘 i j (t : 𝔙.Cochain1))
    (overlapRestrictC1_mem_cocycles1 𝔙 𝔘 D i j t.2)

/-- **The Leray LIFT condition (surjectivity input).**  Every `𝔙`-cocycle `t` is, modulo a
`𝔙`-coboundary, the refinement `refineC1 g` of some `𝔘`-cocycle `g`.  This is the cocycle-level form
of surjectivity of `refineH1 hr`; geometrically it is the Leray cover-refinement lift fed by
overlap-acyclicity `H¹(overlap, 𝒪) = 0` (`dbar_solvable_ball`). -/
def RefinementLift (hr : IsRefinement 𝔙 𝔘 r) (D : Divisor X) : Prop :=
  ∀ t : ↥(𝔙.cocycles1 D), ∃ g : ↥(𝔘.cocycles1 D),
    hr.refineC1 (g : 𝔘.Cochain1) - (t : 𝔙.Cochain1) ∈ 𝔙.coboundaries1 D

/-- **A disk-acyclic fine cover gives the Leray lift condition.**  If the refining cover `𝔙` is
already disk-acyclic, then every `𝔙`-cocycle is a coboundary, so the Leray lift condition holds
trivially by taking the coarse cocycle `g = 0`.  This is the refinement-side bridge that the
chart-disk acyclicity atom ultimately feeds. -/
theorem refinementLift_of_isDiskAcyclic (hr : IsRefinement 𝔙 𝔘 r) (D : Divisor X)
    (h : IsDiskAcyclic 𝔙.toFiniteFamily D) : RefinementLift hr D := by
  intro t
  have ht : (t : 𝔙.Cochain1) ∈ 𝔙.toFiniteFamily.coboundaries1 D := h t t.2
  refine ⟨⟨0, by simp [FiniteFamily.cocycles1, FiniteFamily.sections1]⟩, ?_⟩
  rw [show (hr.refineC1 (0 : 𝔘.Cochain1)) = 0 by simp]
  simpa using (Submodule.neg_mem _ ht)

/-- **A function-level disk-acyclic fine cover gives the Leray lift condition.**  This is the bridge
the chart-disk PoU kernel is meant to feed: once `FunctionDiskAcyclic` is produced, the refinement
lift condition follows by the previous disk-acyclic reduction. -/
theorem refinementLift_of_funcLevel (hr : IsRefinement 𝔙 𝔘 r) (D : Divisor X)
    (h : FunctionDiskAcyclic 𝔙.toFiniteFamily D) : RefinementLift hr D :=
  refinementLift_of_isDiskAcyclic hr D (isDiskAcyclic_of_funcLevel 𝔙.toFiniteFamily D h)

/-- **The Leray DESCEND condition (injectivity input).**  A `𝔘`-cocycle whose refinement is a
`𝔙`-coboundary was already a `𝔘`-coboundary (`ker (refineH1 hr) = 0`).  This is Forster 12.8
(injectivity of the coarse→fine map on `H¹`); for `𝒪` with germ-class sections it is the H⁰ gluing
of the splitting `η`, again an overlap-acyclicity consequence. -/
def RefinementDescend (hr : IsRefinement 𝔙 𝔘 r) (D : Divisor X) : Prop :=
  ∀ g : ↥(𝔘.cocycles1 D),
    hr.refineC1 (g : 𝔘.Cochain1) ∈ 𝔙.coboundaries1 D → (g : 𝔘.Cochain1) ∈ 𝔘.coboundaries1 D

/-- **A disk-acyclic coarse cover gives the Leray descend condition.**  If the coarse cover `𝔘` is
already disk-acyclic, then every coarse cocycle is a coboundary, so the Leray descend condition holds
trivially.  This is the companion bridge to `refinementLift_of_isDiskAcyclic`. -/
theorem refinementDescend_of_isDiskAcyclic (hr : IsRefinement 𝔙 𝔘 r) (D : Divisor X)
    (h : IsDiskAcyclic 𝔘.toFiniteFamily D) : RefinementDescend hr D := by
  intro g _
  exact h g g.2

/-- **A function-level disk-acyclic coarse cover gives the Leray descend condition.**  Companion to
`refinementLift_of_funcLevel`. -/
theorem refinementDescend_of_funcLevel (hr : IsRefinement 𝔙 𝔘 r) (D : Divisor X)
    (h : FunctionDiskAcyclic 𝔘.toFiniteFamily D) : RefinementDescend hr D :=
  refinementDescend_of_isDiskAcyclic hr D (isDiskAcyclic_of_funcLevel 𝔘.toFiniteFamily D h)

/-- `refineH1 hr [g] = [t]` (in `H¹`) ⟺ `refineC1 g − t` is a `𝔙`-coboundary.  The bridge between the
quotient `H¹`-class equality and the cocycle-level "mod coboundary" statement (`Submodule.Quotient.eq`;
membership in `(coboundaries1).submoduleOf (cocycles1)` is defeq to `↑· ∈ coboundaries1`). -/
theorem refineH1_mk_eq_iff (hr : IsRefinement 𝔙 𝔘 r) (g : ↥(𝔘.cocycles1 D))
    (t : ↥(𝔙.cocycles1 D)) :
    hr.refineH1 D (Submodule.Quotient.mk g) = Submodule.Quotient.mk t ↔
      hr.refineC1 (g : 𝔘.Cochain1) - (t : 𝔙.Cochain1) ∈ 𝔙.coboundaries1 D := by
  rw [refineH1_mk, Submodule.Quotient.eq]
  rfl

/-- **Surjectivity of `refineH1` ⟺ the Leray LIFT condition.**  The cocycle-level lift predicate is
exactly surjectivity of the induced `H¹` map (so `RefinementLift` is a faithful interface, not merely
a sufficient condition). -/
theorem refineH1_surjective_iff_lift (hr : IsRefinement 𝔙 𝔘 r) :
    Function.Surjective (hr.refineH1 D) ↔ RefinementLift hr D := by
  constructor
  · intro hsurj t
    obtain ⟨q, hq⟩ := hsurj (Submodule.Quotient.mk t)
    induction q using Submodule.Quotient.induction_on with
    | _ g => exact ⟨g, (refineH1_mk_eq_iff D hr g t).1 hq⟩
  · intro hlift q
    induction q using Submodule.Quotient.induction_on with
    | _ t =>
      obtain ⟨g, hg⟩ := hlift t
      exact ⟨Submodule.Quotient.mk g, (refineH1_mk_eq_iff D hr g t).2 hg⟩

/-- **Surjectivity of `refineH1` from the Leray LIFT condition** (the direction the iso needs). -/
theorem refineH1_surjective_of_lift (hr : IsRefinement 𝔙 𝔘 r) (hlift : RefinementLift hr D) :
    Function.Surjective (hr.refineH1 D) :=
  (refineH1_surjective_iff_lift D hr).2 hlift

/-- **Injectivity of `refineH1` ⟺ the Leray DESCEND condition.** -/
theorem refineH1_injective_iff_descend (hr : IsRefinement 𝔙 𝔘 r) :
    Function.Injective (hr.refineH1 D) ↔ RefinementDescend hr D := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  constructor
  · intro hker g hg
    have hmk : Submodule.Quotient.mk g = (0 : 𝔘.cechH1 D) := by
      refine hker (Submodule.Quotient.mk g) ?_
      rw [show (0 : 𝔙.cechH1 D) = Submodule.Quotient.mk (0 : ↥(𝔙.cocycles1 D)) from rfl,
        refineH1_mk_eq_iff, ZeroMemClass.coe_zero, sub_zero]
      exact hg
    -- `mk g = 0` ⇔ `g ∈ submoduleOf`, defeq to `↑g ∈ coboundaries1 𝔘 D`.
    exact (Submodule.Quotient.mk_eq_zero
      ((𝔘.coboundaries1 D).submoduleOf (𝔘.cocycles1 D))).1 hmk
  · intro hdesc q hq
    induction q using Submodule.Quotient.induction_on with
    | _ g =>
      rw [show (0 : 𝔙.cechH1 D) = Submodule.Quotient.mk (0 : ↥(𝔙.cocycles1 D)) from rfl,
        refineH1_mk_eq_iff, ZeroMemClass.coe_zero, sub_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      exact hdesc g hq

/-- **Injectivity of `refineH1` from the Leray DESCEND condition** (the direction the iso needs). -/
theorem refineH1_injective_of_descend (hr : IsRefinement 𝔙 𝔘 r)
    (hdesc : RefinementDescend hr D) :
    Function.Injective (hr.refineH1 D) :=
  (refineH1_injective_iff_descend D hr).2 hdesc

/-- **The Leray cover-independence isomorphism (conditional on the analytic inputs).**  Given the
LIFT (surjectivity) and DESCEND (injectivity) conditions for a refinement `𝔙 ⪯ 𝔘`, `refineH1 hr` is a
`ℂ`-linear ISOMORPHISM `cechH1 𝔘 D ≃ₗ[ℂ] cechH1 𝔙 D`.  Sorry-free reduction of the cover-independence
iso to the two honest cocycle-level analytic conditions (which are the disk/overlap-acyclicity content;
see the `## SURJECTIVITY` plan).  For mutually-refining covers use the unconditional `refineH1_equiv`
instead. -/
noncomputable def refineH1_equiv_of_leray (hr : IsRefinement 𝔙 𝔘 r)
    (hlift : RefinementLift hr D) (hdesc : RefinementDescend hr D) :
    𝔘.cechH1 D ≃ₗ[ℂ] 𝔙.cechH1 D :=
  LinearEquiv.ofBijective (hr.refineH1 D)
    ⟨refineH1_injective_of_descend D hr hdesc, refineH1_surjective_of_lift D hr hlift⟩

/-- **The Leray cover-independence isomorphism from function-level acyclicity.**  This is the
refinement-layer endpoint the chart-disk function theorem will ultimately feed: once both the fine and
coarse covers are shown function-level disk-acyclic, the `RefinementLift`/`RefinementDescend` bridge
produces the `cechH1` isomorphism. -/
noncomputable def refineH1_equiv_of_funcLevel (hr : IsRefinement 𝔙 𝔘 r)
    (hlift : FunctionDiskAcyclic 𝔙.toFiniteFamily D) (hdesc : FunctionDiskAcyclic 𝔘.toFiniteFamily D) :
    𝔘.cechH1 D ≃ₗ[ℂ] 𝔙.cechH1 D :=
  refineH1_equiv_of_leray D hr
    (refinementLift_of_funcLevel hr D hlift)
    (refinementDescend_of_funcLevel hr D hdesc)

end IsRefinement
end FiniteCover

/-! ## SURJECTIVITY — the precise plan and the exact remaining obstruction

This file reduces the STEP B Leray cover-independence iso to two cocycle-level analytic conditions:

  * `RefinementLift  hr D`  (surjectivity) — every `𝔙`-cocycle is `refineC1 g + δ⁰η` for a `𝔘`-cocycle
    `g`;  proven equivalent to `Function.Surjective (refineH1 hr)` (`refineH1_surjective_iff_lift`).
  * `RefinementDescend hr D` (injectivity) — a `𝔘`-cocycle whose refinement is a `𝔙`-coboundary is a
    `𝔘`-coboundary;  proven equivalent to `Function.Injective (refineH1 hr)`
    (`refineH1_injective_iff_descend`).

`refineH1_equiv_of_leray` then gives the iso from these two.  Everything above is SORRY-FREE.

For two covers that MUTUALLY refine, `refineH1_equiv` discharges BOTH conditions with NO analysis
(pure STEP A).  The genuinely-analytic gap is only for a STRICTLY-finer Leray refinement `𝔙 ⪯ 𝔘`
(the common-refinement case `exists_cechModel` needs), where there is no back-refinement.

### The standard construction of `RefinementLift` (Forster §12, Leray)

Let `t` be a `𝔙`-cocycle (`𝔙` strictly finer, refinement index `r : 𝔙.ι → 𝔘.ι`).  To build the
`𝔘`-cocycle `g` with `refineC1 g = t + δ⁰η`:

  STEP L1 (per coarse overlap).  Fix a coarse overlap `W = 𝔘.U i ⊓ 𝔘.U j`.  The fine sets
    `{𝔙.U a ⊓ W}_a` cover `W`, and `t` restricted to them is a 1-cocycle for that induced fine cover
    of `W`.  Because `W` is `H¹(𝒪)`-ACYCLIC (a connected/simply-connected overlap of a Leray cover,
    `IsLeray`), this restricted cocycle is a coboundary on `W`: there is a 0-cochain `ζ^{ij}_a` on
    `𝔙.U a ⊓ W` with `t_{ab}|_W = ζ^{ij}_b − ζ^{ij}_a`.
  STEP L2 (assemble the coarse cocycle).  Set `g_{ij} := ζ^{ij}_a − (refine of nothing)` glued across
    `a`; the differences `ζ^{ij}_b − ζ^{ij}_a = t_{ab}` patch to a single germ `g_{ij}` on `W` (the H⁰
    sheaf-gluing on the acyclic `W`).  One checks `δ¹_𝔘 g = 0` and `refineC1 g − t = δ⁰_𝔙 η` with
    `η_a := ζ^{r a, r a}_a` (the diagonal 0-cochain), all by `rawRestrictG`-bookkeeping.
  `RefinementDescend` is the SAME argument one degree down (Forster 12.8): given `refineC1 g = δ⁰_𝔙 η`,
    the per-coarse-overlap acyclicity glues `η` to a 0-cochain `ζ` on the coarse cover with
    `g = δ⁰_𝔘 ζ`.

### What is REACHABLE on top of the proven atoms, and the EXACT obstruction

The disk engine `DbarDiskCohomology.dbar_solvable_ball` / `dbar_holo_splitting_ball` proves
`H¹(𝒪) = 0` for a literal **Euclidean ball in `ℂ`**, at the level of *smooth/holomorphic FUNCTIONS*
(`ℂ → ℂ`).  STEP L1 needs `H¹(W, 𝒪_D) = 0` for an arbitrary coarse overlap `W ⊆ X` as a sheaf
statement at the *germ-class* (`MGerm`) level.  The exact missing pieces (all greenfield, confirmed
absent from Mathlib in the `CechRefinement.lean` PLAN recon):

  OBSTRUCTION 1 — *biholomorphic transport of disk-acyclicity to an abstract overlap.*  `IsLeray`
    gives `SimplyConnectedSpace ↥(𝔘.U i)` and connected overlaps, but NOT a biholomorphism
    `↥W ≃ ball` (that is the Riemann mapping / uniformization theorem, which Mathlib does not have for
    Riemann surfaces).  Without it one cannot pull `dbar_solvable_ball` back to `W`.  The honest fix in
    THIS repo's chart-disk model is to NOT use an abstract Leray `W` but to take `W` itself a chart
    disk — i.e. restate STEP L1 only for the chart-disk cover (the `ChartDiskCover` route already used
    by `CechModelGeometry`), where each cover set / overlap IS a disk in a single chart.  That is the
    "PARTIAL SIDESTEP" of the `CechRefinement.lean` PLAN.

  OBSTRUCTION 2 — *germ-class ↔ holomorphic-function bridge.*  `dbar_holo_splitting_ball` re-splits a
    smooth Čech splitting into a HOLOMORPHIC one as FUNCTIONS on the ball; STEP L1 needs the same at
    the `MGerm`/`OmegaDGerm` level (sections of `𝒪_D` are germ-classes modulo `codiscreteWithin`).
    Bridging is the `CechH0` codiscrete ↔ `𝓝[≠]` dictionary — the SAME bridge `exists_cechModel`'s
    comparison field requires.  This is in `CechH0`/`CechSection` territory (READ-ONLY here) and is not
    re-derivable in this file without duplicating it.

  OBSTRUCTION 3 — *the nested Čech "acyclic ⟹ cocycle is a coboundary" step itself.*  Even granting
    `H¹(disk, 𝒪) = 0` as a clean germ-level atom, STEP L1 turns a fine cocycle ON an overlap into a
    coboundary by a one-dimension-down Leray/Čech computation (a mini cover-independence).  This is
    genuinely a second instance of the same theorem and is the bulk of the "~several hundred LoC on
    top of the disk atom" estimate; it is NOT a quick reduction.

CONCLUSION.  The reduction to `RefinementLift` / `RefinementDescend` is complete and gap-free; the
remaining work is to PRODUCE those two predicates for a chart-disk Leray refinement.  The single most
load-bearing missing lemma is a germ-level *disk-acyclicity atom*

    `H¹(𝔙|_W, 𝒪_D) = 0`  for `W` a chart disk,  i.e.  every `MGerm`-cocycle on a finite fine cover
    of a chart disk `W` is an `MGerm`-coboundary,

obtained by transporting `dbar_holo_splitting_ball` through the `CechH0` germ↔function bridge
(OBSTRUCTION 2) on a literal chart disk (sidestepping OBSTRUCTION 1), then run once per coarse overlap
(OBSTRUCTION 3).  Building that atom requires editing `CechSection`/`CechH0` (out of scope for this
file) or importing a new bridge; hence it is left as written prose, not a tactic gap.  The mutual-
refinement iso `refineH1_equiv` is the unconditional gap-free fallback already delivered.
-/

end Jacobians.Dolbeault
