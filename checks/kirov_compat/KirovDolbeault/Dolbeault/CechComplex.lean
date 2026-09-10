/-
  Dolbeault ladder — the concrete Čech complex and `H¹`, on a fixed finite cover.

  Design note (a module-instance diamond, found while
  building this): if the cochain spaces are `Π p, ↥(OmegaD D …)` (products of submodule-coes of
  function spaces), the quotient `↥(ker δ¹) ⧸ …` fails `HasQuotient` synthesis — two defeq-but-not-
  syntactic `Module ℂ (↥U → ℂ)` paths (`Pi.module` vs the algebra-induced one) clash through the
  `Submodule.module` layer (cf. `reference_module_real_diamond`). Fix (and the standard Čech setup):
  the cochains are *raw* functions `Π p, (↥… → ℂ)` (a clean, diamond-free `ℂ`-module), and the sheaf
  condition `𝒪_D` is carried as a `Submodule` *within* that ambient. `H¹` is then a quotient over a
  submodule-coe of the raw function-Pi, which is diamond-free.

  Light scaffolding: definitions + `δ² = 0` and the dimensions, with the analytic content isolated
  downstream. The only remaining gaps reachable from here are the two mechanical restriction leaves in
  `CechSection` plus `δ² = 0` (also mechanical).
-/
import KirovDolbeault.Dolbeault.CechSection
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A **finite family** of opens of `X` (no covering condition). The Čech complex and `H¹` below are
defined at this level, so they apply both to a genuine `FiniteCover` (covering `X`) and to a family
covering only a chart-disk subregion — the latter is the honest, *inhabited* base for the disk-
acyclicity input (`H¹(disk, 𝒪) = 0`). (Previously the Čech complex lived on `FiniteCover`, whose
`covers = ⊤` made the single-chart `SharedChartCover` uninhabited and the disk-acyclicity vacuous.) -/
structure FiniteFamily (X : Type*) [TopologicalSpace X] where
  ι : Type
  [fintype : Fintype ι]
  U : ι → Opens X

attribute [instance] FiniteFamily.fintype

/-- A finite open **cover** of `X`: a finite family whose sets cover `X`. For the Leray/Stein property
used by finiteness one takes the `U i` to be chart-disks; that refinement is recorded where needed. -/
structure FiniteCover (X : Type*) [TopologicalSpace X] extends FiniteFamily X where
  covers : ⨆ i, U i = ⊤

namespace FiniteFamily

variable (𝔘 : FiniteFamily X) (D : Divisor X)

/-- A finite family is **Leray** (for `𝒪`): each set is simply connected — a simply-connected open
subset of a Riemann surface is biholomorphic to a disk or `ℂ`, hence `H¹(U_i, 𝒪) = 0` (the sets are
`𝒪`-acyclic).

This is *exactly* the hypothesis under which Čech `H¹` computes sheaf cohomology, and no more: every
node of the Riemann–Roch ladder is an `H¹` statement, and for `H¹` Cartan's comparison sequence
`0 → Ȟ¹(𝔘, 𝒪) → H¹(X, 𝒪) → Ȟ⁰(𝔘, ℋ¹(𝒪))` is an isomorphism as soon as the cover SETS are acyclic
(then the presheaf `ℋ¹(𝒪) : U ↦ H¹(U,𝒪)` vanishes on the cover, so `Ȟ⁰(𝔘, ℋ¹) = 0`). Acyclicity of
the *pairwise overlaps* is needed only for `H²` and higher, so it is NOT part of this predicate — it
was dead weight in the ladder (`GoodCover` proves the proven comparison never uses it), and dropping
it makes `LerayCoverExists.exists_lerayCover` UNCONDITIONAL (the chart-ball cover's simply-connected
sets are proven, `chartBallCover_simplyConnected`). The chart-disk cover satisfies this. -/
def IsLeray (𝔘 : FiniteFamily X) : Prop :=
  ∀ i : 𝔘.ι, SimplyConnectedSpace ↥(𝔘.U i)

/-- A finite family covers a specified open `W` when the supremum of its opens is exactly `W`.  This
is the local-cover analogue of `FiniteCover.covers`, used for families such as `{U_i ∩ W}_i` that
cover only an overlap region rather than all of `X`. -/
def CoversOpen (𝔘 : FiniteFamily X) (W : Opens X) : Prop :=
  ⨆ i, 𝔘.U i = W

/-- Restrict a finite family to an open subset `W`, replacing each `U_i` by `U_i ∩ W`.  The result is
still a finite family on `X`; it generally covers only `W`, not all of `X`. -/
def restrictToOpen (𝔘 : FiniteFamily X) (W : Opens X) : FiniteFamily X where
  ι := 𝔘.ι
  fintype := inferInstance
  U i := 𝔘.U i ⊓ W

@[simp] theorem restrictToOpen_U (𝔘 : FiniteFamily X) (W : Opens X) (i : 𝔘.ι) :
    (𝔘.restrictToOpen W).U i = 𝔘.U i ⊓ W :=
  rfl

theorem restrictToOpen_le_left (𝔘 : FiniteFamily X) (W : Opens X) (i : 𝔘.ι) :
    (𝔘.restrictToOpen W).U i ≤ 𝔘.U i :=
  inf_le_left

theorem restrictToOpen_le_right (𝔘 : FiniteFamily X) (W : Opens X) (i : 𝔘.ι) :
    (𝔘.restrictToOpen W).U i ≤ W :=
  inf_le_right

/-- The restricted family covers the part of `W` covered by the original family. -/
theorem iSup_restrictToOpen (𝔘 : FiniteFamily X) (W : Opens X) :
    (⨆ i, (𝔘.restrictToOpen W).U i) = (⨆ i, 𝔘.U i) ⊓ W := by
  simp [restrictToOpen, iSup_inf_eq]

/-- Restricting a genuine cover to `W` gives a local finite family covering `W`. -/
theorem restrictToOpen_covers_of_cover (𝔘 : FiniteCover X) (W : Opens X) :
    (𝔘.toFiniteFamily.restrictToOpen W).CoversOpen W := by
  rw [CoversOpen, iSup_restrictToOpen, 𝔘.covers, top_inf_eq]

/-! ### Cochain spaces — germ-classes (`MGerm`), the junk-free sections (no junk quotient). -/

/-- 0-cochains: a germ-class on each `↥(U i)`. -/
abbrev Cochain0 : Type _ := Π i, MGerm (𝔘.U i)

/-- 1-cochains: a germ-class on each pairwise intersection. -/
abbrev Cochain1 : Type _ := Π p : 𝔘.ι × 𝔘.ι, MGerm (𝔘.U p.1 ⊓ 𝔘.U p.2)

/-- 2-cochains: a germ-class on each triple intersection. -/
abbrev Cochain2 : Type _ := Π t : 𝔘.ι × 𝔘.ι × 𝔘.ι, MGerm (𝔘.U t.1 ⊓ 𝔘.U t.2.1 ⊓ 𝔘.U t.2.2)

/-- Nested germ restriction collapses to a single one (`openIncl` composes; the order proofs are
irrelevant). The cocycle identity that makes `δ² = 0`. -/
theorem rawRestrictG_comp_apply {U V W : Opens X} (h1 : V ≤ U) (h2 : W ≤ V) (f : MGerm U) :
    rawRestrictG h2 (rawRestrictG h1 f) = rawRestrictG (h2.trans h1) f := by
  induction f using Filter.Germ.inductionOn with | _ f => rfl

/-- Čech differential `δ⁰ : C⁰ → C¹`, `(δ⁰f)_{ij} = f_j|_{U_i∩U_j} − f_i|_{U_i∩U_j}`. -/
noncomputable def cechDelta0 : 𝔘.Cochain0 →ₗ[ℂ] 𝔘.Cochain1 :=
  LinearMap.pi fun p =>
    rawRestrictG inf_le_right ∘ₗ LinearMap.proj p.2 - rawRestrictG inf_le_left ∘ₗ LinearMap.proj p.1

/-- Čech differential `δ¹ : C¹ → C²`,
`(δ¹g)_{ijk} = g_{jk}|_{ijk} − g_{ik}|_{ijk} + g_{ij}|_{ijk}`. -/
noncomputable def cechDelta1 : 𝔘.Cochain1 →ₗ[ℂ] 𝔘.Cochain2 :=
  LinearMap.pi fun t =>
    rawRestrictG (le_inf (inf_le_left.trans inf_le_right) inf_le_right) ∘ₗ LinearMap.proj (t.2.1, t.2.2)
      - rawRestrictG (le_inf (inf_le_left.trans inf_le_left) inf_le_right) ∘ₗ LinearMap.proj (t.1, t.2.2)
      + rawRestrictG inf_le_left ∘ₗ LinearMap.proj (t.1, t.2.1)

/-- `δ² = 0`: the alternating sum of restrictions cancels. Nested restrictions collapse
(`rawRestrictG_comp`), so the six terms `g_k − g_j − g_k + g_i + g_j − g_i` pair up and vanish. -/
theorem cechDelta1_comp_cechDelta0 : (𝔘.cechDelta1) ∘ₗ (𝔘.cechDelta0) = 0 := by
  refine LinearMap.ext fun f => ?_
  funext t
  obtain ⟨i, j, k⟩ := t
  simp only [cechDelta0, cechDelta1, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.proj_apply, map_sub, rawRestrictG_comp_apply,
    LinearMap.zero_apply, Pi.zero_apply]
  abel

/-! ### The `𝒪_D` sheaf condition, as submodules of the germ-class cochains. -/

/-- 0-cochains that are `𝒪_D`-sections on each `U i`. -/
def sections0 : Submodule ℂ 𝔘.Cochain0 where
  carrier := {f | ∀ i, f i ∈ OmegaDGerm D (𝔘.U i)}
  add_mem' hf hg i := add_mem (hf i) (hg i)
  zero_mem' _i := Submodule.zero_mem _
  smul_mem' c _f hf i := Submodule.smul_mem _ c (hf i)

/-- 1-cochains that are `𝒪_D`-sections on each pairwise intersection. -/
def sections1 : Submodule ℂ 𝔘.Cochain1 where
  carrier := {g | ∀ p, g p ∈ OmegaDGerm D (𝔘.U p.1 ⊓ 𝔘.U p.2)}
  add_mem' hf hg p := add_mem (hf p) (hg p)
  zero_mem' _p := Submodule.zero_mem _
  smul_mem' c _g hg p := Submodule.smul_mem _ c (hg p)

/-- The `𝒪_D` 1-cocycles: `ker δ¹` intersected with the `𝒪_D` sections. -/
noncomputable def cocycles1 : Submodule ℂ 𝔘.Cochain1 :=
  LinearMap.ker 𝔘.cechDelta1 ⊓ 𝔘.sections1 D

/-- The `𝒪_D` 1-coboundaries: the image of the `𝒪_D` 0-sections under `δ⁰`. -/
noncomputable def coboundaries1 : Submodule ℂ 𝔘.Cochain1 :=
  Submodule.map 𝔘.cechDelta0 (𝔘.sections0 D)

/-- **Čech `H¹(𝔘, 𝒪_D) = Z¹/B¹`** — cocycles modulo coboundaries, a `ℂ`-module. The cochains are
germ-classes (`MGerm`, junk-free), so this is the genuine `H¹`; `Z¹/B¹` is the one inherent
cohomology quotient. (`B¹ ⊆ Z¹` by `δ² = 0` + restriction preserving `𝒪_D`.) -/
abbrev cechH1 : Type _ :=
  ↥(𝔘.cocycles1 D) ⧸ (𝔘.coboundaries1 D).submoduleOf (𝔘.cocycles1 D)

/-- `H⁰(𝔘, 𝒪_D)` = global matching `𝒪_D`-sections = `ker δ⁰ ∩ sections`. Junk-free (germ-class
cochains), so `h⁰` below is a plain `finrank` — **no quotient**. -/
noncomputable def globalSections : Submodule ℂ 𝔘.Cochain0 :=
  LinearMap.ker 𝔘.cechDelta0 ⊓ 𝔘.sections0 D

/-- `h⁰(D)` (Forster's `h⁰(X, 𝒪_D)`) — a plain submodule `finrank`, junk already quotiented by `MGerm`. -/
noncomputable def h0Dim : ℕ := Module.finrank ℂ ↥(𝔘.globalSections D)

/-- `h¹(D)` (Forster's `h¹(X, 𝒪_D)`). -/
noncomputable def h1Dim : ℕ := Module.finrank ℂ (𝔘.cechH1 D)

end FiniteFamily

end Jacobians.Dolbeault
