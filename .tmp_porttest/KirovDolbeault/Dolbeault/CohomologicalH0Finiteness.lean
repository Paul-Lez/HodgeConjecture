/-
  Dolbeault ladder — **finiteness of `H⁰(𝔘, 𝒪_D)`** (Forster GTM 81 §14 / §16 compactness),
  for an ARBITRARY finite cover `𝔘` and an ARBITRARY divisor `D`.

  ## What this file proves

      `finiteDimensional_globalSections (𝔘 : FiniteCover X) (D : Divisor X) :
         FiniteDimensional ℂ ↥(𝔘.globalSections D)`

  i.e. `l(D) = h⁰(D) < ∞`.  This is **Gap 1** of `CohomologicalRR.exists_skyscraperLES`: the
  `[FiniteDimensional ℂ H⁰(𝒪_{D+P})]` instance hypothesis that the skyscraper assembly
  (`SkyscraperAssembly.skyscraperLES_of_chartDisk`) previously had to *assume* (no repo lemma existed).
  It is now *derived*.

  ## The argument (the SAME light skyscraper reduction used for `H¹` in `CechFinitenessDtwist`)

  `globalSections D = ker δ⁰ ⊓ sections0 D` is a *submodule* (no quotient — `H⁰` is junk-free).  Adding
  a point `P` only weakens the order bound, so `globalSections D ≤ globalSections (D+P)`, and the
  correction quotient

      `globalSections (D+P) ⧸ globalSections D`

  injects into the finite-dimensional section quotient `sections0 (D+P) ⧸ sections0 D`
  (`CechFinitenessDtwist.finiteDimensional_sections0_quotient`, a finite product of ≤ 1-dimensional
  principal-part stalk quotients) via `finiteDimensional_inf_quotient` (with `K = ker δ⁰`).  Hence
  finiteness of `H⁰` propagates *both ways* along the inclusion `globalSections D ↪ globalSections (D+P)`:

    * **forward** (`H⁰(D)` finite ⟹ `H⁰(D+P)` finite): `H⁰(D+P)` is the extension of the finite
      submodule `H⁰(D)` by the finite correction quotient (`Module.Finite.of_submodule_quotient`);
    * **backward** (`H⁰(D+P)` finite ⟹ `H⁰(D)` finite): a submodule of a finite-dimensional space.

  The bidirectional per-point step then drives the standard `Int.induction_on` (a single point, `±1`
  at a time) + `Finsupp.induction` (one point at a time) on the divisor, with **base** `D = 0`:
  `H⁰(0)` is finite because `finrank ℂ H⁰(0) = h0Dim 0 = l(0) = 1 > 0`
  (`h0Dim_eq_lDim` + `lDim_zero_eq_one`, Liouville), via `FiniteDimensional.of_finrank_pos`.

  Everything is complete; `#print axioms finiteDimensional_globalSections` is
  `[propext, Classical.choice, Quot.sound]`.
-/
import KirovDolbeault.Dolbeault.CechFinitenessDtwist
import KirovDolbeault.Dolbeault.CechH0

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily

variable (𝔘 : FiniteCover X) (D : Divisor X) (P : X)

/-! ### Order-weakening inclusions (the H⁰ analogue of the `CohomologicalRR` `_le_add_single` facts) -/

/-- The `𝒪_D`-functions on `U` are contained in the `𝒪_{D+P}`-functions (adding the effective point
`P` only weakens the order bound `−(D+P) ≤ −D`). -/
theorem OmegaD_le_add_single (U : Opens X) :
    OmegaD D U ≤ OmegaD (D + Finsupp.single P 1) U := by
  classical
  refine fun g hg => ⟨hg.1, fun x => le_trans ?_ (hg.2 x)⟩
  exact_mod_cast neg_le_neg (by
    rw [Finsupp.add_apply, Finsupp.single_apply]; split <;> omega :
      (D : Divisor X) x.1 ≤ (D + Finsupp.single P 1 : Divisor X) x.1)

/-- The `𝒪_D` 0-sections are contained in the `𝒪_{D+P}` 0-sections. -/
theorem sections0_le_add_single' :
    𝔘.sections0 D ≤ 𝔘.sections0 (D + Finsupp.single P 1) :=
  fun _ hf i => Submodule.map_mono (OmegaD_le_add_single D P (𝔘.U i)) (hf i)

/-- The global `𝒪_D`-sections are contained in the global `𝒪_{D+P}`-sections (same `ker δ⁰`, weaker
sheaf condition). -/
theorem globalSections_le_add_single' :
    𝔘.globalSections D ≤ 𝔘.globalSections (D + Finsupp.single P 1) :=
  inf_le_inf_left _ (𝔘.sections0_le_add_single' D P)

/-! ### The H⁰ correction quotient is finite-dimensional -/

/-- **`globalSections (D+P) ⧸ globalSections D` is finite-dimensional.**  `globalSections = ker δ⁰ ⊓
sections0`, so the quotient injects (via `K = ker δ⁰`) into the finite section quotient
`sections0 (D+P) ⧸ sections0 D` (`finiteDimensional_inf_quotient`,
`finiteDimensional_sections0_quotient`). -/
theorem finiteDimensional_globalSections_quotient :
    FiniteDimensional ℂ
      (𝔘.globalSections (D + Finsupp.single P 1) ⧸
        (𝔘.globalSections D).submoduleOf (𝔘.globalSections (D + Finsupp.single P 1))) :=
  finiteDimensional_inf_quotient (LinearMap.ker 𝔘.cechDelta0) (𝔘.sections0 D)
    (𝔘.sections0 (D + Finsupp.single P 1)) (𝔘.sections0_le_add_single' D P)
    (𝔘.finiteDimensional_sections0_quotient D P)

/-! ### The per-point step (both directions) -/

/-- **Forward per-point step.**  `H⁰(𝒪_D)` finite ⟹ `H⁰(𝒪_{D+P})` finite.  `H⁰(𝒪_{D+P})` is the
extension of the finite submodule `H⁰(𝒪_D)` (via the order-weakening inclusion) by the finite
correction quotient `globalSections (D+P) ⧸ globalSections D`
(`Module.Finite.of_submodule_quotient`). -/
theorem finiteDimensional_globalSections_add_single_of
    (h : FiniteDimensional ℂ ↥(𝔘.globalSections D)) :
    FiniteDimensional ℂ ↥(𝔘.globalSections (D + Finsupp.single P 1)) := by
  haveI := h
  -- View `H⁰(D)` as the submodule `N = (globalSections D).submoduleOf (globalSections (D+P))` of
  -- `H⁰(D+P)`; it is `≃ₗ` to `H⁰(D)` (`comapSubtypeEquivOfLe`), hence finite.
  haveI hN : FiniteDimensional ℂ
      ↥((𝔘.globalSections D).submoduleOf (𝔘.globalSections (D + Finsupp.single P 1))) :=
    Module.Finite.equiv
      (Submodule.comapSubtypeEquivOfLe (𝔘.globalSections_le_add_single' D P)).symm
  -- The quotient `H⁰(D+P) ⧸ N` is the finite correction quotient.
  haveI hQ := 𝔘.finiteDimensional_globalSections_quotient D P
  -- `H⁰(D+P)` is the extension of `N` (finite) by the finite quotient.
  exact Module.Finite.of_submodule_quotient
    ((𝔘.globalSections D).submoduleOf (𝔘.globalSections (D + Finsupp.single P 1)))

/-- **Backward per-point step.**  `H⁰(𝒪_{D+P})` finite ⟹ `H⁰(𝒪_D)` finite: `H⁰(𝒪_D)` is (via the
order-weakening inclusion, injective) a submodule of the finite-dimensional `H⁰(𝒪_{D+P})`. -/
theorem finiteDimensional_globalSections_of_add_single
    (h : FiniteDimensional ℂ ↥(𝔘.globalSections (D + Finsupp.single P 1))) :
    FiniteDimensional ℂ ↥(𝔘.globalSections D) :=
  haveI := h
  FiniteDimensional.of_injective
    (Submodule.inclusion (𝔘.globalSections_le_add_single' D P))
    (Submodule.inclusion_injective _)

/-- **The bidirectional per-point step.**  `H⁰(𝒪_{D+P})` is finite iff `H⁰(𝒪_D)` is. -/
theorem finiteDimensional_globalSections_add_single_iff :
    FiniteDimensional ℂ ↥(𝔘.globalSections (D + Finsupp.single P 1)) ↔
      FiniteDimensional ℂ ↥(𝔘.globalSections D) :=
  ⟨𝔘.finiteDimensional_globalSections_of_add_single D P,
    𝔘.finiteDimensional_globalSections_add_single_of D P⟩

/-! ### Divisor induction -/

/-- `H⁰(𝒪_{D + single P k})` is finite iff `H⁰(𝒪_D)` is, for any integer `k` (`Int.induction_on`;
`±1` at a time is the per-point step). -/
theorem finiteDimensional_globalSections_add_singlePoint_iff (k : ℤ) :
    FiniteDimensional ℂ ↥(𝔘.globalSections (D + Finsupp.single P k)) ↔
      FiniteDimensional ℂ ↥(𝔘.globalSections D) := by
  induction k using Int.induction_on with
  | zero => rw [Finsupp.single_zero, add_zero]
  | succ k ih =>
    rw [show (Finsupp.single P ((k : ℤ) + 1) : Divisor X)
        = Finsupp.single P (k : ℤ) + Finsupp.single P 1 from by rw [← Finsupp.single_add],
      ← add_assoc, 𝔘.finiteDimensional_globalSections_add_single_iff (D + Finsupp.single P (k : ℤ)) P]
    exact ih
  | pred k ih =>
    rw [← ih,
      (𝔘.finiteDimensional_globalSections_add_single_iff
        (D + Finsupp.single P (-(k : ℤ) - 1)) P).symm,
      add_assoc, ← Finsupp.single_add, show (-(k : ℤ) - 1 + 1) = -(k : ℤ) from by ring]

/-! ### The base case `D = 0` (Liouville: `h⁰(0) = l(0) = 1 > 0`) -/

/-- **Base case (Liouville).**  `H⁰(𝒪)` is finite-dimensional: `finrank ℂ H⁰(0) = h0Dim 0 = l(0) = 1`
is positive (`h0Dim_eq_lDim` + `lDim_zero_eq_one`), so `FiniteDimensional.of_finrank_pos`. -/
theorem finiteDimensional_globalSections_zero :
    FiniteDimensional ℂ ↥(𝔘.globalSections (0 : Divisor X)) := by
  refine FiniteDimensional.of_finrank_pos ?_
  have h : Module.finrank ℂ ↥(𝔘.globalSections (0 : Divisor X)) = 1 := by
    have := 𝔘.h0Dim_eq_lDim 0
    rw [h0Dim] at this
    rw [this, lDim_zero_eq_one]
  rw [h]; norm_num

/-- **Finiteness of `H⁰(𝒪_D)` for any divisor `D`, on a FIXED cover, from the `D = 0` base** (the
divisor induction).  `Finsupp.induction` on `D` adds one point at a time; each addition is the
single-point step. -/
theorem finiteDimensional_globalSections_of_zero (D : Divisor X) :
    FiniteDimensional ℂ ↥(𝔘.globalSections D) := by
  induction D using Finsupp.induction with
  | zero => exact 𝔘.finiteDimensional_globalSections_zero
  | single_add a b f _ _ ih =>
    rw [add_comm]
    exact (𝔘.finiteDimensional_globalSections_add_singlePoint_iff f a b).mpr ih

end FiniteCover

/-! ### The general theorem (any cover, any divisor) -/

/-- **Finiteness of `H⁰(𝔘, 𝒪_D)` for any cover and any divisor** (Forster §14/§16 compactness;
`l(D) = h⁰(D) < ∞`).  The Liouville base `H⁰(0)` (finrank `1`) is climbed to general `D` one point at
a time via the principal-part skyscraper stalk quotient
(`finiteDimensional_globalSections_of_zero`).  This is **Gap 1** of the χ-additivity skyscraper LES:
the `[FiniteDimensional ℂ H⁰(𝒪_{D+P})]` instance the assembly previously had to assume is now derived.

`#print axioms finiteDimensional_globalSections` → `[propext, Classical.choice, Quot.sound]`. -/
theorem finiteDimensional_globalSections (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ ↥(𝔘.globalSections D) :=
  𝔘.finiteDimensional_globalSections_of_zero D

/-- **Instance form** of `finiteDimensional_globalSections`, so that the skyscraper assembly's
`[FiniteDimensional ℂ H⁰(𝒪_{D+P})]` instance hypothesis is discharged automatically. -/
instance (priority := 100) finiteDimensional_globalSections_instance
    (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ ↥(𝔘.globalSections D) :=
  finiteDimensional_globalSections 𝔘 D

end Jacobians.Dolbeault
