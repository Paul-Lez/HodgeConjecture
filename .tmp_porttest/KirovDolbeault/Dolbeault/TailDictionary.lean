/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailUnwind

/-!
# The Čech↔tail dictionary, pinched: `CechTailComparison ↔ UnwindRegularity`

Rung 4 (`TailUnwind.lean`) proved `CechTailComparison 𝔇 g G D → UnwindRegularity G D`
(via the rung-2 Miranda VI.3.6 engine).  This file proves the CONVERSE, making the
dictionary's strength exact: **given the slot frame (`SlotExactK`, `K ≥ 0`), the
Čech↔tail comparison law is EQUIVALENT to the isolation-free §17.7 pole-bound
regularity** (`cechTailComparison_iff_unwindRegularity`).

The converse direction is pure coefficient algebra: the factorization upgrades `fE` to
the `L(K−D)` order bounds (`UnwindRegularity` + `exists_lSysInclMono_eq_iff`), and then
every gap index `m < D b` sits strictly BELOW the slot-product order
`orderW fE b + K b ≥ D b`, so the order-`m` Laurent coefficient vanishes by the kernel
law (`laurentCoeff_eq_zero_iff`) — `tailPairingSlot_eq_zero_of_mem_linearSystem`.

Consequences recorded here:

* `cechTailComparison_concrete_of_isolated` — for the concrete fine-sheaf
  `G = (cousinResidueData_of_witnessR …).toGlobalResidue`, `CechTailComparison` IS a
  theorem at every level `D` satisfying the cover-isolation discipline
  `BadPointsIsolated 𝔇 K D` (via `unwindRegularity_concrete_of_isolated`).
* `K_apply_eq_zero_of_not_isolated` — at any non-cover-isolated point,
  `SeparatesPoles` + `K ≥ 0` force `K b = 0`: the residual (non-isolated) case of the
  unconditional discharge is a SIMPLE-pole case with the slot a unit at `b`
  (route `docs/planning/DICT_ROUTE.md`, discovery D2).

The remaining open core is exactly `UnwindRegularity` for the concrete `G` WITHOUT
`BadPointsIsolated`; the route to it (global-cutoff subtraction, vanish-engine +
one explicit chart-`j₀` correction term) is `docs/planning/DICT_ROUTE.md`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter Module

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace Dolbeault

open FineResidue

variable {𝔇 : ChartDiskCover X} {K : Divisor X}

/-! ## Part 0 — `K = 0` at non-isolated points (discovery D2) -/

/-- **Non-isolated points are `K`-free**: under the pole-separation discipline
(`SeparatesPoles`) and effectivity (`K ≥ 0`), any point lying in two distinct cover sets
has `K b = 0`.  Hence the residual non-isolated case of the §17.7 detection is a clean
SIMPLE-pole case (the `dz`-slot is a unit at `b`). -/
theorem K_apply_eq_zero_of_not_isolated (hsep : SeparatesPoles 𝔇 K)
    (hKeff : ∀ x, 0 ≤ K x) {b : X} (hniso : ¬ ∃ j₀, MLIsolated 𝔇 j₀ b) : K b = 0 := by
  obtain ⟨j, hbj⟩ := FiniteCover.exists_cover_index 𝔇.toFiniteCover b
  have h1 : ∃ i, i ≠ j ∧ b ∈ (𝔇.U i : Set X) := by
    by_contra hc
    exact hniso ⟨j, hbj, fun i hi hbi => hc ⟨i, hi, hbi⟩⟩
  obtain ⟨i, hij, hbi⟩ := h1
  exact le_antisymm (hsep i j hij b ⟨hbi, hbj⟩) (hKeff b)

/-! ## Part 1 — gap slot pairings vanish below the `L(K−D)` bound -/

/-- **Coefficients below the pole bound vanish**: for `f ∈ L(K−D)`, every slot tail
pairing at an index `m < D b` is zero — the slot product has order
`orderW f b + K b ≥ D b > m`, so the order-`m` coefficient vanishes by the kernel law.
This is the easy (converse) half of the Čech↔tail dictionary. -/
theorem tailPairingSlot_eq_zero_of_mem_linearSystem
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hexact : SlotExactK 𝔇 g K) (hKeff : ∀ x, 0 ≤ K x)
    {D : Divisor X} {f : MeromorphicFunction X} (hfD : f ∈ linearSystem (X := X) (K - D))
    {j : 𝔇.toFiniteCover.ι} {b : X} (hb : b ∈ (𝔇.U j : Set X)) {m : ℤ} (hmD : m < D b) :
    tailPairingSlot 𝔇 g j b m f = 0 := by
  obtain ⟨hread, hordread⟩ := MeromorphicFunction.meromorphicAt_centerRead_and_order hb f
  obtain ⟨hgan, hgord⟩ := slot_analyticAt_and_order hexact hb (hKeff b)
  set H : ℂ → ℂ := fun ζ => f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ with hHdef
  have hHmer : MeromorphicAt H (chartMap 𝔇 j b) := by
    have h := hread.mul hgan.meromorphicAt
    exact h
  have hHord : meromorphicOrderAt H (chartMap 𝔇 j b)
      = f.orderW b + ((K b : ℤ) : WithTop ℤ) := by
    rw [show H = (fun ζ => f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ)) * g j from rfl,
      meromorphicOrderAt_mul hread hgan.meromorphicAt, hordread, hgord]
  -- the `L(K−D)` lower bound at `b`: `orderW f b ≥ D b − K b`
  have hlo : ((D b - K b : ℤ) : WithTop ℤ) ≤ f.orderW b := by
    have h1 := hfD b
    have e2 : (-((K - D : Divisor X) b) : WithTop ℤ)
        = ((-((K - D : Divisor X) b) : ℤ) : WithTop ℤ) := rfl
    rw [e2] at h1
    have hKD : (-((K - D : Divisor X) b) : ℤ) = D b - K b := by
      rw [Finsupp.sub_apply]
      ring
    rwa [hKD] at h1
  -- hence the slot product has order `≥ D b`
  have hDb : ((D b : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H (chartMap 𝔇 j b) := by
    rw [hHord]
    have hsum : ((D b - K b : ℤ) : WithTop ℤ) + ((K b : ℤ) : WithTop ℤ)
        = ((D b : ℤ) : WithTop ℤ) := by
      have harith : (D b - K b) + K b = (D b : ℤ) := by ring
      exact_mod_cast congrArg (fun z : ℤ => (z : WithTop ℤ)) harith
    calc ((D b : ℤ) : WithTop ℤ)
        = ((D b - K b : ℤ) : WithTop ℤ) + ((K b : ℤ) : WithTop ℤ) := hsum.symm
      _ ≤ f.orderW b + ((K b : ℤ) : WithTop ℤ) := add_le_add hlo le_rfl
  have hmlt : ((m : ℤ) : WithTop ℤ) < meromorphicOrderAt H (chartMap 𝔇 j b) :=
    lt_of_lt_of_le (by exact_mod_cast hmD) hDb
  show laurentCoeff m H (chartMap 𝔇 j b) = 0
  exact (laurentCoeff_eq_zero_iff hHmer (le_of_lt hmlt)).mpr hmlt

/-! ## Part 2 — the dictionary pinched: `CechTailComparison ↔ UnwindRegularity` -/

/-- **The converse of rung 4**: the isolation-free §17.7 pole-bound regularity implies
the Čech↔tail comparison law — the factorization upgrades `fE` to the `L(K−D)` bounds,
and every gap coefficient sits below the upgraded order. -/
theorem cechTailComparison_of_unwindRegularity
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hexact : SlotExactK 𝔇 g K) (hKeff : ∀ x, 0 ≤ K x)
    (G : GlobalResidue 𝔇.toFiniteCover K) {D : Divisor X}
    (hreg : G.UnwindRegularity D) : CechTailComparison 𝔇 g G D := by
  intro E hED fE lam hfac j b hb m _hmE hmD
  obtain ⟨u, hu⟩ := hreg E hED (Submodule.Quotient.mk fE) lam hfac
  have hfD : (fE : MeromorphicFunction X) ∈ linearSystem (X := X) (K - D) :=
    (exists_lSysInclMono_eq_iff hED fE).mp ⟨u, hu⟩
  exact tailPairingSlot_eq_zero_of_mem_linearSystem hexact hKeff hfD hb hmD

/-- **The dictionary, pinched** (the honest-strength note of `TailUnwind.lean` made
exact): given the slot frame, `CechTailComparison 𝔇 g G D` is EQUIVALENT to
`UnwindRegularity G D` — the open keystone residual is exactly the isolation-free
§17.7 regularity for the concrete fine-sheaf `G`. -/
theorem cechTailComparison_iff_unwindRegularity
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hexact : SlotExactK 𝔇 g K) (hKeff : ∀ x, 0 ≤ K x)
    (G : GlobalResidue 𝔇.toFiniteCover K) (D : Divisor X) :
    CechTailComparison 𝔇 g G D ↔ G.UnwindRegularity D :=
  ⟨fun hcmp => G.unwindRegularity_of_cechTailComparison hexact hKeff hcmp,
    fun hreg => cechTailComparison_of_unwindRegularity hexact hKeff G hreg⟩

/-! ## Part 3 — the concrete fine-sheaf dictionary under the isolation discipline -/

/-- **`CechTailComparison` is a THEOREM for the concrete fine-sheaf residue at every
level `D` whose bad points are cover-isolated** — the per-instance form of the
dictionary, via `unwindRegularity_concrete_of_isolated`.  The unconditional discharge
(dropping `BadPointsIsolated`) is the open core; route in
`docs/planning/DICT_ROUTE.md`. -/
theorem cechTailComparison_concrete_of_isolated [Nonempty X]
    [DecidableEq 𝔇.toFiniteCover.ι] (hsep : SeparatesPoles 𝔇 K)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g)
    (hexact : SlotExactK 𝔇 g K) (hwit : CupMLWitnessR 𝔇 hsep g)
    (hwitness : ExactOrderWitness 𝔇) (hKeff : ∀ x, 0 ≤ K x) (D : Divisor X)
    (hiso : BadPointsIsolated 𝔇 K D) :
    CechTailComparison 𝔇 g ((cousinResidueData_of_witnessR hsep g hg
      (SlotMatchesK_of_exact hexact) hwit).toGlobalResidue) D :=
  cechTailComparison_of_unwindRegularity hexact hKeff _
    (unwindRegularity_concrete_of_isolated hsep hg hexact hwit hwitness hKeff D hiso)

end Dolbeault

end Jacobians

end
