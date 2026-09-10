/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailRegularity

/-!
# Re-pointing the §17.9 chain at the Laurent-tail regularity (rung 4)

`GlobalResidue.UnwindRegularity` (`SerreUnwind.lean`) is the single isolated analytic input of
the §17.9 surjectivity chain (`pairing_surjective_of_globalResidue`).  Its geometric content —
Forster §17.7 / Miranda VI.3.6 pole-bound regularity — is now a THEOREM in the tail frame
(`tailRegularitySlot_lSysInclMono`, rung 2, unconditional).  This file re-points the chain:

* `CechTailComparison` — the **restated chain input**: a pure functional-comparison law with
  NO regularity content.  It says only that when the level-`E` Čech residue functional of `v`
  factors through `H¹(𝒪_E) → H¹(𝒪_D)`, the slot tail pairings of `v` vanish on the gap window
  `E b ≤ m < D b`.  This is the Čech↔tail dictionary (each gap monomial tail is realized by a
  one-point Čech cocycle that is a coboundary at level `D`, so the factored functional kills
  it; `SerreUnwindDetect` proves the isolated-marked-point instance).  The Miranda 3.6
  pole-bound upgrade is NOT assumed — it is supplied by rung 2.
* `GlobalResidue.unwindRegularity_of_cechTailComparison` — `CechTailComparison` (+ the slot
  frame `SlotExactK`, `K ≥ 0`) ⟹ `UnwindRegularity G D`, by `tailRegularitySlot_lSysInclMono`.
* `pairing_surjective_of_cechTailComparison` — the end-to-end §17.9 surjectivity with the
  re-pointed input: `Function.Surjective (G.toSerreResidueRealization.pairing D)` from
  {`GlobalResidue`, `LocallyRealizable`, `SlotExactK`, `K ≥ 0`, `CechTailComparison`}.

## Honest comparison of strength

`CechTailComparison` is NOT literally weaker than `UnwindRegularity` as a bare proposition —
it is a *different factorization* of the same input: the (now proven) geometric regularity has
been subtracted out, and what remains is exactly the evaluation dictionary between the Čech
residue functional and the Laurent-tail pairing.  Both walls of the Čech-side discharge
(`docs/planning/UNWIND_BLOCKER.md`) live entirely inside this dictionary; the surrounding
chain is theorem.  Status and the remaining bridge are documented in
`docs/planning/TAIL_BLOCKER.md`.
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

/-- **The re-pointed §17.9 chain input — the Čech↔tail comparison law.**  If the level-`E`
Čech residue functional of `fE ∈ L(K−E)` factors through the monotone inclusion
`H¹(𝒪_E) → H¹(𝒪_D)` (`E ≤ D`), then all slot tail pairings of `fE` vanish on the gap window
`E b ≤ m < D b`, in every cover chart.

This is a pure FUNCTIONAL-COMPARISON statement: it carries none of the §17.7 pole-bound
regularity content (that is the rung-2 theorem `tailRegularitySlot_lSysInclMono`).  Its
discharge for the concrete fine-sheaf `GlobalResidue` is the evaluation of the Čech residue
on the one-point monomial test cocycles — the isolated-marked-point case is proven
(`resCocycle_cup_testCocycle_ne_zero`, `SerreUnwindDetect.lean`); the general case is the
multi-chart evaluation of `docs/planning/UNWIND_BLOCKER.md` / `docs/planning/TAIL_BLOCKER.md`. -/
def CechTailComparison (𝔇 : ChartDiskCover X) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    {K : Divisor X} (G : GlobalResidue 𝔇.toFiniteCover K) (D : Divisor X) : Prop :=
  ∀ (E : Divisor X) (hED : ∀ x, E x ≤ D x) (fE : ↥(linearSystem (X := X) (K - E)))
    (lam : Module.Dual ℂ (𝔇.toFiniteCover.cechH1 D)),
    G.pairing E (Submodule.Quotient.mk fE)
        = lam ∘ₗ 𝔇.toFiniteCover.h1InclMono hED →
    ∀ (j : 𝔇.toFiniteCover.ι) (b : X), b ∈ (𝔇.U j : Set X) → ∀ m : ℤ,
      E b ≤ m → m < D b → tailPairingSlot 𝔇 g j b m (fE : MeromorphicFunction X) = 0

/-- **`UnwindRegularity` from the Čech↔tail comparison** (rung 4): the comparison law plus the
slot frame (`SlotExactK`, `K ≥ 0`) imply the §17.7 pole-bound regularity at `D` — the Miranda
VI.3.6 content is supplied unconditionally by rung 2 (`tailRegularitySlot_lSysInclMono`),
with no cover-isolation discipline (`BadPointsIsolated`) anywhere. -/
theorem GlobalResidue.unwindRegularity_of_cechTailComparison
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hexact : SlotExactK 𝔇 g K) (hKeff : ∀ x, 0 ≤ K x)
    (G : GlobalResidue 𝔇.toFiniteCover K) {D : Divisor X}
    (hcmp : CechTailComparison 𝔇 g G D) : G.UnwindRegularity D := by
  intro E hED v lam hfac
  obtain ⟨fE, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  exact tailRegularitySlot_lSysInclMono hexact hKeff hED fE
    (hcmp E hED fE lam hfac)

/-- **§17.9 surjectivity, re-pointed end-to-end form**: the assembled Serre residue pairing is
SURJECTIVE at `D` from {global residue functional, local realizability, slot frame,
Čech↔tail comparison} — `UnwindRegularity` no longer appears as an input; its geometric heart
is the rung-2 theorem. -/
theorem pairing_surjective_of_cechTailComparison
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hexact : SlotExactK 𝔇 g K) (hKeff : ∀ x, 0 ≤ K x)
    (G : GlobalResidue 𝔇.toFiniteCover K) (D : Divisor X) (P : X)
    (hR : 𝔇.toFiniteCover.LocallyRealizable)
    (hcmp : CechTailComparison 𝔇 g G D) :
    Function.Surjective (G.toSerreResidueRealization.pairing D) :=
  pairing_surjective_of_globalResidue G D P hR
    (G.unwindRegularity_of_cechTailComparison hexact hKeff hcmp)

end Dolbeault

end Jacobians

end
