/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Constructions

set_option autoImplicit true

/-! # Preconnectedness of the regular subset on a general compact connected
complex 1-manifold (ZZ154)

This file provides the general-`Y` analogue of
`RegularValueSetConnected.lean`. It packages two purely topological
reductions that downstream consumers (notably `FibreCardOnRegularSubset`
via ZZ134) need:

1.  **Subtype-from-ambient**: an ambient `IsPreconnected (S : Set Y)`
    upgrades to `IsPreconnected (Set.univ : Set ↥S)`. This is a clean
    one-liner via `Subtype.preconnectedSpace`.

2.  **Regular-subset reduction**: parameterised on the standard
    topological fact

    *   for any finite `C : Set Y`, the complement `Cᶜ ⊆ Y` is
        preconnected,

    we deliver, for any finite critical-value set `C`, the
    subtype-preconnectedness conclusion in the literal shape
    `fibre_card_eq_of_locallyConstant_subtype_reg` consumes:
    `IsPreconnected (Set.univ : Set (Cᶜ : Set Y))`.

The mathematical content of (2) — that a connected complex 1-manifold
(equivalently, real 2-manifold) minus finitely many points is
preconnected — is the standard "go around the puncture" path argument.
A full mathlib derivation requires either a chart-by-chart path
construction or a bridge through `IsManifold (𝓘(ℝ, ℝ × ℝ)) ω` /
two-dimensional manifold connectedness, neither of which is in mathlib
v4.29.0. Following the exact pattern of `RegularValueSetConnected.lean`
(ZZ83 for the sphere case), we therefore name this fact as a clean
topological boundary hypothesis here and let downstream consumers
discharge it from whatever sphere/manifold-specific machinery is
available.

No gaps, no `axiom`. -/

@[expose] public section

noncomputable section

open Set Topology

namespace Jacobians.Discharge
namespace Manifold

universe u

/-! ## Subtype-from-ambient bridge -/

/-- **Subtype-preconnectedness from ambient preconnectedness.** If
`S : Set Y` is preconnected as an ambient set, then the universe of the
subtype `↥S` is preconnected. This is the literal shape consumed by
`fibre_card_eq_of_locallyConstant_subtype_reg`. -/
lemma isPreconnected_univ_subtype_of_isPreconnected_set_general
    {Y : Type u} [TopologicalSpace Y]
    {S : Set Y} (h : IsPreconnected S) :
    IsPreconnected (Set.univ : Set S) := by
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace h
  exact isPreconnected_univ

/-! ## Regular-subset reduction -/

/-- **Subtype preconnectedness of `Cᶜ`, given ambient preconnectedness
of `Cᶜ`.** Bare wrapper around the subtype-from-ambient bridge,
specialised to the complement form `Cᶜ` that is the literal output of
`Y \ f(criticalSet f)`. -/
theorem regularSubset_isPreconnected_subtype_of_compl
    {Y : Type u} [TopologicalSpace Y]
    (C : Set Y)
    (h_amb : IsPreconnected (Cᶜ : Set Y)) :
    IsPreconnected (Set.univ : Set ((Cᶜ : Set Y))) :=
  isPreconnected_univ_subtype_of_isPreconnected_set_general h_amb

/-- **Headline structural theorem (parameterised on the topological
hypothesis).** Given that the complement of any finite set in `Y` is
preconnected (the standard "connected complex 1-manifold minus finitely
many points stays connected" fact), the regular subset
`(f(criticalSet f))ᶜ` is preconnected as a subtype, in the exact form
`FibreCardOnRegularSubset` consumes.

The hypothesis `h_topo` is the clean topological boundary: for compact
connected complex 1-manifolds (equivalently real 2-manifolds), this is
known classically; we name it here so the downstream consumer can
compose against it without bringing the chart-by-chart construction
into this file. -/
theorem regularSubset_isPreconnected_of_finite_complement_hypothesis
    {Y : Type u} [TopologicalSpace Y]
    (h_topo : ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y))
    (C : Set Y) (hC_fin : C.Finite) :
    IsPreconnected (Set.univ : Set ((Cᶜ : Set Y))) :=
  regularSubset_isPreconnected_subtype_of_compl C (h_topo C hC_fin)

/-- **Bare ambient form.** The same conclusion as
`regularSubset_isPreconnected_of_finite_complement_hypothesis`, stated
in the ambient `Set Y` form rather than as a subtype. Both shapes are
useful: the ambient form composes with `IsLocallyConstant.of_isOpen`
arguments in `Y`, while the subtype form is what
`fibre_card_eq_of_locallyConstant_subtype_reg` consumes directly. -/
theorem regularSubset_isPreconnected_ambient_of_finite_complement_hypothesis
    {Y : Type u} [TopologicalSpace Y]
    (h_topo : ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y))
    (C : Set Y) (hC_fin : C.Finite) :
    IsPreconnected (Cᶜ : Set Y) :=
  h_topo C hC_fin

end Manifold
end Jacobians.Discharge
