/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.Sets.Closeds

/-!
# Generic points in quasi-sober spaces

Every point of a quasi-sober space is a specialization of the generic point of an irreducible
component, and a closed subset of a quasi-sober space is quasi-sober.
-/

@[expose] public section

open Topology

variable {X : Type*} [TopologicalSpace X] [QuasiSober X]

/-- Every point of a quasi-sober space is a specialization of the generic point of an irreducible
component. -/
lemma genericPoints.exists_specializes (y : X) : ∃ x ∈ genericPoints X, x ⤳ y :=
  ⟨_, (genericPoints.ofComponent ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩).2,
    (genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent⟩

/-- A closed subset of a quasi-sober space is quasi-sober, as an instance for `Closeds`. -/
instance (S : TopologicalSpace.Closeds X) : QuasiSober S :=
  S.isClosed.isClosedEmbedding_subtypeVal.quasiSober
