/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.TauCeti.SheafOfModules.Restriction
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sets.OpenCover

/-!
# Finite local trivializations on compact spaces

On a compact topological space, every local trivialization atlas of a sheaf of modules admits a
finite subatlas. The result retains the actual local isomorphisms, not just the underlying finite
open cover, and is useful when passing from local line-bundle data to finite Čech data.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace TauCeti.SheafOfModules.LocalTrivializations

universe u

variable {T : Type u} [TopologicalSpace T] [CompactSpace T]
  {R : Sheaf (_root_.Opens.grothendieckTopology T) RingCat.{u}}
  [∀ U : Opens T,
    HasWeakSheafify ((_root_.Opens.grothendieckTopology T).over U) AddCommGrpCat.{u}]
  [∀ U : Opens T,
    ((_root_.Opens.grothendieckTopology T).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

omit [CompactSpace T] in
theorem isOpenCover (t : LocalTrivializations M) : IsOpenCover t.X :=
  (_root_.Opens.coversTop_iff (T := T) t.X).mp t.coversTop

/-- The finite set of members chosen from a local trivialization atlas by compactness. -/
def finiteIndexSet (t : LocalTrivializations M) : Finset t.I :=
  Classical.choose t.isOpenCover.exists_finite_of_compactSpace

/-- The opens indexed by `finiteIndexSet` still cover the whole compact space. -/
theorem finiteIndexSet_isOpenCover (t : LocalTrivializations M) :
    IsOpenCover (fun i : t.finiteIndexSet ↦ t.X i.1) :=
  by
    simpa [finiteIndexSet] using
      Classical.choose_spec t.isOpenCover.exists_finite_of_compactSpace

/-- Restrict a local trivialization atlas to a finite subcover. -/
def finiteOfCompact (t : LocalTrivializations M) : LocalTrivializations M :=
  t.ofRefinement
    (fun i : t.finiteIndexSet ↦ t.X i.1)
    (by
      rw [_root_.Opens.coversTop_iff]
      exact t.finiteIndexSet_isOpenCover)
    (fun i ↦ i.1)
    (fun _ ↦ 𝟙 _)

/-- The compact refinement has a finite indexing type. -/
instance (t : LocalTrivializations M) : Finite t.finiteOfCompact.I := by
  unfold finiteOfCompact
  rw [ofRefinement_I]
  infer_instance

end TauCeti.SheafOfModules.LocalTrivializations
