/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.LocallyFinsupp

/-!
# Functions with locally finite support

The topological support of a function with locally finite support is the union of the closures of
the points of its support, and it is finite on a compact space. The functions with locally finite
support whose support lies in a given set form an additive subgroup, the analogue of
`Finsupp.supported`.

## Main definitions

* `Function.locallyFinsupp.supported X Y s`: the functions with locally finite support whose
  support lies in `s`.
* `Function.locallyFinsupp.supported.single x hx y`: the function with value `y` at the point `x`
  of `s`, as an element of `supported X Y s`.

## Main results

* `LocallyFiniteSupport.tsupport_eq_iUnion`, `LocallyFiniteSupport.mem_tsupport_iff`: the
  topological support of a function with locally finite support.
* `Function.locallyFinsupp.finite_support`: finiteness of the support on a compact space, and
  `Function.locallyFinsupp.toFinsuppAddMonoidHom`, the resulting finitely supported function.
-/

@[expose] public section

open Topology

namespace LocallyFiniteSupport

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [Zero Y] {f : X → Y}

/-- The topological support of a function with locally finite support is the union of the
closures of the points of its support. -/
lemma tsupport_eq_iUnion (hf : LocallyFiniteSupport f) :
    tsupport f = ⋃ x ∈ Function.support f, closure {x} := by
  have e := hf.locallyFinite_support.closure_iUnion
  rwa [Set.iUnion_coe_set, Set.iUnion_coe_set, Set.biUnion_of_singleton] at e

/-- A point lies in the topological support of a function with locally finite support iff it is
a specialization of a point of the support. -/
lemma mem_tsupport_iff (hf : LocallyFiniteSupport f) {y : X} :
    y ∈ tsupport f ↔ ∃ x, f x ≠ 0 ∧ x ⤳ y := by
  rw [hf.tsupport_eq_iUnion]
  simp [specializes_iff_mem_closure]

end LocallyFiniteSupport

namespace Function.locallyFinsupp

variable {X : Type*} [TopologicalSpace X] {Y : Type*}

/-- A function with locally finite support on a compact space has finite support; no separation
axiom is needed. -/
lemma finite_support [Zero Y] [CompactSpace X] (D : locallyFinsupp X Y) : D.support.Finite := by
  simpa using D.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ

section CompactSpace

variable [CompactSpace X] [AddMonoid Y]

/-- On a compact space, a function with locally finite support as a finitely supported function;
an additive monoid homomorphism. -/
noncomputable def toFinsuppAddMonoidHom : locallyFinsupp X Y →+ X →₀ Y where
  toFun D := Finsupp.ofSupportFinite D D.finite_support
  map_zero' := Finsupp.ext fun _ ↦ rfl
  map_add' _ _ := Finsupp.ext fun _ ↦ rfl

/-- `toFinsuppAddMonoidHom` does not change the values. -/
@[simp]
lemma toFinsuppAddMonoidHom_apply (D : locallyFinsupp X Y) (x : X) :
    toFinsuppAddMonoidHom D x = D x :=
  rfl

/-- `toFinsuppAddMonoidHom` sends `single x y` to `Finsupp.single x y`. -/
@[simp]
lemma toFinsuppAddMonoidHom_single [DecidableEq X] (x : X) (y : Y) :
    toFinsuppAddMonoidHom (locallyFinsuppWithin.single x y) = Finsupp.single x y :=
  Finsupp.ext fun _ ↦ by simp [Finsupp.single_apply, eq_comm]

end CompactSpace

variable (X Y) [AddGroup Y]

/-- The functions with locally finite support whose support lies in the set `s`, as a subgroup;
this is the analogue of `Finsupp.supported`. -/
def supported (s : Set X) : AddSubgroup (locallyFinsupp X Y) where
  carrier D := D.support ⊆ s
  zero_mem' _ h := (h rfl).elim
  add_mem' {a b} ha hb := (Function.support_add a b).trans (Set.union_subset ha hb)
  neg_mem' {a} ha := (locallyFinsuppWithin.support_neg a).trans_subset ha

variable {X Y}

/-- Membership in `supported X Y s` is containment of the support in `s`. -/
lemma mem_supported {s : Set X} {D : locallyFinsupp X Y} : D ∈ supported X Y s ↔ D.support ⊆ s :=
  Iff.rfl

/-- `supported X Y s` grows with `s`. -/
lemma supported_mono {s t : Set X} (h : s ⊆ t) : supported X Y s ≤ supported X Y t :=
  fun _ hD ↦ Set.Subset.trans hD h

/-- The function `single x y` is supported in `s` iff it is zero or `x ∈ s`. -/
@[simp]
lemma single_mem_supported [DecidableEq X] {s : Set X} {x : X} {y : Y} :
    locallyFinsuppWithin.single x y ∈ supported X Y s ↔ y = 0 ∨ x ∈ s := by
  rw [mem_supported, locallyFinsuppWithin.support, locallyFinsuppWithin.coe_single]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · simp [Pi.support_single_of_ne hy, hy]

/-- Functions supported in disjoint sets have only the zero function in common. -/
lemma disjoint_supported_supported {s t : Set X} (h : Disjoint s t) :
    Disjoint (supported X Y s) (supported X Y t) :=
  AddSubgroup.disjoint_def.2 fun hs ht ↦ locallyFinsuppWithin.ext fun _ ↦
    by_contra fun hx ↦ h.notMem_of_mem_left (hs hx) (ht hx)

open scoped Classical in
/-- The function with value `y` at the point `x` of `s` and `0` elsewhere, as an element of
`supported X Y s`. -/
noncomputable def supported.single {s : Set X} (x : X) (hx : x ∈ s) (y : Y) : supported X Y s :=
  ⟨locallyFinsuppWithin.single x y, single_mem_supported.2 (Or.inr hx)⟩

/-- The values of `supported.single x hx y`: `y` at `x` and `0` elsewhere. -/
@[simp]
lemma supported.single_apply [DecidableEq X] {s : Set X} (x : X) (hx : x ∈ s) (y : Y) (z : X) :
    (supported.single x hx y : locallyFinsupp X Y) z = if z = x then y else 0 := by
  simp [supported.single]

/-- `supported.single x hx 0` is the zero function, whatever the point `x`. -/
@[simp]
lemma supported.single_zero {s : Set X} (x : X) (hx : x ∈ s) :
    supported.single x hx (0 : Y) = 0 := by
  classical
  exact Subtype.ext locallyFinsuppWithin.single_zero

end Function.locallyFinsupp
