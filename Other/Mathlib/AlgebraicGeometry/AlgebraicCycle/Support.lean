/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.Topology.Sets.Closeds
public import Other.Mathlib.Topology.LocallyFinsupp

/-!
# The support of an algebraic cycle

The support of an algebraic cycle `c` on a scheme `X` is the topological support `tsupport c`, the
closure of the set of points with a nonzero coefficient, as a closed subset of `X`. It is the union
of the closures of these points, because the set of these points is locally finite.

## Main definitions

* `AlgebraicCycle.closedSupport`: the support of a cycle, as a closed subset of `X`.

## Main results

* `AlgebraicCycle.coe_closedSupport_eq_iUnion`: the support is the union of the closures of the
  points with a nonzero coefficient.
* `AlgebraicCycle.closedSupport_map_le`: the support of a pushforward lies in the closure of the
  image of the support.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}} {R : Type*}

section Zero

variable [Zero R] (c : AlgebraicCycle X R)

/-- The support of an algebraic cycle: the closure of the set of points with a nonzero
coefficient. -/
def closedSupport : Closeds X :=
  Closeds.closure c.support

/-- The underlying set of `c.closedSupport` is the topological support of `c`, by definition. -/
@[simp]
lemma coe_closedSupport : (c.closedSupport : Set X) = tsupport c :=
  rfl

/-- The support of a cycle is the union of the closures of the points with a nonzero coefficient:
these points form a locally finite set, so the closure of their union is the union of their
closures. -/
lemma coe_closedSupport_eq_iUnion : (c.closedSupport : Set X) = ⋃ x ∈ c.support, closure {x} :=
  c.locallyFiniteSupport.tsupport_eq_iUnion

variable {c} in
/-- A point `y` lies in the support of `c` iff some point `x` with a nonzero coefficient
specializes to `y`. Recall that the order on the points of a scheme is the specialization order,
so `y ≤ x` means `x ⤳ y`. -/
lemma mem_closedSupport {y : X} : y ∈ c.closedSupport ↔ ∃ x, c x ≠ 0 ∧ y ≤ x := by
  simp_rw [Scheme.le_iff_specializes]
  exact c.locallyFiniteSupport.mem_tsupport_iff

/-- Every point with a nonzero coefficient lies in the support. -/
lemma support_subset_closedSupport : c.support ⊆ c.closedSupport :=
  subset_tsupport c

variable {c} in
/-- The support of `c` is the smallest closed subset containing every point with a nonzero
coefficient: it lies in a closed subset `S` iff all these points do. -/
lemma closedSupport_le_iff {S : Closeds X} : c.closedSupport ≤ S ↔ c.support ⊆ S :=
  Closeds.closure_le

/-- The closure of a point with a nonzero coefficient lies in the support, as closed subsets. -/
lemma closure_singleton_le_closedSupport {x : X} (h : c x ≠ 0) :
    Closeds.closure {x} ≤ c.closedSupport :=
  Closeds.gc.monotone_l (Set.singleton_subset_iff.2 h)

variable {c} in
/-- A cycle has empty support iff it is zero. -/
@[simp]
lemma closedSupport_eq_bot_iff : c.closedSupport = ⊥ ↔ c = 0 := by
  rw [← Closeds.coe_eq_empty, coe_closedSupport, tsupport_eq_empty_iff]
  exact ⟨fun h ↦ DFunLike.coe_injective h, fun h ↦ h ▸ rfl⟩

/-- The zero cycle has empty support. -/
@[simp]
lemma closedSupport_zero : closedSupport (0 : AlgebraicCycle X R) = ⊥ :=
  closedSupport_eq_bot_iff.2 rfl

/-- The support of the cycle with the single nonzero coefficient `r` at the point `x` is the
closure of `{x}`. The hypothesis `r ≠ 0` is needed: `single x 0 = 0` has empty support. -/
@[simp]
lemma closedSupport_single_of_ne [DecidableEq X] {x : X} {r : R} (h : r ≠ 0) :
    closedSupport (Function.locallyFinsuppWithin.single x r) = Closeds.closure {x} :=
  congrArg Closeds.closure <| Set.ext fun z ↦ by simp [h]

end Zero

/-- The support of a sum of cycles lies in the union of their supports. The inclusion can be
strict, since coefficients may cancel. -/
lemma closedSupport_add_le [AddMonoid R] (c d : AlgebraicCycle X R) :
    (c + d).closedSupport ≤ c.closedSupport ⊔ d.closedSupport :=
  tsupport_add c d

/-- Negating a cycle does not change its support. -/
@[simp]
lemma closedSupport_neg [AddGroup R] (c : AlgebraicCycle X R) :
    (-c).closedSupport = c.closedSupport :=
  Closeds.ext (tsupport_neg c)

section Map

variable [Semiring R] {Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] {N : Type*} [DecidableEq N]
  (wx : X → N) (wy : Y → N) (c : AlgebraicCycle X R)

/-- Every point with a nonzero coefficient in the pushforward `map f wx wy c` is the image of a
point with a nonzero coefficient in `c`. The inclusion can be strict: a coefficient of the
pushforward is a weighted sum over a fibre of `f`, which may vanish. -/
lemma support_map_subset : (map f wx wy c).support ⊆ f.base '' c.support :=
  Function.locallyFinsupp.support_map_subset_of_forall_mem _ _ _ _ _ subset_rfl
    fun x hx _ ↦ ⟨x, hx, rfl⟩

/-- The support of the pushforward of a cycle `c` along `f` lies in the closure of the image of
the points with a nonzero coefficient in `c`, which is also the closure of the image of the support
of `c`. As for `support_map_subset`, the inclusion can be strict. -/
lemma closedSupport_map_le :
    (map f wx wy c).closedSupport ≤ Closeds.closure (f.base '' c.support) :=
  Closeds.gc.monotone_l (support_map_subset f wx wy c)

end Map

end AlgebraicGeometry.AlgebraicCycle
