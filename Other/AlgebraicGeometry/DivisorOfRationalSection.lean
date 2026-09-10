/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ChowGroup
public import HodgeConjecture.Lemmas.AlgebraicGeometry.OrderOfVanishing

/-!
# Divisors of rational functions and of Cartier data

This file constructs the Weil divisor attached to local rational-function data on an integral
Noetherian scheme, as an element of `CodimensionCycle S 1`.

* `Scheme.principalCodimensionOneDivisor S f` is the divisor of a rational function `f`. Its
  local finiteness comes from `Scheme.ord_locallyFiniteSupport` and its purity from the fact
  that `Scheme.ord` is zero at every point whose coheight is not one.
* `Scheme.CartierData S` is an open cover together with a nonzero rational function on each
  member, the functions having equal order of vanishing at every point of every overlap. This
  is the Weil-divisor-relevant part of a Cartier divisor: no comparison of the functions
  themselves is required, only of their orders.
* `Scheme.CartierData.divisor` glues these orders into a codimension-one cycle. Local finiteness
  is inherited from the single-function case on each member of the cover, using that a nonzero
  rational function on a Noetherian integral scheme has globally finite divisor.

Nothing here uses smoothness, projectivity or the complex numbers.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The divisor of a rational function on an integral Noetherian scheme, as a codimension-one
cycle. The zero function gives the zero cycle. -/
def Scheme.principalCodimensionOneDivisor (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S]
    (f : S.functionField) : CodimensionCycle S 1 :=
  ⟨{ toFun := S.ord f
     supportWithinDomain' := by simp
     supportLocallyFiniteWithinDomain' := by
       change ∀ x, x ∈ Set.univ → ∃ t ∈ nhds x, Set.Finite (t ∩ Function.support (S.ord f))
       exact fun x _ ↦ S.ord_locallyFiniteSupport f x },
    by
      intro y hy
      by_contra hcodim
      exact hy (Scheme.ord_eq_zero_of_coheight_neq_one hcodim f)⟩

@[simp]
lemma Scheme.principalCodimensionOneDivisor_apply (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S]
    (f : S.functionField) (x : S) : S.principalCodimensionOneDivisor f x = S.ord f x := rfl

/-- Every nonempty open of an irreducible scheme contains the generic point. -/
lemma Scheme.genericPoint_mem_of_nonempty (S : Scheme.{u}) [IrreducibleSpace S] (U : S.Opens)
    [Nonempty U] : genericPoint S ∈ U := by
  refine ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr ?_
  simpa using Set.nonempty_coe_sort.mp ‹Nonempty ↥U›

/-- Two nonempty opens of an irreducible scheme meet. -/
lemma Scheme.nonempty_inf (S : Scheme.{u}) [IrreducibleSpace S] (U V : S.Opens)
    [Nonempty U] [Nonempty V] : Nonempty ((U ⊓ V : S.Opens)) :=
  ⟨⟨genericPoint S,
    ⟨S.genericPoint_mem_of_nonempty U, S.genericPoint_mem_of_nonempty V⟩⟩⟩

/--
Local data for a divisor: an open cover of `S` by nonempty opens together with a nonzero
rational function on each member, any two of which have the same order of vanishing at every
common point.

This is exactly what is needed to define a Weil divisor; a Cartier divisor in the usual sense
gives such data, the order agreement following from the transition functions being units.
-/
structure Scheme.CartierData (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] where
  /-- The index type of the trivializing cover. -/
  ι : Type u
  /-- The members of the cover. -/
  opens : ι → S.Opens
  /-- Every member of the cover is nonempty, so carries the generic point. -/
  nonempty (i : ι) : Nonempty (opens i)
  /-- The members cover `S`. -/
  covers (x : S) : ∃ i, x ∈ opens i
  /-- The local equation on each member, as a rational function. -/
  fn : ι → S.functionField
  /-- The local equations are nonzero. -/
  fn_ne_zero (i : ι) : fn i ≠ 0
  /-- The local equations have equal order of vanishing on overlaps. -/
  ord_eq (i j : ι) (x : S) (hi : x ∈ opens i) (hj : x ∈ opens j) :
    S.ord (fn i) x = S.ord (fn j) x

namespace Scheme.CartierData

variable {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S] (c : S.CartierData)

/-- Two members of the cover meet, the scheme being irreducible and the members nonempty. -/
lemma nonempty_inf (i j : c.ι) : Nonempty ((c.opens i ⊓ c.opens j : S.Opens)) := by
  have := c.nonempty i
  have := c.nonempty j
  exact S.nonempty_inf _ _

/-- A chosen member of the cover containing a given point. -/
def index (x : S) : c.ι := (c.covers x).choose

lemma mem_opens_index (x : S) : x ∈ c.opens (c.index x) := (c.covers x).choose_spec

/-- The order-of-vanishing function of the local data. -/
def ordFun (x : S) : ℤ := S.ord (c.fn (c.index x)) x

lemma ordFun_eq (i : c.ι) (x : S) (hx : x ∈ c.opens i) : c.ordFun x = S.ord (c.fn i) x :=
  c.ord_eq _ i x (c.mem_opens_index x) hx

lemma ordFun_eq_zero_of_coheight_ne_one {x : S} (hx : coheight x ≠ 1) : c.ordFun x = 0 :=
  Scheme.ord_eq_zero_of_coheight_neq_one hx _

/-- The Weil divisor of the local data, as a codimension-one cycle. -/
def divisor : CodimensionCycle S 1 :=
  ⟨{ toFun := c.ordFun
     supportWithinDomain' := by simp
     supportLocallyFiniteWithinDomain' := by
       change ∀ x, x ∈ Set.univ → ∃ t ∈ nhds x, Set.Finite (t ∩ Function.support c.ordFun)
       intro x _
       refine ⟨(c.opens (c.index x)).carrier,
         (c.opens (c.index x)).isOpen.mem_nhds (c.mem_opens_index x), ?_⟩
       refine Set.Finite.subset
         (S.ord_support_finite (c.fn (c.index x)) (c.fn_ne_zero (c.index x))) ?_
       rintro y ⟨hyU, hy⟩
       rw [Function.mem_support] at hy ⊢
       rwa [c.ordFun_eq (c.index x) y hyU] at hy },
    by
      intro y hy
      by_contra hcodim
      exact hy (c.ordFun_eq_zero_of_coheight_ne_one hcodim)⟩

@[simp]
lemma divisor_apply (x : S) : c.divisor x = c.ordFun x := rfl

lemma divisor_apply_of_mem (i : c.ι) (x : S) (hx : x ∈ c.opens i) :
    c.divisor x = S.ord (c.fn i) x := c.ordFun_eq i x hx

/-- A single nonzero rational function is Cartier data on the trivial cover. -/
def ofFunctionField (f : S.functionField) (hf : f ≠ 0) : S.CartierData where
  ι := PUnit.{u + 1}
  opens _ := ⊤
  nonempty _ := ⟨⟨(genericPoint S), trivial⟩⟩
  covers _ := ⟨PUnit.unit, trivial⟩
  fn _ := f
  fn_ne_zero _ := hf
  ord_eq _ _ _ _ _ := rfl

@[simp]
lemma ofFunctionField_divisor (f : S.functionField) (hf : f ≠ 0) :
    (ofFunctionField f hf).divisor = S.principalCodimensionOneDivisor f := by
  refine CodimensionCycle.ext fun x ↦ ?_
  change (ofFunctionField f hf).ordFun x = S.ord f x
  exact (ofFunctionField f hf).ordFun_eq PUnit.unit x trivial

end Scheme.CartierData

end AlgebraicGeometry
