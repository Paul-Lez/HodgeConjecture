/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.AlgebraicCycleSupport
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates

import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothDimensionFormula
import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Other.AlgebraicGeometry.CycleComponentNormalGeometry

/-!
# Exact local coordinates on small-dimensional cycle components

This file proves exact dimension and local-coordinate statements for reduced cycle components in
the cases covered by the pointwise dimension formula: components of dimension zero or one in an
arbitrary smooth complex variety, and all components in ambient relative dimension at most two.

The local coordinates are constructed on the smooth locus of the component.  Their number is
proved to be exactly the dimension of the component, rather than being included as an assumption.
The support library now proves the arbitrary-dimensional catenary formula and the resulting
global dimension of each component.  Extending the coordinate package still requires a local
bridge showing that every closed point of the component has that coheight; that bridge is not
proved here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace RingHom

/-- A standard-smooth ring map is standard smooth of some relative dimension. -/
lemma IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.IsStandardSmooth) :
    ∃ n, f.IsStandardSmoothOfRelativeDimension n := by
  let : Algebra R S := f.toAlgebra
  change Algebra.IsStandardSmooth R S at hf
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hf.out
  refine ⟨P.dimension, ?_⟩
  change Algebra.IsStandardSmoothOfRelativeDimension P.dimension R S
  exact ⟨ι, σ, hσ, hι, P, rfl⟩

end RingHom

namespace AlgebraicGeometry

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ) {f : X ⟶ Spec ↧ℂ} {d p : ℕ}

/-- A component whose generic point has coheight equal to the ambient dimension has dimension
zero. -/
lemma orderKrullDim_cycleComponent_eq_zero_of_coheight_eq_dimension
    [IsIntegral X] [SmoothOfRelativeDimension d f] (x : X)
    (hx : Order.coheight x = d) :
    Order.krullDim (cycleComponent X x) =
      (↑(0 : ℕ∞) : WithBot ℕ∞) := by
  rw [orderKrullDim_cycleComponent]
  have h := SmoothOfRelativeDimension.height_add_coheight_eq_of_coheight_eq_dimension
    (f := f) (d := d) x hx
  rw [hx] at h
  have hheight : Order.height x = 0 := by
    apply bot_unique
    exact (ENat.add_le_add_iff_right (ENat.natCast_ne_top d)).mp (by simpa using h.le)
  rw [hheight]

/-- A component whose generic point has coheight one less than the ambient dimension has
dimension one. -/
lemma orderKrullDim_cycleComponent_eq_one_of_coheight_succ_eq_dimension
    [IsIntegral X] [SmoothOfRelativeDimension d f] (x : X)
    (hx : Order.coheight x = p) (hd : p + 1 = d) :
    Order.krullDim (cycleComponent X x) =
      (↑(1 : ℕ∞) : WithBot ℕ∞) := by
  rw [orderKrullDim_cycleComponent]
  have h :=
    SmoothOfRelativeDimension.height_add_coheight_eq_of_coheight_succ_eq_dimension
      (f := f) (d := d) x hx hd
  rw [hx] at h
  have hheight : Order.height x = 1 := by
    have hpfin : (p : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top p
    apply ENat.add_left_injective_of_ne_top hpfin
    calc
      Order.height x + (p : ℕ∞) = d := h
      _ = (1 : ℕ∞) + p := by
        exact_mod_cast (by lia : d = 1 + p)
  rw [hheight]

/-- In ambient relative dimension at most two, a component of coheight `p` has dimension exactly
`d - p`. -/
lemma orderKrullDim_cycleComponent_eq_sub_of_le_two
    [IsIntegral X] [SmoothOfRelativeDimension d f] (x : X)
    (hx : Order.coheight x = p) (hd : d ≤ 2) :
    Order.krullDim (cycleComponent X x) = d - p := by
  rw [orderKrullDim_cycleComponent]
  have h := SmoothOfRelativeDimension.height_add_coheight_eq_of_le_two
    (f := f) (d := d) hd x
  rw [hx] at h
  have hp : p ≤ d := by
    have hp' := SmoothOfRelativeDimension.coheight_le_complex
      (f := f) (d := d) x
    rw [hx] at hp'
    exact_mod_cast hp'
  have hheight : Order.height x = d - p := by
    apply ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top p)
    calc
      Order.height x + (p : ℕ∞) = d := h
      _ = (d - p : ℕ) + p := by
        exact_mod_cast (Nat.sub_add_cancel hp).symm
  rw [hheight]
  have hcast : ((d - p : ℕ) : ℕ∞) = (d : ℕ∞) - (p : ℕ∞) :=
    ENat.natCast_sub d p
  exact congrArg (fun n : ℕ∞ ↦ (↑n : WithBot ℕ∞)) hcast.symm

/-- A closed point of a zero-dimensional cycle component has coheight zero in the component. -/
lemma coheight_eq_zero_of_isClosed_of_cycleComponent_orderKrullDim_eq_zero
    (x : X) (z : cycleComponent X x) (_hz : IsClosed {z})
    (hdim : Order.krullDim (cycleComponent X x) =
      (↑(0 : ℕ∞) : WithBot ℕ∞)) :
    Order.coheight z = 0 := by
  have hle : (Order.coheight z : WithBot ℕ∞) ≤ (↑(0 : ℕ∞) : WithBot ℕ∞) := by
    simpa only [hdim] using Order.coheight_le_krullDim z
  exact bot_unique (WithBot.coe_le_coe.mp hle)

/-- A closed point of a one-dimensional integral cycle component has coheight one in the
component. -/
lemma coheight_eq_one_of_isClosed_of_cycleComponent_orderKrullDim_eq_one
    (x : X) (z : cycleComponent X x) (hz : IsClosed {z})
    (hdim : Order.krullDim (cycleComponent X x) =
      (↑(1 : ℕ∞) : WithBot ℕ∞)) :
    Order.coheight z = 1 := by
  have hzmin : IsMin z := by
    intro y hy
    have hy' : y ∈ closure {z} := by
      rw [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
      exact hy
    rw [hz.closure_eq] at hy'
    exact (Set.mem_singleton_iff.mp hy').ge
  have hztop : z < (⊤ : cycleComponent X x) := by
    rw [lt_iff_le_not_ge]
    refine ⟨le_top, fun htopz ↦ ?_⟩
    have heq : z = (⊤ : cycleComponent X x) := by
      apply inseparable_iff_eq.mp
      rw [inseparable_iff_specializes_and, ← Scheme.le_iff_specializes,
        ← Scheme.le_iff_specializes]
      exact ⟨htopz, le_top⟩
    have hheightZero : Order.height (⊤ : cycleComponent X x) = 0 := by
      rw [← heq]
      exact Order.IsMin.height_eq_zero hzmin
    have hheightTop :
        (↑(Order.height (⊤ : cycleComponent X x)) : WithBot ℕ∞) =
          (↑(1 : ℕ∞) : WithBot ℕ∞) := by
      rw [Order.height_top_eq_krullDim, hdim]
    rw [hheightZero] at hheightTop
    norm_num at hheightTop
  have hpos : 0 < Order.coheight z := Order.coheight_pos_of_lt_top hztop
  have hle : (Order.coheight z : WithBot ℕ∞) ≤
      (↑(1 : ℕ∞) : WithBot ℕ∞) := by
    simpa only [hdim] using Order.coheight_le_krullDim z
  have hle' : Order.coheight z ≤ 1 := WithBot.coe_le_coe.mp (by simpa using hle)
  exact le_antisymm hle' (Order.one_le_iff_pos.mpr hpos)

/-- A closed point of an integral smooth complex `d`-fold has coheight `d`. -/
lemma SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
    [IsIntegral X] [SmoothOfRelativeDimension d f] (x : X) (hx : IsClosed {x}) :
    Order.coheight x = d := by
  have hxmin : IsMin x := by
    intro y hy
    have hy' : y ∈ closure {x} := by
      rw [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
      exact hy
    rw [hx.closure_eq] at hy'
    exact (Set.mem_singleton_iff.mp hy').ge
  have h := SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed
    (f := f) (d := d) x hx
  rw [Order.IsMin.height_eq_zero hxmin, zero_add] at h
  exact h

/-- In ambient dimension at most two, a closed point of a reduced component of coheight `p` has
coheight exactly `d - p` inside that component. -/
lemma cycleComponent_closedPoint_coheight_eq_sub_of_le_two
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] [SmoothOfRelativeDimension d structureMap]
    (x : X) (z : ComplexPoint (cycleComponent X x)
      (cycleComponentι X x ≫ structureMap))
    (hx : Order.coheight x = p) (hd : d ≤ 2) :
    Order.coheight z.underlying = d - p := by
  have hp : p ≤ d := cycleComponent_codimension_le structureMap x hx
  have hzclosed : IsClosed {z.underlying} :=
    cycleComponent_complexPoint_underlying_isClosed structureMap x z
  have hcases :
      (d = 0 ∧ p = 0) ∨
      (d = 1 ∧ p = 0) ∨ (d = 1 ∧ p = 1) ∨
      (d = 2 ∧ p = 0) ∨ (d = 2 ∧ p = 1) ∨ (d = 2 ∧ p = 2) := by
    lia
  rcases hcases with h00 | h10 | h11 | h20 | h21 | h22
  · obtain ⟨rfl, rfl⟩ := h00
    exact coheight_eq_zero_of_isClosed_of_cycleComponent_orderKrullDim_eq_zero
      x z.underlying hzclosed
        (orderKrullDim_cycleComponent_eq_zero_of_coheight_eq_dimension
          (f := structureMap) (d := 0) x hx)
  · obtain ⟨rfl, rfl⟩ := h10
    exact coheight_eq_one_of_isClosed_of_cycleComponent_orderKrullDim_eq_one
      x z.underlying hzclosed
        (orderKrullDim_cycleComponent_eq_one_of_coheight_succ_eq_dimension
          (f := structureMap) (d := 1) (p := 0) x hx rfl)
  · obtain ⟨rfl, rfl⟩ := h11
    exact coheight_eq_zero_of_isClosed_of_cycleComponent_orderKrullDim_eq_zero
      x z.underlying hzclosed
        (orderKrullDim_cycleComponent_eq_zero_of_coheight_eq_dimension
          (f := structureMap) (d := 1) x hx)
  · obtain ⟨rfl, rfl⟩ := h20
    have hxgeneric : x = genericPoint X :=
      CodimensionCycle.eq_genericPoint_of_coheight_zero x hx
    subst x
    let e : cycleComponent X (genericPoint X) ≃o X :=
      (cycleComponentOrderIsoIic X (genericPoint X)).trans OrderIso.IicTop
    have he : Order.coheight (e z.underlying) = Order.coheight z.underlying :=
      Order.coheight_orderIso e z.underlying
    have he_apply : e z.underlying =
        cycleComponentι X (genericPoint X) z.underlying := by
      rfl
    rw [he_apply] at he
    have hambient : Order.coheight
        (cycleComponentι X (genericPoint X) z.underlying) = 2 :=
      SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
        (f := structureMap) (d := 2)
          (cycleComponentι X (genericPoint X) z.underlying)
          (cycleComponent_complexPoint_ambient_underlying_isClosed
            structureMap (genericPoint X) z)
    rw [hambient] at he
    exact he.symm
  · obtain ⟨rfl, rfl⟩ := h21
    exact coheight_eq_one_of_isClosed_of_cycleComponent_orderKrullDim_eq_one
      x z.underlying hzclosed
        (orderKrullDim_cycleComponent_eq_one_of_coheight_succ_eq_dimension
          (f := structureMap) (d := 2) (p := 1) x hx rfl)
  · obtain ⟨rfl, rfl⟩ := h22
    exact coheight_eq_zero_of_isClosed_of_cycleComponent_orderKrullDim_eq_zero
      x z.underlying hzclosed
        (orderKrullDim_cycleComponent_eq_zero_of_coheight_eq_dimension
          (f := structureMap) (d := 2) x hx)

/-- Separate exact local coordinates on a smooth cycle component and on its smooth ambient
variety.  The component coordinates use exactly `n` variables.  This package does not assert
that the two coordinate systems straighten the closed immersion simultaneously. -/
structure CycleComponentSeparateLocalCoordinates
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (x : X) (d n : ℕ)
    [SmoothOfRelativeDimension d structureMap] where
  /-- A complex point of the reduced component. -/
  point : ComplexPoint (cycleComponent X x)
    (cycleComponentι X x ≫ structureMap)
  /-- The point lies in the component's smooth locus. -/
  point_mem_smoothLocus : point.underlying ∈
    (cycleComponentι X x ≫ structureMap).smoothLocus
  /-- The underlying point is closed in the component. -/
  point_isClosed : IsClosed {point.underlying}
  /-- An affine neighborhood in the smooth locus of the component. -/
  componentNeighborhood :
    (cycleComponentι X x ≫ structureMap).smoothLocus.toScheme.Opens
  /-- The component neighborhood is affine. -/
  componentNeighborhood_isAffine : IsAffineOpen componentNeighborhood
  /-- The chosen point belongs to the component neighborhood. -/
  point_mem_componentNeighborhood :
    (⟨point.underlying, point_mem_smoothLocus⟩ :
      (cycleComponentι X x ≫ structureMap).smoothLocus.toScheme) ∈
        componentNeighborhood
  /-- An étale coordinate homomorphism with exactly `n` component coordinates. -/
  componentCoordinateRingHom : MvPolynomial (Fin n) ℂ →+*
    Γ((cycleComponentι X x ≫ structureMap).smoothLocus.toScheme,
      componentNeighborhood)
  /-- The component coordinate map is a homomorphism of complex algebras. -/
  componentCoordinateRingHom_comp_C :
    componentCoordinateRingHom.comp MvPolynomial.C =
      complexRestrictionMap
        ((cycleComponentι X x ≫ structureMap).smoothLocus.ι ≫
          (cycleComponentι X x ≫ structureMap)) componentNeighborhood
  /-- The component coordinate homomorphism is étale. -/
  componentCoordinateRingHom_etale : componentCoordinateRingHom.Etale
  /-- Independently chosen étale coordinates on the ambient `d`-fold. -/
  ambientCoordinates : LocalEtaleCoordinates structureMap d
    (cycleComponentι X x point.underlying)

/-- Exact coheight at closed component points determines the number of coordinates on the smooth
locus.  This is an internal bridge from the dimension calculation to the coordinate package. -/
private lemma nonempty_cycleComponentSeparateLocalCoordinates_of_closedPoint_coheight
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (x : X) (d n : ℕ)
    [SmoothOfRelativeDimension d structureMap]
    (hcoheight : ∀ z : ComplexPoint (cycleComponent X x)
      (cycleComponentι X x ≫ structureMap),
      Order.coheight z.underlying = n) :
    Nonempty (CycleComponentSeparateLocalCoordinates structureMap x d n) := by
  let c : cycleComponent X x ⟶ Spec ↧ℂ :=
    cycleComponentι X x ≫ structureMap
  let S : (cycleComponent X x).Opens := c.smoothLocus
  let g : S.toScheme ⟶ Spec ↧ℂ := S.ι ≫ c
  let : Smooth g := by
    exact cycleComponent_smoothLocus_smooth structureMap x
  obtain ⟨z, hzsmooth, hzclosed⟩ :=
    exists_cycleComponent_smooth_closed_complexPoint structureMap x
  let zs : S.toScheme := ⟨z.underlying, hzsmooth⟩
  obtain ⟨W, hW, hzsW, hstandard⟩ := Smooth.exists_affine_isStandardSmooth g zs
  have hstandardComplex : (complexRestrictionMap g W).IsStandardSmooth :=
    complexRestrictionMap_isStandardSmooth g hstandard
  obtain ⟨m, hm⟩ :=
    hstandardComplex.exists_isStandardSmoothOfRelativeDimension
  have hzsClosed : IsClosed {zs} := by
    have hpreimage : S.ι ⁻¹' ({z.underlying} : Set (cycleComponent X x)) =
        ({zs} : Set S.toScheme) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
    exact hpreimage ▸ hzclosed.preimage S.ι.continuous
  let zw : W.toScheme := ⟨zs, hzsW⟩
  let P : Ideal Γ(S, W) := (hW.primeIdealOf zw).asIdeal
  let : P.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed zw hzsClosed
  have hPm : P.height = m :=
    RingHom.IsStandardSmoothOfRelativeDimension.height_eq_of_isMaximal hm P
  have hPcoheight : P.height = Order.coheight zw :=
    hW.primeIdealOf_height_eq_coheight zw
  have hWcoheight : Order.coheight zs = Order.coheight zw := by
    have h := coheight_eq_of_isOpenImmersion (x := zw) W.ι
    change Order.coheight zs = Order.coheight zw at h
    exact h
  have hScoheight : Order.coheight z.underlying = Order.coheight zs := by
    have h := coheight_eq_of_isOpenImmersion (x := zs) S.ι
    change Order.coheight z.underlying = Order.coheight zs at h
    exact h
  have hmEq : m = n := by
    exact_mod_cast calc
      (m : ℕ∞) = P.height := hPm.symm
      _ = Order.coheight zw := hPcoheight
      _ = Order.coheight zs := hWcoheight.symm
      _ = Order.coheight z.underlying := hScoheight.symm
      _ = n := hcoheight z
  subst m
  obtain ⟨coordinateRingHom, hcomp, hetale⟩ := hm.exists_etale_mvPolynomial
  exact ⟨
    { point := z
      point_mem_smoothLocus := hzsmooth
      point_isClosed := hzclosed
      componentNeighborhood := W
      componentNeighborhood_isAffine := hW
      point_mem_componentNeighborhood := hzsW
      componentCoordinateRingHom := coordinateRingHom
      componentCoordinateRingHom_comp_C := hcomp
      componentCoordinateRingHom_etale := hetale
      ambientCoordinates := localEtaleCoordinates structureMap d
        (cycleComponentι X x z.underlying) }⟩

/-- In ambient dimension at most two, every reduced component of coheight `p` has separate
component and ambient étale coordinates, with exactly `d - p` component coordinates. -/
lemma nonempty_cycleComponentSeparateLocalCoordinates_of_le_two
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (x : X) (d p : ℕ)
    [SmoothOfRelativeDimension d structureMap]
    (hx : Order.coheight x = p) (hd : d ≤ 2) :
    Nonempty (CycleComponentSeparateLocalCoordinates structureMap x d (d - p)) := by
  apply nonempty_cycleComponentSeparateLocalCoordinates_of_closedPoint_coheight
  intro z
  exact cycleComponent_closedPoint_coheight_eq_sub_of_le_two structureMap x z hx hd

/-- A zero-dimensional reduced component in a smooth complex `d`-fold has a local étale chart
with no component coordinates and an independent ambient chart with `d` coordinates. -/
lemma nonempty_cycleComponentSeparateLocalCoordinates_of_coheight_eq_dimension
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) (d : ℕ)
    [SmoothOfRelativeDimension d structureMap]
    (hx : Order.coheight x = d) :
    Nonempty (CycleComponentSeparateLocalCoordinates structureMap x d 0) := by
  apply nonempty_cycleComponentSeparateLocalCoordinates_of_closedPoint_coheight
  intro z
  exact coheight_eq_zero_of_isClosed_of_cycleComponent_orderKrullDim_eq_zero
    x z.underlying (cycleComponent_complexPoint_underlying_isClosed structureMap x z)
      (orderKrullDim_cycleComponent_eq_zero_of_coheight_eq_dimension
        (f := structureMap) (d := d) x hx)

/-- A one-dimensional reduced component in a smooth complex `d`-fold has a local étale chart
with one component coordinate and an independent ambient chart with `d` coordinates. -/
lemma nonempty_cycleComponentSeparateLocalCoordinates_of_coheight_succ_eq_dimension
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (x : X) (d p : ℕ)
    [SmoothOfRelativeDimension d structureMap]
    (hx : Order.coheight x = p) (hd : p + 1 = d) :
    Nonempty (CycleComponentSeparateLocalCoordinates structureMap x d 1) := by
  apply nonempty_cycleComponentSeparateLocalCoordinates_of_closedPoint_coheight
  intro z
  exact coheight_eq_one_of_isClosed_of_cycleComponent_orderKrullDim_eq_one
    x z.underlying (cycleComponent_complexPoint_underlying_isClosed structureMap x z)
      (orderKrullDim_cycleComponent_eq_one_of_coheight_succ_eq_dimension
        (f := structureMap) (d := d) (p := p) x hx hd)

end AlgebraicGeometry
