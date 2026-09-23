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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.LocalGenerator
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension
import HodgeConjecture.Mathlib.Algebra.PolynomialCatenary
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.CatenaryDimension
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension
public import Other.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
public import Other.AlgebraicGeometry.Cycle.Component.NormalGeometry

/-!
# ClosedPointDimension, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Ideal MvPolynomial Topology TopologicalSpace
namespace AlgebraicGeometry
attribute [local instance] overSpecAlgebra
variable (X : Over (Spec ↧ℂ)) {d p : ℕ}

/-- The underlying point of every complex point of a codimension-`p` reduced component has
coheight `d - p`. -/
lemma cycleComponent_complexPoint_coheight_eq_sub
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) :
    Order.coheight z.underlying = d - p :=
  cycleComponent_closedPoint_coheight_eq_sub X x z.underlying hx
    (cycleComponent_complexPoint_underlying_isClosed X x z)

/-- In every ambient dimension, a reduced component of coheight `p` has separate component and
ambient étale coordinates, with exactly `d - p` component coordinates. -/
lemma nonempty_cycleComponentSeparateLocalCoordinates
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) :
    Nonempty (CycleComponentSeparateLocalCoordinates X x d (d - p)) := by
  let c : cycleComponent X.left x ⟶ Spec ↧ℂ :=
    cycleComponentι X.left x ≫ X.hom
  let S : (cycleComponent X.left x).Opens := c.smoothLocus
  let g : S.toScheme ⟶ Spec ↧ℂ := S.ι ≫ c
  let : Smooth g := cycleComponent_smoothLocus_smooth X x
  obtain ⟨z, hzsmooth, hzclosed⟩ :=
    exists_cycleComponent_smooth_closed_complexPoint X x
  let zs : S.toScheme := ⟨z.underlying, hzsmooth⟩
  obtain ⟨W, hW, hzsW, hstandard⟩ := Smooth.exists_affine_isStandardSmooth g zs
  have hstandardComplex := algebraMap_isStandardSmooth (Over.mk g) hstandard
  obtain ⟨m, hm⟩ :=
    hstandardComplex.exists_isStandardSmoothOfRelativeDimension
  have hzsClosed : IsClosed {zs} := by
    have hpreimage : S.ι ⁻¹' ({z.underlying} : Set (cycleComponent X.left x)) =
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
  have hWcoheight : Order.coheight zs = Order.coheight zw :=
    coheight_eq_of_isOpenImmersion (x := zw) W.ι
  have hScoheight : Order.coheight z.underlying = Order.coheight zs :=
    coheight_eq_of_isOpenImmersion (x := zs) S.ι
  have hmEq : m = d - p := by
    exact_mod_cast calc
      (m : ℕ∞) = P.height := hPm.symm
      _ = Order.coheight zw := hPcoheight
      _ = Order.coheight zs := hWcoheight.symm
      _ = Order.coheight z.underlying := hScoheight.symm
      _ = d - p := cycleComponent_complexPoint_coheight_eq_sub X x z hx
  subst m
  obtain ⟨coordinateRingHom, hcomp, hetale⟩ := hm.exists_etale_mvPolynomial
  exact ⟨
    { point := z
      point_mem_smoothLocus := hzsmooth
      point_isClosed := hzclosed
      componentNeighborhood := W
      componentNeighborhood_isAffine := hW
      point_mem_componentNeighborhood := hzsW
      componentCoordinateAlgHom :=
        { toRingHom := coordinateRingHom
          commutes' := fun c ↦ DFunLike.congr_fun hcomp c }
      componentCoordinateAlgHom_etale := hetale
      ambientCoordinates := localEtaleCoordinates X d
        (cycleComponentι X.left x z.underlying) }⟩

end AlgebraicGeometry
end
