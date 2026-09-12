/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module


public import Other.AlgebraicGeometry.ComplexAffineIntegralConnected
public import Other.AlgebraicGeometry.SmoothLocalNonvanishing
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Connectedness of smooth integral complex schemes

The complex points of a smooth integral complex scheme are connected. The affine case follows
from Noether normalization and the connected root cover of an irreducible polynomial. A local
étale coordinate chart supplies a connected nonempty open in the general case, and its complex
points are dense in the whole scheme.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open ComplexAlgHom Point

noncomputable section

/-- The complex points of a smooth integral quasi-separated complex scheme form a connected
space. -/
theorem connectedSpace (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [QuasiSeparatedSpace X.left] : ConnectedSpace (ComplexPoint X) := by
  let _ : LocallyOfFiniteType X.hom := inferInstance
  let _ : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (X := X.left) (Z := Set.univ) Set.univ_nonempty isOpen_univ.isLocallyClosed
  let z : ComplexPoint X :=
    let w := (pointEquivClosedPoint X.hom).symm ⟨x, hx⟩
    Over.homMk w.1 w.2
  let d := dim X.left
  let D := localEtaleCoordinates X d z
  let A := Γ(D.neighborhood.toScheme, ⊤)
  let P := complexPolynomialRing d
  let _ : Nonempty D.neighborhood := ⟨⟨z.underlying, D.mem⟩⟩
  let _ : Algebra P A := D.coordinateRingHomOnOpen.toAlgebra
  let _ : Algebra ℂ A := (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra
  let _ : IsScalarTower ℂ P A := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra.Etale P A :=
    RingHom.etale_algebraMap.mp D.coordinateRingHomOnOpen_etale
  let _ : IsDomain A := inferInstance
  let _ : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.trans (R := ℂ) (S := P) (A := A) inferInstance inferInstance
  let _ : Algebra.Smooth ℂ P := Algebra.Smooth.mk inferInstance inferInstance
  let _ : Algebra.Smooth ℂ A := Algebra.Smooth.comp ℂ P A
  let _ : ConnectedSpace (A →ₐ[ℂ] ℂ) :=
    connectedSpace_complexAlgHom_of_smooth_integral A
  let _ : ConnectedSpace (ComplexPoint (openScheme X D.neighborhood)) :=
    D.pointAlgHomHomeomorph.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_of_open X D.neighborhood

end

end AlgebraicGeometry.ComplexPoint
