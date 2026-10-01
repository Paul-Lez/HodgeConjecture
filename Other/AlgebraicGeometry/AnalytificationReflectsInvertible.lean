/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalytificationReflectsStalkRankOne
public import Other.TauCeti.SheafOfModules.JacobsonLocalTriviality

/-!
# Descent of invertibility along analytification

A coherent algebraic model of an analytic line bundle is invertible when the comparison map on
every stalk is faithfully flat.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom]

/-- A coherent algebraic model of an analytic line bundle is itself a line bundle. -/
theorem algebraic_isInvertible_of_analytificationIso
    (F : X.left.Modules) [F.IsCoherent]
    (M : SheafOfModules.{0} (holomorphicRingSheaf X d))
    (hff : ∀ z : ComplexPoint X,
      ((analytificationToPresheafedSpace X d).stalkMap z).hom.FaithfullyFlat)
    (eFM : (moduleAnalytification X d).obj F ≅ M)
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    TauCeti.SheafOfModules.IsInvertible F := by
  have hJX : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hF : F.IsCoherent := inferInstance
  let : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType F
  let Y := X.left.toLocallyRingedSpace
  have hJY : JacobsonSpace Y := hJX
  have hFY : (show SheafOfModules.{0} Y.ringSheaf from F).IsCoherent := hF
  have hBasis (x : closedPoints X.left) :
      Nonempty (Module.Basis PUnit
        (X.left.presheaf.stalk x.1)
        ((SheafOfModules.stalkFunctor
          (R := X.left.presheaf) (hR := X.left.ringCatSheaf.property) x.1).obj F)) :=
    ⟨Module.basisPUnitOfLinearEquivSelf _ _
      (exists_algebraicStalkLinearEquiv_of_isInvertible_closedPoint
        X d F M x hff eFM hM).some⟩
  exact @AlgebraicGeometry.LocallyRingedSpace.isInvertible_of_isCoherent_of_basis_closedPoints
    Y hJY (show SheafOfModules.{0} Y.ringSheaf from F) hFY hBasis

end AlgebraicGeometry.ComplexPoint
