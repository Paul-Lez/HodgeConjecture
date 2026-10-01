/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalytificationModules
public import Other.AlgebraicGeometry.HolomorphicLocallyRingedSpace
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.PullbackStalk

/-!
# Stalks of analytified modules

The stalk of the analytification of an algebraic sheaf of modules is extension of scalars along
the comparison map from the algebraic local ring to the holomorphic local ring.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- The stalk of an analytified module is obtained by extension of scalars from the algebraic
local ring to the holomorphic local ring. -/
def moduleAnalytificationStalkIso (z : ComplexPoint X) :
    moduleAnalytification X d ⋙
        SheafOfModules.stalkFunctor
          (R := (holomorphicFunctionSheaf X d).presheaf)
          (hR := (holomorphicRingSheaf X d).property) z ≅
      SheafOfModules.stalkFunctor
          (R := X.left.presheaf)
          (hR := X.left.ringCatSheaf.property) z.underlying ⋙
        ModuleCat.extendScalars
          ((analytificationToPresheafedSpace X d).stalkMap z).hom :=
  SheafOfModules.pullbackStalkIso
    (hS := X.left.ringCatSheaf.property)
    (hR := (holomorphicRingSheaf X d).property)
    (regularToHolomorphicSheaf X d).hom z

end AlgebraicGeometry.ComplexPoint
