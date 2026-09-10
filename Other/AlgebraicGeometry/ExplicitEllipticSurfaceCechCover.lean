/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceOneForms
public import Other.AlgebraicGeometry.AnalyticNestedTransitionClass

/-!
# A nested four-open cover of the explicit elliptic surface

The two affine elliptic charts in the first factor cover the surface.  Their intersection is
in turn covered using the same two charts in the second factor.  This packages the standard
four product-chart cover in precisely the form used by `analyticNestedTransitionExtClass`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The inverse image of the selected affine elliptic chart under the first projection. -/
abbrev surfaceFstCechOpen (i : Fin 2) :
    Opens (TopCat.of (ComplexPoint (Over.mk surfaceToBase))) :=
  surfaceAnalyticOpen
    (pullback.fst curveToBase curveToBase ⁻¹ᵁ chart (differentialChartIndex i))

/-- The inverse image of the selected affine elliptic chart under the second projection. -/
abbrev surfaceSndCechOpen (i : Fin 2) :
    Opens (TopCat.of (ComplexPoint (Over.mk surfaceToBase))) :=
  surfaceAnalyticOpen
    (pullback.snd curveToBase curveToBase ⁻¹ᵁ chart (differentialChartIndex i))

/-- The two first-factor opens cover the whole analytic surface. -/
theorem surfaceFstCechOpen_cover :
    surfaceFstCechOpen 0 ⊔ surfaceFstCechOpen 1 = ⊤ := by
  apply top_unique
  intro z _
  have hc (x : curve) : x ∈ chart 2 ∨ x ∈ chart 1 := by
    have hx : x ∈ chart 1 ⊔ chart 2 := by
      rw [chart_one_sup_chart_two]
      trivial
    exact hx.elim Or.inr Or.inl
  rcases hc (pullback.fst curveToBase curveToBase z.underlying) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The two second-factor opens cover the whole analytic surface. -/
theorem surfaceSndCechOpen_cover :
    surfaceSndCechOpen 0 ⊔ surfaceSndCechOpen 1 = ⊤ := by
  apply top_unique
  intro z _
  have hc (x : curve) : x ∈ chart 2 ∨ x ∈ chart 1 := by
    have hx : x ∈ chart 1 ⊔ chart 2 := by
      rw [chart_one_sup_chart_two]
      trivial
    exact hx.elim Or.inr Or.inl
  rcases hc (pullback.snd curveToBase curveToBase z.underlying) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The overlap of the two first-factor members of the nested cover. -/
abbrev surfaceCechOuterOverlap := surfaceFstCechOpen 0 ⊓ surfaceFstCechOpen 1

/-- The two members of the inner cover, obtained by intersecting the outer overlap with a
second-factor chart. -/
abbrev surfaceCechInnerOpen (i : Fin 2) :=
  surfaceCechOuterOverlap ⊓ surfaceSndCechOpen i

/-- The inner opens cover the first-factor overlap. -/
theorem surfaceCechInnerOpen_cover :
    surfaceCechInnerOpen 0 ⊔ surfaceCechInnerOpen 1 =
      surfaceCechOuterOverlap := by
  change (surfaceCechOuterOverlap ⊓ surfaceSndCechOpen 0) ⊔
      (surfaceCechOuterOverlap ⊓ surfaceSndCechOpen 1) =
    surfaceCechOuterOverlap
  rw [← inf_sup_left, surfaceSndCechOpen_cover]
  simp

/-- The additive analytic structure sheaf on the explicit surface. -/
abbrev surfaceCechHolomorphicFunctionSheaf :
    AnalyticAdditiveSheaf (Over.mk surfaceToBase) :=
  holomorphicAdditiveFunctionSheaf (Over.mk surfaceToBase) 2

/-- A holomorphic function on the deepest product-chart intersection determines the nested
degree-two Mayer--Vietoris extension for the explicit surface. -/
def surfaceHolomorphicNestedTransitionClass
    (c : surfaceCechHolomorphicFunctionSheaf.obj.obj
      (.op (surfaceCechInnerOpen 0 ⊓ surfaceCechInnerOpen 1))) :
    Abelian.Ext.{1} (constantIntegerSheaf (Over.mk surfaceToBase))
      surfaceCechHolomorphicFunctionSheaf 2 :=
  analyticNestedTransitionExtClass (Over.mk surfaceToBase)
    surfaceCechHolomorphicFunctionSheaf
    (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
    (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
    surfaceFstCechOpen_cover inf_le_left inf_le_left surfaceCechInnerOpen_cover c

/-- Exact obstruction to nonvanishing of the explicit four-open class: its inner transition
class must fail to extend from degree-one classes on the two first-factor opens. -/
theorem surfaceHolomorphicNestedTransitionClass_eq_zero_iff
    (c : surfaceCechHolomorphicFunctionSheaf.obj.obj
      (.op (surfaceCechInnerOpen 0 ⊓ surfaceCechInnerOpen 1))) :
    surfaceHolomorphicNestedTransitionClass c = 0 ↔
      ∃ γ : Abelian.Ext.{1}
          (analyticOpenFreeAbelianSheaf (Over.mk surfaceToBase) (surfaceFstCechOpen 0) ⊞
            analyticOpenFreeAbelianSheaf (Over.mk surfaceToBase) (surfaceFstCechOpen 1))
          surfaceCechHolomorphicFunctionSheaf 1,
        analyticOuterExtRestriction (Over.mk surfaceToBase)
            surfaceCechHolomorphicFunctionSheaf
            (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
            surfaceFstCechOpen_cover γ =
          analyticRelativeTransitionExtClass (Over.mk surfaceToBase)
            surfaceCechHolomorphicFunctionSheaf
            (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
            surfaceCechOuterOverlap inf_le_left inf_le_left
            surfaceCechInnerOpen_cover c :=
  analyticNestedTransitionExtClass_eq_zero_iff (Over.mk surfaceToBase)
    surfaceCechHolomorphicFunctionSheaf
    (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
    (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
    surfaceFstCechOpen_cover inf_le_left inf_le_left surfaceCechInnerOpen_cover c

/-- The universal double residue for the explicit product cover. -/
abbrev surfaceHolomorphicUniversalDoubleResidue :=
  analyticUniversalDoubleResidue (Over.mk surfaceToBase)
    surfaceCechHolomorphicFunctionSheaf
    (surfaceFstCechOpen 0) (surfaceFstCechOpen 1) surfaceFstCechOpen_cover

/-- The explicit nested degree-two class is nonzero exactly when the universal double residue
detects its inner transition class. -/
theorem surfaceHolomorphicNestedTransitionClass_ne_zero_iff_universalDoubleResidue
    (c : surfaceCechHolomorphicFunctionSheaf.obj.obj
      (.op (surfaceCechInnerOpen 0 ⊓ surfaceCechInnerOpen 1))) :
    surfaceHolomorphicNestedTransitionClass c ≠ 0 ↔
      surfaceHolomorphicUniversalDoubleResidue
        (analyticRelativeTransitionExtClass (Over.mk surfaceToBase)
          surfaceCechHolomorphicFunctionSheaf
          (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
          surfaceCechOuterOverlap inf_le_left inf_le_left
          surfaceCechInnerOpen_cover c) ≠ 0 :=
  analyticNestedTransitionExtClass_ne_zero_iff_universalDoubleResidue
    (Over.mk surfaceToBase) surfaceCechHolomorphicFunctionSheaf
    (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
    (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
    surfaceFstCechOpen_cover inf_le_left inf_le_left surfaceCechInnerOpen_cover c

end AlgebraicGeometry.ExplicitEllipticCandidate
