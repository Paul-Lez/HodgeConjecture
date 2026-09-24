/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingConnecting

/-!
# Pullback naturality of the actual rational winding class

The rational winding cocycle and its cohomology class commute with every
continuous map, including the prescribed integer-grading comparison. This keeps
the literal complement homeomorphisms in the local support calculation visible.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace ChernWinding
variable {Y Y' : TopCat.{0}} (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (f : Y' ⟶ Y)
  (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0)

lemma rationalWindingCocycle_naturality :
    HomologicalComplex.cyclesMap
      (HomologicalComplex.linearDualMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ))) 1
      (rationalWindingCocycle g hg) = rationalWindingCocycle (g.comp (topMap f)) hgf := by
  let k := HomologicalComplex.linearDualMap
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ))
  apply (ModuleCat.mono_iff_injective ((singularChains Y').linearDualCochainComplex.iCycles 1)).mp
    inferInstance
  have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i k 1)
    (rationalWindingCocycle g hg)
  simp only [ConcreteCategory.comp_apply, iCycles_rationalWindingCocycle] at h
  rw [h, iCycles_rationalWindingCocycle]
  exact congrArg ModuleCat.Hom.hom (chainComplexMap_comp_rationalWindingCochain g hg f hgf)

lemma rationalWindingCohomologyClass_naturality :
    HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ))) 1
      (rationalWindingCohomologyClass g hg) =
    rationalWindingCohomologyClass (g.comp (topMap f)) hgf := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
      (HomologicalComplex.linearDualMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ))) 1)
    (rationalWindingCocycle g hg)
  simp only [ConcreteCategory.comp_apply] at h
  erw [rationalWindingCocycle_naturality g hg f hgf] at h
  exact h

/-- The actual integer-graded winding class is natural under continuous pullback. -/
lemma rationalWindingIntCohomologyClass_naturality :
    HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap
        (HomologicalComplex.linearDualMap
          (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)))
        ComplexShape.embeddingUpNat) 1 (rationalWindingIntCohomologyClass g hg) =
    rationalWindingIntCohomologyClass (g.comp (topMap f)) hgf := by
  let k := HomologicalComplex.linearDualMap
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ))
  let e := (singularChains Y').linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl
  let eY := (singularChains Y).linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl
  have hn := HomologicalComplex.extendHomologyIso_hom_naturality k
    ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl
  have h := ConcreteCategory.congr_hom hn (rationalWindingIntCohomologyClass g hg)
  apply e.toLinearEquiv.injective
  change e.hom (HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat) 1
      (rationalWindingIntCohomologyClass g hg)) =
    e.hom (e.inv (rationalWindingCohomologyClass (g.comp (topMap f)) hgf))
  have he (w) : e.hom (e.inv w) = w := e.toLinearEquiv.apply_symm_apply w
  rw [he]
  change e.hom (HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat) 1
      (rationalWindingIntCohomologyClass g hg)) =
    HomologicalComplex.homologyMap k 1
      (eY.hom (eY.inv (rationalWindingCohomologyClass g hg))) at h
  have heY (w) : eY.hom (eY.inv w) = w := eY.toLinearEquiv.apply_symm_apply w
  rw [heY] at h
  exact h.trans (rationalWindingCohomologyClass_naturality g hg f hgf)

end ChernWinding
