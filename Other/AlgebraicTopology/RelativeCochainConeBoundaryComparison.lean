/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.RelativeCochainConeForgetComparison
public import Other.Algebra.Homology.DegreewiseSplitConnecting
public import Other.Algebra.Homology.DerivedCategory.MappingCoconeBoundary

/-!
# Boundary normalization of the relative cochain cone comparison

The legacy triangle completion can be ambiguous away from the boundary image. Its second
commutative square nevertheless fixes the map on every boundary class. In particular the
positive inclusion of a subspace cochain into the restriction cone maps to the degreewise
split connecting class, with no additional minus sign.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopPair.{u})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The second square of the completed triangle determines its value on the connecting map. -/
@[reassoc]
theorem relativeDualShiftIsoCochainCone_connecting_hom :
    (CochainComplex.trianglehOfDegreewiseSplit
        (relativeDualCochainShortComplexInt R X)
        (relativeDualCochainDegreewiseSplitting R X)).mor₃ ≫
      (relativeDualShiftIsoCochainCone R X).hom =
    (HomotopyCategory.quotient (ModuleCat R) (.up ℤ)).map
      (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)) := by
  change (CochainComplex.trianglehOfDegreewiseSplit
        (relativeDualCochainShortComplexInt R X)
        (relativeDualCochainDegreewiseSplitting R X)).rotate.mor₂ ≫
      (relativeCochainConeTriangleIso R X).hom.hom₃ = _
  rw [(relativeCochainConeTriangleIso R X).hom.comm₂]
  unfold relativeCochainConeTriangleIso
  rw [Pretriangulated.isoTriangleOfIso₁₂_hom_hom₂]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse cone comparison sends the positive cone inclusion to the positive split
connecting morphism. This identifies boundary classes without identifying the entire
completed triangle map with a canonical choice. -/
@[reassoc]
theorem relativeDualShiftIsoCochainCone_inr_inv :
    (HomotopyCategory.quotient (ModuleCat R) (.up ℤ)).map
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)) ≫
      (relativeDualShiftIsoCochainCone R X).inv =
    (CochainComplex.trianglehOfDegreewiseSplit
        (relativeDualCochainShortComplexInt R X)
        (relativeDualCochainDegreewiseSplitting R X)).mor₃ := by
  rw [← relativeDualShiftIsoCochainCone_connecting_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On homology, the positive cone inclusion is the degreewise split connecting map. -/
theorem relativeCochainConeHomologyIsoDualRelativeInt_boundary (n : ℕ) :
    HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)) ((n : ℤ) - 1) ≫
      (relativeCochainConeHomologyIsoDualRelativeInt R X n).hom =
    (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) 0).shiftMap
      (CochainComplex.homOfDegreewiseSplit
        (relativeDualCochainShortComplexInt R X)
        (relativeDualCochainDegreewiseSplitting R X))
      ((n : ℤ) - 1) (n : ℤ) (by omega) := by
  let Q := HomotopyCategory.quotient (ModuleCat R) (.up ℤ)
  let H := HomotopyCategory.homologyFunctor (ModuleCat R) (.up ℤ) 0
  let F (j : ℤ) := HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) j
  let S := relativeDualCochainShortComplexInt R X
  let C := CochainComplex.mappingCone (relativeCochainRestrictionInt R X)
  let i := CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)
  let e := relativeDualShiftIsoCochainCone R X
  have hn : (1 : ℤ) + ((n : ℤ) - 1) = (n : ℤ) := by omega
  have hF : HomologicalComplex.homologyMap i ((n : ℤ) - 1) ≫
      (F ((n : ℤ) - 1)).inv.app C =
    (F ((n : ℤ) - 1)).inv.app S.X₃ ≫
      (H.shift ((n : ℤ) - 1)).map (Q.map i) :=
    (F ((n : ℤ) - 1)).inv.naturality i
  change HomologicalComplex.homologyMap i ((n : ℤ) - 1) ≫
    (F ((n : ℤ) - 1)).inv.app C ≫
    (H.shift ((n : ℤ) - 1)).map e.inv ≫
    (H.shiftIso 1 ((n : ℤ) - 1) (n : ℤ) hn).hom.app (Q.obj S.X₁) ≫
    (F (n : ℤ)).hom.app S.X₁ = _
  rw [← Category.assoc, hF, Category.assoc, ← Functor.map_comp_assoc,
    relativeDualShiftIsoCochainCone_inr_inv]
  change (F ((n : ℤ) - 1)).inv.app S.X₃ ≫
    H.shiftMap (ShiftedHom.map (CochainComplex.homOfDegreewiseSplit S
      (relativeDualCochainDegreewiseSplitting R X)) Q)
      ((n : ℤ) - 1) (n : ℤ) hn ≫ (F (n : ℤ)).hom.app S.X₁ = _
  rw [HomotopyCategory.homologyFunctor_shiftMap]
  dsimp only [F]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The boundary of the legacy cone comparison is exactly the usual connecting map
of the dual cochain short exact sequence. -/
theorem relativeCochainConeHomologyIsoDualRelativeInt_boundary_eq_δ (n : ℕ) :
    HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)) ((n : ℤ) - 1) ≫
      (relativeCochainConeHomologyIsoDualRelativeInt R X n).hom =
    (relativeDualCochainShortComplexInt_shortExact R X).δ
      ((n : ℤ) - 1) (n : ℤ) (by change (n : ℤ) - 1 + 1 = (n : ℤ); omega) := by
  rw [relativeCochainConeHomologyIsoDualRelativeInt_boundary,
    CochainComplex.homology_shiftMap_homOfDegreewiseSplit_eq_δ _ _
      (relativeDualCochainShortComplexInt_shortExact R X) ((n : ℤ) - 1) (n : ℤ) (by omega)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The old triangle completion and explicit cone comparison agree on every boundary class. -/
theorem relativeCochainCone_legacy_canonical_boundary (n : ℕ) :
    HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)) ((n : ℤ) - 1) ≫
      (relativeCochainConeHomologyIsoDualRelativeInt R X n).hom =
    HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)) ((n : ℤ) - 1) ≫
      (relativeDualCochainHomologyIsoCone R X n).inv := by
  rw [relativeCochainConeHomologyIsoDualRelativeInt_boundary_eq_δ]
  exact (CochainComplex.mappingCocone.homologyMap_inr_comp_shortExactHomologyIsoCone_inv
    (relativeDualCochainShortComplexInt R X) (relativeDualCochainDegreewiseSplitting R X)
    (relativeDualCochainShortComplexInt_shortExact R X) ((n : ℤ) - 1) n (by omega)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equality of the actual relative-cohomology equivalences, restricted to the boundary image. -/
theorem relativeCochainConeCohomologyEquiv_eq_canonical_of_boundary (n : ℕ)
    (z : (relativeDualCochainShortComplexInt R X).X₃.homology ((n : ℤ) - 1)) :
    relativeCochainConeCohomologyEquiv R X n
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)) ((n : ℤ) - 1) z) =
    relativeCochainConeCohomologyEquivCanonical R X n
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)) ((n : ℤ) - 1) z) := by
  have h := ConcreteCategory.congr_hom (relativeCochainCone_legacy_canonical_boundary R X n) z
  exact congrArg (relativeDualCochainCohomologyEquiv R X n) h

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback of pairs preserves the positive boundary class under the canonical
relative-cohomology comparison. -/
theorem relativeCochainConeCohomologyEquivCanonical_boundary_naturality
    {X Y : TopPair.{u}} (f : X ⟶ Y) (n : ℕ)
    (z : (relativeDualCochainShortComplexInt R Y).X₃.homology ((n : ℤ) - 1)) :
    relativeCochainConeCohomologyEquivCanonical R X n
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X)) ((n : ℤ) - 1)
        (HomologicalComplex.homologyMap (relativeDualCochainShortComplexIntMap R f).τ₃
          ((n : ℤ) - 1) z)) =
    relativeCohomologyMap R n f
      (relativeCochainConeCohomologyEquivCanonical R Y n
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R Y))
          ((n : ℤ) - 1) z)) := by
  have hi : CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R Y) ≫
      relativeCochainConeMap R f =
    (relativeDualCochainShortComplexIntMap R f).τ₃ ≫
      CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R X) := by
    simp [relativeCochainConeMap, CochainComplex.mappingCone.map]
  have h := relativeCochainConeCohomologyEquivCanonical_naturality R f n
    (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt R Y)) ((n : ℤ) - 1) z)
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp, hi,
    HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply] at h
  exact h

end AlgebraicTopology.Singular
