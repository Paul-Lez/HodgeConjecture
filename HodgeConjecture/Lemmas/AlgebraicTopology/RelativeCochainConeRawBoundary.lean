/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.RelativeCochainConeNaturality
public import HodgeConjecture.Lemmas.Algebra.Homology.ExtendConnecting
public import HodgeConjecture.Lemmas.AlgebraicTopology.LinearDualConnecting

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

set_option maxHeartbeats 2000000 in
theorem relativeCochainCone_rawBoundary
    (X : TopPair.{u}) (a : (relativeDualCochainShortComplexNat R X).X₃.homology 1) :
    relativeCochainConeCohomologyEquivCanonical R X 2
        ((HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.triangle
            (relativeCochainRestrictionInt R X)).mor₂ 1).hom
          (((relativeDualCochainShortComplexNat R X).X₃.extendHomologyIso
            ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl).inv.hom a)) =
      (HomologicalComplex.linearDualHomologyEquiv
        ((chainPairFunctor R).obj X).left 1 a).comp
        ((relativeChainShortComplex_shortExact R X).δ 2 1
          (ComplexShape.down_mk 2 1 (by simp))).hom := by
  let C := relativeChainShortComplex R X
  let D := HomologicalComplex.linearDualShortComplex C
  let E := relativeDualCochainShortComplexInt R X
  change D.X₃.homology 1 at a
  let hC := relativeChainShortComplex_shortExact R X
  let hD := HomologicalComplex.linearDualShortComplex_shortExact C hC
  have hE : E.ShortExact := relativeDualCochainShortComplexInt_shortExact R X
  change (D.map (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat R))).ShortExact at hE
  have hDE :
      hE.δ (1 : ℤ) (2 : ℤ) (ComplexShape.up_mk _ _ (by simp)) ≫
          (D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
            (j := 2) (j' := (2 : ℤ)) rfl).hom =
        (D.X₃.extendHomologyIso ComplexShape.embeddingUpNat
            (j := 1) (j' := (1 : ℤ)) rfl).hom ≫
          hD.δ 1 2 (ComplexShape.up_mk _ _ (by simp)) := by
    exact HomologicalComplex.extendShortComplex_connecting (R := R) D hD hE 1
  let aE := (D.X₃.extendHomologyIso ComplexShape.embeddingUpNat
    (j := 1) (j' := (1 : ℤ)) rfl).inv.hom a
  have hcone :=
    CochainComplex.mappingCocone.homologyMap_mappingCone_triangle_mor₂_shortExactHomologyIsoCone_inv
      E hE 1 2 (by simp)
  have hcomp := congrArg (fun q => q ≫
    (D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
      (j := 2) (j' := (2 : ℤ)) rfl).hom) hcone
  have hcomp' := hcomp.trans hDE
  have hcomp_a := ConcreteCategory.congr_hom hcomp' aE
  change (D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
    (j := 2) (j' := (2 : ℤ)) rfl).hom.hom
      ((CochainComplex.mappingCocone.shortExactHomologyIsoCone E hE 1 2
        (by simp)).inv.hom
        ((HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.triangle E.g).mor₂ 1).hom aE)) =
    (hD.δ 1 2 (ComplexShape.up_mk _ _ (by simp))).hom
      ((D.X₃.extendHomologyIso ComplexShape.embeddingUpNat
        (j := 1) (j' := (1 : ℤ)) rfl).hom.hom aE) at hcomp_a
  have haE :
      (D.X₃.extendHomologyIso ComplexShape.embeddingUpNat
        (j := 1) (j' := (1 : ℤ)) rfl).hom.hom aE = a := by
    dsimp only [aE]
    simp
  have hraw :
      (relativeDualCochainHomologyIsoCone R X 2).inv.hom
        ((HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.triangle
            (relativeCochainRestrictionInt R X)).mor₂ 1).hom aE) =
      (D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
        (j := 2) (j' := (2 : ℤ)) rfl).inv.hom
          ((hD.δ 1 2 (ComplexShape.up_mk _ _ (by simp))).hom a) := by
    apply (D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
      (j := 2) (j' := (2 : ℤ)) rfl).toLinearEquiv.injective
    change (D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
      (j := 2) (j' := (2 : ℤ)) rfl).hom.hom
      ((CochainComplex.mappingCocone.shortExactHomologyIsoCone E hE 1 2
        (by simp)).inv.hom
        ((HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.triangle E.g).mor₂ 1).hom aE)) = _
    rw [hcomp_a, haE]
    exact (D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
      (j := 2) (j' := (2 : ℤ)) rfl).toLinearEquiv.apply_symm_apply _ |>.symm
  change relativeCochainConeCohomologyEquivCanonical R X 2
    ((HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.triangle
        (relativeCochainRestrictionInt R X)).mor₂ 1).hom aE) = _
  change relativeDualCochainCohomologyEquiv R X 2
      ((relativeDualCochainHomologyIsoCone R X 2).inv.hom
        ((HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.triangle E.g).mor₂ 1).hom aE)) = _
  simp only [E, relativeDualCochainShortComplexInt_g]
  refine (congrArg (relativeDualCochainCohomologyEquiv R X 2) hraw).trans ?_
  ext z
  change HomologicalComplex.linearDualHomologyEquiv C.X₃ 2
      ((D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
        (j := 2) (j' := (2 : ℤ)) rfl).hom.hom
        ((D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
          (j := 2) (j' := (2 : ℤ)) rfl).inv.hom
          ((hD.δ 1 2 (ComplexShape.up_mk _ _ (by simp))).hom a))) z = _
  have hcancel :
      (D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
        (j := 2) (j' := (2 : ℤ)) rfl).hom.hom
        ((D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
          (j := 2) (j' := (2 : ℤ)) rfl).inv.hom
          ((hD.δ 1 2 (ComplexShape.up_mk _ _ (by simp))).hom a)) =
        (hD.δ 1 2 (ComplexShape.up_mk _ _ (by simp))).hom a :=
    (D.X₁.extendHomologyIso ComplexShape.embeddingUpNat
      (j := 2) (j' := (2 : ℤ)) rfl).toLinearEquiv.apply_symm_apply _
  rw [hcancel]
  exact HomologicalComplex.linearDualShortComplex_connecting_pairing C hC 1 a z

end AlgebraicTopology.Singular
