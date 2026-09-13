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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.HolomorphicDeRham

import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicPoincare
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Topology.Sheaves.Sheafify
import HodgeConjecture.Mathlib.Topology.Sheaves.StalkExact

/-!
# The holomorphic de Rham complex

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.HolomorphicDeRham`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Scalar multiplication on the constant complex presheaf. -/
def complexScalarPresheaf (c : ℂ) :
    constantComplexAddCommGrpPresheaf X ⟶
      constantComplexAddCommGrpPresheaf X where
  app _ := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)
  naturality {U V} i := by
    ext x
    rfl

/-- Scalar multiplication on the constant complex sheaf. -/
def complexScalarSheaf (c : ℂ) :
    constantComplexSheaf X ⟶ constantComplexSheaf X := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  exact (presheafToSheaf J AddCommGrpCat).map
    (complexScalarPresheaf X c)

/-- Scalar multiplication on the constant complex-valued complex concentrated in degree zero. -/
@[implicit_reducible]
def complexScalarComplex (c : ℂ) :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexSheaf X) ⟶
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexSheaf X) :=
  (CochainComplex.single₀ _).map (complexScalarSheaf X c)

/-- Scalar multiplication on the integer-indexed constant complex-valued complex. -/
def complexScalarComplexInt (c : ℂ) :
    constantComplexSheafComplexInt X ⟶
      constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap (complexScalarComplex X c)
    ComplexShape.embeddingUpNat

end AlgebraicGeometry.ComplexPoint

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

@[simp] lemma scalarHolomorphicDeRhamPresheaf_apply
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (c : ℂ)
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : HolomorphicForm X d U p) :
    (scalarHolomorphicDeRhamPresheaf X d p c).app U x = c • x := rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_zero
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    scalarHolomorphicDeRhamPresheaf X d p 0 = 0 := by
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_one
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    scalarHolomorphicDeRhamPresheaf X d p 1 = 𝟙 _ := by
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_add
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (a b : ℂ) :
    scalarHolomorphicDeRhamPresheaf X d p (a + b) =
      scalarHolomorphicDeRhamPresheaf X d p a +
        scalarHolomorphicDeRhamPresheaf X d p b := by
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp [add_smul]
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_mul
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (a b : ℂ) :
    scalarHolomorphicDeRhamPresheaf X d p (a * b) =
      scalarHolomorphicDeRhamPresheaf X d p b ≫
        scalarHolomorphicDeRhamPresheaf X d p a := by
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp [mul_smul]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplex_zero
    [SmoothOfRelativeDimension d X.hom] :
    scalarHolomorphicDeRhamComplex X d 0 = 0 := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf X d p 0) = 0
  rw [scalarHolomorphicDeRhamPresheaf_zero, Functor.map_zero]

@[simp] lemma scalarHolomorphicDeRhamComplex_one
    [SmoothOfRelativeDimension d X.hom] :
    scalarHolomorphicDeRhamComplex X d 1 = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf X d p 1) = 𝟙 _
  rw [scalarHolomorphicDeRhamPresheaf_one]
  exact (presheafToSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    AddCommGrpCat).map_id _

@[simp] lemma scalarHolomorphicDeRhamComplex_add
    [SmoothOfRelativeDimension d X.hom] (a b : ℂ) :
    scalarHolomorphicDeRhamComplex X d (a + b) =
      scalarHolomorphicDeRhamComplex X d a +
        scalarHolomorphicDeRhamComplex X d b := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf X d p (a + b)) = _
  rw [scalarHolomorphicDeRhamPresheaf_add, Functor.map_add]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplex_mul
    [SmoothOfRelativeDimension d X.hom] (a b : ℂ) :
    scalarHolomorphicDeRhamComplex X d (a * b) =
      scalarHolomorphicDeRhamComplex X d b ≫
        scalarHolomorphicDeRhamComplex X d a := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf X d p (a * b)) = _
  rw [scalarHolomorphicDeRhamPresheaf_mul, Functor.map_comp]
  rfl

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the constant
complex presheaf. This is the presheaf-level source of conjugate-linearity. -/
lemma complexScalarPresheaf_comp_conj (c : ℂ) :
    complexScalarPresheaf X c ≫ conjConstantComplexPresheaf X =
      conjConstantComplexPresheaf X ≫
        complexScalarPresheaf X (starRingEnd ℂ c) := by
  ext U : 2
  exact AddMonoidHom.ext (map_mul (starRingEnd ℂ) c)

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the constant
complex sheaf. -/
lemma complexScalarSheaf_comp_conj (c : ℂ) :
    complexScalarSheaf X c ≫ conjConstantComplexSheaf X =
      conjConstantComplexSheaf X ≫
        complexScalarSheaf X (starRingEnd ℂ c) := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  change (presheafToSheaf J AddCommGrpCat).map (complexScalarPresheaf X c) ≫
      (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) =
    (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (complexScalarPresheaf X (starRingEnd ℂ c))
  rw [← Functor.map_comp, ← Functor.map_comp, complexScalarPresheaf_comp_conj]

/-- The inclusion of constant zero-forms commutes with complex scalar multiplication. -/
lemma constantsToHolomorphicDeRhamZero_scalar
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    constantsToHolomorphicDeRhamZeroSheaf X d ≫
      (let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))
      (presheafToSheaf J AddCommGrpCat).map
        (scalarHolomorphicDeRhamPresheaf X d 0 c)) =
    complexScalarSheaf X c ≫
      constantsToHolomorphicDeRhamZeroSheaf X d := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  change (presheafToSheaf J AddCommGrpCat).map
      (constantsToHolomorphicDeRhamZero X d) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (scalarHolomorphicDeRhamPresheaf X d 0 c) =
    (presheafToSheaf J AddCommGrpCat).map
      (complexScalarPresheaf X c) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (constantsToHolomorphicDeRhamZero X d)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  let f := holomorphicFormOfConstant X d U
  change (c • LinearMap.id).toAddMonoidHom.comp f.toAddMonoidHom =
    f.toAddMonoidHom.comp (DistribSMul.toAddMonoidHom ℂ c)
  ext x
  exact (f.map_smul c x).symm

/-- The constant-to-de Rham comparison commutes with complex scalar multiplication. -/
lemma constantsToHolomorphicDeRhamComplex_scalar
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    constantsToHolomorphicDeRhamComplex X d ≫
      scalarHolomorphicDeRhamComplex X d c =
    complexScalarComplex X c ≫
      constantsToHolomorphicDeRhamComplex X d := by
  apply HomologicalComplex.hom_ext
  intro p
  rcases p with _ | p
  · exact constantsToHolomorphicDeRhamZero_scalar X d c
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 (constantComplexSheaf X) (p + 1)
      (Nat.succ_ne_zero p)).eq_of_src

/-- Conjugation intertwines the two scalar multiplications in degree zero. -/
lemma complexScalarComplex_comp_conj (c : ℂ) :
    complexScalarComplex X c ≫ conjConstantComplexComplex X =
      conjConstantComplexComplex X ≫
        complexScalarComplex X (starRingEnd ℂ c) := by
  unfold complexScalarComplex conjConstantComplexComplex
  rw [← Functor.map_comp, ← Functor.map_comp, complexScalarSheaf_comp_conj]

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the
integer-indexed constant complex. -/
lemma complexScalarComplexInt_comp_conj (c : ℂ) :
    complexScalarComplexInt X c ≫ conjConstantComplexSheafComplexInt X =
      conjConstantComplexSheafComplexInt X ≫
        complexScalarComplexInt X (starRingEnd ℂ c) := by
  unfold complexScalarComplexInt conjConstantComplexSheafComplexInt
    constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    complexScalarComplex_comp_conj]

@[simp] lemma scalarHolomorphicDeRhamComplexInt_zero
    [IsIntegral X.left] [Smooth X.hom] :
    scalarHolomorphicDeRhamComplexInt X 0 = 0 := by
  unfold scalarHolomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_zero, HomologicalComplex.extendMap_zero]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplexInt_one
    [IsIntegral X.left] [Smooth X.hom] :
    scalarHolomorphicDeRhamComplexInt X 1 = 𝟙 _ := by
  unfold scalarHolomorphicDeRhamComplexInt holomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_one]
  exact HomologicalComplex.extendMap_id _ _

@[simp] lemma scalarHolomorphicDeRhamComplexInt_add
    [IsIntegral X.left] [Smooth X.hom] (a b : ℂ) :
    scalarHolomorphicDeRhamComplexInt X (a + b) =
      scalarHolomorphicDeRhamComplexInt X a +
        scalarHolomorphicDeRhamComplexInt X b := by
  unfold scalarHolomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_add, HomologicalComplex.extendMap_add]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplexInt_mul
    [IsIntegral X.left] [Smooth X.hom] (a b : ℂ) :
    scalarHolomorphicDeRhamComplexInt X (a * b) =
      scalarHolomorphicDeRhamComplexInt X b ≫
        scalarHolomorphicDeRhamComplexInt X a := by
  unfold scalarHolomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_mul, HomologicalComplex.extendMap_comp]
  rfl

/-- The integer-indexed constant-to-de Rham comparison commutes with complex scalar
multiplication. -/
lemma constantsToHolomorphicDeRhamComplexInt_scalar
    [IsIntegral X.left] [Smooth X.hom] (c : ℂ) :
    constantsToHolomorphicDeRhamComplexInt X ≫
      scalarHolomorphicDeRhamComplexInt X c =
    complexScalarComplexInt X c ≫
      constantsToHolomorphicDeRhamComplexInt X := by
  change HomologicalComplex.extendMap
      (constantsToHolomorphicDeRhamComplex X (dim X.left)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (scalarHolomorphicDeRhamComplex X (dim X.left) c) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      (complexScalarComplex X c) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (constantsToHolomorphicDeRhamComplex X (dim X.left)) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    constantsToHolomorphicDeRhamComplex_scalar]

end AlgebraicGeometry.ComplexPoint
