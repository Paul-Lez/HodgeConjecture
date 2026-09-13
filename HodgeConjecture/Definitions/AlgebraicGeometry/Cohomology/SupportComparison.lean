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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.WithSupport
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SingularSheafComparison
public import HodgeConjecture.Lemmas.Algebra.Homology.MappingConeQuasiIso
public import Mathlib.Algebra.Homology.ModelCategory.Injective

/-!
# Singular comparison with support

This file proves the categorical input needed to replace the constant-sheaf term in the
mapping-cone model for supported cohomology by a singular-cochain resolution. In particular,
direct image along an open embedding preserves injective additive sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace Topology.IsOpenEmbedding

variable {X Y : TopCat.{0}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)

end Topology.IsOpenEmbedding

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

section

variable {A S I : CochainComplex C ℤ}
  [A.IsStrictlyGE 0] [S.IsStrictlyGE 0] [I.IsStrictlyGE 0]
  (a : A ⟶ S) [Mono a] [QuasiIso a]
  (r : A ⟶ I)

/-- A map into a bounded-below degreewise-injective complex extends strictly across a monic
quasi-isomorphism. This is the lifting property in the injective model structure. -/
noncomputable def liftToInjective (hI : ∀ n : ℤ, Injective (I.X n)) : S ⟶ I := by
  let A' : Plus C := ⟨A, 0, inferInstance⟩
  let S' : Plus C := ⟨S, 0, inferInstance⟩
  let I' : Plus C := ⟨I, 0, inferInstance⟩
  let a' : A' ⟶ S' := ObjectProperty.homMk a
  let r' : A' ⟶ I' := ObjectProperty.homMk r
  let Z' := ⊤_ Plus C
  let p : I' ⟶ Z' := terminal.from I'
  let b : S' ⟶ Z' := terminal.from S'
  let sq : CommSq r' a' p b := CommSq.mk (Subsingleton.elim _ _)
  letI : Mono a' := (Plus.mono_iff a').2 (inferInstance : Mono a)
  letI : WeakEquivalence a' :=
    (Plus.modelCategoryQuillen.weakEquivalence_iff a').2 (inferInstance : QuasiIso a)
  letI : IsFibrant I' :=
    (Plus.modelCategoryQuillen.isFibrant_iff I').2 hI
  exact sq.lift.hom

end

end CochainComplex

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The constant-to-singular-cochain resolution is a monomorphism of complexes. -/
lemma constantsToSingularCochainSheafComplex_mono
    (R : Type) [Field R] (Y : TopCat.{0}) :
    Mono (constantsToSingularCochainSheafComplex R Y) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  cases n with
  | zero =>
      change Mono (constantsToSingularCochainZeroSheaf R Y)
      exact constantsToSingularCochainZeroSheaf_mono R Y
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        (constantCoefficientSheaf R Y) (n + 1) (by lia)).mono _

/-- Extending the constant-to-singular-cochain resolution to integer degrees remains monic. -/
lemma constantsToSingularCochainComplexInt_mono
    (R : Type) [Field R] (Y : TopCat.{0}) :
    Mono (HomologicalComplex.extendMap
      (constantsToSingularCochainSheafComplex R Y) ComplexShape.embeddingUpNat) := by
  let a := constantsToSingularCochainSheafComplex R Y
  let : Mono a := constantsToSingularCochainSheafComplex_mono R Y
  apply HomologicalComplex.mono_of_mono_f
  intro n
  by_cases hn : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hn
    change Mono ((HomologicalComplex.extendMap a ComplexShape.embeddingUpNat).f (m : ℤ))
    rw [HomologicalComplex.extendMap_f a ComplexShape.embeddingUpNat
      (i := m) (i' := (m : ℤ)) rfl]
    infer_instance
  · exact (((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat Y)).obj
      (constantCoefficientSheaf R Y)).isZero_extend_X
        ComplexShape.embeddingUpNat n (fun i hi ↦ hn ⟨i, hi⟩)).mono _

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The rational constant-to-singular comparison is a monomorphism of integer-indexed sheaf
complexes. -/
lemma rationalToSingularCochainComplexInt_mono :
    Mono (rationalToSingularCochainComplexInt X) := by
  change Mono (HomologicalComplex.extendMap
    (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ
      (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat)
  exact AlgebraicTopology.Singular.constantsToSingularCochainComplexInt_mono ℚ _

variable [IsIntegral X.left] [Smooth X.hom]

local instance bettiSupportComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance bettiSupportComparisonMono : Mono (rationalToSingularCochainComplexInt X) :=
  rationalToSingularCochainComplexInt_mono X

local instance bettiSupportComparisonQuasiIso : QuasiIso (rationalToSingularCochainComplexInt X) :=
  rationalToSingularCochainComplexInt_quasiIso X

end AlgebraicGeometry.ComplexPoint
