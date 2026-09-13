/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenRestriction
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportComparison
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportHypercohomology

/-!
# Comparing an ambient resolution with a resolution on an open subspace

The comparison is lifted on the open subspace across the actual restricted
augmentation. Exact open restriction and the normalized constant-sheaf
comparison prove that this augmentation is a monic quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]

omit [EnoughInjectives C] in
lemma injective_extend_nat (I : CochainComplex C ℕ) (hI : ∀ n, Injective (I.X n))
    (q : ℤ) : Injective ((I.extend ComplexShape.embeddingUpNat).X q) := by
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    exact Injective.of_iso (I.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).symm (hI n)
  · exact (I.isZero_extend_X ComplexShape.embeddingUpNat q (fun n hn => hq ⟨n, hn⟩)).injective

omit [EnoughInjectives C] in
lemma mono_extendMap_nat {K L : CochainComplex C ℕ} (a : K ⟶ L) [Mono a] :
    Mono (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) := by
  apply HomologicalComplex.mono_of_mono_f
  intro q
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    rw [HomologicalComplex.extendMap_f a ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ)) rfl]
    infer_instance
  · exact (K.isZero_extend_X ComplexShape.embeddingUpNat q (fun n hn => hq ⟨n, hn⟩)).mono _

variable {A K I : CochainComplex C ℕ} (a : A ⟶ K) [Mono a] [QuasiIso a]
  (r : A ⟶ I) (hI : ∀ n, Injective (I.X n))

/-- Strict injective lifting for nonnegative cochain complexes, transported
through the fully faithful extension to integer degrees. -/
def liftToInjectiveNat : K ⟶ I := by
  let := mono_extendMap_nat a
  let : CochainComplex.IsStrictlyGE (A.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let : CochainComplex.IsStrictlyGE (K.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let : CochainComplex.IsStrictlyGE (I.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let f := liftToInjective
      (A := A.extend ComplexShape.embeddingUpNat)
      (S := K.extend ComplexShape.embeddingUpNat)
      (I := I.extend ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap r ComplexShape.embeddingUpNat)
      (injective_extend_nat I hI)
  exact (ComplexShape.embeddingUpNat.extendFunctor C).preimage f

end CochainComplex

namespace TopCat.Sheaf

variable (X : TopCat.{0}) (U : Opens X) (A : AddCommGrpCat.{0})

set_option backward.isDefEq.respectTransparency false in
/-- The fixed injective resolution of the constant coefficient sheaf. -/
def ambientConstantInjectiveResolution :
    InjectiveResolution (C := Sheaf AddCommGrpCat.{0} X)
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) :=
  injectiveResolution (C := Sheaf AddCommGrpCat.{0} X) _

end TopCat.Sheaf
