/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ModelCategory.Injective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Lifting along a monic quasi-isomorphism into a termwise-injective complex

In an abelian category with enough injectives, a map from a bounded-below complex into a
bounded-below termwise-injective complex extends along a monic quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

section

variable {A S I : CochainComplex C ℤ}
  [A.IsStrictlyGE 0] [S.IsStrictlyGE 0] [I.IsStrictlyGE 0]
  (a : A ⟶ S) [Mono a] [QuasiIso a]
  (r : A ⟶ I)

/-- In an abelian category with enough injectives, let `a : A → S` be a monomorphism and
quasi-isomorphism of integer-indexed complexes that are zero in negative degrees. Let `I` also
be zero in negative degrees and have injective terms. For a complex map `r : A → I`, this
chooses a complex map `l : S → I` with `l ∘ a = r`. -/
def liftToInjective (hI : ∀ n : ℤ, Injective (I.X n)) : S ⟶ I :=
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
  sq.lift.hom

end

end CochainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable {A S I : CochainComplex C ℤ}
  [A.IsStrictlyGE 0] [S.IsStrictlyGE 0] [I.IsStrictlyGE 0]
  (a : A ⟶ S) [Mono a] [QuasiIso a]
  (r : A ⟶ I)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
set_option linter.unusedSectionVars false in
/-- The injective lift strictly extends the prescribed map. -/
lemma comp_liftToInjective (hI : ∀ n : ℤ, Injective (I.X n)) :
    a ≫ liftToInjective a r hI = r := by
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
  exact congrArg (fun f ↦ f.hom) sq.fac_left

end CochainComplex

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

/-- In an abelian category with enough injectives, let `a : A → K` be a monomorphism and
quasi-isomorphism of nonnegative cochain complexes, and let every term of `I` be injective. For
a map `r : A → I`, this chooses a map `l : K → I` satisfying `l ∘ a = r` as an equality of
complex maps. -/
def liftToInjectiveNat : K ⟶ I :=
  letI := mono_extendMap_nat a
  letI : CochainComplex.IsStrictlyGE (A.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  letI : CochainComplex.IsStrictlyGE (K.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  letI : CochainComplex.IsStrictlyGE (I.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let f := liftToInjective
      (A := A.extend ComplexShape.embeddingUpNat)
      (S := K.extend ComplexShape.embeddingUpNat)
      (I := I.extend ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap r ComplexShape.embeddingUpNat)
      (injective_extend_nat I hI)
  (ComplexShape.embeddingUpNat.extendFunctor C).preimage f

end CochainComplex

end
