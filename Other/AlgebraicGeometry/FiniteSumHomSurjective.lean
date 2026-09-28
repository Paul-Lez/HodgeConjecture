/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Fullness on finite sums from fullness on the summands

In a preadditive category a finite coproduct `∐ᵢ A` carries coordinate inclusions and
projections, so a morphism `∐ᵢ A ⟶ ∐ₖ B` is exactly a matrix of morphisms `A ⟶ B`.  If an
additive functor `F` preserving those coproducts is *full on the summands* — every
`F A ⟶ F B` is `F g` — then it is full on the finite sums, after transport along the
comparison isomorphisms `F (∐ᵢ A) ≅ ∐ᵢ F A`.

This is the categorical half of the passage from rank one to arbitrary finite twist sums in the
Serre-presentation route to GAGA; the analogous statement for *free* module sheaves is
`Other/AlgebraicGeometry/FiniteFreeAnalytification.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Coordinates

variable {A : C} {ι : Type} [Fintype ι] [DecidableEq ι] [HasCoproduct (fun _ : ι => A)]

/-- The `i`-th coordinate inclusion of a finite constant coproduct. -/
abbrev sumι (i : ι) : A ⟶ ∐ (fun _ : ι => A) := Sigma.ι (fun _ : ι => A) i

/-- The `i`-th coordinate projection of a finite constant coproduct. -/
def sumπ (i : ι) : (∐ fun _ : ι => A) ⟶ A :=
  Sigma.desc (fun j => if j = i then 𝟙 A else 0)

omit [Fintype ι] in
@[reassoc (attr := simp)]
lemma sumι_sumπ (i j : ι) :
    sumι (A := A) j ≫ sumπ (A := A) i = if j = i then 𝟙 A else 0 :=
  Sigma.ι_desc _ _

lemma sum_sumπ_sumι : ∑ i : ι, sumπ (A := A) i ≫ sumι (A := A) i =
    𝟙 (∐ fun _ : ι => A) := by
  apply Sigma.hom_ext
  intro j
  rw [Preadditive.comp_sum, Category.comp_id]
  simp [sumι_sumπ_assoc, ite_comp, Finset.sum_ite_eq]

end Coordinates

section Matrix

variable {A B : C} {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [HasCoproduct (fun _ : ι => A)] [HasCoproduct (fun _ : κ => B)]

/-- The morphism of finite sums with prescribed matrix entries. -/
def sumMatrix (a : ι → κ → (A ⟶ B)) : (∐ fun _ : ι => A) ⟶ (∐ fun _ : κ => B) :=
  ∑ i, ∑ k, sumπ (A := A) i ≫ a i k ≫ sumι (A := B) k

@[simp]
lemma sumι_sumMatrix_sumπ (a : ι → κ → (A ⟶ B)) (i : ι) (k : κ) :
    sumι (A := A) i ≫ sumMatrix a ≫ sumπ (A := B) k = a i k := by
  simp [sumMatrix, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
    comp_ite, ite_comp]

omit [Fintype ι] [DecidableEq ι] in
lemma hom_ext_sumMatrix {f g : (∐ fun _ : ι => A) ⟶ (∐ fun _ : κ => B)}
    (h : ∀ i k, sumι (A := A) i ≫ f ≫ sumπ (A := B) k =
      sumι (A := A) i ≫ g ≫ sumπ (A := B) k) : f = g := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.comp_id (sumι (A := A) i ≫ f), ← Category.comp_id (sumι (A := A) i ≫ g),
    ← sum_sumπ_sumι (A := B) (ι := κ)]
  simp only [Preadditive.comp_sum, Category.assoc]
  refine Finset.sum_congr rfl fun k _ => ?_
  simpa only [Category.assoc] using congrArg (fun q => q ≫ sumι (A := B) k) (h i k)

end Matrix

section Functor

variable {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive]
variable {A : C} {ι : Type} [Fintype ι] [DecidableEq ι]
  [HasCoproduct (fun _ : ι => A)] [HasCoproduct (fun _ : ι => F.obj A)]
  [PreservesColimit (Discrete.functor (fun _ : ι => A)) F]

omit [Preadditive C] [Preadditive D] [F.Additive] [Fintype ι] [DecidableEq ι] in
lemma sumι_preservesCoproductIso_inv (i : ι) :
    sumι (A := F.obj A) i ≫ (PreservesCoproduct.iso F (fun _ : ι => A)).inv =
      F.map (sumι (A := A) i) := by
  rw [PreservesCoproduct.inv_hom]
  exact ι_comp_sigmaComparison F (fun _ : ι => A) i

omit [Fintype ι] in
lemma preservesCoproductIso_hom_sumπ (i : ι) :
    (PreservesCoproduct.iso F (fun _ : ι => A)).hom ≫ sumπ (A := F.obj A) i =
      F.map (sumπ (A := A) i) := by
  have h : (PreservesCoproduct.iso F (fun _ : ι => A)).inv ≫ F.map (sumπ (A := A) i) =
      sumπ (A := F.obj A) i := by
    rw [PreservesCoproduct.inv_hom]
    simp only [sumπ]
    rw [sigmaComparison_map_desc]
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc, Sigma.ι_desc]
    by_cases hji : j = i <;> simp [hji]
  rw [← h, Iso.hom_inv_id_assoc]

end Functor

section Main

variable {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive]
variable {A B : C} {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [HasCoproduct (fun _ : ι => A)] [HasCoproduct (fun _ : ι => F.obj A)]
  [HasCoproduct (fun _ : κ => B)] [HasCoproduct (fun _ : κ => F.obj B)]
  [PreservesColimit (Discrete.functor (fun _ : ι => A)) F]
  [PreservesColimit (Discrete.functor (fun _ : κ => B)) F]

/-- **From the summands to finite sums.**  If every morphism `F A ⟶ F B` is the image of a
morphism `A ⟶ B`, then every morphism `∐ᵢ F A ⟶ ∐ₖ F B` is the image of a morphism
`∐ᵢ A ⟶ ∐ₖ B`, after transport along the coproduct comparison isomorphisms. -/
theorem exists_sumMatrix_of_hom_surjective
    (hsurj : Function.Surjective (fun g : A ⟶ B => F.map g))
    (h : (∐ fun _ : ι => F.obj A) ⟶ (∐ fun _ : κ => F.obj B)) :
    ∃ g : (∐ fun _ : ι => A) ⟶ (∐ fun _ : κ => B),
      (PreservesCoproduct.iso F (fun _ : ι => A)).inv ≫ F.map g ≫
        (PreservesCoproduct.iso F (fun _ : κ => B)).hom = h := by
  classical
  choose a ha using fun (i : ι) (k : κ) =>
    hsurj (sumι (A := F.obj A) i ≫ h ≫ sumπ (A := F.obj B) k)
  refine ⟨sumMatrix a, hom_ext_sumMatrix fun i k => ?_⟩
  calc sumι (A := F.obj A) i ≫
        ((PreservesCoproduct.iso F (fun _ : ι => A)).inv ≫ F.map (sumMatrix a) ≫
          (PreservesCoproduct.iso F (fun _ : κ => B)).hom) ≫ sumπ (A := F.obj B) k
      = (sumι (A := F.obj A) i ≫ (PreservesCoproduct.iso F (fun _ : ι => A)).inv) ≫
          F.map (sumMatrix a) ≫
            ((PreservesCoproduct.iso F (fun _ : κ => B)).hom ≫ sumπ (A := F.obj B) k) := by
        simp only [Category.assoc]
    _ = F.map (sumι (A := A) i) ≫ F.map (sumMatrix a) ≫ F.map (sumπ (A := B) k) := by
        rw [sumι_preservesCoproductIso_inv, preservesCoproductIso_hom_sumπ]
    _ = F.map (sumι (A := A) i ≫ sumMatrix a ≫ sumπ (A := B) k) := by
        rw [F.map_comp, F.map_comp]
    _ = F.map (a i k) := by rw [sumι_sumMatrix_sumπ]
    _ = sumι (A := F.obj A) i ≫ h ≫ sumπ (A := F.obj B) k := ha i k

end Main

end CategoryTheory.Limits
