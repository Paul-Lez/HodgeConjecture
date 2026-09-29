/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Factoring complex maps and homotopies through termwise universal maps

If precomposition with each component of a complex map is bijective on morphisms
into every target term, maps of complexes and their homotopies descend uniquely
at the level of components. Into a K-injective target, equality after precomposition
with a quasi-isomorphism also gives an actual homotopy.
-/

open CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace HomologicalComplex
variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  {K L J : HomologicalComplex C c} (η : K ⟶ L)
  (hbij : ∀ i j, Function.Bijective (fun f : L.X i ⟶ J.X j => η.f i ≫ f))

/-- Factor a map of complexes through a morphism that is termwise universal for the target. -/
def descOfPrecompBijective (f : K ⟶ J) : L ⟶ J where
  f i := ((hbij i i).surjective (f.f i)).choose
  comm' i j hij := by
    apply (hbij i j).injective
    dsimp only
    rw [← Category.assoc, ((hbij i i).surjective (f.f i)).choose_spec,
      η.comm_assoc, ((hbij j j).surjective (f.f j)).choose_spec]
    exact f.comm i j

@[reassoc (attr := simp)]
lemma comp_descOfPrecompBijective (f : K ⟶ J) :
    η ≫ descOfPrecompBijective η hbij f = f := by
  ext i
  exact ((hbij i i).surjective (f.f i)).choose_spec

include hbij in
lemma precomp_injective_of_degreewise : Function.Injective (fun f : L ⟶ J => η ≫ f) := by
  intro f g h
  ext i
  exact (hbij i i).injective (congrArg (fun f => f.f i) h)

/-- A homotopy after termwise universal precomposition descends to a homotopy before it. -/
def homotopyOfPrecompBijective {f g : L ⟶ J} (H : Homotopy (η ≫ f) (η ≫ g)) :
    Homotopy f g where
  hom i j := ((hbij i j).surjective (H.hom i j)).choose
  zero i j hij := by
    apply (hbij i j).injective
    dsimp only
    rw [((hbij i j).surjective (H.hom i j)).choose_spec, H.zero i j hij, comp_zero]
  comm i := by
    apply (hbij i i).injective
    dsimp only
    rw [Preadditive.comp_add, Preadditive.comp_add,
      ← dNext_comp_left, ← prevD_comp_left]
    have he : (fun i j => η.f i ≫ ((hbij i j).surjective (H.hom i j)).choose) = H.hom := by
      funext i j
      exact ((hbij i j).surjective (H.hom i j)).choose_spec
    rw [he]
    exact H.comm i
end HomologicalComplex

namespace CochainComplex
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {A K J : CochainComplex C ℤ} [J.IsKInjective]

/-- Into a K-injective target, equality after a quasi-isomorphism gives an actual homotopy. -/
def homotopyOfPrecompQuasiIso (a : A ⟶ K) [QuasiIso a] (f g : K ⟶ J)
    (h : a ≫ f = a ≫ g) : Homotopy f g := by
  apply HomotopyCategory.homotopyOfEq
  apply (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj K) J).injective
  change DerivedCategory.Q.map f = DerivedCategory.Q.map g
  apply (cancel_epi (DerivedCategory.Q.map a)).mp
  rw [← Functor.map_comp, ← Functor.map_comp, h]
end CochainComplex
