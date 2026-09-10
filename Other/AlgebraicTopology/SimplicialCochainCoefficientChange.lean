/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SimplicialCochainExtension
public import Other.Algebra.Homology.LinearDual

/-!
# Change of coefficients on simplicial cochains

A ring homomorphism `f : R →+* S` sends an `R`-valued cochain on a simplicial set, viewed as a
function on simplices, to the `S`-valued cochain obtained by postcomposition with `f`. This
commutes with the simplicial coboundary, so it defines a map between the algebraic-dual cochain
complexes after forgetting the scalar structures.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (X : SSet.{u})

/-- The coboundary of a cochain, evaluated on a simplex, is the alternating sum of its values
on the faces. -/
lemma dualToFun_dualMap_d (n : ℕ)
    (φ : Module.Dual R ((X.chainComplex (ModuleCat.of R R)).X n)) (x : X _⦋n + 1⦌) :
    dualToFun R X (n + 1)
        (((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom.dualMap φ) x =
      ∑ i : Fin (n + 2), (-1) ^ (i : ℕ) • dualToFun R X n φ (X.δ i x) := by
  simp only [dualToFun_apply, LinearMap.dualMap_apply, chainOfSimplex]
  have h := congrArg (fun g ↦ φ (g.hom 1)) (X.ιChainComplex_d (ModuleCat.of R R) x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  simp [ModuleCat.hom_sum, LinearMap.sum_apply, map_sum]

/-- Change of coefficients on cochains in a fixed degree: postcomposition with `f` on the
function model. -/
def dualCoefficientChange (n : ℕ) :
    Module.Dual R ((X.chainComplex (ModuleCat.of R R)).X n) →+
      Module.Dual S ((X.chainComplex (ModuleCat.of S S)).X n) where
  toFun φ := dualOfFun S X n (f ∘ dualToFun R X n φ)
  map_zero' := by
    apply dualToFun_injective S X n
    rw [dualToFun_dualOfFun, map_zero, map_zero]
    funext x
    simp
  map_add' φ ψ := by
    apply dualToFun_injective S X n
    simp only [map_add, dualToFun_dualOfFun]
    funext x
    simp

@[simp]
lemma dualToFun_dualCoefficientChange (n : ℕ)
    (φ : Module.Dual R ((X.chainComplex (ModuleCat.of R R)).X n)) :
    dualToFun S X n (dualCoefficientChange f X n φ) = f ∘ dualToFun R X n φ :=
  dualToFun_dualOfFun S X n _

/-- Change of coefficients commutes with the coboundary. -/
lemma dualCoefficientChange_dualMap_d (n : ℕ)
    (φ : Module.Dual R ((X.chainComplex (ModuleCat.of R R)).X n)) :
    dualCoefficientChange f X (n + 1)
        (((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom.dualMap φ) =
      ((X.chainComplex (ModuleCat.of S S)).d (n + 1) n).hom.dualMap
        (dualCoefficientChange f X n φ) := by
  apply dualToFun_injective S X (n + 1)
  funext x
  rw [dualToFun_dualCoefficientChange, Function.comp_apply, dualToFun_dualMap_d,
    dualToFun_dualMap_d, map_sum]
  simp only [map_zsmul, dualToFun_dualCoefficientChange, Function.comp_apply]

/-- Change of coefficients as a morphism of the algebraic-dual cochain complexes, with the
scalar structures forgotten. -/
def linearDualCoefficientChange :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (X.chainComplex (ModuleCat.of R R)).linearDualCochainComplex ⟶
      ((forget₂ (ModuleCat.{u} S) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (X.chainComplex (ModuleCat.of S S)).linearDualCochainComplex where
  f n := AddCommGrpCat.ofHom (dualCoefficientChange f X n)
  comm' i j hij := by
    obtain rfl := hij
    ext φ
    simp only [Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.linearDualCochainComplex_d]
    change ((X.chainComplex (ModuleCat.of S S)).d (i + 1) i).hom.dualMap
        (dualCoefficientChange f X i φ) =
      dualCoefficientChange f X (i + 1)
        (((X.chainComplex (ModuleCat.of R R)).d (i + 1) i).hom.dualMap φ)
    exact (dualCoefficientChange_dualMap_d f X i φ).symm

@[simp]
lemma linearDualCoefficientChange_f (n : ℕ) :
    (linearDualCoefficientChange f X).f n = AddCommGrpCat.ofHom (dualCoefficientChange f X n) :=
  rfl

/-- Change of coefficients is compatible with restriction along morphisms of simplicial sets. -/
lemma dualCoefficientChange_dualMap {Y : SSet.{u}} (g : X ⟶ Y) (n : ℕ)
    (ψ : Module.Dual R ((Y.chainComplex (ModuleCat.of R R)).X n)) :
    dualCoefficientChange f X n (((chainComplexMap g (ModuleCat.of R R)).f n).hom.dualMap ψ) =
      ((chainComplexMap g (ModuleCat.of S S)).f n).hom.dualMap
        (dualCoefficientChange f Y n ψ) := by
  apply dualToFun_injective S X n
  rw [dualToFun_dualCoefficientChange]
  change f ∘ dualEquivFun R X n (((chainComplexMap g (ModuleCat.of R R)).f n).hom.dualMap ψ) =
    dualEquivFun S X n (((chainComplexMap g (ModuleCat.of S S)).f n).hom.dualMap
      (dualCoefficientChange f Y n ψ))
  rw [dualEquivFun_dualMap, dualEquivFun_dualMap]
  funext x
  simp only [Function.comp_apply]
  exact (congrFun (dualToFun_dualCoefficientChange f Y n ψ) (g.app _ x)).symm

end SSet
