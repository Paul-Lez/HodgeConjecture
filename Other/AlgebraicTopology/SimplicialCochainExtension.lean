/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Extension by zero of simplicial cochains

Let `R` be a commutative ring. The simplicial `n`-chains of a simplicial set `X` with
coefficients in `R` form the free module on the `n`-simplices of `X`, so a cochain (a linear
functional on `n`-chains) is the same as an arbitrary `R`-valued function on `n`-simplices.
This file records that identification, `SSet.dualEquivFun`, and uses it to show that for a
morphism `f : S ⟶ T` of simplicial sets which is injective on `n`-simplices, the restriction of
cochains along `f` has an explicit linear section, `SSet.dualExtension`: extend a cochain on `S`
by zero on the simplices of `T` which are not in the image of `f`. In particular restriction of
cochains along `f` is surjective.

No field hypothesis is needed, in contrast with `LinearMap.dualMap_surjective_of_injective`.
The two cases of interest are the inclusion of a subcomplex, and the map on singular simplicial
sets induced by an injective continuous map of topological spaces.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

variable (R : Type u) [CommRing R]

section Chains

variable (X : SSet.{u}) (n : ℕ)

/-- The `n`-chain of `X` consisting of a single `n`-simplex with coefficient one. -/
def chainOfSimplex (x : X _⦋n⦌) : (X.chainComplex (ModuleCat.of R R)).X n :=
  (X.ιChainComplex (R := ModuleCat.of R R) x).hom 1

/-- Evaluate a cochain on the basis chains of the `n`-simplices. -/
def dualToFun :
    Module.Dual R ((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] (X _⦋n⦌ → R) where
  toFun φ x := φ (chainOfSimplex R X n x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma dualToFun_apply (φ : Module.Dual R ((X.chainComplex (ModuleCat.of R R)).X n))
    (x : X _⦋n⦌) :
    dualToFun R X n φ x = φ (chainOfSimplex R X n x) :=
  rfl

/-- The cochain with prescribed values on the basis chains of the `n`-simplices. -/
def dualOfFun (g : X _⦋n⦌ → R) :
    Module.Dual R ((X.chainComplex (ModuleCat.of R R)).X n) :=
  (Cofan.IsColimit.desc (X.isColimitChainComplexXCofan (ModuleCat.of R R) n)
    fun x ↦ ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R R R).symm (g x))).hom

lemma dualToFun_dualOfFun (g : X _⦋n⦌ → R) :
    dualToFun R X n (dualOfFun R X n g) = g := by
  funext x
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun x ↦ ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R R R).symm (g x))) x
  have h1 := congrArg (fun z ↦ ModuleCat.Hom.hom z 1) h
  change dualOfFun R X n g (chainOfSimplex R X n x) = g x
  exact h1.trans ((LinearMap.ringLmapEquivSelf R R R).apply_symm_apply (g x))

lemma dualToFun_injective : Function.Injective (dualToFun R X n) := by
  intro φ ψ h
  have : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply chainComplex_hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact congrFun h x
  exact congrArg ModuleCat.Hom.hom this

/-- Cochains on `X` in degree `n` are the same as arbitrary functions on `n`-simplices. -/
def dualEquivFun :
    Module.Dual R ((X.chainComplex (ModuleCat.of R R)).X n) ≃ₗ[R] (X _⦋n⦌ → R) :=
  LinearEquiv.ofBijective (dualToFun R X n)
    ⟨dualToFun_injective R X n, fun g ↦ ⟨dualOfFun R X n g, dualToFun_dualOfFun R X n g⟩⟩

@[simp]
lemma dualEquivFun_apply (φ : Module.Dual R ((X.chainComplex (ModuleCat.of R R)).X n))
    (x : X _⦋n⦌) :
    dualEquivFun R X n φ x = φ (chainOfSimplex R X n x) :=
  rfl

end Chains

section Extension

variable {S T : SSet.{u}} (f : S ⟶ T) (n : ℕ)

/-- Basis chains are natural with respect to morphisms of simplicial sets. -/
lemma chainComplexMap_chainOfSimplex (x : S _⦋n⦌) :
    ((chainComplexMap f (ModuleCat.of R R)).f n).hom (chainOfSimplex R S n x) =
      chainOfSimplex R T n (f.app _ x) :=
  congrArg (fun g ↦ g.hom 1) (SSet.ι_chainComplexMap_f S T f (ModuleCat.of R R) x)

/-- Under the function model for cochains, restriction along `f` is precomposition with `f`. -/
lemma dualEquivFun_dualMap (ψ : Module.Dual R ((T.chainComplex (ModuleCat.of R R)).X n)) :
    dualEquivFun R S n (((chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap ψ) =
      dualEquivFun R T n ψ ∘ f.app _ := by
  funext x
  change ψ (((chainComplexMap f (ModuleCat.of R R)).f n).hom (chainOfSimplex R S n x)) =
    ψ (chainOfSimplex R T n (f.app _ x))
  rw [chainComplexMap_chainOfSimplex]

variable (hf : Function.Injective (f.app (Opposite.op (SimplexCategory.mk n))))

open Classical in
/-- Extend a function on the `n`-simplices of `S` by zero along `f`. -/
def extendByZero : (S _⦋n⦌ → R) →ₗ[R] (T _⦋n⦌ → R) where
  toFun g t := if h : ∃ s, f.app _ s = t then g h.choose else 0
  map_add' g g' := by
    funext t
    by_cases h : ∃ s, f.app (Opposite.op (SimplexCategory.mk n)) s = t
    · simp only [Pi.add_apply, dif_pos h]
    · simp only [Pi.add_apply, dif_neg h, add_zero]
  map_smul' a g := by
    funext t
    by_cases h : ∃ s, f.app (Opposite.op (SimplexCategory.mk n)) s = t
    · simp only [Pi.smul_apply, dif_pos h, RingHom.id_apply]
    · simp only [Pi.smul_apply, dif_neg h, smul_zero, RingHom.id_apply]

open Classical in
include hf in
lemma extendByZero_app (g : S _⦋n⦌ → R) (s : S _⦋n⦌) :
    extendByZero R f n g (f.app _ s) = g s := by
  have h : ∃ s', f.app (Opposite.op (SimplexCategory.mk n)) s' = f.app _ s := ⟨s, rfl⟩
  dsimp only [extendByZero, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]
  exact congrArg g (hf h.choose_spec)

/-- Extension by zero of cochains along a morphism which is injective on `n`-simplices: a linear
section of restriction of cochains along `f`. -/
def dualExtension :
    Module.Dual R ((S.chainComplex (ModuleCat.of R R)).X n) →ₗ[R]
      Module.Dual R ((T.chainComplex (ModuleCat.of R R)).X n) :=
  (dualEquivFun R T n).symm.toLinearMap ∘ₗ extendByZero R f n ∘ₗ
    (dualEquivFun R S n).toLinearMap

include hf in
lemma dualMap_dualExtension (φ : Module.Dual R ((S.chainComplex (ModuleCat.of R R)).X n)) :
    ((chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap (dualExtension R f n φ) = φ := by
  apply (dualEquivFun R S n).injective
  rw [dualEquivFun_dualMap]
  simp only [dualExtension, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  funext s
  exact extendByZero_app R f n hf (dualEquivFun R S n φ) s

include hf in
lemma dualMap_comp_dualExtension :
    ((chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap.comp (dualExtension R f n) =
      LinearMap.id :=
  LinearMap.ext (dualMap_dualExtension R f n hf)

include hf in
lemma dualMap_surjective :
    Function.Surjective ((chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap :=
  fun φ ↦ ⟨dualExtension R f n φ, dualMap_dualExtension R f n hf φ⟩

end Extension

section Subcomplex

variable {T : SSet.{u}} (S : T.Subcomplex) (n : ℕ)

/-- The inclusion of a subcomplex is injective on `n`-simplices. -/
lemma Subcomplex.ι_app_injective :
    Function.Injective (S.ι.app (Opposite.op (SimplexCategory.mk n))) :=
  injective_of_mono _

/-- Restriction of cochains to a subcomplex is surjective. -/
lemma Subcomplex.dualMap_surjective :
    Function.Surjective ((chainComplexMap S.ι (ModuleCat.of R R)).f n).hom.dualMap :=
  SSet.dualMap_surjective R S.ι n (Subcomplex.ι_app_injective S n)

lemma Subcomplex.dualMap_comp_dualExtension :
    ((chainComplexMap S.ι (ModuleCat.of R R)).f n).hom.dualMap.comp
        (dualExtension R S.ι n) = LinearMap.id :=
  SSet.dualMap_comp_dualExtension R S.ι n (Subcomplex.ι_app_injective S n)

end Subcomplex

end SSet

namespace TopCat

variable (R : Type u) [CommRing R]

/-- An injective continuous map is injective on singular `n`-simplices. -/
lemma toSSet_map_app_injective {X Y : TopCat.{u}} (g : X ⟶ Y) (hg : Function.Injective g)
    (n : ℕ) :
    Function.Injective ((toSSet.map g).app (Opposite.op (SimplexCategory.mk n))) := by
  have : Mono g := (TopCat.mono_iff_injective g).mpr hg
  have : Mono (toSSet.map g) := Functor.map_mono toSSet g
  exact injective_of_mono _

/-- Restriction of singular cochains along an injective continuous map is surjective. -/
lemma singularChainComplexFunctor_dualMap_surjective {X Y : TopCat.{u}} (g : X ⟶ Y)
    (hg : Function.Injective g) (n : ℕ) :
    Function.Surjective
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).map g).f n).hom.dualMap :=
  SSet.dualMap_surjective R (toSSet.map g) n (toSSet_map_app_injective g hg n)

/-- Extension by zero of singular cochains along an injective continuous map. -/
def singularCochainExtension {X Y : TopCat.{u}} (g : X ⟶ Y) (n : ℕ) :
    Module.Dual R
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)).obj X).X n) →ₗ[R]
      Module.Dual R
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)).obj Y).X n) :=
  SSet.dualExtension R (toSSet.map g) n

lemma singularChainComplexFunctor_dualMap_comp_singularCochainExtension {X Y : TopCat.{u}}
    (g : X ⟶ Y) (hg : Function.Injective g) (n : ℕ) :
    ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).map g).f n).hom.dualMap.comp (singularCochainExtension R g n) =
      LinearMap.id :=
  SSet.dualMap_comp_dualExtension R (toSSet.map g) n (toSSet_map_app_injective g hg n)

end TopCat
