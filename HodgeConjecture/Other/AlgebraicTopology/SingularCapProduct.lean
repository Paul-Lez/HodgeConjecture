/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.DeltaZeroIter
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Dual.Defs
public import HodgeConjecture.Other.AlgebraicTopology.SingularCochainCohomology

/-!
# The simplicial cap product

This file starts the chain-level foundation for Alexander--Poincare duality.  It defines the
front and back faces of a simplex and the cap product of a simplicial cochain with a simplicial
chain.  The construction uses the coproduct universal property of the unnormalised simplicial
chain group, so it does not choose chain representatives or a basis equivalence.

The convention on a simplex `x = [v₀, ..., vₚ₊ₒ]` is

`φ ∩ x = φ([v₀, ..., vₚ]) [vₚ, ..., vₚ₊ₒ]`.

We prove naturality at chain level.  The signed boundary formula, and hence descent to
homology, is developed after the elementary face identities below.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial
open scoped Simplicial

universe u

namespace AlgebraicTopology.Simplicial

/-- The inclusion of the first `p + 1` vertices in the vertices of a `(p + q)`-simplex. -/
def frontInclusion (p q : ℕ) : SimplexCategory.mk p ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom
    { toFun i := ⟨i.val, by omega⟩
      monotone' := by
        intro i j hij
        exact hij }

/-- The inclusion of the last `q + 1` vertices in the vertices of a `(p + q)`-simplex. -/
def backInclusion (p q : ℕ) : SimplexCategory.mk q ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom
    { toFun i := ⟨p + i.val, by omega⟩
      monotone' := by
        intro i j hij
        rw [Fin.le_iff_val_le_val]
        exact add_le_add_right (Fin.le_iff_val_le_val.mp hij) p }

@[simp]
lemma frontInclusion_apply (p q : ℕ) (i : Fin (p + 1)) :
    ((frontInclusion p q).toOrderHom i).val = i.val :=
  rfl

@[simp]
lemma backInclusion_apply (p q : ℕ) (i : Fin (q + 1)) :
    ((backInclusion p q).toOrderHom i).val = p + i.val :=
  rfl

/-- An index among the first `p + 1` faces of a `(p + q + 1)`-simplex. -/
def earlyFaceIndex (p q : ℕ) (i : Fin (p + 1)) : Fin (p + q + 2) :=
  ⟨i.val, by omega⟩

/-- An index among the last `q + 1` faces of a `(p + q + 1)`-simplex. -/
def lateFaceIndex (p q : ℕ) (j : Fin (q + 1)) : Fin (p + q + 2) :=
  ⟨p + 1 + j.val, by omega⟩

/-- The inclusion of the first `p + 2` vertices in a `(p + q + 1)`-simplex. -/
def nextFrontInclusion (p q : ℕ) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk (p + q + 1) :=
  SimplexCategory.mkHom
    { toFun i := ⟨i.val, by omega⟩
      monotone' := by
        intro i j hij
        exact hij }

/-- The inclusion of the last `q + 1` vertices after the first `p + 1` vertices. -/
def nextBackInclusion (p q : ℕ) :
    SimplexCategory.mk q ⟶ SimplexCategory.mk (p + q + 1) :=
  SimplexCategory.mkHom
    { toFun i := ⟨p + 1 + i.val, by omega⟩
      monotone' := by
        intro i j hij
        rw [Fin.le_iff_val_le_val]
        simpa only [Nat.add_comm] using
          add_le_add_left (Fin.le_iff_val_le_val.mp hij) (p + 1) }

/-- Split a sum over all faces into the first `p + 1` and final `q + 1` faces. -/
lemma sum_early_add_late {M : Type*} [AddCommMonoid M] (p q : ℕ)
    (f : Fin (p + q + 2) → M) :
    ∑ k, f k =
      (∑ i : Fin (p + 1), f (earlyFaceIndex p q i)) +
        ∑ j : Fin (q + 1), f (lateFaceIndex p q j) := by
  let h : p + q + 2 = (p + 1) + (q + 1) := by omega
  let e : Fin (p + q + 2) ≃ Fin ((p + 1) + (q + 1)) := finCongr h
  calc
    ∑ k, f k = ∑ k : Fin ((p + 1) + (q + 1)), f (e.symm k) := by
      apply Fintype.sum_equiv e
      intro k
      rfl
    _ = (∑ i : Fin (p + 1), f (earlyFaceIndex p q i)) +
        ∑ j : Fin (q + 1), f (lateFaceIndex p q j) := by
      rw [Fin.sum_univ_add]
      congr 1

/-- Taking an early face and then its front face equals taking the corresponding face of the
next front face. -/
lemma frontInclusion_comp_earlyFace (p q : ℕ) (i : Fin (p + 1)) :
    frontInclusion p q ≫ SimplexCategory.δ (earlyFaceIndex p q i) =
      SimplexCategory.δ (Fin.castSucc i) ≫ nextFrontInclusion p q := by
  ext k
  simp only [frontInclusion, nextFrontInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  by_cases hki : k.castSucc < i.castSucc
  · rw [Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_castSucc_lt]
    · rfl
    · rw [Fin.lt_def] at hki ⊢
      simp only [Fin.val_castSucc] at hki ⊢
      exact hki
    · exact hki
  · rw [Fin.succAbove_of_le_castSucc, Fin.succAbove_of_le_castSucc]
    · rfl
    · rw [Fin.le_iff_val_le_val] at ⊢
      simp only [Fin.val_castSucc]
      exact Fin.le_iff_val_le_val.mp (le_of_not_gt hki)
    · exact le_of_not_gt hki

/-- Taking an early face and then its back face drops the first `p + 1` vertices. -/
lemma backInclusion_comp_earlyFace (p q : ℕ) (i : Fin (p + 1)) :
    backInclusion p q ≫ SimplexCategory.δ (earlyFaceIndex p q i) =
      nextBackInclusion p q := by
  ext k
  simp only [backInclusion, nextBackInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_le_castSucc]
  · change p + k.val + 1 = p + 1 + k.val
    omega
  · rw [Fin.le_iff_val_le_val]
    change i.val ≤ p + k.val
    omega

/-- A late face does not change the front face. -/
lemma frontInclusion_comp_lateFace (p q : ℕ) (j : Fin (q + 1)) :
    frontInclusion p q ≫ SimplexCategory.δ (lateFaceIndex p q j) =
      frontInclusion p (q + 1) := by
  ext k
  simp only [frontInclusion, SimplexCategory.δ, SimplexCategory.len_mk,
    SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · rw [Fin.lt_def]
    have hk : k.val < p + 1 := by
      simpa only [SimplexCategory.len_mk] using k.isLt
    change k.val < p + 1 + j.val
    omega

/-- On the back face, the `j`-th late face is face `j + 1`. -/
lemma backInclusion_comp_lateFace (p q : ℕ) (j : Fin (q + 1)) :
    backInclusion p q ≫ SimplexCategory.δ (lateFaceIndex p q j) =
      SimplexCategory.δ j.succ ≫ backInclusion p (q + 1) := by
  ext k
  simp only [backInclusion, SimplexCategory.δ, SimplexCategory.len_mk,
    SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply]
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  dsimp [backInclusion, lateFaceIndex, Fin.succAbove]
  split_ifs <;> simp at * <;> omega

/-- Dropping the last vertex of the next front face gives the ordinary front face. -/
lemma lastFace_comp_nextFrontInclusion (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ nextFrontInclusion p q =
      frontInclusion p (q + 1) := by
  ext k
  simp only [frontInclusion, nextFrontInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt]
  rfl
  exact k.castSucc_lt_last

/-- Dropping the first vertex of the ordinary back face gives the next back face. -/
lemma firstFace_comp_backInclusion (p q : ℕ) :
    SimplexCategory.δ 0 ≫ backInclusion p (q + 1) = nextBackInclusion p q := by
  ext k
  simp only [backInclusion, nextBackInclusion, SimplexCategory.δ,
    SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, Fin.zero_succAbove]
  change p + (k.val + 1) = p + 1 + k.val
  omega

variable (X : SSet.{u})

/-- The front `p`-face of a `(p + q)`-simplex. -/
def frontFace {p q : ℕ} (x : X _⦋p + q⦌) : X _⦋p⦌ :=
  X.map (frontInclusion p q).op x

/-- The back `q`-face of a `(p + q)`-simplex. -/
def backFace {p q : ℕ} (x : X _⦋p + q⦌) : X _⦋q⦌ :=
  X.map (backInclusion p q).op x

variable {X}

/-- The front `(p + 1)`-face of a `(p + q + 1)`-simplex. -/
def nextFrontFace (X : SSet.{u}) {p q : ℕ} (x : X _⦋p + q + 1⦌) : X _⦋p + 1⦌ :=
  X.map (nextFrontInclusion p q).op x

/-- The final `q`-face of a `(p + q + 1)`-simplex, after discarding the first `p + 1`
vertices. -/
def nextBackFace (X : SSet.{u}) {p q : ℕ} (x : X _⦋p + q + 1⦌) : X _⦋q⦌ :=
  X.map (nextBackInclusion p q).op x

/-- The equality morphism which reassociates the degree of a simplex so it can be viewed as
an input to cap product by a cochain of successor degree. -/
def capDegreeReassoc (p q : ℕ) :
    SimplexCategory.mk (p + 1 + q) ⟶ SimplexCategory.mk (p + q + 1) :=
  eqToHom (by congr 1; omega)

/-- Reassociate the degree of a simplex through the simplicial functor. -/
def reassocSimplex (X : SSet.{u}) {p q : ℕ} (x : X _⦋p + q + 1⦌) :
    X _⦋p + 1 + q⦌ :=
  X.map (capDegreeReassoc p q).op x

lemma frontInclusion_succ_comp_capDegreeReassoc (p q : ℕ) :
    frontInclusion (p + 1) q ≫ capDegreeReassoc p q = nextFrontInclusion p q := by
  ext i
  simp [frontInclusion, capDegreeReassoc, nextFrontInclusion,
    SimplexCategory.eqToHom_toOrderHom]

lemma backInclusion_succ_comp_capDegreeReassoc (p q : ℕ) :
    backInclusion (p + 1) q ≫ capDegreeReassoc p q = nextBackInclusion p q := by
  ext i
  simp [backInclusion, capDegreeReassoc, nextBackInclusion,
    SimplexCategory.eqToHom_toOrderHom]

lemma frontFace_reassocSimplex (X : SSet.{u}) {p q : ℕ}
    (x : X _⦋p + q + 1⦌) :
    frontFace (p := p + 1) (q := q) X (reassocSimplex X x) =
      nextFrontFace X x := by
  simp only [frontFace, reassocSimplex, nextFrontFace, ← Functor.map_comp_apply,
    ← op_comp, frontInclusion_succ_comp_capDegreeReassoc]

lemma backFace_reassocSimplex (X : SSet.{u}) {p q : ℕ}
    (x : X _⦋p + q + 1⦌) :
    backFace (p := p + 1) (q := q) X (reassocSimplex X x) =
      nextBackFace X x := by
  simp only [backFace, reassocSimplex, nextBackFace, ← Functor.map_comp_apply,
    ← op_comp, backInclusion_succ_comp_capDegreeReassoc]

/-- An early face of a simplex restricts on the front to the corresponding face. -/
lemma frontFace_earlyFace {p q : ℕ} (x : X _⦋p + q + 1⦌) (i : Fin (p + 1)) :
    frontFace X (X.δ (earlyFaceIndex p q i) x) =
      X.δ i.castSucc (nextFrontFace X x) := by
  simp only [frontFace, nextFrontFace, SimplicialObject.δ_def,
    ← Functor.map_comp_apply, ← op_comp, frontInclusion_comp_earlyFace]

/-- An early face of a simplex has the common final `q`-face. -/
lemma backFace_earlyFace {p q : ℕ} (x : X _⦋p + q + 1⦌) (i : Fin (p + 1)) :
    backFace X (X.δ (earlyFaceIndex p q i) x) = nextBackFace X x := by
  simp only [backFace, nextBackFace, SimplicialObject.δ_def,
    ← Functor.map_comp_apply, ← op_comp, backInclusion_comp_earlyFace]

/-- A late face of a simplex has the common front `p`-face. -/
lemma frontFace_lateFace {p q : ℕ} (x : X _⦋p + q + 1⦌) (j : Fin (q + 1)) :
    frontFace X (X.δ (lateFaceIndex p q j) x) =
      frontFace (p := p) (q := q + 1) X x := by
  simp only [frontFace, SimplicialObject.δ_def,
    ← Functor.map_comp_apply, ← op_comp, frontInclusion_comp_lateFace]

/-- On the back, a late face of a simplex becomes face `j + 1`. -/
lemma backFace_lateFace {p q : ℕ} (x : X _⦋p + q + 1⦌) (j : Fin (q + 1)) :
    backFace X (X.δ (lateFaceIndex p q j) x) =
      X.δ j.succ (backFace (p := p) (q := q + 1) X x) := by
  simp only [backFace, SimplicialObject.δ_def,
    ← Functor.map_comp_apply, ← op_comp, backInclusion_comp_lateFace]

/-- The last face of the next front face is the ordinary front face. -/
lemma lastFace_nextFrontFace {p q : ℕ} (x : X _⦋p + q + 1⦌) :
    X.δ (Fin.last (p + 1)) (nextFrontFace X x) =
      frontFace (p := p) (q := q + 1) X x := by
  simp only [nextFrontFace, frontFace, SimplicialObject.δ_def,
    ← Functor.map_comp_apply, ← op_comp, lastFace_comp_nextFrontInclusion]

/-- The first face of the ordinary back face is the next back face. -/
lemma firstFace_backFace {p q : ℕ} (x : X _⦋p + q + 1⦌) :
    X.δ 0 (backFace (p := p) (q := q + 1) X x) = nextBackFace X x := by
  simp only [backFace, nextBackFace, SimplicialObject.δ_def,
    ← Functor.map_comp_apply, ← op_comp, firstFace_comp_backInclusion]

/-- Front faces commute with maps of simplicial sets. -/
lemma frontFace_naturality {Y : SSet.{u}} (f : X ⟶ Y) {p q : ℕ}
    (x : X _⦋p + q⦌) :
    frontFace Y (f.app _ x) = f.app _ (frontFace X x) := by
  exact (NatTrans.naturality_apply f (frontInclusion p q).op x).symm

/-- Back faces commute with maps of simplicial sets. -/
lemma backFace_naturality {Y : SSet.{u}} (f : X ⟶ Y) {p q : ℕ}
    (x : X _⦋p + q⦌) :
    backFace Y (f.app _ x) = f.app _ (backFace X x) := by
  exact (NatTrans.naturality_apply f (backInclusion p q).op x).symm

variable (R : Type u) [Field R]

/-- Unnormalised simplicial chains with coefficients in a field, in one degree. -/
abbrev ChainGroup (X : SSet.{u}) (n : ℕ) : ModuleCat.{u} R :=
  (X.chainComplex (ModuleCat.of R R)).X n

/-- Algebraic simplicial cochains in one degree. -/
abbrev Cochain (X : SSet.{u}) (n : ℕ) := Module.Dual R (ChainGroup R X n)

/-- Reassociate a chain degree from `p + q + 1` to `(p + 1) + q`. -/
def reassocChain {X : SSet.{u}} (p q : ℕ) :
    ChainGroup R X (p + q + 1) →ₗ[R] ChainGroup R X (p + 1 + q) :=
  ((X.chainComplex (ModuleCat.of R R)).XIsoOfEq (by omega)).hom.hom

/-- The chain containing one simplex with coefficient one. -/
def chainOfSimplex {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) : ChainGroup R X n :=
  (X.ιChainComplex (R := ModuleCat.of R R) x).hom 1

lemma XIsoOfEq_chainOfSimplex {X : SSet.{u}} {m n : ℕ} (h : m = n)
    (x : X _⦋m⦌) :
    (((X.chainComplex (ModuleCat.of R R)).XIsoOfEq h).hom.hom) (chainOfSimplex R x) =
      chainOfSimplex R
        (X.map (eqToHom (congrArg SimplexCategory.mk h.symm)).op x) := by
  subst n
  simp [HomologicalComplex.XIsoOfEq, chainOfSimplex]

lemma XIsoOfEq_chainOfSimplex_reassoc {X : SSet.{u}} {p q : ℕ}
    (x : X _⦋p + q + 1⦌) :
    (((X.chainComplex (ModuleCat.of R R)).XIsoOfEq
      (by omega : p + q + 1 = p + 1 + q)).hom.hom) (chainOfSimplex R x) =
      chainOfSimplex R (reassocSimplex X x) := by
  simpa only [reassocSimplex, capDegreeReassoc] using
    XIsoOfEq_chainOfSimplex R (X := X)
      (by omega : p + q + 1 = p + 1 + q) x

@[simp]
lemma reassocChain_chainOfSimplex {X : SSet.{u}} {p q : ℕ}
    (x : X _⦋p + q + 1⦌) :
    reassocChain R p q (chainOfSimplex R x) =
      chainOfSimplex R (reassocSimplex X x) :=
  XIsoOfEq_chainOfSimplex_reassoc R x

@[simp]
lemma chainOfSimplex_map {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom (chainOfSimplex R x) =
      chainOfSimplex R (f.app _ x) := by
  have h := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f (X := X) (Y := Y) (f := f)
      (R := ModuleCat.of R R) x) 1
  change ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom
      ((X.ιChainComplex (R := ModuleCat.of R R) x).hom 1) =
    (Y.ιChainComplex (R := ModuleCat.of R R) (f.app _ x)).hom 1
  simpa only [ConcreteCategory.comp_apply] using h

/-- The boundary on unnormalised simplicial chains in degree `n + 1`. -/
def boundary {X : SSet.{u}} (n : ℕ) :
    ChainGroup R X (n + 1) →ₗ[R] ChainGroup R X n :=
  ((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom

@[simp]
lemma boundary_chainOfSimplex {X : SSet.{u}} {n : ℕ} (x : X _⦋n + 1⦌) :
    boundary R n (chainOfSimplex R x) =
      ∑ i : Fin (n + 2), (-1 : R) ^ i.val • chainOfSimplex R (X.δ i x) := by
  have h := ConcreteCategory.congr_hom
    (SSet.ιChainComplex_d X (R := ModuleCat.of R R) x) 1
  change ((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom
      ((X.ιChainComplex (R := ModuleCat.of R R) x).hom 1) = _
  calc
    _ = (∑ i : Fin (n + 2),
          (-1 : ℤ) ^ i.val •
            (X.ιChainComplex (R := ModuleCat.of R R) (X.δ i x)).hom) 1 := by
      simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_sum,
        ModuleCat.hom_zsmul] using h
    _ = _ := by
      rw [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Int.cast_smul_eq_zsmul R]
      norm_num
      rfl

/-- The algebraic coboundary, obtained by dualising the simplicial boundary. -/
def coboundary {X : SSet.{u}} (n : ℕ) :
    Cochain R X n →ₗ[R] Cochain R X (n + 1) :=
  (boundary R n).dualMap

@[simp]
lemma coboundary_apply {X : SSet.{u}} (n : ℕ) (phi : Cochain R X n)
    (c : ChainGroup R X (n + 1)) :
    coboundary R n phi c = phi (boundary R n c) :=
  rfl

@[simp]
lemma coboundary_chainOfSimplex {X : SSet.{u}} {n : ℕ} (phi : Cochain R X n)
    (x : X _⦋n + 1⦌) :
    coboundary R n phi (chainOfSimplex R x) =
      ∑ i : Fin (n + 2), (-1 : R) ^ i.val •
        phi (chainOfSimplex R (X.δ i x)) := by
  rw [coboundary_apply, boundary_chainOfSimplex]
  simp

/-- Consecutive coboundaries vanish. -/
lemma coboundary_coboundary {X : SSet.{u}} (n : ℕ) (phi : Cochain R X n) :
    coboundary R (n + 1) (coboundary R n phi) = 0 := by
  apply LinearMap.ext
  intro c
  change phi (boundary R n (boundary R (n + 1) c)) = 0
  have h := (X.chainComplex (ModuleCat.of R R)).d_comp_d (n + 2) (n + 1) n
  rw [show boundary R n (boundary R (n + 1) c) = 0 by
    exact ConcreteCategory.congr_hom h c, map_zero]

/-- The categorical cap-product map by a fixed cochain.  On a simplex `x`, it evaluates the
cochain on the front face and multiplies the back face by the resulting scalar. -/
def capHom {X : SSet.{u}} (p q : ℕ) (φ : Cochain R X p) :
    ChainGroup R X (p + q) ⟶ ChainGroup R X q :=
  (X.isColimitChainComplexXCofan (ModuleCat.of R R) (p + q)).desc
    (Cofan.mk _ fun x ↦ ModuleCat.ofHom <|
      LinearMap.toSpanSingleton R _ <|
        φ (chainOfSimplex R (frontFace X x)) •
          chainOfSimplex R (backFace X x))

/-- The cap-product map by a fixed cochain, as a linear map. -/
def cap {X : SSet.{u}} (p q : ℕ) (phi : Cochain R X p) :
    ChainGroup R X (p + q) →ₗ[R] ChainGroup R X q :=
  (capHom R p q phi).hom

@[reassoc]
lemma iota_capHom {X : SSet.{u}} (p q : ℕ) (phi : Cochain R X p)
    (x : X _⦋p + q⦌) :
    X.ιChainComplex (R := ModuleCat.of R R) x ≫ capHom R p q phi =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ <|
        phi (chainOfSimplex R (frontFace X x)) •
          chainOfSimplex R (backFace X x)) := by
  exact (X.isColimitChainComplexXCofan (ModuleCat.of R R) (p + q)).fac _ (Discrete.mk x)

@[simp]
lemma cap_chainOfSimplex {X : SSet.{u}} (p q : ℕ) (phi : Cochain R X p)
    (x : X _⦋p + q⦌) :
    cap R p q phi (chainOfSimplex R x) =
      phi (chainOfSimplex R (frontFace X x)) • chainOfSimplex R (backFace X x) := by
  have h := ConcreteCategory.congr_hom (iota_capHom R p q phi x) 1
  simpa [cap, chainOfSimplex] using h

/-- The cap product of a cochain with the boundary of one simplex, split at the overlap
vertex.  This is the finite-sum core of the cap-product boundary identity. -/
lemma cap_boundary_chainOfSimplex {X : SSet.{u}} (p q : ℕ) (phi : Cochain R X p)
    (x : X _⦋p + q + 1⦌) :
    cap R p q phi (boundary R (p + q) (chainOfSimplex R x)) =
      (∑ i : Fin (p + 1), (-1 : R) ^ i.val •
        (phi (chainOfSimplex R (X.δ i.castSucc (nextFrontFace X x))) •
          chainOfSimplex R (nextBackFace X x))) +
      ∑ j : Fin (q + 1), (-1 : R) ^ (p + 1 + j.val) •
        (phi (chainOfSimplex R (frontFace (p := p) (q := q + 1) X x)) •
          chainOfSimplex R
            (X.δ j.succ (backFace (p := p) (q := q + 1) X x))) := by
  rw [boundary_chainOfSimplex, map_sum]
  simp_rw [map_smul, cap_chainOfSimplex]
  rw [sum_early_add_late p q]
  simp_rw [frontFace_earlyFace, backFace_earlyFace,
    frontFace_lateFace, backFace_lateFace]
  rfl

/-- Evaluate the coboundary on the next front face, separating its last face. -/
lemma coboundary_nextFrontFace {X : SSet.{u}} (p q : ℕ) (phi : Cochain R X p)
    (x : X _⦋p + q + 1⦌) :
    coboundary R p phi (chainOfSimplex R (nextFrontFace X x)) =
      (∑ i : Fin (p + 1), (-1 : R) ^ i.val •
        phi (chainOfSimplex R (X.δ i.castSucc (nextFrontFace X x)))) +
      (-1 : R) ^ (p + 1) •
        phi (chainOfSimplex R (frontFace (p := p) (q := q + 1) X x)) := by
  rw [coboundary_chainOfSimplex, Fin.sum_univ_castSucc]
  simp_rw [lastFace_nextFrontFace]
  rfl

/-- Boundary of the cap product with one simplex, with the overlap face displayed first. -/
lemma boundary_cap_chainOfSimplex {X : SSet.{u}} (p q : ℕ) (phi : Cochain R X p)
    (x : X _⦋p + q + 1⦌) :
    boundary R q (cap R p (q + 1) phi (chainOfSimplex R x)) =
      phi (chainOfSimplex R (frontFace (p := p) (q := q + 1) X x)) •
        (chainOfSimplex R (nextBackFace X x) +
          ∑ j : Fin (q + 1), (-1 : R) ^ (j.val + 1) •
            chainOfSimplex R
              (X.δ j.succ (backFace (p := p) (q := q + 1) X x))) := by
  rw [cap_chainOfSimplex, map_smul, boundary_chainOfSimplex]
  congr 1
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, firstFace_backFace, Fin.val_succ]

/-- Signed boundary identity for the cap product on a simplex.  Its cochain term is written
without a degree cast: it is exactly the value that the cap product by `δphi` has on `x`. -/
theorem boundary_cap_chainOfSimplex_eq {X : SSet.{u}} (p q : ℕ) (phi : Cochain R X p)
    (x : X _⦋p + q + 1⦌) :
    boundary R q (cap R p (q + 1) phi (chainOfSimplex R x)) =
      (-1 : R) ^ p •
        (cap R p q phi (boundary R (p + q) (chainOfSimplex R x)) -
          coboundary R p phi (chainOfSimplex R (nextFrontFace X x)) •
            chainOfSimplex R (nextBackFace X x)) := by
  rw [boundary_cap_chainOfSimplex, cap_boundary_chainOfSimplex,
    coboundary_nextFrontFace]
  have hsign (n : ℕ) :
      (-1 : R) ^ p * (-1 : R) ^ (p + 1 + n) = (-1 : R) ^ (n + 1) := by
    rw [← pow_add, show p + (p + 1 + n) = (p + p) + (n + 1) by omega,
      pow_add, (Even.add_self p).neg_one_pow, one_mul]
  have hsign0 : (-1 : R) ^ p * (-1 : R) ^ (p + 1) = -1 := by
    simpa using hsign 0
  simp only [add_smul, smul_add, smul_sub, Finset.sum_smul,
    Finset.smul_sum, smul_smul, smul_eq_mul]
  simp_rw [← mul_assoc, hsign]
  simp only [hsign0, neg_one_mul, mul_comm]
  simp only [neg_smul]
  abel

/-- On a generator, the coboundary term in the cap boundary formula is itself a cap
product after the canonical reassociation of the source degree. -/
lemma cap_coboundary_reassoc_chainOfSimplex {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) (x : X _⦋p + q + 1⦌) :
    cap R (p + 1) q (coboundary R p phi)
        (reassocChain R p q (chainOfSimplex R x)) =
      coboundary R p phi (chainOfSimplex R (nextFrontFace X x)) •
        chainOfSimplex R (nextBackFace X x) := by
  rw [reassocChain_chainOfSimplex, cap_chainOfSimplex,
    frontFace_reassocSimplex, backFace_reassocSimplex]

/-- The cap product by a coboundary is chain-null-homotopic.  The displayed formula is
the homotopy identity, with `reassocChain` accounting only for the associativity of natural
number addition in the source degree. -/
theorem cap_coboundary_eq {X : SSet.{u}} (p q : ℕ) (phi : Cochain R X p) :
    (cap R (p + 1) q (coboundary R p phi)).comp (reassocChain R p q) =
      (cap R p q phi).comp (boundary R (p + q)) -
        (-1 : R) ^ p • (boundary R q).comp (cap R p (q + 1) phi) := by
  let lhs := (cap R (p + 1) q (coboundary R p phi)).comp (reassocChain R p q)
  let rhs := (cap R p q phi).comp (boundary R (p + q)) -
    (-1 : R) ^ p • (boundary R q).comp (cap R p (q + 1) phi)
  have hcat : ModuleCat.ofHom lhs = ModuleCat.ofHom rhs := by
    apply SSet.chainComplex_hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hiota :
        (X.ιChainComplex (R := ModuleCat.of R R) x).hom a =
          a • chainOfSimplex R x := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change lhs ((X.ιChainComplex (R := ModuleCat.of R R) x).hom a) =
      rhs ((X.ιChainComplex (R := ModuleCat.of R R) x).hom a)
    rw [hiota]
    simp only [lhs, rhs, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, map_smul]
    rw [cap_coboundary_reassoc_chainOfSimplex,
      boundary_cap_chainOfSimplex_eq]
    have hs : (-1 : R) ^ p * (-1 : R) ^ p = 1 := by
      rw [← pow_add, (Even.add_self p).neg_one_pow]
    simp only [smul_sub, smul_smul, hs, one_smul]
    simp only [← mul_assoc, hs, one_mul]
    abel
  change lhs = rhs
  simpa only [ModuleCat.hom_ofHom] using congrArg ModuleCat.Hom.hom hcat

/-- For a cocycle, cap product intertwines boundaries up to the conventional sign. -/
theorem cap_boundary_compatibility_of_cocycle {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) (hphi : coboundary R p phi = 0) :
    (boundary R q).comp (cap R p (q + 1) phi) =
      (-1 : R) ^ p • (cap R p q phi).comp (boundary R (p + q)) := by
  let lhs := (boundary R q).comp (cap R p (q + 1) phi)
  let rhs := (-1 : R) ^ p • (cap R p q phi).comp (boundary R (p + q))
  have hcat : ModuleCat.ofHom lhs = ModuleCat.ofHom rhs := by
    apply SSet.chainComplex_hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change lhs ((X.ιChainComplex (R := ModuleCat.of R R) x).hom a) =
      rhs ((X.ιChainComplex (R := ModuleCat.of R R) x).hom a)
    have hiota :
        (X.ιChainComplex (R := ModuleCat.of R R) x).hom a =
          a • chainOfSimplex R x := by
      rw [chainOfSimplex, ← map_smul]
      simp
    have hphi_apply :
        coboundary R p phi (chainOfSimplex R (nextFrontFace X x)) = 0 := by
      rw [hphi]
      rfl
    rw [hiota]
    simp only [lhs, rhs, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
    rw [boundary_cap_chainOfSimplex_eq, hphi_apply, zero_smul, sub_zero]
  change lhs = rhs
  simpa only [ModuleCat.hom_ofHom] using congrArg ModuleCat.Hom.hom hcat

/-- Elementwise form of `cap_boundary_compatibility_of_cocycle`. -/
theorem boundary_cap_eq_of_cocycle {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) (hphi : coboundary R p phi = 0)
    (c : ChainGroup R X (p + q + 1)) :
    boundary R q (cap R p (q + 1) phi c) =
      (-1 : R) ^ p • cap R p q phi (boundary R (p + q) c) := by
  have h := LinearMap.congr_fun
    (cap_boundary_compatibility_of_cocycle R p q phi hphi) c
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using h

@[simp]
lemma capHom_zero {X : SSet.{u}} (p q : ℕ) :
    capHom R p q (0 : Cochain R X p) = 0 := by
  apply SSet.chainComplex_hom_ext
  intro x
  rw [iota_capHom, comp_zero]
  simp

lemma capHom_add {X : SSet.{u}} (p q : ℕ) (phi psi : Cochain R X p) :
    capHom R p q (phi + psi) = capHom R p q phi + capHom R p q psi := by
  apply SSet.chainComplex_hom_ext
  intro x
  rw [iota_capHom, Preadditive.comp_add, iota_capHom, iota_capHom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply]
  simp [add_smul]

lemma capHom_smul {X : SSet.{u}} (p q : ℕ) (a : R) (phi : Cochain R X p) :
    capHom R p q (a • phi) = a • capHom R p q phi := by
  apply SSet.chainComplex_hom_ext
  intro x
  rw [iota_capHom, Linear.comp_smul, iota_capHom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply]
  simp only [smul_smul]
  congr 1
  ring

/-- The cap product, linear in the cochain argument. -/
def capLinear {X : SSet.{u}} (p q : ℕ) :
    Cochain R X p →ₗ[R] (ChainGroup R X (p + q) →ₗ[R] ChainGroup R X q) where
  toFun := cap R p q
  map_add' phi psi := by
    change (capHom R p q (phi + psi)).hom =
      (capHom R p q phi).hom + (capHom R p q psi).hom
    rw [← ModuleCat.hom_add]
    exact congrArg ModuleCat.Hom.hom (capHom_add R p q phi psi)
  map_smul' a phi := by
    change (capHom R p q (a • phi)).hom = a • (capHom R p q phi).hom
    rw [← ModuleCat.hom_smul]
    exact congrArg ModuleCat.Hom.hom (capHom_smul R p q a phi)

@[simp]
lemma capLinear_apply {X : SSet.{u}} (p q : ℕ) (phi : Cochain R X p) :
    capLinear R p q phi = cap R p q phi :=
  rfl

/-- Pullback of an algebraic simplicial cochain. -/
def cochainMap {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    Cochain R Y n →ₗ[R] Cochain R X n :=
  ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap

@[simp]
lemma cochainMap_apply {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (phi : Cochain R Y n) (c : ChainGroup R X n) :
    cochainMap R f n phi c =
      phi (((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom c) :=
  rfl

/-- Chain-level naturality of the cap product. -/
theorem cap_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (p q : ℕ)
    (phi : Cochain R Y p) (c : ChainGroup R X (p + q)) :
    ((SSet.chainComplexMap f (ModuleCat.of R R)).f q).hom
        (cap R p q (cochainMap R f p phi) c) =
      cap R p q phi
        (((SSet.chainComplexMap f (ModuleCat.of R R)).f (p + q)).hom c) := by
  let lhs : ChainGroup R X (p + q) ⟶ ChainGroup R Y q :=
    capHom R p q (cochainMap R f p phi) ≫
      (SSet.chainComplexMap f (ModuleCat.of R R)).f q
  let rhs : ChainGroup R X (p + q) ⟶ ChainGroup R Y q :=
    (SSet.chainComplexMap f (ModuleCat.of R R)).f (p + q) ≫ capHom R p q phi
  have h : lhs = rhs := by
    apply SSet.chainComplex_hom_ext
    intro x
    dsimp [lhs, rhs]
    rw [iota_capHom_assoc,
      SSet.ι_chainComplexMap_f_assoc, iota_capHom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply]
    rw [cochainMap_apply, map_smul, chainOfSimplex_map,
      frontFace_naturality, backFace_naturality]
    simp only [map_smul, chainOfSimplex_map, smul_smul]
  exact ConcreteCategory.congr_hom h c

/-! ## Descent to homology -/

/-- Algebraic simplicial cocycles. -/
abbrev Cocycle (R : Type u) [Field R] (X : SSet.{u}) (p : ℕ) :=
  LinearMap.ker (coboundary R p : Cochain R X p →ₗ[R] Cochain R X (p + 1))

/-- Maps of short complexes with the same middle component induce the same map on homology. -/
lemma homologyMap_eq_of_τ₂_eq
    {S T : ShortComplex (ModuleCat.{u} R)} [S.HasHomology] [T.HasHomology]
    (f g : S ⟶ T) (h : f.τ₂ = g.τ₂) :
    ShortComplex.homologyMap f = ShortComplex.homologyMap g := by
  rw [← cancel_epi S.homologyπ, ← cancel_mono T.homologyι]
  simp only [Category.assoc]
  rw [ShortComplex.π_homologyMap_ι, ShortComplex.π_homologyMap_ι, h]

/-- The explicit three-degree cap morphism ending in degree zero. -/
noncomputable def capShortComplexHomZero {X : SSet.{u}} (p : ℕ)
    (phi : Cochain R X p) (hphi : coboundary R p phi = 0) :
    (X.chainComplex (ModuleCat.of R R)).sc' (p + 1) p
        ((ComplexShape.down ℕ).next p) ⟶
      (X.chainComplex (ModuleCat.of R R)).sc' 1 0 0 := by
  let s : R := (-1 : R) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine
    { τ₁ := ModuleCat.ofHom (s • cap R p 1 phi)
      τ₂ := capHom R p 0 phi
      τ₃ := 0
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change boundary R 0 (s • cap R p 1 phi c) =
      cap R p 0 phi (boundary R p c)
    rw [map_smul]
    have h := boundary_cap_eq_of_cocycle R p 0 phi hphi c
    simpa [s, hs, smul_smul] using congrArg (fun z ↦ s • z) h
  · change capHom R p 0 phi ≫
        (X.chainComplex (ModuleCat.of R R)).d 0 0 =
      (X.chainComplex (ModuleCat.of R R)).d p ((ComplexShape.down ℕ).next p) ≫ 0
    rw [(X.chainComplex (ModuleCat.of R R)).shape 0 0 (by simp),
      comp_zero, comp_zero]

/-- The explicit three-degree cap morphism ending in a positive degree. -/
noncomputable def capShortComplexHomSucc {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) (hphi : coboundary R p phi = 0) :
    (X.chainComplex (ModuleCat.of R R)).sc' (p + (q + 2)) (p + (q + 1)) (p + q) ⟶
      (X.chainComplex (ModuleCat.of R R)).sc' (q + 2) (q + 1) q := by
  let s : R := (-1 : R) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine
    { τ₁ := ModuleCat.ofHom (s • cap R p (q + 2) phi)
      τ₂ := capHom R p (q + 1) phi
      τ₃ := ModuleCat.ofHom (s • cap R p q phi)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change boundary R (q + 1) (s • cap R p (q + 2) phi c) =
      cap R p (q + 1) phi (boundary R (p + (q + 1)) c)
    rw [map_smul]
    have h := boundary_cap_eq_of_cocycle R p (q + 1) phi hphi c
    simpa [s, hs, smul_smul] using congrArg (fun z ↦ s • z) h
  · apply ModuleCat.hom_ext
    exact cap_boundary_compatibility_of_cocycle R p q phi hphi

/-- The short-complex morphism induced by capping with a cocycle.  The adjacent-degree
components carry the sign needed to turn the signed cap boundary formula into strictly
commutative squares. -/
noncomputable def capShortComplexHom {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) (hphi : coboundary R p phi = 0) :
    (X.chainComplex (ModuleCat.of R R)).sc (p + q) ⟶
      (X.chainComplex (ModuleCat.of R R)).sc q := by
  let K := X.chainComplex (ModuleCat.of R R)
  cases q with
  | zero =>
      exact
        (K.isoSc' (p + 1) p ((ComplexShape.down ℕ).next p)
            (ChainComplex.prev ℕ p) rfl).hom ≫
          capShortComplexHomZero R p phi hphi ≫
          (K.isoSc' 1 0 0 (ChainComplex.prev ℕ 0)
            ChainComplex.next_nat_zero).inv
  | succ q =>
      exact
        (K.isoSc' (p + (q + 2)) (p + (q + 1)) (p + q)
            (by rw [ChainComplex.prev]; omega)
            (by rw [show p + (q + 1) = (p + q) + 1 by omega,
              ChainComplex.next_nat_succ])).hom ≫
          capShortComplexHomSucc R p q phi hphi ≫
          (K.isoSc' (q + 2) (q + 1) q
            (by rw [ChainComplex.prev]; omega) (ChainComplex.next_nat_succ q)).inv

@[simp]
lemma capShortComplexHom_τ₂ {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) (hphi : coboundary R p phi = 0) :
    (capShortComplexHom R p q phi hphi).τ₂ = capHom R p q phi := by
  cases q <;> simp [capShortComplexHom, capShortComplexHomZero,
    capShortComplexHomSucc] <;> cat_disch

/-- Additivity of the homology map induced by cap product with cocycles. -/
lemma capShortComplexHom_homologyMap_add {X : SSet.{u}} (p q : ℕ)
    (phi psi : Cochain R X p) (hphi : coboundary R p phi = 0)
    (hpsi : coboundary R p psi = 0)
    (hadd : coboundary R p (phi + psi) = 0) :
    ShortComplex.homologyMap (capShortComplexHom R p q (phi + psi) hadd) =
      ShortComplex.homologyMap (capShortComplexHom R p q phi hphi) +
        ShortComplex.homologyMap (capShortComplexHom R p q psi hpsi) := by
  rw [← ShortComplex.homologyMap_add]
  apply homologyMap_eq_of_τ₂_eq
  simp [capShortComplexHom_τ₂, capHom_add]
  rfl

/-- Linearity in scalars of the homology map induced by cap product with cocycles. -/
lemma capShortComplexHom_homologyMap_smul {X : SSet.{u}} (p q : ℕ)
    (a : R) (phi : Cochain R X p) (hphi : coboundary R p phi = 0)
    (hsmul : coboundary R p (a • phi) = 0) :
    ShortComplex.homologyMap (capShortComplexHom R p q (a • phi) hsmul) =
      a • ShortComplex.homologyMap (capShortComplexHom R p q phi hphi) := by
  rw [← ShortComplex.homologyMap_smul]
  apply homologyMap_eq_of_τ₂_eq
  simp [capShortComplexHom_τ₂, capHom_smul]
  rfl

/-- Reassociation of a degree gives the corresponding canonical isomorphism of homology
short complexes. -/
noncomputable def reassocShortComplexIso {X : SSet.{u}} (p q : ℕ) :
    (X.chainComplex (ModuleCat.of R R)).sc (p + q + 1) ≅
      (X.chainComplex (ModuleCat.of R R)).sc (p + 1 + q) :=
  eqToIso (congrArg (fun n ↦ (X.chainComplex (ModuleCat.of R R)).sc n)
    (by omega : p + q + 1 = p + 1 + q))

lemma reassocShortComplexIso_hom_τ₂ {X : SSet.{u}} (p q : ℕ) :
    (reassocShortComplexIso R (X := X) p q).hom.τ₂ =
      ModuleCat.ofHom (reassocChain R (X := X) p q) := by
  let K := X.chainComplex (ModuleCat.of R R)
  have eqToIso_sc_hom_τ₂ {m n : ℕ} (h : m = n) :
      (eqToIso (congrArg (fun i ↦ K.sc i) h)).hom.τ₂ = (K.XIsoOfEq h).hom := by
    subst n
    rfl
  exact eqToIso_sc_hom_τ₂ (by omega)

/-- The short-complex map obtained by transporting cap product by a coboundary to the
right-associated source degree. -/
noncomputable def capCoboundaryShortComplexHom {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) :
    (X.chainComplex (ModuleCat.of R R)).sc (p + q + 1) ⟶
      (X.chainComplex (ModuleCat.of R R)).sc q :=
  (reassocShortComplexIso R p q).hom ≫
    capShortComplexHom R (p + 1) q (coboundary R p phi)
      (coboundary_coboundary R p phi)

lemma capCoboundaryShortComplexHom_τ₂ {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) :
    (capCoboundaryShortComplexHom R p q phi).τ₂ = ModuleCat.ofHom
      ((cap R (p + 1) q (coboundary R p phi)).comp (reassocChain R p q)) := by
  simp [capCoboundaryShortComplexHom, reassocShortComplexIso_hom_τ₂,
    capShortComplexHom_τ₂]
  congr 1

/-- The middle component of the null-homotopic cap map is the difference of the two
terms in its chain homotopy formula. -/
lemma capCoboundaryShortComplexHom_τ₂_eq {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) :
    (capCoboundaryShortComplexHom R p q phi).τ₂ =
      ModuleCat.ofHom (boundary R (p + q)) ≫ capHom R p q phi -
        (-1 : R) ^ p •
          (capHom R p (q + 1) phi ≫ ModuleCat.ofHom (boundary R q)) := by
  rw [capCoboundaryShortComplexHom_τ₂]
  apply ModuleCat.hom_ext
  exact cap_coboundary_eq R p q phi

set_option backward.isDefEq.respectTransparency false in
/-- Cap product by a coboundary induces the zero map on homology, after the canonical
reassociation of its source degree. -/
theorem capCoboundary_homologyMap_eq_zero {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) :
    ShortComplex.homologyMap (capCoboundaryShortComplexHom R p q phi) = 0 := by
  rw [← cancel_epi
    ((X.chainComplex (ModuleCat.of R R)).sc (p + q + 1)).homologyπ]
  rw [← cancel_mono ((X.chainComplex (ModuleCat.of R R)).sc q).homologyι]
  simp only [Category.assoc, zero_comp, comp_zero]
  rw [ShortComplex.π_homologyMap_ι,
    capCoboundaryShortComplexHom_τ₂_eq]
  have hsource :
      ((X.chainComplex (ModuleCat.of R R)).sc (p + q + 1)).iCycles ≫
        ModuleCat.ofHom (boundary R (p + q)) = 0 := by
    exact (X.chainComplex (ModuleCat.of R R)).iCycles_d (p + q + 1) (p + q)
  have htarget :
      ModuleCat.ofHom (boundary R q) ≫
        ((X.chainComplex (ModuleCat.of R R)).sc q).pOpcycles = 0 := by
    exact (X.chainComplex (ModuleCat.of R R)).d_pOpcycles (q + 1) q
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
    Linear.comp_smul]
  simp only [← Category.assoc, hsource, zero_comp]
  simp only [Category.assoc, htarget, comp_zero, smul_zero, sub_zero]

/-- Without the degree reassociation in the source, cap product by a coboundary still
induces the zero map on homology. -/
theorem capShortComplexHom_coboundary_homologyMap_eq_zero {X : SSet.{u}}
    (p q : ℕ) (phi : Cochain R X p) :
    ShortComplex.homologyMap
      (capShortComplexHom R (p + 1) q (coboundary R p phi)
        (coboundary_coboundary R p phi)) = 0 := by
  rw [← cancel_epi
    (ShortComplex.homologyMap (reassocShortComplexIso R (X := X) p q).hom)]
  rw [← ShortComplex.homologyMap_comp, comp_zero]
  exact capCoboundary_homologyMap_eq_zero R p q phi

/-- Cap product with a cocycle, descended to the actual simplicial homology objects. -/
noncomputable def capHomologyMap {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) (hphi : coboundary R p phi = 0) :
    (X.chainComplex (ModuleCat.of R R)).homology (p + q) →ₗ[R]
      (X.chainComplex (ModuleCat.of R R)).homology q :=
  (ShortComplex.homologyMap (capShortComplexHom R p q phi hphi)).hom

/-- Cap product by a coboundary is zero on simplicial homology. -/
@[simp]
theorem capHomologyMap_coboundary {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) :
    capHomologyMap R (p + 1) q (coboundary R p phi)
      (coboundary_coboundary R p phi) = 0 := by
  exact congrArg ModuleCat.Hom.hom
    (capShortComplexHom_coboundary_homologyMap_eq_zero R p q phi)

/-- Cap product by cocycles, linear in the cocycle and valued in linear maps on homology. -/
noncomputable def capCocycleHomologyLinear {X : SSet.{u}} (p q : ℕ) :
    Cocycle R X p →ₗ[R]
      ((X.chainComplex (ModuleCat.of R R)).homology (p + q) →ₗ[R]
        (X.chainComplex (ModuleCat.of R R)).homology q) where
  toFun phi := capHomologyMap R p q phi.1 phi.2
  map_add' phi psi := by
    exact congrArg ModuleCat.Hom.hom
      (capShortComplexHom_homologyMap_add R p q phi.1 psi.1 phi.2 psi.2
        (phi + psi).2)
  map_smul' a phi := by
    exact congrArg ModuleCat.Hom.hom
      (capShortComplexHom_homologyMap_smul R p q a phi.1 phi.2 (a • phi).2)

@[simp]
lemma capCocycleHomologyLinear_apply {X : SSet.{u}} (p q : ℕ)
    (phi : Cocycle R X p) :
    capCocycleHomologyLinear R p q phi = capHomologyMap R p q phi.1 phi.2 :=
  rfl

/-- The cohomology of algebraic simplicial cochains, using the same short-complex model
as singular cochain cohomology. -/
abbrev CochainCohomology (R : Type u) [Field R] (X : SSet.{u}) (p : ℕ) :
    ModuleCat.{u} R :=
  ((X.chainComplex (ModuleCat.of R R)).sc p).linearDual.homology

/-- Cycles in the reversed dual short complex are precisely simplicial cocycles. -/
def cohomologyCycleToCocycle {X : SSet.{u}} (p : ℕ) :
    LinearMap.ker
        (((X.chainComplex (ModuleCat.of R R)).sc p).linearDual.g.hom) →ₗ[R]
      Cocycle R X p where
  toFun phi := ⟨phi.1, by
    let phi' : Cochain R X p := phi.1
    change coboundary R p phi' = 0
    apply LinearMap.ext
    intro c
    simp only [LinearMap.zero_apply]
    have hphi := phi.2
    change
      ((((X.chainComplex (ModuleCat.of R R)).sc p).f.hom.dualMap) phi') = 0 at hphi
    rw [HomologicalComplex.shortComplexFunctor_obj_f] at hphi
    let K := X.chainComplex (ModuleCat.of R R)
    let hp : p + 1 = (ComplexShape.down ℕ).prev p := (ChainComplex.prev ℕ p).symm
    have hc := LinearMap.congr_fun hphi ((K.XIsoOfEq hp).hom.hom c)
    change phi' ((K.d ((ComplexShape.down ℕ).prev p) p).hom
      ((K.XIsoOfEq hp).hom.hom c)) = 0 at hc
    have hd := ConcreteCategory.congr_hom (K.XIsoOfEq_hom_comp_d hp p) c
    change (K.d ((ComplexShape.down ℕ).prev p) p).hom
      ((K.XIsoOfEq hp).hom.hom c) = (K.d (p + 1) p).hom c at hd
    change phi' ((K.d (p + 1) p).hom c) = 0
    rw [← hd]
    exact hc⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Cap product on the explicit cocycles in the short-complex model for cohomology. -/
noncomputable def cohomologyCycleCapLinear {X : SSet.{u}} (p q : ℕ) :
    LinearMap.ker
        (((X.chainComplex (ModuleCat.of R R)).sc p).linearDual.g.hom) →ₗ[R]
      ((X.chainComplex (ModuleCat.of R R)).homology (p + q) →ₗ[R]
        (X.chainComplex (ModuleCat.of R R)).homology q) :=
  (capCocycleHomologyLinear R p q).comp (cohomologyCycleToCocycle R p)

/-- In positive degree, an explicit boundary in the dual short complex is the usual
simplicial coboundary, after the canonical identification of the preceding degree. -/
lemma cohomologyCycleToCocycle_moduleCatToCycles_succ {X : SSet.{u}}
    (p : ℕ)
    (eta : (((X.chainComplex (ModuleCat.of R R)).sc (p + 1)).linearDual).X₁) :
    let K := X.chainComplex (ModuleCat.of R R)
    let hnext : (ComplexShape.down ℕ).next (p + 1) = p :=
      ChainComplex.next_nat_succ p
    let eta' : Cochain R X p :=
      (eta : Module.Dual R (K.X ((ComplexShape.down ℕ).next (p + 1)))).comp
        (K.XIsoOfEq hnext).inv.hom
    cohomologyCycleToCocycle R (p + 1)
        ((((K.sc (p + 1)).linearDual).moduleCatToCycles) eta) =
      ⟨coboundary R p eta', coboundary_coboundary R p eta'⟩ := by
  dsimp only
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  let K := X.chainComplex (ModuleCat.of R R)
  let hnext : (ComplexShape.down ℕ).next (p + 1) = p :=
    ChainComplex.next_nat_succ p
  let etaF : Module.Dual R (K.X ((ComplexShape.down ℕ).next (p + 1))) := eta
  change etaF ((K.d (p + 1) ((ComplexShape.down ℕ).next (p + 1))).hom c) =
    etaF ((K.XIsoOfEq hnext).inv.hom ((K.d (p + 1) p).hom c))
  have hd := ConcreteCategory.congr_hom (K.d_comp_XIsoOfEq_inv hnext (p + 1)) c
  exact congrArg etaF hd.symm

/-- Cap product on dual cycles annihilates the explicit boundaries used in the
short-complex quotient model for cohomology. -/
lemma cohomologyCycleCapLinear_vanishes_on_boundaries {X : SSet.{u}}
    (p q : ℕ) :
    let T := ((X.chainComplex (ModuleCat.of R R)).sc p).linearDual
    LinearMap.range T.moduleCatToCycles ≤
      LinearMap.ker (cohomologyCycleCapLinear R p q) := by
  dsimp only
  rintro _ ⟨eta, rfl⟩
  cases p with
  | zero =>
      change cohomologyCycleCapLinear R 0 q
        ((((X.chainComplex (ModuleCat.of R R)).sc 0).linearDual.moduleCatToCycles) eta) = 0
      let K := X.chainComplex (ModuleCat.of R R)
      have hz : ((K.sc 0).linearDual).moduleCatToCycles eta = 0 := by
        apply Subtype.ext
        change ((K.sc 0).g.hom.dualMap) eta = 0
        have hg : (K.sc 0).g = 0 := by
          change K.d 0 ((ComplexShape.down ℕ).next 0) = 0
          apply K.shape
          rw [ChainComplex.next_nat_zero]
          simp
        rw [hg]
        apply LinearMap.ext
        intro c
        let etaF : Module.Dual R (K.sc 0).X₃ := eta
        change etaF (0 : (K.sc 0).X₃) = 0
        exact map_zero etaF
      rw [hz]
      exact map_zero (cohomologyCycleCapLinear R 0 q)
  | succ p =>
      change cohomologyCycleCapLinear R (p + 1) q
        ((((X.chainComplex (ModuleCat.of R R)).sc (p + 1)).linearDual.moduleCatToCycles)
          eta) = 0
      rw [cohomologyCycleCapLinear, LinearMap.comp_apply,
        cohomologyCycleToCocycle_moduleCatToCycles_succ,
        capCocycleHomologyLinear_apply, capHomologyMap_coboundary]

/-- Cap product on the explicit quotient of cocycles by coboundaries. -/
noncomputable def capCohomologyExplicitLinear {X : SSet.{u}} (p q : ℕ) :
    let T := ((X.chainComplex (ModuleCat.of R R)).sc p).linearDual
    T.moduleCatLeftHomologyData.H →ₗ[R]
      ((X.chainComplex (ModuleCat.of R R)).homology (p + q) →ₗ[R]
        (X.chainComplex (ModuleCat.of R R)).homology q) :=
  let T := ((X.chainComplex (ModuleCat.of R R)).sc p).linearDual
  (LinearMap.range T.moduleCatToCycles).liftQ
    (cohomologyCycleCapLinear R p q)
    (cohomologyCycleCapLinear_vanishes_on_boundaries R p q)

/-- The cap product as a linear map from simplicial cochain cohomology to maps on
simplicial homology. -/
noncomputable def capCohomologyLinear {X : SSet.{u}} (p q : ℕ) :
    CochainCohomology R X p →ₗ[R]
      ((X.chainComplex (ModuleCat.of R R)).homology (p + q) →ₗ[R]
        (X.chainComplex (ModuleCat.of R R)).homology q) :=
  let T := ((X.chainComplex (ModuleCat.of R R)).sc p).linearDual
  (capCohomologyExplicitLinear R p q).comp T.moduleCatHomologyIso.hom.hom

/-- On the cohomology class of an explicit dual cycle, `capCohomologyLinear` agrees with
the cocycle-level cap product. -/
@[simp]
lemma capCohomologyLinear_on_cycle {X : SSet.{u}} (p q : ℕ)
    (phi : LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc p).linearDual.g.hom)) :
    let T := ((X.chainComplex (ModuleCat.of R R)).sc p).linearDual
    capCohomologyLinear R p q
        (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
      cohomologyCycleCapLinear R p q phi := by
  dsimp only
  let T := ((X.chainComplex (ModuleCat.of R R)).sc p).linearDual
  change capCohomologyExplicitLinear R p q
      (T.moduleCatHomologyIso.hom.hom
        (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))) = _
  have h := ConcreteCategory.congr_hom T.moduleCatHomologyIso.inv_hom_id
    (Submodule.Quotient.mk phi)
  change T.moduleCatHomologyIso.hom.hom
      (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
    Submodule.Quotient.mk phi at h
  rw [h]
  rfl

/-- Cocycles which differ by a coboundary induce the same cap map on homology. -/
theorem capCocycleHomologyLinear_eq_of_sub_eq_coboundary {X : SSet.{u}}
    (p q : ℕ) (phi psi : Cocycle R X (p + 1)) (eta : Cochain R X p)
    (h : phi.1 - psi.1 = coboundary R p eta) :
    capCocycleHomologyLinear R (p + 1) q phi =
      capCocycleHomologyLinear R (p + 1) q psi := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  let deta : Cocycle R X (p + 1) :=
    ⟨coboundary R p eta, coboundary_coboundary R p eta⟩
  have hdeta : phi - psi = deta := by
    apply Subtype.ext
    exact h
  rw [hdeta]
  exact capHomologyMap_coboundary R p q eta

/-- The homology cap product is represented by the chain-level cap product on cycles. -/
lemma capHomologyMap_on_cycles {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) (hphi : coboundary R p phi = 0) :
    ((X.chainComplex (ModuleCat.of R R)).homologyπ (p + q) ≫
        ModuleCat.ofHom (capHomologyMap R p q phi hphi)) =
      ShortComplex.cyclesMap (capShortComplexHom R p q phi hphi) ≫
        (X.chainComplex (ModuleCat.of R R)).homologyπ q := by
  exact ShortComplex.homologyπ_naturality (capShortComplexHom R p q phi hphi)

/-- On the underlying chain groups, the map on cycles used to define `capHomologyMap` is
literally the cap product. -/
@[reassoc]
lemma capCyclesMap_i {X : SSet.{u}} (p q : ℕ)
    (phi : Cochain R X p) (hphi : coboundary R p phi = 0) :
    ShortComplex.cyclesMap (capShortComplexHom R p q phi hphi) ≫
        ((X.chainComplex (ModuleCat.of R R)).sc q).iCycles =
      ((X.chainComplex (ModuleCat.of R R)).sc (p + q)).iCycles ≫ capHom R p q phi := by
  rw [ShortComplex.cyclesMap_i, capShortComplexHom_τ₂]
  rfl

end AlgebraicTopology.Simplicial

namespace AlgebraicTopology.Singular

open CategoryTheory

variable (R : Type u) [Field R]

/-! ## Relative chain-level cap product -/

/-- Chains in one degree of the relative singular chain complex. -/
abbrev RelativeChainGroup (X : TopPair.{u}) (n : ℕ) : ModuleCat.{u} R :=
  ((relativeChainFunctor R).obj X).X n

/-- Cochains on the relative singular chain complex. -/
abbrev RelativeCochain (X : TopPair.{u}) (n : ℕ) :=
  Module.Dual R (RelativeChainGroup R X n)

/-- The differential on relative singular chains. -/
def relativeBoundary (X : TopPair.{u}) (n : ℕ) :
    RelativeChainGroup R X (n + 1) →ₗ[R] RelativeChainGroup R X n :=
  (((relativeChainFunctor R).obj X).d (n + 1) n).hom

/-- The algebraic coboundary on relative singular cochains. -/
def relativeCoboundary (X : TopPair.{u}) (n : ℕ) :
    RelativeCochain R X n →ₗ[R] RelativeCochain R X (n + 1) :=
  (relativeBoundary R X n).dualMap

lemma relativeCoboundary_relativeCoboundary (X : TopPair.{u}) (n : ℕ)
    (phi : RelativeCochain R X n) :
    relativeCoboundary R X (n + 1) (relativeCoboundary R X n phi) = 0 := by
  apply LinearMap.ext
  intro c
  change phi (((((relativeChainFunctor R).obj X).d (n + 2) (n + 1) ≫
    ((relativeChainFunctor R).obj X).d (n + 1) n).hom) c) = 0
  rw [((relativeChainFunctor R).obj X).d_comp_d, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero]

/-- A relative cochain pulled back to an absolute cochain along the relative-chain
projection. -/
def relativeCochainToAbsolute (X : TopPair.{u}) (n : ℕ) :
    RelativeCochain R X n →ₗ[R]
      Simplicial.Cochain R (TopCat.toSSet.obj X.fst) n :=
  ((relativeChainProjection R X).f n).hom.dualMap

@[simp]
lemma relativeCochainToAbsolute_apply (X : TopPair.{u}) (n : ℕ)
    (phi : RelativeCochain R X n)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X.fst) n) :
    relativeCochainToAbsolute R X n phi c =
      phi (((relativeChainProjection R X).f n).hom c) :=
  rfl

/-- Pullback along the relative-chain projection commutes with coboundaries. -/
lemma relativeCochainToAbsolute_coboundary (X : TopPair.{u}) (n : ℕ)
    (phi : RelativeCochain R X n) :
    relativeCochainToAbsolute R X (n + 1) (relativeCoboundary R X n phi) =
      Simplicial.coboundary R n (relativeCochainToAbsolute R X n phi) := by
  apply LinearMap.ext
  intro c
  let K := ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).obj X.fst
  change phi ((((relativeChainFunctor R).obj X).d (n + 1) n).hom
      (((relativeChainProjection R X).f (n + 1)).hom c)) =
    phi (((relativeChainProjection R X).f n).hom ((K.d (n + 1) n).hom c))
  have h := ConcreteCategory.congr_hom
    ((relativeChainProjection R X).comm (n + 1) n) c
  exact congrArg phi h

/-- The relative boundary of a projected ambient chain is the projection of its ambient
boundary. -/
lemma relativeBoundary_projection (X : TopPair.{u}) (n : ℕ)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X.fst) (n + 1)) :
    relativeBoundary R X n (((relativeChainProjection R X).f (n + 1)).hom c) =
      ((relativeChainProjection R X).f n).hom (Simplicial.boundary R n c) := by
  exact ConcreteCategory.congr_hom
    ((relativeChainProjection R X).comm (n + 1) n) c

/-- The pullback of a relative cochain to the subspace is zero. -/
lemma cochainMap_relativeCochainToAbsolute_eq_zero (X : TopPair.{u}) (n : ℕ)
    (phi : RelativeCochain R X n) :
    Simplicial.cochainMap R (TopCat.toSSet.map X.map) n
      (relativeCochainToAbsolute R X n phi) = 0 := by
  apply LinearMap.ext
  intro c
  have hz := congrArg (fun f ↦ f.f n)
    (subspaceChainMap_relativeChainProjection R X)
  have hc := ConcreteCategory.congr_hom hz c
  change phi (((relativeChainProjection R X).f n).hom
    ((((chainPairFunctor R).obj X).hom.f n).hom c)) = 0
  rw [show ((relativeChainProjection R X).f n).hom
    ((((chainPairFunctor R).obj X).hom.f n).hom c) = 0 by exact hc]
  exact map_zero phi

/-- Before quotienting the chain variable, cap a pulled-back relative cochain with an
absolute ambient chain. -/
def relativeCapLift (X : TopPair.{u}) (p q : ℕ) (phi : RelativeCochain R X p) :
    Simplicial.ChainGroup R (TopCat.toSSet.obj X.fst) (p + q) →ₗ[R]
      Simplicial.ChainGroup R (TopCat.toSSet.obj X.fst) q :=
  Simplicial.cap R p q (relativeCochainToAbsolute R X p phi)

lemma relativeCapLift_add (X : TopPair.{u}) (p q : ℕ)
    (phi psi : RelativeCochain R X p) :
    relativeCapLift R X p q (phi + psi) =
      relativeCapLift R X p q phi + relativeCapLift R X p q psi := by
  change Simplicial.capLinear R p q
      (relativeCochainToAbsolute R X p (phi + psi)) = _
  rw [map_add, map_add]
  rfl

lemma relativeCapLift_smul (X : TopPair.{u}) (p q : ℕ)
    (a : R) (phi : RelativeCochain R X p) :
    relativeCapLift R X p q (a • phi) = a • relativeCapLift R X p q phi := by
  change Simplicial.capLinear R p q
      (relativeCochainToAbsolute R X p (a • phi)) = _
  rw [map_smul, map_smul]
  rfl

/-- The lifted relative cap product vanishes on chains coming from the subspace. -/
lemma subspaceChainMap_relativeCapLift_eq_zero (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    ((chainPairFunctor R).obj X).hom.f (p + q) ≫
      ModuleCat.ofHom (relativeCapLift R X p q phi) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have h := Simplicial.cap_naturality R (TopCat.toSSet.map X.map) p q
    (relativeCochainToAbsolute R X p phi) c
  rw [cochainMap_relativeCochainToAbsolute_eq_zero] at h
  have hzero :
      Simplicial.cap R p q
        (0 : Simplicial.Cochain R (TopCat.toSSet.obj X.snd) p) c = 0 := by
    change (Simplicial.capHom R p q 0).hom c = 0
    rw [Simplicial.capHom_zero]
    rfl
  rw [hzero, map_zero] at h
  exact h.symm

/-- Each component of the relative-chain projection has its defining cokernel universal
property. -/
noncomputable def relativeChainProjectionComponentIsCokernelForCap
    (X : TopPair.{u}) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (f := ((chainPairFunctor R).obj X).hom.f n)
      ((relativeChainProjection R X).f n) (by
        have h := congrArg (fun f ↦ f.f n)
          (subspaceChainMap_relativeChainProjection R X)
        change ((chainPairFunctor R).obj X).hom.f n ≫
          (relativeChainProjection R X).f n = 0 at h
        exact h)) := by
  exact CokernelCofork.mapIsColimit _
    (cokernelIsCokernel ((chainPairFunctor R).obj X).hom)
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)

/-- The relative cap product, descended through the relative-chain quotient. -/
noncomputable def relativeCapHom (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    ((relativeChainFunctor R).obj X).X (p + q) ⟶
      ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).obj X.fst |>.X q :=
  (relativeChainProjectionComponentIsCokernelForCap R X (p + q)).desc
    (CokernelCofork.ofπ (ModuleCat.ofHom (relativeCapLift R X p q phi))
      (subspaceChainMap_relativeCapLift_eq_zero R X p q phi))

/-- The relative cap product as a linear map in the chain variable. -/
noncomputable def relativeCap (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    RelativeChainGroup R X (p + q) →ₗ[R]
      Simplicial.ChainGroup R (TopCat.toSSet.obj X.fst) q :=
  (relativeCapHom R X p q phi).hom

/-- Pulling a relative chain back to an ambient representative and then capping agrees
with the lifted absolute cap product. -/
@[reassoc]
lemma relativeChainProjection_relativeCapHom (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    (relativeChainProjection R X).f (p + q) ≫ relativeCapHom R X p q phi =
      ModuleCat.ofHom (relativeCapLift R X p q phi) := by
  exact (Cofork.IsColimit.π_desc
    (relativeChainProjectionComponentIsCokernelForCap R X (p + q))
    (t := CokernelCofork.ofπ (ModuleCat.ofHom (relativeCapLift R X p q phi))
      (subspaceChainMap_relativeCapLift_eq_zero R X p q phi))).trans
    (CokernelCofork.π_ofπ _ _ _)

set_option backward.isDefEq.respectTransparency false in
lemma relativeCapHom_add (X : TopPair.{u}) (p q : ℕ)
    (phi psi : RelativeCochain R X p) :
    relativeCapHom R X p q (phi + psi) =
      relativeCapHom R X p q phi + relativeCapHom R X p q psi := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap R X (p + q))
  change (relativeChainProjection R X).f (p + q) ≫
      relativeCapHom R X p q (phi + psi) =
    (relativeChainProjection R X).f (p + q) ≫
      (relativeCapHom R X p q phi + relativeCapHom R X p q psi)
  rw [relativeChainProjection_relativeCapHom, Preadditive.comp_add,
    relativeChainProjection_relativeCapHom, relativeChainProjection_relativeCapHom]
  apply ModuleCat.hom_ext
  exact relativeCapLift_add R X p q phi psi

set_option backward.isDefEq.respectTransparency false in
lemma relativeCapHom_smul (X : TopPair.{u}) (p q : ℕ)
    (a : R) (phi : RelativeCochain R X p) :
    relativeCapHom R X p q (a • phi) = a • relativeCapHom R X p q phi := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap R X (p + q))
  change (relativeChainProjection R X).f (p + q) ≫
      relativeCapHom R X p q (a • phi) =
    (relativeChainProjection R X).f (p + q) ≫
      (a • relativeCapHom R X p q phi)
  rw [relativeChainProjection_relativeCapHom, Linear.comp_smul,
    relativeChainProjection_relativeCapHom]
  apply ModuleCat.hom_ext
  exact relativeCapLift_smul R X p q a phi

/-- Relative cap product, bilinear in a relative cochain and a relative chain, and valued
in absolute ambient chains. -/
noncomputable def relativeCapLinear (X : TopPair.{u}) (p q : ℕ) :
    RelativeCochain R X p →ₗ[R]
      (RelativeChainGroup R X (p + q) →ₗ[R]
        Simplicial.ChainGroup R (TopCat.toSSet.obj X.fst) q) where
  toFun phi := relativeCap R X p q phi
  map_add' phi psi := congrArg ModuleCat.Hom.hom
    (relativeCapHom_add R X p q phi psi)
  map_smul' a phi := congrArg ModuleCat.Hom.hom
    (relativeCapHom_smul R X p q a phi)

@[simp]
lemma relativeCapLinear_apply (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    relativeCapLinear R X p q phi = relativeCap R X p q phi :=
  rfl

@[simp]
lemma relativeCap_projection_apply (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X.fst) (p + q)) :
    relativeCap R X p q phi ((relativeChainProjection R X).f (p + q) c) =
      relativeCapLift R X p q phi c := by
  exact ConcreteCategory.congr_hom
    (relativeChainProjection_relativeCapHom R X p q phi) c

/-- For a relative cocycle, the lifted cap product satisfies the signed boundary identity
on ambient chain representatives. -/
theorem boundary_relativeCapLift_eq_of_cocycle (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) (hphi : relativeCoboundary R X p phi = 0) :
    (Simplicial.boundary R q).comp (relativeCapLift R X p (q + 1) phi) =
      (-1 : R) ^ p •
        (relativeCapLift R X p q phi).comp (Simplicial.boundary R (p + q)) := by
  apply Simplicial.cap_boundary_compatibility_of_cocycle
  rw [← relativeCochainToAbsolute_coboundary, hphi, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- For a relative cocycle, relative cap product intertwines the relative source boundary
and the absolute target boundary up to the conventional sign. -/
theorem boundary_relativeCap_eq_of_cocycle (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) (hphi : relativeCoboundary R X p phi = 0) :
    (Simplicial.boundary R q).comp (relativeCap R X p (q + 1) phi) =
      (-1 : R) ^ p •
        (relativeCap R X p q phi).comp (relativeBoundary R X (p + q)) := by
  apply LinearMap.ext
  intro z
  let π := (relativeChainProjection R X).f (p + q + 1)
  let : Epi π := Cofork.IsColimit.epi
    (relativeChainProjectionComponentIsCokernelForCap R X (p + q + 1))
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance z
  dsimp only [π]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  erw [relativeCap_projection_apply R X p (q + 1) phi c,
    relativeBoundary_projection R X (p + q) c,
    relativeCap_projection_apply R X p q phi (Simplicial.boundary R (p + q) c)]
  exact LinearMap.congr_fun
    (boundary_relativeCapLift_eq_of_cocycle R X p q phi hphi) c

/-! ### The same-pair relative cap product on homology

This is the intermediate pairing
`H^p(X, A) ⊗ H_{p+q}(X, A) → H_q(X)`.  It is distinct from the triad pairing
`H^p(X, A) ⊗ H_{p+q}(X, A ∪ B) → H_q(X, B)` needed for the supported form of
Alexander--Poincare duality. -/

/-- Relative cocycles in the algebraic dual of the relative singular chain complex. -/
abbrev RelativeCocycle (X : TopPair.{u}) (p : ℕ) :=
  LinearMap.ker (relativeCoboundary R X p)

/-- The explicit relative-to-absolute cap morphism ending in degree zero. -/
noncomputable def relativeCapShortComplexHomZero (X : TopPair.{u}) (p : ℕ)
    (phi : RelativeCochain R X p) (hphi : relativeCoboundary R X p phi = 0) :
    ((relativeChainFunctor R).obj X).sc' (p + 1) p
        ((ComplexShape.down ℕ).next p) ⟶
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X.fst).sc'
        1 0 0 := by
  let s : R := (-1 : R) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine
    { τ₁ := ModuleCat.ofHom (s • relativeCap R X p 1 phi)
      τ₂ := relativeCapHom R X p 0 phi
      τ₃ := 0
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change Simplicial.boundary R 0 (s • relativeCap R X p 1 phi c) =
      relativeCap R X p 0 phi (relativeBoundary R X p c)
    rw [map_smul]
    have h := LinearMap.congr_fun
      (boundary_relativeCap_eq_of_cocycle R X p 0 phi hphi) c
    change Simplicial.boundary R 0 (relativeCap R X p 1 phi c) =
      s • relativeCap R X p 0 phi (relativeBoundary R X p c) at h
    simpa [s, hs, smul_smul] using congrArg (fun z ↦ s • z) h
  · change relativeCapHom R X p 0 phi ≫
        (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)).obj X.fst).d 0 0 =
      ((relativeChainFunctor R).obj X).d p ((ComplexShape.down ℕ).next p) ≫ 0
    rw [((((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).obj X.fst).shape 0 0 (by simp)), comp_zero, comp_zero]

/-- The explicit relative-to-absolute cap morphism ending in a positive degree. -/
noncomputable def relativeCapShortComplexHomSucc (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) (hphi : relativeCoboundary R X p phi = 0) :
    ((relativeChainFunctor R).obj X).sc'
        (p + ((q + 1) + 1)) (p + (q + 1)) (p + q) ⟶
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X.fst).sc'
        ((q + 1) + 1) (q + 1) q := by
  let s : R := (-1 : R) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine
    { τ₁ := ModuleCat.ofHom (s • relativeCap R X p ((q + 1) + 1) phi)
      τ₂ := relativeCapHom R X p (q + 1) phi
      τ₃ := ModuleCat.ofHom (s • relativeCap R X p q phi)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change Simplicial.boundary R (q + 1)
        (s • relativeCap R X p ((q + 1) + 1) phi c) =
      relativeCap R X p (q + 1) phi
        (relativeBoundary R X (p + (q + 1)) c)
    rw [map_smul]
    have h := LinearMap.congr_fun
      (boundary_relativeCap_eq_of_cocycle R X p (q + 1) phi hphi) c
    change Simplicial.boundary R (q + 1)
        (relativeCap R X p ((q + 1) + 1) phi c) =
      s • relativeCap R X p (q + 1) phi
        (relativeBoundary R X (p + (q + 1)) c) at h
    simpa [s, hs, smul_smul] using congrArg (fun z ↦ s • z) h
  · apply ModuleCat.hom_ext
    exact boundary_relativeCap_eq_of_cocycle R X p q phi hphi

/-- The short-complex morphism underlying the same-pair relative cap product. -/
noncomputable def relativeCapShortComplexHom (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) (hphi : relativeCoboundary R X p phi = 0) :
    ((relativeChainFunctor R).obj X).sc (p + q) ⟶
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X.fst).sc q := by
  let Krel := (relativeChainFunctor R).obj X
  let Kabs := ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).obj X.fst
  cases q with
  | zero =>
      exact
        (Krel.isoSc' (p + 1) p ((ComplexShape.down ℕ).next p)
            (ChainComplex.prev ℕ p) rfl).hom ≫
          relativeCapShortComplexHomZero R X p phi hphi ≫
          (Kabs.isoSc' 1 0 0 (ChainComplex.prev ℕ 0)
            ChainComplex.next_nat_zero).inv
  | succ q =>
      exact
        (Krel.isoSc' (p + ((q + 1) + 1)) (p + (q + 1)) (p + q)
            (by rw [ChainComplex.prev]; omega)
            (by rw [show p + (q + 1) = (p + q) + 1 by omega,
              ChainComplex.next_nat_succ])).hom ≫
          relativeCapShortComplexHomSucc R X p q phi hphi ≫
          (Kabs.isoSc' ((q + 1) + 1) (q + 1) q
            (by rw [ChainComplex.prev]) (ChainComplex.next_nat_succ q)).inv

@[simp]
lemma relativeCapShortComplexHom_τ₂ (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) (hphi : relativeCoboundary R X p phi = 0) :
    (relativeCapShortComplexHom R X p q phi hphi).τ₂ =
      relativeCapHom R X p q phi := by
  cases q <;> simp [relativeCapShortComplexHom, relativeCapShortComplexHomZero,
    relativeCapShortComplexHomSucc] <;> cat_disch

/-- Additivity of the homology map induced by the same-pair relative cap product. -/
lemma relativeCapShortComplexHom_homologyMap_add (X : TopPair.{u}) (p q : ℕ)
    (phi psi : RelativeCochain R X p) (hphi : relativeCoboundary R X p phi = 0)
    (hpsi : relativeCoboundary R X p psi = 0)
    (hadd : relativeCoboundary R X p (phi + psi) = 0) :
    ShortComplex.homologyMap (relativeCapShortComplexHom R X p q (phi + psi) hadd) =
      ShortComplex.homologyMap (relativeCapShortComplexHom R X p q phi hphi) +
        ShortComplex.homologyMap (relativeCapShortComplexHom R X p q psi hpsi) := by
  rw [← ShortComplex.homologyMap_add]
  apply Simplicial.homologyMap_eq_of_τ₂_eq
  simp [relativeCapShortComplexHom_τ₂, relativeCapHom_add]
  rfl

/-- Scalar compatibility of the homology map induced by relative cap product. -/
lemma relativeCapShortComplexHom_homologyMap_smul (X : TopPair.{u}) (p q : ℕ)
    (a : R) (phi : RelativeCochain R X p)
    (hphi : relativeCoboundary R X p phi = 0)
    (hsmul : relativeCoboundary R X p (a • phi) = 0) :
    ShortComplex.homologyMap (relativeCapShortComplexHom R X p q (a • phi) hsmul) =
      a • ShortComplex.homologyMap (relativeCapShortComplexHom R X p q phi hphi) := by
  rw [← ShortComplex.homologyMap_smul]
  apply Simplicial.homologyMap_eq_of_τ₂_eq
  simp [relativeCapShortComplexHom_τ₂, relativeCapHom_smul]
  rfl

/-- Cap product with a relative cocycle, descended in the chain variable to relative
homology and valued in absolute homology. -/
noncomputable def relativeCapHomologyMap (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) (hphi : relativeCoboundary R X p phi = 0) :
    RelativeHomology R X (p + q) →ₗ[R] Homology R X.fst q :=
  (ShortComplex.homologyMap (relativeCapShortComplexHom R X p q phi hphi)).hom

/-- The same-pair relative cap product is linear in relative cocycles. -/
noncomputable def relativeCapCocycleHomologyLinear (X : TopPair.{u}) (p q : ℕ) :
    RelativeCocycle R X p →ₗ[R]
      (RelativeHomology R X (p + q) →ₗ[R] Homology R X.fst q) where
  toFun phi := relativeCapHomologyMap R X p q phi.1 phi.2
  map_add' phi psi := congrArg ModuleCat.Hom.hom
    (relativeCapShortComplexHom_homologyMap_add R X p q phi.1 psi.1 phi.2 psi.2
      (phi + psi).2)
  map_smul' a phi := congrArg ModuleCat.Hom.hom
    (relativeCapShortComplexHom_homologyMap_smul R X p q a phi.1 phi.2 (a • phi).2)

@[simp]
lemma relativeCapCocycleHomologyLinear_apply (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCocycle R X p) :
    relativeCapCocycleHomologyLinear R X p q phi =
      relativeCapHomologyMap R X p q phi.1 phi.2 :=
  rfl

/-- Reassociate a relative-chain degree from `p + q + 1` to `(p + 1) + q`. -/
noncomputable def relativeReassocChain (X : TopPair.{u}) (p q : ℕ) :
    RelativeChainGroup R X (p + q + 1) →ₗ[R]
      RelativeChainGroup R X (p + 1 + q) :=
  ((((relativeChainFunctor R).obj X).XIsoOfEq (by omega)).hom).hom

/-- Reassociation commutes with projection from absolute to relative chains. -/
lemma relativeChainProjection_reassoc_apply (X : TopPair.{u}) (p q : ℕ)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X.fst) (p + q + 1)) :
    relativeReassocChain R X p q (((relativeChainProjection R X).f (p + q + 1)).hom c) =
      ((relativeChainProjection R X).f (p + 1 + q)).hom
        (Simplicial.reassocChain R p q c) := by
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.XIsoOfEq_hom_naturality
      (relativeChainProjection R X) (by omega)) c

set_option backward.isDefEq.respectTransparency false in
/-- Cap product by a relative coboundary is chain-null-homotopic. -/
theorem relativeCap_coboundary_eq (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    (relativeCap R X (p + 1) q (relativeCoboundary R X p phi)).comp
        (relativeReassocChain R X p q) =
      (relativeCap R X p q phi).comp (relativeBoundary R X (p + q)) -
        (-1 : R) ^ p •
          (Simplicial.boundary R q).comp (relativeCap R X p (q + 1) phi) := by
  apply LinearMap.ext
  intro z
  let π := (relativeChainProjection R X).f (p + q + 1)
  let : Epi π := Cofork.IsColimit.epi
    (relativeChainProjectionComponentIsCokernelForCap R X (p + q + 1))
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance z
  dsimp only [π]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  erw [relativeChainProjection_reassoc_apply R X p q c,
    relativeCap_projection_apply R X (p + 1) q
      (relativeCoboundary R X p phi) (Simplicial.reassocChain R p q c),
    relativeBoundary_projection R X (p + q) c,
    relativeCap_projection_apply R X p q phi (Simplicial.boundary R (p + q) c),
    relativeCap_projection_apply R X p (q + 1) phi c]
  change Simplicial.cap R (p + 1) q
      (relativeCochainToAbsolute R X (p + 1) (relativeCoboundary R X p phi))
        (Simplicial.reassocChain R p q c) = _
  rw [relativeCochainToAbsolute_coboundary]
  exact LinearMap.congr_fun
    (Simplicial.cap_coboundary_eq R p q (relativeCochainToAbsolute R X p phi)) c

/-- Reassociation of the source degree as an isomorphism of relative homology short
complexes. -/
noncomputable def relativeReassocShortComplexIso (X : TopPair.{u}) (p q : ℕ) :
    ((relativeChainFunctor R).obj X).sc (p + q + 1) ≅
      ((relativeChainFunctor R).obj X).sc (p + 1 + q) :=
  eqToIso (congrArg (fun n ↦ ((relativeChainFunctor R).obj X).sc n)
    (by omega : p + q + 1 = p + 1 + q))

lemma relativeReassocShortComplexIso_hom_τ₂ (X : TopPair.{u}) (p q : ℕ) :
    (relativeReassocShortComplexIso R X p q).hom.τ₂ =
      ModuleCat.ofHom (relativeReassocChain R X p q) := by
  let K := (relativeChainFunctor R).obj X
  have eqToIso_sc_hom_τ₂ {m n : ℕ} (h : m = n) :
      (eqToIso (congrArg (fun i ↦ K.sc i) h)).hom.τ₂ = (K.XIsoOfEq h).hom := by
    subst n
    rfl
  exact eqToIso_sc_hom_τ₂ (by omega)

/-- The short-complex map obtained by capping with a relative coboundary, with its source
degree canonically reassociated. -/
noncomputable def relativeCapCoboundaryShortComplexHom (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    ((relativeChainFunctor R).obj X).sc (p + q + 1) ⟶
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).obj X.fst).sc q :=
  (relativeReassocShortComplexIso R X p q).hom ≫
    relativeCapShortComplexHom R X (p + 1) q (relativeCoboundary R X p phi)
      (relativeCoboundary_relativeCoboundary R X p phi)

lemma relativeCapCoboundaryShortComplexHom_τ₂ (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    (relativeCapCoboundaryShortComplexHom R X p q phi).τ₂ = ModuleCat.ofHom
      ((relativeCap R X (p + 1) q (relativeCoboundary R X p phi)).comp
        (relativeReassocChain R X p q)) := by
  simp [relativeCapCoboundaryShortComplexHom,
    relativeReassocShortComplexIso_hom_τ₂, relativeCapShortComplexHom_τ₂]
  congr 1

/-- The middle component of the relative coboundary cap map is the difference of the two
terms in its chain homotopy formula. -/
lemma relativeCapCoboundaryShortComplexHom_τ₂_eq (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    (relativeCapCoboundaryShortComplexHom R X p q phi).τ₂ =
      ((relativeChainFunctor R).obj X).d (p + q + 1) (p + q) ≫
          relativeCapHom R X p q phi -
        (-1 : R) ^ p •
          (relativeCapHom R X p (q + 1) phi ≫
            (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
              (ModuleCat.of R R)).obj X.fst).d (q + 1) q) := by
  rw [relativeCapCoboundaryShortComplexHom_τ₂]
  apply ModuleCat.hom_ext
  exact relativeCap_coboundary_eq R X p q phi

set_option backward.isDefEq.respectTransparency false in
/-- Cap product by a relative coboundary induces the zero map from relative homology to
absolute homology. -/
theorem relativeCapCoboundary_homologyMap_eq_zero (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    ShortComplex.homologyMap (relativeCapCoboundaryShortComplexHom R X p q phi) = 0 := by
  rw [← cancel_epi (((relativeChainFunctor R).obj X).sc (p + q + 1)).homologyπ]
  rw [← cancel_mono
    (((((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).obj X.fst).sc q).homologyι)]
  simp only [Category.assoc, zero_comp, comp_zero]
  rw [ShortComplex.π_homologyMap_ι,
    relativeCapCoboundaryShortComplexHom_τ₂_eq]
  have hsource :
      (((relativeChainFunctor R).obj X).sc (p + q + 1)).iCycles ≫
        ((relativeChainFunctor R).obj X).d (p + q + 1) (p + q) = 0 :=
    ((relativeChainFunctor R).obj X).iCycles_d (p + q + 1) (p + q)
  have htarget :
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)).obj X.fst).d (q + 1) q ≫
        (((((singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)).obj X.fst).sc q).pOpcycles) = 0 :=
    (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).obj X.fst).d_pOpcycles (q + 1) q
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
    Linear.comp_smul]
  simp only [← Category.assoc, hsource, zero_comp]
  simp only [Category.assoc, htarget, comp_zero, smul_zero, sub_zero]

/-- Without the degree reassociation, cap product by a relative coboundary still induces
the zero map on homology. -/
theorem relativeCapShortComplexHom_coboundary_homologyMap_eq_zero
    (X : TopPair.{u}) (p q : ℕ) (phi : RelativeCochain R X p) :
    ShortComplex.homologyMap
      (relativeCapShortComplexHom R X (p + 1) q (relativeCoboundary R X p phi)
        (relativeCoboundary_relativeCoboundary R X p phi)) = 0 := by
  rw [← cancel_epi
    (ShortComplex.homologyMap (relativeReassocShortComplexIso R X p q).hom)]
  rw [← ShortComplex.homologyMap_comp, comp_zero]
  exact relativeCapCoboundary_homologyMap_eq_zero R X p q phi

/-- A relative coboundary acts trivially on relative homology by cap product. -/
@[simp]
theorem relativeCapHomologyMap_coboundary (X : TopPair.{u}) (p q : ℕ)
    (phi : RelativeCochain R X p) :
    relativeCapHomologyMap R X (p + 1) q (relativeCoboundary R X p phi)
      (relativeCoboundary_relativeCoboundary R X p phi) = 0 := by
  exact congrArg ModuleCat.Hom.hom
    (relativeCapShortComplexHom_coboundary_homologyMap_eq_zero R X p q phi)

/-- Relative cocycles differing by a relative coboundary induce the same map on
relative homology. -/
theorem relativeCapCocycleHomologyLinear_eq_of_sub_eq_coboundary
    (X : TopPair.{u}) (p q : ℕ)
    (phi psi : RelativeCocycle R X (p + 1)) (eta : RelativeCochain R X p)
    (h : phi.1 - psi.1 = relativeCoboundary R X p eta) :
    relativeCapCocycleHomologyLinear R X (p + 1) q phi =
      relativeCapCocycleHomologyLinear R X (p + 1) q psi := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  let deta : RelativeCocycle R X (p + 1) :=
    ⟨relativeCoboundary R X p eta,
      relativeCoboundary_relativeCoboundary R X p eta⟩
  have hdeta : phi - psi = deta := by
    apply Subtype.ext
    exact h
  rw [hdeta]
  exact relativeCapHomologyMap_coboundary R X p q eta

/-- Cohomology of the algebraic relative cochain complex. -/
abbrev RelativeCochainCohomology (X : TopPair.{u}) (p : ℕ) : ModuleCat.{u} R :=
  (((relativeChainFunctor R).obj X).sc p).linearDual.homology

/-- Cycles in the reversed dual relative short complex are relative cocycles. -/
def relativeCohomologyCycleToCocycle (X : TopPair.{u}) (p : ℕ) :
    LinearMap.ker
        ((((relativeChainFunctor R).obj X).sc p).linearDual.g.hom) →ₗ[R]
      RelativeCocycle R X p where
  toFun phi := ⟨phi.1, by
    let phi' : RelativeCochain R X p := phi.1
    change relativeCoboundary R X p phi' = 0
    apply LinearMap.ext
    intro c
    simp only [LinearMap.zero_apply]
    have hphi := phi.2
    change (((((relativeChainFunctor R).obj X).sc p).f.hom.dualMap) phi') = 0 at hphi
    rw [HomologicalComplex.shortComplexFunctor_obj_f] at hphi
    let K := (relativeChainFunctor R).obj X
    let hp : p + 1 = (ComplexShape.down ℕ).prev p := (ChainComplex.prev ℕ p).symm
    have hc := LinearMap.congr_fun hphi ((K.XIsoOfEq hp).hom.hom c)
    change phi' ((K.d ((ComplexShape.down ℕ).prev p) p).hom
      ((K.XIsoOfEq hp).hom.hom c)) = 0 at hc
    have hd := ConcreteCategory.congr_hom (K.XIsoOfEq_hom_comp_d hp p) c
    change (K.d ((ComplexShape.down ℕ).prev p) p).hom
      ((K.XIsoOfEq hp).hom.hom c) = (K.d (p + 1) p).hom c at hd
    change phi' ((K.d (p + 1) p).hom c) = 0
    rw [← hd]
    exact hc⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Same-pair relative cap product on explicit dual cycles. -/
noncomputable def relativeCohomologyCycleCapLinear (X : TopPair.{u}) (p q : ℕ) :
    LinearMap.ker
        ((((relativeChainFunctor R).obj X).sc p).linearDual.g.hom) →ₗ[R]
      (RelativeHomology R X (p + q) →ₗ[R] Homology R X.fst q) :=
  (relativeCapCocycleHomologyLinear R X p q).comp
    (relativeCohomologyCycleToCocycle R X p)

/-- In positive degree, a boundary in the dual relative short complex is the usual
relative coboundary after the canonical identification of the preceding degree. -/
lemma relativeCohomologyCycleToCocycle_moduleCatToCycles_succ
    (X : TopPair.{u}) (p : ℕ)
    (eta : ((((relativeChainFunctor R).obj X).sc (p + 1)).linearDual).X₁) :
    let K := (relativeChainFunctor R).obj X
    let hnext : (ComplexShape.down ℕ).next (p + 1) = p :=
      ChainComplex.next_nat_succ p
    let eta' : RelativeCochain R X p :=
      (eta : Module.Dual R (K.X ((ComplexShape.down ℕ).next (p + 1)))).comp
        (K.XIsoOfEq hnext).inv.hom
    relativeCohomologyCycleToCocycle R X (p + 1)
        ((((K.sc (p + 1)).linearDual).moduleCatToCycles) eta) =
      ⟨relativeCoboundary R X p eta',
        relativeCoboundary_relativeCoboundary R X p eta'⟩ := by
  dsimp only
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  let K := (relativeChainFunctor R).obj X
  let hnext : (ComplexShape.down ℕ).next (p + 1) = p :=
    ChainComplex.next_nat_succ p
  let etaF : Module.Dual R (K.X ((ComplexShape.down ℕ).next (p + 1))) := eta
  change etaF ((K.d (p + 1) ((ComplexShape.down ℕ).next (p + 1))).hom c) =
    etaF ((K.XIsoOfEq hnext).inv.hom ((K.d (p + 1) p).hom c))
  have hd := ConcreteCategory.congr_hom (K.d_comp_XIsoOfEq_inv hnext (p + 1)) c
  exact congrArg etaF hd.symm

/-- Relative cap product on dual cycles annihilates the boundaries in the explicit
cohomology quotient. -/
lemma relativeCohomologyCycleCapLinear_vanishes_on_boundaries
    (X : TopPair.{u}) (p q : ℕ) :
    let T := (((relativeChainFunctor R).obj X).sc p).linearDual
    LinearMap.range T.moduleCatToCycles ≤
      LinearMap.ker (relativeCohomologyCycleCapLinear R X p q) := by
  dsimp only
  rintro _ ⟨eta, rfl⟩
  cases p with
  | zero =>
      change relativeCohomologyCycleCapLinear R X 0 q
        (((((relativeChainFunctor R).obj X).sc 0).linearDual.moduleCatToCycles) eta) = 0
      let K := (relativeChainFunctor R).obj X
      have hz : ((K.sc 0).linearDual).moduleCatToCycles eta = 0 := by
        apply Subtype.ext
        change ((K.sc 0).g.hom.dualMap) eta = 0
        have hg : (K.sc 0).g = 0 := by
          change K.d 0 ((ComplexShape.down ℕ).next 0) = 0
          apply K.shape
          rw [ChainComplex.next_nat_zero]
          simp
        rw [hg]
        apply LinearMap.ext
        intro c
        let etaF : Module.Dual R (K.sc 0).X₃ := eta
        change etaF (0 : (K.sc 0).X₃) = 0
        exact map_zero etaF
      rw [hz]
      exact map_zero (relativeCohomologyCycleCapLinear R X 0 q)
  | succ p =>
      change relativeCohomologyCycleCapLinear R X (p + 1) q
        (((((relativeChainFunctor R).obj X).sc
          (p + 1)).linearDual.moduleCatToCycles) eta) = 0
      rw [relativeCohomologyCycleCapLinear, LinearMap.comp_apply,
        relativeCohomologyCycleToCocycle_moduleCatToCycles_succ,
        relativeCapCocycleHomologyLinear_apply, relativeCapHomologyMap_coboundary]

/-- Same-pair relative cap product on the explicit quotient of relative cocycles by
relative coboundaries. -/
noncomputable def relativeCapCohomologyExplicitLinear
    (X : TopPair.{u}) (p q : ℕ) :
    let T := (((relativeChainFunctor R).obj X).sc p).linearDual
    T.moduleCatLeftHomologyData.H →ₗ[R]
      (RelativeHomology R X (p + q) →ₗ[R] Homology R X.fst q) :=
  let T := (((relativeChainFunctor R).obj X).sc p).linearDual
  (LinearMap.range T.moduleCatToCycles).liftQ
    (relativeCohomologyCycleCapLinear R X p q)
    (relativeCohomologyCycleCapLinear_vanishes_on_boundaries R X p q)

/-- Same-pair relative cap product on algebraic relative cochain cohomology. -/
noncomputable def relativeCapCochainCohomologyLinear
    (X : TopPair.{u}) (p q : ℕ) :
    RelativeCochainCohomology R X p →ₗ[R]
      (RelativeHomology R X (p + q) →ₗ[R] Homology R X.fst q) :=
  let T := (((relativeChainFunctor R).obj X).sc p).linearDual
  (relativeCapCohomologyExplicitLinear R X p q).comp
    T.moduleCatHomologyIso.hom.hom

/-- On the class of an explicit relative dual cycle, the cochain-cohomology cap product
agrees with the cocycle-level construction. -/
@[simp]
lemma relativeCapCochainCohomologyLinear_on_cycle
    (X : TopPair.{u}) (p q : ℕ)
    (phi : LinearMap.ker
      ((((relativeChainFunctor R).obj X).sc p).linearDual.g.hom)) :
    let T := (((relativeChainFunctor R).obj X).sc p).linearDual
    relativeCapCochainCohomologyLinear R X p q
        (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
      relativeCohomologyCycleCapLinear R X p q phi := by
  dsimp only
  let T := (((relativeChainFunctor R).obj X).sc p).linearDual
  change relativeCapCohomologyExplicitLinear R X p q
      (T.moduleCatHomologyIso.hom.hom
        (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))) = _
  have h := ConcreteCategory.congr_hom T.moduleCatHomologyIso.inv_hom_id
    (Submodule.Quotient.mk phi)
  change T.moduleCatHomologyIso.hom.hom
      (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
    Submodule.Quotient.mk phi at h
  rw [h]
  rfl

/-- Same-pair relative cap product on the repository's standard relative cohomology and
relative homology objects. -/
noncomputable def relativeCapCohomologyLinear (X : TopPair.{u}) (p q : ℕ) :
    RelativeCohomology R X p →ₗ[R]
      (RelativeHomology R X (p + q) →ₗ[R] Homology R X.fst q) :=
  (relativeCapCochainCohomologyLinear R X p q).comp
    ((((relativeChainFunctor R).obj X).sc p).linearDualHomologyEquiv.symm.toLinearMap)

set_option backward.isDefEq.respectTransparency false in
/-- On the standard relative cohomology class represented by an explicit relative
cocycle, the same-pair cap product agrees with the cocycle-level map. -/
@[simp]
lemma relativeCapCohomologyLinear_on_cycle
    (X : TopPair.{u}) (p q : ℕ)
    (phi : LinearMap.ker
      ((((relativeChainFunctor R).obj X).sc p).linearDual.g.hom)) :
    let S := ((relativeChainFunctor R).obj X).sc p
    relativeCapCohomologyLinear R X p q
        (S.linearDualHomologyEquiv
          (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))) =
      relativeCohomologyCycleCapLinear R X p q phi := by
  dsimp only
  rw [relativeCapCohomologyLinear, LinearMap.comp_apply]
  let S := ((relativeChainFunctor R).obj X).sc p
  have h := S.linearDualHomologyEquiv.symm_apply_apply
    (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))
  change relativeCapCochainCohomologyLinear R X p q
      (S.linearDualHomologyEquiv.symm
        (S.linearDualHomologyEquiv
          (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)))) = _
  rw [h]
  exact relativeCapCochainCohomologyLinear_on_cycle R X p q phi

/-- Singular cocycles, represented on the algebraic singular cochain complex. -/
abbrev Cocycle (X : TopCat.{u}) (p : ℕ) :=
  Simplicial.Cocycle R (TopCat.toSSet.obj X) p

/-- Cap product with a singular cocycle, as an honest map between the standard singular
homology objects. -/
noncomputable def capHomologyMap (X : TopCat.{u}) (p q : ℕ)
    (phi : Cocycle R X p) : Homology R X (p + q) →ₗ[R] Homology R X q :=
  Simplicial.capHomologyMap R p q phi.1 phi.2

/-- Cap product by singular cocycles, linear in the cocycle argument. -/
noncomputable def capCocycleHomologyLinear (X : TopCat.{u}) (p q : ℕ) :
    Cocycle R X p →ₗ[R]
      (Homology R X (p + q) →ₗ[R] Homology R X q) :=
  Simplicial.capCocycleHomologyLinear R p q

@[simp]
lemma capCocycleHomologyLinear_apply (X : TopCat.{u}) (p q : ℕ)
    (phi : Cocycle R X p) :
    capCocycleHomologyLinear R X p q phi = capHomologyMap R X p q phi :=
  rfl

/-- Singular cap product, descended all the way to the repository's standard singular
cochain cohomology and singular homology objects. -/
noncomputable def capCohomologyLinear (X : TopCat.{u}) (p q : ℕ) :
    CochainCohomology R X p →ₗ[R]
      (Homology R X (p + q) →ₗ[R] Homology R X q) :=
  Simplicial.capCohomologyLinear R p q

end AlgebraicTopology.Singular
