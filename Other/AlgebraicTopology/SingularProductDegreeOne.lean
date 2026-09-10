/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularCapNaturality
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# Degree-one products in singular chains

This file constructs the two-triangle shuffle product of two simplicial one-chains.  It is the
degree `(1,1)` part of the Eilenberg--Zilber map and is enough to manufacture a two-cycle in a
product from two one-cycles.  The construction uses the coproduct universal property of the
unnormalised simplicial chain groups, so it applies to arbitrary (possibly infinite) singular
chains without choosing bases.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace AlgebraicTopology.Simplicial

variable (R : Type u) [Field R]

/-- Extend a function on simplices linearly to the unnormalised chain group. -/
def linearOfChainGenerators {X : SSet.{u}} {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module R M]
    (f : X.obj (Opposite.op (SimplexCategory.mk n)) → M) :
    ChainGroup R X n →ₗ[R] M :=
  ((X.isColimitChainComplexXCofan (ModuleCat.of R R) n).desc
    (Cofan.mk _ fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (f x)))).hom

@[simp]
lemma linearOfChainGenerators_chainOfSimplex {X : SSet.{u}} {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module R M]
    (f : X.obj (Opposite.op (SimplexCategory.mk n)) → M)
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    linearOfChainGenerators R f (chainOfSimplex R x) = f x := by
  have h := ConcreteCategory.congr_hom
    ((X.isColimitChainComplexXCofan (ModuleCat.of R R) n).fac
      (Cofan.mk _ fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (f x)))
      (Discrete.mk x)) (1 : R)
  change ((X.isColimitChainComplexXCofan (ModuleCat.of R R) n).desc
      (Cofan.mk _ fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (f x)))).hom
        ((X.ιChainComplex (R := ModuleCat.of R R) x).hom 1) =
      (LinearMap.toSpanSingleton R M (f x)) 1 at h
  exact h.trans (LinearMap.toSpanSingleton_apply_one R M (f x))

/-- Extend a function of two simplices bilinearly to the two chain groups. -/
def bilinearOfChainGenerators {X Y : SSet.{u}} {n m : ℕ}
    {M : Type u} [AddCommGroup M] [Module R M]
    (f : X.obj (Opposite.op (SimplexCategory.mk n)) →
      Y.obj (Opposite.op (SimplexCategory.mk m)) → M) :
    ChainGroup R X n →ₗ[R] ChainGroup R Y m →ₗ[R] M :=
  linearOfChainGenerators R fun x => linearOfChainGenerators R (f x)

@[simp]
lemma bilinearOfChainGenerators_chainOfSimplex_left {X Y : SSet.{u}} {n m : ℕ}
    {M : Type u} [AddCommGroup M] [Module R M]
    (f : X.obj (Opposite.op (SimplexCategory.mk n)) →
      Y.obj (Opposite.op (SimplexCategory.mk m)) → M)
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    bilinearOfChainGenerators R f (chainOfSimplex R x) =
      linearOfChainGenerators R (f x) := by
  exact linearOfChainGenerators_chainOfSimplex R _ x

@[simp]
lemma bilinearOfChainGenerators_chainOfSimplex {X Y : SSet.{u}} {n m : ℕ}
    {M : Type u} [AddCommGroup M] [Module R M]
    (f : X.obj (Opposite.op (SimplexCategory.mk n)) →
      Y.obj (Opposite.op (SimplexCategory.mk m)) → M)
    (x : X.obj (Opposite.op (SimplexCategory.mk n)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk m))) :
    bilinearOfChainGenerators R f (chainOfSimplex R x) (chainOfSimplex R y) = f x y := by
  rw [bilinearOfChainGenerators_chainOfSimplex_left,
    linearOfChainGenerators_chainOfSimplex]

/-- Linear maps out of an unnormalised chain group are determined by their values on simplex
generators. -/
theorem linearMap_ext_chainOfSimplex {X : SSet.{u}} {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module R M]
    {f g : ChainGroup R X n →ₗ[R] M}
    (h : ∀ x : X.obj (Opposite.op (SimplexCategory.mk n)),
      f (chainOfSimplex R x) = g (chainOfSimplex R x)) :
    f = g := by
  have hcat : ModuleCat.ofHom f = ModuleCat.ofHom g := by
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
    change f ((X.ιChainComplex (R := ModuleCat.of R R) x).hom a) =
      g ((X.ιChainComplex (R := ModuleCat.of R R) x).hom a)
    rw [hiota, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hcat

/-- The first triangle in the standard triangulation of the product of two one-simplices. -/
def degreeOneShuffleFirst {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    (X ⊗ Y : SSet.{u}).obj (Opposite.op (SimplexCategory.mk 2)) :=
  ⟨X.σ 1 x, Y.σ 0 y⟩

/-- The second triangle in the standard triangulation of the product of two one-simplices. -/
def degreeOneShuffleSecond {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    (X ⊗ Y : SSet.{u}).obj (Opposite.op (SimplexCategory.mk 2)) :=
  ⟨X.σ 0 x, Y.σ 1 y⟩

/-- The signed two-triangle chain associated to a pair of one-simplices. -/
def degreeOneShuffleSimplex {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    ChainGroup R (X ⊗ Y) 2 :=
  chainOfSimplex R (degreeOneShuffleFirst x y) -
    chainOfSimplex R (degreeOneShuffleSecond x y)

/-- A vertex in the first factor times a one-simplex in the second factor. -/
def degreeZeroOneSimplex {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    (X ⊗ Y : SSet.{u}).obj (Opposite.op (SimplexCategory.mk 1)) :=
  ⟨X.σ 0 x, y⟩

/-- A one-simplex in the first factor times a vertex in the second factor. -/
def degreeOneZeroSimplex {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
    (X ⊗ Y : SSet.{u}).obj (Opposite.op (SimplexCategory.mk 1)) :=
  ⟨x, Y.σ 0 y⟩

@[simp]
lemma delta_zero_degreeOneShuffleFirst {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    (X ⊗ Y).δ 0 (degreeOneShuffleFirst x y) =
      degreeZeroOneSimplex (X.δ 0 x) y := by
  apply Prod.ext
  · change X.δ 0 (X.σ 1 x) = X.σ 0 (X.δ 0 x)
    simpa using SSet.δ_comp_σ_of_le_apply (S := X)
      (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide) x
  · change Y.δ 0 (Y.σ 0 y) = y
    simpa using SSet.δ_comp_σ_self_apply (S := Y) (0 : Fin 2) y

@[simp]
lemma delta_one_degreeOneShuffleFirst {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    (X ⊗ Y).δ 1 (degreeOneShuffleFirst x y) = ⟨x, y⟩ := by
  apply Prod.ext
  · change X.δ 1 (X.σ 1 x) = x
    simpa using SSet.δ_comp_σ_self_apply (S := X) (1 : Fin 2) x
  · change Y.δ 1 (Y.σ 0 y) = y
    simpa using SSet.δ_comp_σ_succ_apply (S := Y) (0 : Fin 2) y

@[simp]
lemma delta_two_degreeOneShuffleFirst {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    (X ⊗ Y).δ 2 (degreeOneShuffleFirst x y) =
      degreeOneZeroSimplex x (Y.δ 1 y) := by
  apply Prod.ext
  · change X.δ 2 (X.σ 1 x) = x
    simpa using SSet.δ_comp_σ_succ_apply (S := X) (1 : Fin 2) x
  · change Y.δ 2 (Y.σ 0 y) = Y.σ 0 (Y.δ 1 y)
    simpa using SSet.δ_comp_σ_of_gt_apply (S := Y)
      (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) y

@[simp]
lemma delta_zero_degreeOneShuffleSecond {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    (X ⊗ Y).δ 0 (degreeOneShuffleSecond x y) =
      degreeOneZeroSimplex x (Y.δ 0 y) := by
  apply Prod.ext
  · change X.δ 0 (X.σ 0 x) = x
    simpa using SSet.δ_comp_σ_self_apply (S := X) (0 : Fin 2) x
  · change Y.δ 0 (Y.σ 1 y) = Y.σ 0 (Y.δ 0 y)
    simpa using SSet.δ_comp_σ_of_le_apply (S := Y)
      (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide) y

@[simp]
lemma delta_one_degreeOneShuffleSecond {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    (X ⊗ Y).δ 1 (degreeOneShuffleSecond x y) = ⟨x, y⟩ := by
  apply Prod.ext
  · change X.δ 1 (X.σ 0 x) = x
    simpa using SSet.δ_comp_σ_succ_apply (S := X) (0 : Fin 2) x
  · change Y.δ 1 (Y.σ 1 y) = y
    simpa using SSet.δ_comp_σ_self_apply (S := Y) (1 : Fin 2) y

@[simp]
lemma delta_two_degreeOneShuffleSecond {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    (X ⊗ Y).δ 2 (degreeOneShuffleSecond x y) =
      degreeZeroOneSimplex (X.δ 1 x) y := by
  apply Prod.ext
  · change X.δ 2 (X.σ 0 x) = X.σ 0 (X.δ 1 x)
    simpa using SSet.δ_comp_σ_of_gt_apply (S := X)
      (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) x
  · change Y.δ 2 (Y.σ 1 y) = y
    simpa using SSet.δ_comp_σ_succ_apply (S := Y) (1 : Fin 2) y

/-- Boundary of the signed two-triangle shuffle on a pair of one-simplices. -/
theorem boundary_degreeOneShuffleSimplex {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    boundary R 1 (degreeOneShuffleSimplex R x y) =
      chainOfSimplex R (degreeZeroOneSimplex (X.δ 0 x) y) -
        chainOfSimplex R (degreeZeroOneSimplex (X.δ 1 x) y) -
        chainOfSimplex R (degreeOneZeroSimplex x (Y.δ 0 y)) +
        chainOfSimplex R (degreeOneZeroSimplex x (Y.δ 1 y)) := by
  rw [degreeOneShuffleSimplex, map_sub, boundary_chainOfSimplex,
    boundary_chainOfSimplex]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, one_smul]
  erw [delta_zero_degreeOneShuffleFirst, delta_one_degreeOneShuffleFirst,
    delta_two_degreeOneShuffleFirst, delta_zero_degreeOneShuffleSecond,
    delta_one_degreeOneShuffleSecond, delta_two_degreeOneShuffleSecond]
  norm_num
  abel

/-- The degree `(1,1)` shuffle product, bilinearly extended to arbitrary one-chains. -/
def degreeOneShuffle {X Y : SSet.{u}} :
    ChainGroup R X 1 →ₗ[R] ChainGroup R Y 1 →ₗ[R] ChainGroup R (X ⊗ Y) 2 :=
  bilinearOfChainGenerators R fun x y => degreeOneShuffleSimplex R x y

@[simp]
lemma degreeOneShuffle_chainOfSimplex {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    degreeOneShuffle R (chainOfSimplex R x) (chainOfSimplex R y) =
      degreeOneShuffleSimplex R x y :=
  bilinearOfChainGenerators_chainOfSimplex R _ x y

/-- Product of a zero-chain in the first factor with a one-chain in the second factor. -/
def degreeZeroOne {X Y : SSet.{u}} :
    ChainGroup R X 0 →ₗ[R] ChainGroup R Y 1 →ₗ[R] ChainGroup R (X ⊗ Y) 1 :=
  bilinearOfChainGenerators R fun x y =>
    chainOfSimplex R (degreeZeroOneSimplex x y)

@[simp]
lemma degreeZeroOne_chainOfSimplex {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    degreeZeroOne R (chainOfSimplex R x) (chainOfSimplex R y) =
      chainOfSimplex R (degreeZeroOneSimplex x y) :=
  bilinearOfChainGenerators_chainOfSimplex R _ x y

/-- Product of a one-chain in the first factor with a zero-chain in the second factor. -/
def degreeOneZero {X Y : SSet.{u}} :
    ChainGroup R X 1 →ₗ[R] ChainGroup R Y 0 →ₗ[R] ChainGroup R (X ⊗ Y) 1 :=
  bilinearOfChainGenerators R fun x y =>
    chainOfSimplex R (degreeOneZeroSimplex x y)

@[simp]
lemma degreeOneZero_chainOfSimplex {X Y : SSet.{u}}
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
    degreeOneZero R (chainOfSimplex R x) (chainOfSimplex R y) =
      chainOfSimplex R (degreeOneZeroSimplex x y) :=
  bilinearOfChainGenerators_chainOfSimplex R _ x y

/-- The degree `(1,1)` shuffle obeys the Leibniz boundary formula. -/
theorem boundary_degreeOneShuffle {X Y : SSet.{u}}
    (c : ChainGroup R X 1) (d : ChainGroup R Y 1) :
    boundary R 1 (degreeOneShuffle R c d) =
      degreeZeroOne R (boundary R 0 c) d -
        degreeOneZero R c (boundary R 0 d) := by
  have hmaps :
      LinearMap.compr₂ (degreeOneShuffle R :
        ChainGroup R X 1 →ₗ[R] ChainGroup R Y 1 →ₗ[R] ChainGroup R (X ⊗ Y) 2)
          (boundary R 1) =
        ((degreeZeroOne R :
          ChainGroup R X 0 →ₗ[R] ChainGroup R Y 1 →ₗ[R] ChainGroup R (X ⊗ Y) 1).comp
            (boundary R 0)) -
          LinearMap.compl₂ (degreeOneZero R :
            ChainGroup R X 1 →ₗ[R] ChainGroup R Y 0 →ₗ[R] ChainGroup R (X ⊗ Y) 1)
              (boundary R 0) := by
    apply linearMap_ext_chainOfSimplex R
    intro x
    apply linearMap_ext_chainOfSimplex R
    intro y
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.compl₂_apply]
    rw [degreeOneShuffle_chainOfSimplex]
    change boundary R 1 (degreeOneShuffleSimplex R x y) =
      degreeZeroOne R (boundary R 0 (chainOfSimplex R x)) (chainOfSimplex R y) -
        degreeOneZero R (chainOfSimplex R x) (boundary R 0 (chainOfSimplex R y))
    rw [boundary_degreeOneShuffleSimplex, boundary_chainOfSimplex,
      boundary_chainOfSimplex]
    simp [Fin.sum_univ_succ]
    abel
  exact LinearMap.congr_fun (LinearMap.congr_fun hmaps c) d

/-- The shuffle of two one-cycles is a two-cycle. -/
theorem boundary_degreeOneShuffle_eq_zero {X Y : SSet.{u}}
    (c : ChainGroup R X 1) (d : ChainGroup R Y 1)
    (hc : boundary R 0 c = 0) (hd : boundary R 0 d = 0) :
    boundary R 1 (degreeOneShuffle R c d) = 0 := by
  rw [boundary_degreeOneShuffle R c d, hc, hd]
  simp

/-! ## The external cochain and its evaluation -/

/-- The degree `(1,1)` external cochain.  On a product two-simplex it evaluates the first
cochain on the front edge and the second cochain on the back edge. -/
noncomputable def degreeOneExternalCochain {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1) :
    Cochain R (X ⊗ Y) 2 :=
  linearOfChainGenerators R fun z =>
    phi (chainOfSimplex R (frontFace (p := 1) (q := 1) X z.1)) *
      psi (chainOfSimplex R (backFace (p := 1) (q := 1) Y z.2))

@[simp]
lemma degreeOneExternalCochain_chainOfSimplex {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1)
    (z : (X ⊗ Y : SSet.{u}).obj (Opposite.op (SimplexCategory.mk 2))) :
    degreeOneExternalCochain R phi psi (chainOfSimplex R z) =
      phi (chainOfSimplex R (frontFace (p := 1) (q := 1) X z.1)) *
        psi (chainOfSimplex R (backFace (p := 1) (q := 1) Y z.2)) := by
  apply linearOfChainGenerators_chainOfSimplex

/-- A one-cocycle vanishes on every degenerate edge. -/
lemma oneCocycle_degenerate {X : SSet.{u}} (phi : Cochain R X 1)
    (hphi : coboundary R 1 phi = 0)
    (v : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    phi (chainOfSimplex R (X.σ 0 v)) = 0 := by
  have h0 : X.δ 0 (X.σ 0 (X.σ 0 v)) = X.σ 0 v := by
    simpa using SSet.δ_comp_σ_self_apply (S := X) (0 : Fin 2) (X.σ 0 v)
  have h1 : X.δ 1 (X.σ 0 (X.σ 0 v)) = X.σ 0 v := by
    simpa using SSet.δ_comp_σ_succ_apply (S := X) (0 : Fin 2) (X.σ 0 v)
  have h2 : X.δ 2 (X.σ 0 (X.σ 0 v)) = X.σ 0 v := by
    calc
      X.δ 2 (X.σ 0 (X.σ 0 v)) = X.σ 0 (X.δ 1 (X.σ 0 v)) := by
        simpa using SSet.δ_comp_σ_of_gt_apply (S := X)
          (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) (X.σ 0 v)
      _ = X.σ 0 v := by
        rw [show X.δ 1 (X.σ 0 v) = v by
          simpa using SSet.δ_comp_σ_succ_apply (S := X) (0 : Fin 1) v]
  have hboundary :
      boundary R 1 (chainOfSimplex R (X.σ 0 (X.σ 0 v))) =
        chainOfSimplex R (X.σ 0 v) := by
    rw [boundary_chainOfSimplex]
    simp only [Fin.sum_univ_succ]
    erw [h0, h1, h2]
    norm_num
  have h := LinearMap.congr_fun hphi
    (chainOfSimplex R (X.σ 0 (X.σ 0 v)))
  rw [coboundary_apply, hboundary] at h
  simpa using h

lemma frontFace_one_one_eq_delta_two {X : SSet.{u}}
    (z : X.obj (Opposite.op (SimplexCategory.mk 2))) :
    frontFace (p := 1) (q := 1) X z = X.δ 2 z := by
  unfold frontFace
  rw [show frontInclusion 1 1 = SimplexCategory.δ 2 by
    ext i
    fin_cases i <;> rfl]
  rfl

lemma backFace_one_one_eq_delta_zero {X : SSet.{u}}
    (z : X.obj (Opposite.op (SimplexCategory.mk 2))) :
    backFace (p := 1) (q := 1) X z = X.δ 0 z := by
  unfold backFace
  rw [show backInclusion 1 1 = SimplexCategory.δ 0 by
    ext i
    fin_cases i <;> rfl]
  rfl

/-- The external cochain evaluates on the two-triangle shuffle as the product of the two
one-cochain evaluations. -/
lemma degreeOneExternalCochain_shuffleSimplex {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1)
    (hphi : coboundary R 1 phi = 0) (hpsi : coboundary R 1 psi = 0)
    (x : X.obj (Opposite.op (SimplexCategory.mk 1)))
    (y : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
    degreeOneExternalCochain R phi psi (degreeOneShuffleSimplex R x y) =
      phi (chainOfSimplex R x) * psi (chainOfSimplex R y) := by
  rw [degreeOneShuffleSimplex, map_sub, degreeOneExternalCochain_chainOfSimplex,
    degreeOneExternalCochain_chainOfSimplex]
  rw [frontFace_one_one_eq_delta_two, backFace_one_one_eq_delta_zero,
    frontFace_one_one_eq_delta_two, backFace_one_one_eq_delta_zero]
  change
    phi (chainOfSimplex R (X.δ 2 (X.σ 1 x))) *
        psi (chainOfSimplex R (Y.δ 0 (Y.σ 0 y))) -
      phi (chainOfSimplex R (X.δ 2 (X.σ 0 x))) *
        psi (chainOfSimplex R (Y.δ 0 (Y.σ 1 y))) = _
  have hxfirst : X.δ 2 (X.σ 1 x) = x := by
    simpa using SSet.δ_comp_σ_succ_apply (S := X) (1 : Fin 2) x
  have hyfirst : Y.δ 0 (Y.σ 0 y) = y := by
    simpa using SSet.δ_comp_σ_self_apply (S := Y) (0 : Fin 2) y
  have hxsecond : X.δ 2 (X.σ 0 x) = X.σ 0 (X.δ 1 x) := by
    simpa using SSet.δ_comp_σ_of_gt_apply (S := X)
      (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) x
  have hysecond : Y.δ 0 (Y.σ 1 y) = Y.σ 0 (Y.δ 0 y) := by
    simpa using SSet.δ_comp_σ_of_le_apply (S := Y)
      (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide) y
  rw [hxfirst, hyfirst, hxsecond, hysecond]
  have hx : phi (chainOfSimplex R (X.σ 0 (X.δ 1 x))) = 0 :=
    oneCocycle_degenerate R phi hphi (X.δ 1 x)
  have hy : psi (chainOfSimplex R (Y.σ 0 (Y.δ 0 y))) = 0 :=
    oneCocycle_degenerate R psi hpsi (Y.δ 0 y)
  rw [hx, hy]
  ring

/-- Bilinear form of `degreeOneExternalCochain_shuffleSimplex`, for arbitrary chains. -/
theorem degreeOneExternalCochain_shuffle {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1)
    (hphi : coboundary R 1 phi = 0) (hpsi : coboundary R 1 psi = 0)
    (c : ChainGroup R X 1) (d : ChainGroup R Y 1) :
    degreeOneExternalCochain R phi psi (degreeOneShuffle R c d) = phi c * psi d := by
  let lhs := LinearMap.compr₂
    (degreeOneShuffle R :
      ChainGroup R X 1 →ₗ[R] ChainGroup R Y 1 →ₗ[R] ChainGroup R (X ⊗ Y) 2)
    (degreeOneExternalCochain R phi psi)
  let rhs := LinearMap.compl₂ ((LinearMap.mul R R).comp phi) psi
  have hmaps : lhs = rhs := by
    apply linearMap_ext_chainOfSimplex R
    intro x
    apply linearMap_ext_chainOfSimplex R
    intro y
    simp only [lhs, rhs, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
      LinearMap.comp_apply]
    rw [degreeOneShuffle_chainOfSimplex]
    exact degreeOneExternalCochain_shuffleSimplex R phi psi hphi hpsi x y
  exact LinearMap.congr_fun (LinearMap.congr_fun hmaps c) d

/-! ## Cocycle and nonvanishing properties -/

/-- The cap-product presentation of the degree `(1,1)` external cochain. -/
noncomputable def degreeOneExternalCochainViaCap {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1) :
    Cochain R (X ⊗ Y) 2 :=
  let phi' := cochainMap R (SemiCartesianMonoidalCategory.fst X Y) 1 phi
  let psi' := cochainMap R (SemiCartesianMonoidalCategory.snd X Y) 1 psi
  psi'.comp (cap R 1 1 phi')

lemma degreeOneExternalCochainViaCap_eq {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1) :
    degreeOneExternalCochainViaCap R phi psi = degreeOneExternalCochain R phi psi := by
  apply linearMap_ext_chainOfSimplex R
  intro z
  rw [degreeOneExternalCochain_chainOfSimplex]
  dsimp only [degreeOneExternalCochainViaCap, LinearMap.comp_apply]
  rw [cap_chainOfSimplex, map_smul]
  simp only [cochainMap_apply, chainOfSimplex_map]
  have hf :
      (SemiCartesianMonoidalCategory.fst X Y).app _
          (frontFace (p := 1) (q := 1) (X ⊗ Y) z) =
        frontFace (p := 1) (q := 1) X z.1 := by
    rw [← frontFace_naturality]
    rfl
  have hb :
      (SemiCartesianMonoidalCategory.snd X Y).app _
          (backFace (p := 1) (q := 1) (X ⊗ Y) z) =
        backFace (p := 1) (q := 1) Y z.2 := by
    rw [← backFace_naturality]
    rfl
  rw [hf, hb]
  rfl

/-- The external product of two one-cocycles is a two-cocycle. -/
theorem coboundary_degreeOneExternalCochain {X Y : SSet.{u}}
    (phi : Cochain R X 1) (psi : Cochain R Y 1)
    (hphi : coboundary R 1 phi = 0) (hpsi : coboundary R 1 psi = 0) :
    coboundary R 2 (degreeOneExternalCochain R phi psi) = 0 := by
  rw [← degreeOneExternalCochainViaCap_eq]
  let phi' := cochainMap R (SemiCartesianMonoidalCategory.fst X Y) 1 phi
  let psi' := cochainMap R (SemiCartesianMonoidalCategory.snd X Y) 1 psi
  have hphi' : coboundary R 1 phi' = 0 := by
    dsimp only [phi']
    rw [coboundary_cochainMap, hphi]
    exact map_zero _
  have hpsi' : coboundary R 1 psi' = 0 := by
    dsimp only [psi']
    rw [coboundary_cochainMap, hpsi]
    exact map_zero _
  apply LinearMap.ext
  intro c
  rw [LinearMap.zero_apply, coboundary_apply]
  change psi' (cap R 1 1 phi' (boundary R 2 c)) = 0
  have hvanish : psi' (boundary R 1 (cap R 1 2 phi' c)) = 0 := by
    have h := LinearMap.congr_fun hpsi' (cap R 1 2 phi' c)
    rw [coboundary_apply] at h
    simpa using h
  rw [boundary_cap_eq_of_cocycle R 1 1 phi' hphi' c] at hvanish
  simpa using hvanish

/-- The cochain-complex cohomology class represented by an explicit two-cocycle. -/
noncomputable def cochainClassOfTwoCocycle {X : SSet.{u}}
    (phi : Cochain R X 2) (hphi : coboundary R 2 phi = 0) :
    CochainCohomology R X 2 := by
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 2
  have hphi' : phi ∈ LinearMap.ker S.f.hom.dualMap := by
    change S.f.hom.dualMap phi = 0
    apply LinearMap.ext
    intro b
    rw [LinearMap.zero_apply]
    let hprev : (ComplexShape.down ℕ).prev 2 = 3 := ChainComplex.prev ℕ 2
    let b' : ChainGroup R X 3 := (K.XIsoOfEq hprev).hom.hom b
    have hd := ConcreteCategory.congr_hom
      (K.XIsoOfEq_hom_comp_d hprev 2) b
    have hv := LinearMap.congr_fun hphi b'
    rw [coboundary_apply] at hv
    change phi (S.f.hom b) = 0
    change phi ((K.d ((ComplexShape.down ℕ).prev 2) 2).hom b) = 0
    rw [← show (K.d 3 2).hom ((K.XIsoOfEq hprev).hom.hom b) =
      (K.d ((ComplexShape.down ℕ).prev 2) 2).hom b from hd]
    exact hv
  exact S.linearDual.moduleCatHomologyClass ⟨phi, hphi'⟩

/-- The cochain-complex cohomology class represented by an explicit one-cocycle. -/
noncomputable def cochainClassOfOneCocycle {X : SSet.{u}}
    (phi : Cochain R X 1) (hphi : coboundary R 1 phi = 0) :
    CochainCohomology R X 1 := by
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 1
  have hphi' : phi ∈ LinearMap.ker S.f.hom.dualMap := by
    change S.f.hom.dualMap phi = 0
    apply LinearMap.ext
    intro b
    rw [LinearMap.zero_apply]
    let hprev : (ComplexShape.down ℕ).prev 1 = 2 := ChainComplex.prev ℕ 1
    let b' : ChainGroup R X 2 := (K.XIsoOfEq hprev).hom.hom b
    have hd := ConcreteCategory.congr_hom
      (K.XIsoOfEq_hom_comp_d hprev 1) b
    have hv := LinearMap.congr_fun hphi b'
    rw [coboundary_apply] at hv
    change phi (S.f.hom b) = 0
    change phi ((K.d ((ComplexShape.down ℕ).prev 1) 1).hom b) = 0
    rw [← show (K.d 2 1).hom ((K.XIsoOfEq hprev).hom.hom b) =
      (K.d ((ComplexShape.down ℕ).prev 1) 1).hom b from hd]
    exact hv
  exact S.linearDual.moduleCatHomologyClass ⟨phi, hphi'⟩

/-- Converting a dual-complex cycle to a simplicial cocycle and then taking its represented
class recovers the original cohomology class. -/
@[simp]
public lemma cochainClassOfOneCocycle_cohomologyCycleToCocycle {X : SSet.{u}}
    (eta : LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc 1).linearDual.g.hom)) :
    cochainClassOfOneCocycle R
        (cohomologyCycleToCocycle R 1 eta).1
        (cohomologyCycleToCocycle R 1 eta).2 =
      ((X.chainComplex (ModuleCat.of R R)).sc 1).linearDual.moduleCatHomologyClass eta := by
  rfl

/-- The homology class represented by an explicit two-cycle. -/
noncomputable def homologyClassOfTwoCycle {X : SSet.{u}}
    (c : ChainGroup R X 2) (hc : boundary R 1 c = 0) :
    (X.chainComplex (ModuleCat.of R R)).homology 2 := by
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 2
  have hc' : c ∈ LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc 2).g.hom) := by
    change ((X.chainComplex (ModuleCat.of R R)).d 2
      ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc
  exact S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk ⟨c, hc'⟩)

/-- Under universal coefficients, evaluation of a represented cohomology class on a
represented homology class is the original cochain-chain pairing. -/
theorem cochainClassOfTwoCocycle_pair {X : SSet.{u}}
    (phi : Cochain R X 2) (hphi : coboundary R 2 phi = 0)
    (c : ChainGroup R X 2) (hc : boundary R 1 c = 0) :
    let S := (X.chainComplex (ModuleCat.of R R)).sc 2
    S.linearDualHomologyEquiv (cochainClassOfTwoCocycle R phi hphi)
      (homologyClassOfTwoCycle R c hc) = phi c := by
  dsimp only
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 2
  have hc' : c ∈ LinearMap.ker S.g.hom := by
    change (K.d 2 ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc
  have hphi' : phi ∈ LinearMap.ker S.f.hom.dualMap := by
    change S.f.hom.dualMap phi = 0
    apply LinearMap.ext
    intro b
    rw [LinearMap.zero_apply]
    let hprev : (ComplexShape.down ℕ).prev 2 = 3 := ChainComplex.prev ℕ 2
    let b' : ChainGroup R X 3 := (K.XIsoOfEq hprev).hom.hom b
    have hd := ConcreteCategory.congr_hom
      (K.XIsoOfEq_hom_comp_d hprev 2) b
    have hv := LinearMap.congr_fun hphi b'
    rw [coboundary_apply] at hv
    change phi (S.f.hom b) = 0
    change phi ((K.d ((ComplexShape.down ℕ).prev 2) 2).hom b) = 0
    rw [← show (K.d 3 2).hom ((K.XIsoOfEq hprev).hom.hom b) =
      (K.d ((ComplexShape.down ℕ).prev 2) 2).hom b from hd]
    exact hv
  let z : LinearMap.ker S.g.hom := ⟨c, hc'⟩
  let eta : LinearMap.ker S.f.hom.dualMap := ⟨phi, hphi'⟩
  change S.linearDualHomologyEquiv (S.linearDual.moduleCatHomologyClass eta)
      (S.moduleCatHomologyClass z) = phi c
  exact S.linearDualHomologyEquiv_class_apply_class eta z

/-- A cocycle with nonzero evaluation proves that an explicit two-cycle has nonzero homology
class. -/
lemma homologyClassOfTwoCycle_ne_zero {X : SSet.{u}}
    (c : ChainGroup R X 2) (hc : boundary R 1 c = 0)
    (phi : Cochain R X 2) (hphi : coboundary R 2 phi = 0)
    (heval : phi c ≠ 0) :
    homologyClassOfTwoCycle R c hc ≠ 0 := by
  intro hzero
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 2
  have hc' : c ∈ LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc 2).g.hom) := by
    change ((X.chainComplex (ModuleCat.of R R)).d 2
      ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc
  let z : LinearMap.ker S.g.hom := ⟨c, hc'⟩
  have hmk : (Submodule.Quotient.mk z : S.moduleCatLeftHomologyData.H) = 0 := by
    have h := congrArg S.moduleCatHomologyIso.hom.hom hzero
    change S.moduleCatHomologyIso.hom.hom
        (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)) =
      S.moduleCatHomologyIso.hom.hom 0 at h
    rw [map_zero] at h
    have hi := S.moduleCatHomologyIso.toLinearEquiv.apply_symm_apply
      (show S.moduleCatLeftHomologyData.H from Submodule.Quotient.mk z)
    exact hi.symm.trans h
  have hzrange : z ∈ LinearMap.range S.moduleCatToCycles :=
    (Submodule.Quotient.mk_eq_zero _).mp hmk
  obtain ⟨b, hb⟩ := hzrange
  let hprev : (ComplexShape.down ℕ).prev 2 = 3 := ChainComplex.prev ℕ 2
  let b' : ChainGroup R X 3 := (K.XIsoOfEq hprev).hom.hom b
  have hb_under : S.f.hom b = c := congrArg Subtype.val hb
  have hd := ConcreteCategory.congr_hom
    (K.XIsoOfEq_hom_comp_d hprev 2) b
  have hb' : boundary R 2 b' = c := by
    change (K.d 3 2).hom b' = c
    change (K.d 3 2).hom ((K.XIsoOfEq hprev).hom.hom b) = c
    rw [show (K.d 3 2).hom ((K.XIsoOfEq hprev).hom.hom b) =
      (K.d ((ComplexShape.down ℕ).prev 2) 2).hom b from hd]
    change (K.d ((ComplexShape.down ℕ).prev 2) 2).hom b = c at hb_under
    exact hb_under
  have hv := LinearMap.congr_fun hphi b'
  rw [coboundary_apply, hb'] at hv
  exact heval (by simpa using hv)

/-- The homology class of the shuffle of two one-cycles. -/
noncomputable def degreeOneShuffleHomologyClass {X Y : SSet.{u}}
    (c : ChainGroup R X 1) (d : ChainGroup R Y 1)
    (hc : boundary R 0 c = 0) (hd : boundary R 0 d = 0) :
    ((X ⊗ Y).chainComplex (ModuleCat.of R R)).homology 2 :=
  homologyClassOfTwoCycle R (degreeOneShuffle R c d)
    (boundary_degreeOneShuffle_eq_zero R c d hc hd)

/-- If cocycles detect both factor cycles, their shuffle gives a nonzero two-dimensional
homology class in the product. -/
theorem degreeOneShuffleHomologyClass_ne_zero {X Y : SSet.{u}}
    (c : ChainGroup R X 1) (d : ChainGroup R Y 1)
    (hc : boundary R 0 c = 0) (hd : boundary R 0 d = 0)
    (phi : Cochain R X 1) (psi : Cochain R Y 1)
    (hphi : coboundary R 1 phi = 0) (hpsi : coboundary R 1 psi = 0)
    (hphi_eval : phi c ≠ 0) (hpsi_eval : psi d ≠ 0) :
    degreeOneShuffleHomologyClass R c d hc hd ≠ 0 := by
  apply homologyClassOfTwoCycle_ne_zero R
    (degreeOneShuffle R c d)
    (boundary_degreeOneShuffle_eq_zero R c d hc hd)
    (degreeOneExternalCochain R phi psi)
    (coboundary_degreeOneExternalCochain R phi psi hphi hpsi)
  rw [degreeOneExternalCochain_shuffle R phi psi hphi hpsi c d]
  exact mul_ne_zero hphi_eval hpsi_eval

/-- A nonzero degree-one cohomology functional admits an explicit cycle and cocycle whose
evaluation is nonzero.  This is the representative-level bridge needed by the shuffle
construction; it uses universal coefficients over a field. -/
theorem exists_oneCycle_oneCocycle_pairing_ne_zero {X : SSet.{u}}
    (alpha : Module.Dual R ((X.chainComplex (ModuleCat.of R R)).homology 1))
    (halpha : alpha ≠ 0) :
    ∃ (c : ChainGroup R X 1) (phi : Cochain R X 1),
      boundary R 0 c = 0 ∧ coboundary R 1 phi = 0 ∧ phi c ≠ 0 := by
  let K := X.chainComplex (ModuleCat.of R R)
  let S := K.sc 1
  let alpha' : Module.Dual R S.homology := alpha
  have halpha' : alpha' ≠ 0 := halpha
  obtain ⟨z, hz⟩ : ∃ z, alpha' z ≠ 0 := by
    by_contra hall
    push Not at hall
    apply halpha'
    ext z
    exact hall z
  obtain ⟨x, hx⟩ := S.moduleCatHomologyClass_surjective z
  obtain ⟨eta, heta⟩ := S.linearDual.moduleCatHomologyClass_surjective
    (S.linearDualHomologyEquiv.symm alpha')
  let phi : Cocycle R X 1 := cohomologyCycleToCocycle R 1 eta
  have hpair := S.linearDualHomologyEquiv_class_apply_class eta x
  rw [heta, S.linearDualHomologyEquiv.apply_symm_apply, hx] at hpair
  have hphi_eval : phi.1 x.1 ≠ 0 := by
    change (show Module.Dual R S.X₂ from eta.1) x.1 ≠ 0
    rw [← hpair]
    exact hz
  have hxcycle := x.2
  have hc : boundary R 0 x.1 = 0 := by
    change (K.d 1 0).hom x.1 = 0
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom x.1 = 0 at hxcycle
    rw [show (ComplexShape.down ℕ).next 1 = 0 from ChainComplex.next_nat_succ 0]
      at hxcycle
    exact hxcycle
  exact ⟨x.1, phi.1, hc, phi.2, hphi_eval⟩

end AlgebraicTopology.Simplicial

namespace AlgebraicTopology.Singular

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

variable (R : Type u) [Field R]

/-! ## Singular chains of a topological product -/

/-- Singular cohomology is invariant under an isomorphism of topological spaces. -/
noncomputable def cohomologyLinearEquivOfIso {X Y : TopCat.{u}} (e : X ≅ Y) (n : ℕ) :
    Cohomology R X n ≃ₗ[R] Cohomology R Y n :=
  LinearEquiv.ofLinearMap
    (cohomologyMap R n e.inv)
    (cohomologyMap R n e.hom)
    (by rw [← cohomologyMap_comp, e.inv_hom_id, cohomologyMap_id])
    (by rw [← cohomologyMap_comp, e.hom_inv_id, cohomologyMap_id])

/-- Singular homology is invariant under an isomorphism of topological spaces. -/
public noncomputable def homologyLinearEquivOfIso {X Y : TopCat.{u}} (e : X ≅ Y) (n : ℕ) :
    Homology R X n ≃ₗ[R] Homology R Y n :=
  LinearEquiv.ofLinearMap
    (homologyMap R n e.hom)
    (homologyMap R n e.inv)
    (by rw [← homologyMap_comp, e.inv_hom_id, homologyMap_id])
    (by rw [← homologyMap_comp, e.hom_inv_id, homologyMap_id])

/-- The cohomology and homology transports along a topological isomorphism preserve the
evaluation pairing. -/
@[simp]
public theorem cohomologyLinearEquivOfIso_apply_homologyLinearEquivOfIso
    {X Y : TopCat.{u}} (e : X ≅ Y) (n : ℕ)
    (alpha : Cohomology R X n) (z : Homology R X n) :
    cohomologyLinearEquivOfIso R e n alpha
        (homologyLinearEquivOfIso R e n z) = alpha z := by
  calc
    _ = alpha (homologyMap R n e.inv (homologyMap R n e.hom z)) := rfl
    _ = alpha (homologyMap R n (e.hom ≫ e.inv) z) := by
      rw [homologyMap_comp, LinearMap.comp_apply]
    _ = alpha z := by rw [e.hom_inv_id, homologyMap_id, LinearMap.id_apply]

/-- A nonzero singular degree-one cohomology class has explicit singular cycle and cocycle
representatives with nonzero evaluation. -/
theorem exists_singularOneCycle_oneCocycle_pairing_ne_zero {X : TopCat.{u}}
    (alpha : Cohomology R X 1) (halpha : alpha ≠ 0) :
    ∃ (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
        (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1),
      Simplicial.boundary R 0 c = 0 ∧
        Simplicial.coboundary R 1 phi = 0 ∧ phi c ≠ 0 :=
  Simplicial.exists_oneCycle_oneCocycle_pairing_ne_zero R alpha halpha

/-- Representative data for a nonzero degree-one cohomology class: a cocycle and a cycle on
which it evaluates nontrivially. -/
structure OneCycleCocyclePairing (X : TopCat.{u}) where
  chain : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1
  cochain : Simplicial.Cochain R (TopCat.toSSet.obj X) 1
  boundary_eq_zero : Simplicial.boundary R 0 chain = 0
  coboundary_eq_zero : Simplicial.coboundary R 1 cochain = 0
  pairing_ne_zero : cochain chain ≠ 0

/-- Representative data for a specified nonzero degree-one cohomology class.  In addition to
the detecting cycle, this records that the selected cocycle represents the supplied class under
the universal-coefficient equivalence. -/
public structure OneCycleCocycleRepresentativePairing (X : TopCat.{u})
    (alpha : Cohomology R X 1) extends OneCycleCocyclePairing R X where
  represents :
    let S := ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).sc 1
    S.linearDualHomologyEquiv
      (Simplicial.cochainClassOfOneCocycle R cochain coboundary_eq_zero) = alpha

/-- Chosen representative data detected by a given nonzero degree-one class. -/
noncomputable def oneCycleCocyclePairingOfNonzero {X : TopCat.{u}}
    (alpha : Cohomology R X 1) (halpha : alpha ≠ 0) :
    OneCycleCocyclePairing R X := by
  let hex :=
    exists_singularOneCycle_oneCocycle_pairing_ne_zero R alpha halpha
  let c := Classical.choose hex
  let hphiExists := Classical.choose_spec hex
  let phi := Classical.choose hphiExists
  let hspec := Classical.choose_spec hphiExists
  exact
    { chain := c
      cochain := phi
      boundary_eq_zero := hspec.1
      coboundary_eq_zero := hspec.2.1
      pairing_ne_zero := hspec.2.2 }

/-- A specified nonzero degree-one class has a detecting cocycle which represents that exact
class. -/
public theorem oneCycleCocycleRepresentativePairing_nonempty {X : TopCat.{u}}
    (alpha : Cohomology R X 1) (halpha : alpha ≠ 0) :
    Nonempty (OneCycleCocycleRepresentativePairing R X alpha) := by
  let K := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)
  let S := K.sc 1
  let alpha' : Module.Dual R S.homology := alpha
  have halpha' : alpha' ≠ 0 := halpha
  obtain ⟨z, hz⟩ : ∃ z, alpha' z ≠ 0 := by
    by_contra hall
    push Not at hall
    apply halpha'
    ext z
    exact hall z
  obtain ⟨x, hx⟩ := S.moduleCatHomologyClass_surjective z
  obtain ⟨eta, heta⟩ := S.linearDual.moduleCatHomologyClass_surjective
    (S.linearDualHomologyEquiv.symm alpha')
  let phi : Simplicial.Cocycle R (TopCat.toSSet.obj X) 1 :=
    Simplicial.cohomologyCycleToCocycle R 1 eta
  have hpair := S.linearDualHomologyEquiv_class_apply_class eta x
  rw [heta, S.linearDualHomologyEquiv.apply_symm_apply, hx] at hpair
  have hphi_eval : phi.1 x.1 ≠ 0 := by
    change (show Module.Dual R S.X₂ from eta.1) x.1 ≠ 0
    rw [← hpair]
    exact hz
  have hxcycle := x.2
  have hc : Simplicial.boundary R 0 x.1 = 0 := by
    change (K.d 1 0).hom x.1 = 0
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom x.1 = 0 at hxcycle
    rw [show (ComplexShape.down ℕ).next 1 = 0 from ChainComplex.next_nat_succ 0]
      at hxcycle
    exact hxcycle
  refine ⟨
    { chain := x.1
      cochain := phi.1
      boundary_eq_zero := hc
      coboundary_eq_zero := phi.2
      pairing_ne_zero := hphi_eval
      represents := ?_ }⟩
  change S.linearDualHomologyEquiv
      (Simplicial.cochainClassOfOneCocycle R phi.1 phi.2) = alpha'
  rw [Simplicial.cochainClassOfOneCocycle_cohomologyCycleToCocycle,
    heta, S.linearDualHomologyEquiv.apply_symm_apply]

/-- Chosen detecting representative of a specified nonzero degree-one class. -/
public noncomputable def oneCycleCocycleRepresentativePairingOfNonzero {X : TopCat.{u}}
    (alpha : Cohomology R X 1) (halpha : alpha ≠ 0) :
    OneCycleCocycleRepresentativePairing R X alpha :=
  Classical.choice (oneCycleCocycleRepresentativePairing_nonempty R alpha halpha)

/-- The singular-set functor preserves the cartesian product.  This packages the canonical
comparison in the direction convenient for the shuffle construction. -/
noncomputable def singularProductComparison (X Y : TopCat.{u}) :
    TopCat.toSSet.obj (X ⊗ Y) ≅
      (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) :=
  CartesianMonoidalCategory.prodComparisonIso TopCat.toSSet X Y

/-- The shuffle product of two singular one-chains, transported to the singular chains of
the topological product. -/
noncomputable def degreeOneShuffleChain {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1) :
    Simplicial.ChainGroup R (TopCat.toSSet.obj (X ⊗ Y)) 2 :=
  ((SSet.chainComplexMap (singularProductComparison X Y).inv
    (ModuleCat.of R R)).f 2).hom (Simplicial.degreeOneShuffle R c d)

/-- The topological shuffle of two singular one-cycles is a singular two-cycle. -/
theorem boundary_degreeOneShuffleChain_eq_zero {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1)
    (hc : Simplicial.boundary R 0 c = 0)
    (hd : Simplicial.boundary R 0 d = 0) :
    Simplicial.boundary R 1 (degreeOneShuffleChain R c d) = 0 := by
  let e := singularProductComparison X Y
  let F := SSet.chainComplexMap e.inv (ModuleCat.of R R)
  have hz := Simplicial.boundary_degreeOneShuffle_eq_zero R c d hc hd
  have hcomm := ConcreteCategory.congr_hom (F.comm 2 1)
    (Simplicial.degreeOneShuffle R c d)
  change (((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
      (ModuleCat.of R R)).d 2 1).hom
        ((F.f 2).hom (Simplicial.degreeOneShuffle R c d)) = 0
  have hcomm' :
      (((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
          (ModuleCat.of R R)).d 2 1).hom
          ((F.f 2).hom (Simplicial.degreeOneShuffle R c d)) =
        (F.f 1).hom (Simplicial.boundary R 1
          (Simplicial.degreeOneShuffle R c d)) := by
    simpa only [ConcreteCategory.comp_apply, Simplicial.boundary] using hcomm
  rw [hcomm', hz, map_zero]

/-- The external cochain on the singular set of a topological product. -/
noncomputable def degreeOneExternalCochain {X Y : TopCat.{u}}
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1) :
    Simplicial.Cochain R (TopCat.toSSet.obj (X ⊗ Y)) 2 :=
  Simplicial.cochainMap R (singularProductComparison X Y).hom 2
    (Simplicial.degreeOneExternalCochain R phi psi)

/-- Evaluation of the external singular cochain on the transported shuffle chain. -/
theorem degreeOneExternalCochain_shuffleChain {X Y : TopCat.{u}}
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1) :
    degreeOneExternalCochain R phi psi (degreeOneShuffleChain R c d) =
      phi c * psi d := by
  rw [degreeOneExternalCochain, Simplicial.cochainMap_apply, degreeOneShuffleChain]
  have hi :
      ((SSet.chainComplexMap (singularProductComparison X Y).hom
          (ModuleCat.of R R)).f 2).hom
          (((SSet.chainComplexMap (singularProductComparison X Y).inv
              (ModuleCat.of R R)).f 2).hom
            (Simplicial.degreeOneShuffle R c d)) =
        Simplicial.degreeOneShuffle R c d := by
    let G := (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
    have hmaps : G.map (singularProductComparison X Y).inv ≫
        G.map (singularProductComparison X Y).hom = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id]
      exact G.map_id _
    have hcomponent := congrArg (fun f => f.f 2) hmaps
    have happ := ConcreteCategory.congr_hom hcomponent
      (Simplicial.degreeOneShuffle R c d)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      ConcreteCategory.comp_apply, ModuleCat.hom_comp, ModuleCat.hom_id,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] using happ
  rw [hi]
  exact Simplicial.degreeOneExternalCochain_shuffle R phi psi hphi hpsi c d

/-- The external product of two singular one-cocycles is a singular two-cocycle on the
topological product. -/
theorem coboundary_degreeOneExternalCochain {X Y : TopCat.{u}}
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0) :
    Simplicial.coboundary R 2 (degreeOneExternalCochain R phi psi) = 0 := by
  rw [degreeOneExternalCochain, Simplicial.coboundary_cochainMap,
    Simplicial.coboundary_degreeOneExternalCochain R phi psi hphi hpsi,
    map_zero]

/-- The singular cohomology class represented by the external product of two degree-one
cocycles. -/
noncomputable def degreeOneExternalCohomologyClass {X Y : TopCat.{u}}
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0) :
    Cohomology R (X ⊗ Y) 2 := by
  let S := ((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
    (ModuleCat.of R R)).sc 2
  exact S.linearDualHomologyEquiv
    (Simplicial.cochainClassOfTwoCocycle R
      (degreeOneExternalCochain R phi psi)
      (coboundary_degreeOneExternalCochain R phi psi hphi hpsi))

/-- The singular homology class of the topological shuffle cycle. -/
noncomputable def degreeOneShuffleHomologyClass {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1)
    (hc : Simplicial.boundary R 0 c = 0)
    (hd : Simplicial.boundary R 0 d = 0) :
    Homology R (X ⊗ Y) 2 :=
  Simplicial.homologyClassOfTwoCycle R (degreeOneShuffleChain R c d)
    (boundary_degreeOneShuffleChain_eq_zero R c d hc hd)

/-- The external cohomology class evaluates on the shuffle homology class as the product
of the two original pairings. -/
theorem degreeOneExternalCohomologyClass_shuffleHomologyClass {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1)
    (hc : Simplicial.boundary R 0 c = 0)
    (hd : Simplicial.boundary R 0 d = 0)
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0) :
    degreeOneExternalCohomologyClass R phi psi hphi hpsi
        (degreeOneShuffleHomologyClass R c d hc hd) =
      phi c * psi d := by
  unfold degreeOneExternalCohomologyClass degreeOneShuffleHomologyClass
  exact (Simplicial.cochainClassOfTwoCocycle_pair R
    (degreeOneExternalCochain R phi psi)
    (coboundary_degreeOneExternalCochain R phi psi hphi hpsi)
    (degreeOneShuffleChain R c d)
    (boundary_degreeOneShuffleChain_eq_zero R c d hc hd)).trans
      (degreeOneExternalCochain_shuffleChain R phi psi hphi hpsi c d)

/-- If both factor cocycles detect their cycles, their external product is a nonzero
singular cohomology class on the topological product. -/
theorem degreeOneExternalCohomologyClass_ne_zero {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1)
    (hc : Simplicial.boundary R 0 c = 0)
    (hd : Simplicial.boundary R 0 d = 0)
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0)
    (hphi_eval : phi c ≠ 0) (hpsi_eval : psi d ≠ 0) :
    degreeOneExternalCohomologyClass R phi psi hphi hpsi ≠ 0 := by
  intro hzero
  have heval := congrArg
    (fun alpha => alpha (degreeOneShuffleHomologyClass R c d hc hd)) hzero
  rw [degreeOneExternalCohomologyClass_shuffleHomologyClass R c d hc hd
    phi psi hphi hpsi, LinearMap.zero_apply] at heval
  exact mul_ne_zero hphi_eval hpsi_eval heval

/-- If singular cocycles detect both factor cycles, their shuffle is nonzero in the singular
homology of the topological product. -/
theorem degreeOneShuffleHomologyClass_ne_zero {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1)
    (hc : Simplicial.boundary R 0 c = 0)
    (hd : Simplicial.boundary R 0 d = 0)
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0)
    (hphi_eval : phi c ≠ 0) (hpsi_eval : psi d ≠ 0) :
    degreeOneShuffleHomologyClass R c d hc hd ≠ 0 := by
  apply Simplicial.homologyClassOfTwoCycle_ne_zero R
    (degreeOneShuffleChain R c d)
    (boundary_degreeOneShuffleChain_eq_zero R c d hc hd)
    (degreeOneExternalCochain R phi psi)
    (coboundary_degreeOneExternalCochain R phi psi hphi hpsi)
  rw [degreeOneExternalCochain_shuffleChain R phi psi hphi hpsi c d]
  exact mul_ne_zero hphi_eval hpsi_eval

/-- Two nonzero degree-one singular cohomology classes produce a nonzero external-product
class in degree two. -/
theorem exists_degreeOneExternalCohomologyClass_ne_zero {X Y : TopCat.{u}}
    (alpha : Cohomology R X 1) (beta : Cohomology R Y 1)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    ∃ gamma : Cohomology R (X ⊗ Y) 2, gamma ≠ 0 := by
  obtain ⟨c, phi, hc, hphi, hphi_eval⟩ :=
    exists_singularOneCycle_oneCocycle_pairing_ne_zero R alpha halpha
  obtain ⟨d, psi, hd, hpsi, hpsi_eval⟩ :=
    exists_singularOneCycle_oneCocycle_pairing_ne_zero R beta hbeta
  exact ⟨degreeOneExternalCohomologyClass R phi psi hphi hpsi,
    degreeOneExternalCohomologyClass_ne_zero R c d hc hd phi psi
      hphi hpsi hphi_eval hpsi_eval⟩

/-- A chosen external-product class associated to two nonzero degree-one classes. -/
noncomputable def degreeOneExternalCohomologyClassOfNonzero {X Y : TopCat.{u}}
    (alpha : Cohomology R X 1) (beta : Cohomology R Y 1)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    Cohomology R (X ⊗ Y) 2 :=
  let a := oneCycleCocycleRepresentativePairingOfNonzero R alpha halpha
  let b := oneCycleCocycleRepresentativePairingOfNonzero R beta hbeta
  degreeOneExternalCohomologyClass R a.cochain b.cochain
    a.coboundary_eq_zero b.coboundary_eq_zero

theorem degreeOneExternalCohomologyClassOfNonzero_ne_zero {X Y : TopCat.{u}}
    (alpha : Cohomology R X 1) (beta : Cohomology R Y 1)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    degreeOneExternalCohomologyClassOfNonzero R alpha beta halpha hbeta ≠ 0 := by
  let a := oneCycleCocycleRepresentativePairingOfNonzero R alpha halpha
  let b := oneCycleCocycleRepresentativePairingOfNonzero R beta hbeta
  exact degreeOneExternalCohomologyClass_ne_zero R
    a.chain b.chain a.boundary_eq_zero b.boundary_eq_zero
    a.cochain b.cochain a.coboundary_eq_zero b.coboundary_eq_zero
    a.pairing_ne_zero b.pairing_ne_zero

end AlgebraicTopology.Singular
