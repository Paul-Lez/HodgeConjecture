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

public import Other.AlgebraicTopology.SingularCoverSmall
public import Mathlib.Algebra.Category.ModuleCat.Colimits

import Other.AlgebraicTopology.SingularExcisionOpenCover

/-!
# Small singular chains with coefficients in a commutative ring

This file transports the integral subdivision homotopy to simplicial chains with coefficients
in an arbitrary commutative ring `R` (in particular `R = ℤ` and `R = ℚ`).  The transport is
constructed directly from the universal bases of the two simplicial chain complexes.  In
particular, it does not assume a universal-coefficient theorem, and it uses no property of
`R` beyond the ring structure: `R` enters only through the coefficient map `ℤ → R`, the
`R`-module `R`, and the forgetful functor `ModuleCat R ⥤ AddCommGrpCat`.

The rational specialisation, with its original names, lives in
`Other.AlgebraicTopology.SingularExcisionField`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

variable (R : Type) [CommRing R]

/-- Chains on a simplicial set with coefficients in the ring `R`. -/
abbrev ScalarSimplicialChainComplex (X : SSet.{0}) :
    ChainComplex (ModuleCat R) ℕ :=
  X.chainComplex (ModuleCat.of R R)

/-- The underlying additive group of an `R`-module. -/
abbrev scalarForget := forget₂ (ModuleCat R) AddCommGrpCat

@[simp]
lemma moduleCat_toSpanSingleton_hom_apply_one (M : ModuleCat R) (v : M) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R M v)).hom 1 = v := by
  change (1 : R) • v = v
  simp

/-- The coefficient map from integral to `R`-chains in one degree. -/
def integralToScalarChainComponent (X : SSet.{0}) (n : ℕ) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (scalarForget R).obj ((ScalarSimplicialChainComplex R X).X n) :=
  (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).desc
    (Cofan.mk _ fun x ↦
      AddCommGrpCat.ofHom (Int.castAddHom R) ≫
        (scalarForget R).map (X.ιChainComplex (R := ModuleCat.of R R) x))

@[reassoc]
lemma iota_integralToScalarChainComponent (X : SSet.{0}) (n : ℕ)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x ≫
        integralToScalarChainComponent R X n =
      AddCommGrpCat.ofHom (Int.castAddHom R) ≫
        (scalarForget R).map (X.ιChainComplex (R := ModuleCat.of R R) x) :=
  (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).fac _ (Discrete.mk x)

/-- The coefficient map sends the integral basis element of a simplex to the `R`-basis
element of the same simplex.  (For a general ring this needs `Int.cast_one`; it is not a
definitional unfolding.) -/
lemma integralToScalarChainComponent_iota_one (X : SSet.{0}) (n : ℕ) (x : X _⦋n⦌) :
    (integralToScalarChainComponent R X n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1) =
      (X.ιChainComplex (R := ModuleCat.of R R) x).hom 1 := by
  have hx := ConcreteCategory.congr_hom (iota_integralToScalarChainComponent R X n x) 1
  simp only [ConcreteCategory.comp_apply] at hx
  rw [hx]
  change ((scalarForget R).map (X.ιChainComplex (R := ModuleCat.of R R) x)).hom
    ((1 : ℤ) : R) = _
  rw [Int.cast_one]
  rfl

/-- Extend an integral map between free simplicial-chain groups `R`-linearly. -/
def scalarizeSimplicialChainComponent (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    (ScalarSimplicialChainComplex R X).X n ⟶
      (ScalarSimplicialChainComplex R Y).X m :=
  (X.isColimitChainComplexXCofan (ModuleCat.of R R) n).desc
    (Cofan.mk _ fun x ↦ ModuleCat.ofHom <|
      LinearMap.toSpanSingleton R _ <|
        (show (ScalarSimplicialChainComplex R Y).X m from
          (integralToScalarChainComponent R Y m).hom
            (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1))))

@[reassoc]
lemma iota_scalarizeSimplicialChainComponent
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := ModuleCat.of R R) x ≫
        scalarizeSimplicialChainComponent R X Y n m f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ <|
        (show (ScalarSimplicialChainComplex R Y).X m from
          (integralToScalarChainComponent R Y m).hom
            (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)))) :=
  (X.isColimitChainComplexXCofan (ModuleCat.of R R) n).fac _ (Discrete.mk x)

lemma integralToScalarChainComponent_naturality
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    integralToScalarChainComponent R X n ≫
        (scalarForget R).map (scalarizeSimplicialChainComponent R X Y n m f) =
      f ≫ integralToScalarChainComponent R Y m := by
  refine (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).hom_ext fun x ↦ ?_
  change X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (integralToScalarChainComponent R X n ≫
        (scalarForget R).map (scalarizeSimplicialChainComponent R X Y n m f)) =
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (f ≫ integralToScalarChainComponent R Y m)
  apply AddCommGrpCat.int_hom_ext
  have hf := ConcreteCategory.congr_hom
    (iota_scalarizeSimplicialChainComponent R X Y n m f x.as) 1
  change (scalarizeSimplicialChainComponent R X Y n m f).hom
      ((integralToScalarChainComponent R X n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as).hom 1)) = _
  rw [integralToScalarChainComponent_iota_one]
  simp only [ConcreteCategory.comp_apply] at hf ⊢
  simpa using hf

lemma scalarizeSimplicialChainComponent_comp
    (X Y Z : SSet.{0}) (n m k : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (g : (Y.chainComplex (AddCommGrpCat.of ℤ)).X m ⟶
      (Z.chainComplex (AddCommGrpCat.of ℤ)).X k) :
    scalarizeSimplicialChainComponent R X Z n k (f ≫ g) =
      scalarizeSimplicialChainComponent R X Y n m f ≫
        scalarizeSimplicialChainComponent R Y Z m k g := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_scalarizeSimplicialChainComponent,
    iota_scalarizeSimplicialChainComponent_assoc]
  ext
  have h := ConcreteCategory.congr_hom
    (integralToScalarChainComponent_naturality R Y Z m k g)
    (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1))
  simp only [ConcreteCategory.comp_apply] at h ⊢
  simpa using h.symm

lemma scalarizeSimplicialChainComponent_id (X : SSet.{0}) (n : ℕ) :
    scalarizeSimplicialChainComponent R X X n n (𝟙 _) = 𝟙 _ := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_scalarizeSimplicialChainComponent]
  ext
  simp only [Category.comp_id,
    ConcreteCategory.id_apply]
  have hx := ConcreteCategory.congr_hom
    (iota_integralToScalarChainComponent R X n x) 1
  simp only [ConcreteCategory.comp_apply] at hx
  simpa using hx

lemma scalarizeSimplicialChainComponent_zero
    (X Y : SSet.{0}) (n m : ℕ) :
    scalarizeSimplicialChainComponent R X Y n m 0 = 0 := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_scalarizeSimplicialChainComponent]
  ext
  simp

lemma scalarizeSimplicialChainComponent_add
    (X Y : SSet.{0}) (n m : ℕ)
    (f g : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    scalarizeSimplicialChainComponent R X Y n m (f + g) =
      scalarizeSimplicialChainComponent R X Y n m f +
        scalarizeSimplicialChainComponent R X Y n m g := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_scalarizeSimplicialChainComponent, Preadditive.comp_add,
    iota_scalarizeSimplicialChainComponent,
    iota_scalarizeSimplicialChainComponent]
  ext
  simp

lemma scalarizeSimplicialChainComponent_neg
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    scalarizeSimplicialChainComponent R X Y n m (-f) =
      -scalarizeSimplicialChainComponent R X Y n m f := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_scalarizeSimplicialChainComponent, Preadditive.comp_neg,
    iota_scalarizeSimplicialChainComponent]
  ext
  simp

/-- The integral-to-`R` coefficient map commutes with the simplicial differential. -/
lemma integralToScalarChainComponent_comm_d (X : SSet.{0}) (n : ℕ) :
    integralToScalarChainComponent R X (n + 1) ≫
        (scalarForget R).map ((ScalarSimplicialChainComplex R X).d (n + 1) n) =
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        integralToScalarChainComponent R X n := by
  refine (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) (n + 1)).hom_ext fun x ↦ ?_
  change X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (integralToScalarChainComponent R X (n + 1) ≫
        (scalarForget R).map ((ScalarSimplicialChainComplex R X).d (n + 1) n)) =
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      ((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        integralToScalarChainComponent R X n)
  rw [← Category.assoc, iota_integralToScalarChainComponent, Category.assoc,
    ← Functor.map_comp, SSet.ιChainComplex_d, ← Category.assoc, SSet.ιChainComplex_d,
    Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, iota_integralToScalarChainComponent]
  simp only [Functor.map_sum, Functor.map_zsmul]
  rw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul]

/-- Scalar extension sends the integral simplicial differential to the `R`-differential. -/
lemma scalarizeSimplicialChainComponent_d (X : SSet.{0}) (n : ℕ) :
    scalarizeSimplicialChainComponent R X X (n + 1) n
        ((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n) =
      (ScalarSimplicialChainComplex R X).d (n + 1) n := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_scalarizeSimplicialChainComponent]
  ext
  change (LinearMap.toSpanSingleton R _ _) 1 = _
  rw [LinearMap.toSpanSingleton_apply_one]
  simp only [ConcreteCategory.comp_apply]
  change (integralToScalarChainComponent R X n).hom
      (((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)) =
    ((ScalarSimplicialChainComplex R X).d (n + 1) n).hom
      ((X.ιChainComplex (R := ModuleCat.of R R) x).hom 1)
  have h := ConcreteCategory.congr_hom
    (integralToScalarChainComponent_comm_d R X n)
    ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)
  simp only [ConcreteCategory.comp_apply] at h ⊢
  rw [integralToScalarChainComponent_iota_one] at h
  exact h.symm

/-- Scalar extension of a chain map between integral simplicial chains. -/
def scalarizeSimplicialChainMap (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    ScalarSimplicialChainComplex R X ⟶ ScalarSimplicialChainComplex R Y where
  f n := scalarizeSimplicialChainComponent R X Y n n (f.f n)
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst i
    rw [← scalarizeSimplicialChainComponent_d R Y j,
      ← scalarizeSimplicialChainComponent_comp, f.comm,
      scalarizeSimplicialChainComponent_comp,
      scalarizeSimplicialChainComponent_d]

@[simp]
lemma scalarizeSimplicialChainMap_f (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) (n : ℕ) :
    (scalarizeSimplicialChainMap R X Y f).f n =
      scalarizeSimplicialChainComponent R X Y n n (f.f n) :=
  rfl

lemma scalarizeSimplicialChainMap_id (X : SSet.{0}) :
    scalarizeSimplicialChainMap R X X (𝟙 _) = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun n ↦ scalarizeSimplicialChainComponent_id R X n

lemma scalarizeSimplicialChainMap_comp (X Y Z : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ))
    (g : Y.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Z.chainComplex (AddCommGrpCat.of ℤ)) :
    scalarizeSimplicialChainMap R X Z (f ≫ g) =
      scalarizeSimplicialChainMap R X Y f ≫
        scalarizeSimplicialChainMap R Y Z g :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    scalarizeSimplicialChainComponent_comp R X Y Z n n n (f.f n) (g.f n)

lemma scalarizeSimplicialChainMap_add (X Y : SSet.{0})
    (f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    scalarizeSimplicialChainMap R X Y (f + g) =
      scalarizeSimplicialChainMap R X Y f +
        scalarizeSimplicialChainMap R X Y g :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    scalarizeSimplicialChainComponent_add R X Y n n (f.f n) (g.f n)

lemma scalarizeSimplicialChainMap_neg (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    scalarizeSimplicialChainMap R X Y (-f) =
      -scalarizeSimplicialChainMap R X Y f :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    scalarizeSimplicialChainComponent_neg R X Y n n (f.f n)

lemma scalarizeSimplicialChainMap_sub (X Y : SSet.{0})
    (f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    scalarizeSimplicialChainMap R X Y (f - g) =
      scalarizeSimplicialChainMap R X Y f -
        scalarizeSimplicialChainMap R X Y g := by
  rw [sub_eq_add_neg, scalarizeSimplicialChainMap_add, scalarizeSimplicialChainMap_neg,
    sub_eq_add_neg]

lemma scalarizeSimplicialChainMap_zero (X Y : SSet.{0}) :
    scalarizeSimplicialChainMap R X Y 0 = 0 :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    scalarizeSimplicialChainComponent_zero R X Y n n

/-- Scalar extension preserves a chain homotopy between integral simplicial chain maps. -/
def scalarizeSimplicialChainHomotopy (X Y : SSet.{0})
    {f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)} (h : Homotopy f g) :
    Homotopy (scalarizeSimplicialChainMap R X Y f)
      (scalarizeSimplicialChainMap R X Y g) where
  hom i j := scalarizeSimplicialChainComponent R X Y i j (h.hom i j)
  zero i j hij := by
    rw [h.zero i j hij, scalarizeSimplicialChainComponent_zero]
  comm i := by
    cases i with
    | zero =>
        have hh := congrArg
          (scalarizeSimplicialChainComponent R X Y 0 0) (h.comm 0)
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex] at hh ⊢
        simp only [scalarizeSimplicialChainComponent_add,
          scalarizeSimplicialChainComponent_comp,
          scalarizeSimplicialChainComponent_d, zero_add] at hh
        change scalarizeSimplicialChainComponent R X Y 0 0 (f.f 0) =
          0 + scalarizeSimplicialChainComponent R X Y 0 1 (h.hom 0 1) ≫
            (ScalarSimplicialChainComplex R Y).d 1 0 +
              scalarizeSimplicialChainComponent R X Y 0 0 (g.f 0)
        simpa only [zero_add] using hh
    | succ n =>
        have hh := congrArg
          (scalarizeSimplicialChainComponent R X Y (n + 1) (n + 1))
            (h.comm (n + 1))
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex] at hh ⊢
        simp only [scalarizeSimplicialChainComponent_add,
          scalarizeSimplicialChainComponent_comp,
          scalarizeSimplicialChainComponent_d] at hh
        exact hh

/-- Scalar extension preserves a chain-homotopy equivalence of simplicial chain complexes. -/
def scalarizeSimplicialChainHomotopyEquiv (X Y : SSet.{0})
    (e : HomotopyEquiv (X.chainComplex (AddCommGrpCat.of ℤ))
      (Y.chainComplex (AddCommGrpCat.of ℤ))) :
    HomotopyEquiv (ScalarSimplicialChainComplex R X)
      (ScalarSimplicialChainComplex R Y) where
  hom := scalarizeSimplicialChainMap R X Y e.hom
  inv := scalarizeSimplicialChainMap R Y X e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (scalarizeSimplicialChainMap_comp R X Y X e.hom e.inv).symm).trans
      ((scalarizeSimplicialChainHomotopy R X X e.homotopyHomInvId).trans
        (Homotopy.ofEq (scalarizeSimplicialChainMap_id R X)))
  homotopyInvHomId :=
    (Homotopy.ofEq (scalarizeSimplicialChainMap_comp R Y X Y e.inv e.hom).symm).trans
      ((scalarizeSimplicialChainHomotopy R Y Y e.homotopyInvHomId).trans
        (Homotopy.ofEq (scalarizeSimplicialChainMap_id R Y)))

/-- Scalar extension of an integral chain map induced by a simplicial map is the
corresponding `R`-chain map. -/
lemma scalarizeSimplicialChainComponent_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ) :
    scalarizeSimplicialChainComponent R X Y n n
        ((SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n) =
      (SSet.chainComplexMap f (ModuleCat.of R R)).f n := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_scalarizeSimplicialChainComponent,
    SSet.ι_chainComplexMap_f]
  ext
  change (LinearMap.toSpanSingleton R _ _) 1 = _
  rw [LinearMap.toSpanSingleton_apply_one]
  change (integralToScalarChainComponent R Y n).hom
      (((SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)) =
    (Y.ιChainComplex (R := ModuleCat.of R R) (f.app _ x)).hom 1
  have hf := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f X Y f (AddCommGrpCat.of ℤ) x) 1
  simp only [ConcreteCategory.comp_apply] at hf
  rw [hf]
  exact integralToScalarChainComponent_iota_one R Y n (f.app _ x)

lemma scalarizeSimplicialChainMap_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    scalarizeSimplicialChainMap R X Y
        (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)) =
      SSet.chainComplexMap f (ModuleCat.of R R) :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    scalarizeSimplicialChainComponent_chainComplexMap R f n

section ScalarSmallChains

variable {ι : Type} (X : TopCat.{0}) (U : ι → Set X)

/-- `R`-chains generated by singular simplices subordinate to one member of a cover. -/
abbrev CoverSmallScalarSingularChainComplex :
    ChainComplex (ModuleCat R) ℕ :=
  (coverSmallSingularSubcomplex X U : SSet).chainComplex (ModuleCat.of R R)

/-- Inclusion of cover-small `R`-singular chains into all `R`-singular chains. -/
def coverSmallScalarSingularChainInclusion :
    CoverSmallScalarSingularChainComplex R X U ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R) :=
  SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (ModuleCat.of R R)

instance coverSmallScalarSingularChainInclusion_mono :
    Mono (coverSmallScalarSingularChainInclusion R X U) := by
  dsimp [coverSmallScalarSingularChainInclusion, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

/-- The proven integral subdivision-and-prism homotopy transports to `R`-coefficients:
the all-open-cover small-chain theorem with coefficients in `R`. -/
theorem coverSmallScalarChainApproximation_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat R) (ComplexShape.down ℕ)
      (coverSmallScalarSingularChainInclusion R X U) := by
  let eZ := coverSmallChainHomotopyEquiv_of_openCover X U hUopen hUcover
  refine ⟨scalarizeSimplicialChainHomotopyEquiv R
    (coverSmallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X) eZ, ?_⟩
  change scalarizeSimplicialChainMap R
      (coverSmallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X) eZ.hom =
    coverSmallScalarSingularChainInclusion R X U
  rw [show eZ.hom = coverSmallIntegralSingularChainInclusion X U from
    coverSmallChainHomotopyEquiv_of_openCover_hom X U hUopen hUcover]
  exact scalarizeSimplicialChainMap_chainComplexMap R
    (coverSmallSingularSubcomplex X U).ι

/-- A selected `R`-coefficient small-chain homotopy equivalence for an open cover. -/
def coverSmallScalarChainHomotopyEquiv_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv (CoverSmallScalarSingularChainComplex R X U)
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)) :=
  (coverSmallScalarChainApproximation_of_openCover R X U hUopen hUcover).choose

lemma coverSmallScalarChainHomotopyEquiv_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coverSmallScalarChainHomotopyEquiv_of_openCover R X U hUopen hUcover).hom =
      coverSmallScalarSingularChainInclusion R X U :=
  (coverSmallScalarChainApproximation_of_openCover R X U hUopen hUcover).choose_spec

/-- The `R`-coefficient small-chain inclusion induces an isomorphism on homology in every
degree. -/
def coverSmallScalarSingularHomologyIso_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (CoverSmallScalarSingularChainComplex R X U).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).homology n :=
  (coverSmallScalarChainHomotopyEquiv_of_openCover R X U hUopen hUcover).toHomologyIso n

lemma coverSmallScalarSingularHomologyIso_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (coverSmallScalarSingularHomologyIso_of_openCover R X U hUopen hUcover n).hom =
      HomologicalComplex.homologyMap
        (coverSmallScalarSingularChainInclusion R X U) n := by
  dsimp [coverSmallScalarSingularHomologyIso_of_openCover]
  change HomologicalComplex.homologyMap
      (coverSmallScalarChainHomotopyEquiv_of_openCover R X U hUopen hUcover).hom n = _
  rw [coverSmallScalarChainHomotopyEquiv_of_openCover_hom]

end ScalarSmallChains

end AlgebraicTopology.Singular
