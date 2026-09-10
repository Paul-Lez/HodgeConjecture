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
public import Mathlib.Data.Complex.Basic

import Other.AlgebraicTopology.SingularExcisionOpenCover

/-!
# Small singular chains with complex coefficients

This file transports the integral subdivision homotopy to complex simplicial chains.  The
transport is constructed directly from the universal bases of the two simplicial chain
complexes.  In particular, it does not assume a universal-coefficient theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- Complex chains on a simplicial set. -/
abbrev ComplexSimplicialChainComplex (X : SSet.{0}) :
    ChainComplex (ModuleCat ℂ) ℕ :=
  X.chainComplex (ModuleCat.of ℂ ℂ)

/-- The underlying additive group of a complex module. -/
abbrev complexForget := forget₂ (ModuleCat ℂ) AddCommGrpCat

@[simp]
lemma complexModuleCat_toSpanSingleton_apply_one (M : ModuleCat ℂ) (v : M) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℂ M v)).hom 1 = v := by
  change (1 : ℂ) • v = v
  simp

/-- The coefficient map from integral to complex chains in one degree. -/
def integralToComplexChainComponent (X : SSet.{0}) (n : ℕ) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      complexForget.obj ((ComplexSimplicialChainComplex X).X n) :=
  (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).desc
    (Cofan.mk _ fun x ↦
      AddCommGrpCat.ofHom (Int.castAddHom ℂ) ≫
        complexForget.map (X.ιChainComplex (R := ModuleCat.of ℂ ℂ) x))

@[reassoc]
lemma iota_integralToComplexChainComponent (X : SSet.{0}) (n : ℕ)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x ≫
        integralToComplexChainComponent X n =
      AddCommGrpCat.ofHom (Int.castAddHom ℂ) ≫
        complexForget.map (X.ιChainComplex (R := ModuleCat.of ℂ ℂ) x) :=
  (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).fac _ (Discrete.mk x)

/-- Extend an integral map between free simplicial-chain groups complex-linearly. -/
def complexizeSimplicialChainComponent (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    (ComplexSimplicialChainComplex X).X n ⟶
      (ComplexSimplicialChainComplex Y).X m :=
  (X.isColimitChainComplexXCofan (ModuleCat.of ℂ ℂ) n).desc
    (Cofan.mk _ fun x ↦ ModuleCat.ofHom <|
      LinearMap.toSpanSingleton ℂ _ <|
        (show (ComplexSimplicialChainComplex Y).X m from
          (integralToComplexChainComponent Y m).hom
            (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1))))

@[reassoc]
lemma iota_complexizeSimplicialChainComponent
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := ModuleCat.of ℂ ℂ) x ≫
        complexizeSimplicialChainComponent X Y n m f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℂ _ <|
        (show (ComplexSimplicialChainComplex Y).X m from
          (integralToComplexChainComponent Y m).hom
            (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)))) :=
  (X.isColimitChainComplexXCofan (ModuleCat.of ℂ ℂ) n).fac _ (Discrete.mk x)

lemma integralToComplexChainComponent_naturality
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    integralToComplexChainComponent X n ≫
        complexForget.map (complexizeSimplicialChainComponent X Y n m f) =
      f ≫ integralToComplexChainComponent Y m := by
  refine (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).hom_ext fun x ↦ ?_
  change X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (integralToComplexChainComponent X n ≫
        complexForget.map (complexizeSimplicialChainComponent X Y n m f)) =
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (f ≫ integralToComplexChainComponent Y m)
  apply AddCommGrpCat.int_hom_ext
  have hx := ConcreteCategory.congr_hom
    (iota_integralToComplexChainComponent X n x.as) 1
  have hf := ConcreteCategory.congr_hom
    (iota_complexizeSimplicialChainComponent X Y n m f x.as) 1
  change (complexizeSimplicialChainComponent X Y n m f).hom
      ((integralToComplexChainComponent X n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as).hom 1)) = _
  have hx' : (integralToComplexChainComponent X n).hom
      ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as).hom 1) =
    (X.ιChainComplex (R := ModuleCat.of ℂ ℂ) x.as).hom 1 := by
    simpa [complexForget] using hx
  rw [hx']
  simp only [ConcreteCategory.comp_apply] at hf ⊢
  simpa using hf

lemma complexizeSimplicialChainComponent_comp
    (X Y Z : SSet.{0}) (n m k : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (g : (Y.chainComplex (AddCommGrpCat.of ℤ)).X m ⟶
      (Z.chainComplex (AddCommGrpCat.of ℤ)).X k) :
    complexizeSimplicialChainComponent X Z n k (f ≫ g) =
      complexizeSimplicialChainComponent X Y n m f ≫
        complexizeSimplicialChainComponent Y Z m k g := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_complexizeSimplicialChainComponent,
    iota_complexizeSimplicialChainComponent_assoc]
  ext
  have h := ConcreteCategory.congr_hom
    (integralToComplexChainComponent_naturality Y Z m k g)
    (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1))
  simp only [ConcreteCategory.comp_apply] at h ⊢
  simpa using h.symm

lemma complexizeSimplicialChainComponent_id (X : SSet.{0}) (n : ℕ) :
    complexizeSimplicialChainComponent X X n n (𝟙 _) = 𝟙 _ := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_complexizeSimplicialChainComponent]
  ext
  simp only [Category.comp_id,
    ConcreteCategory.id_apply]
  have hx := ConcreteCategory.congr_hom
    (iota_integralToComplexChainComponent X n x) 1
  simp only [ConcreteCategory.comp_apply] at hx
  simpa using hx

lemma complexizeSimplicialChainComponent_zero
    (X Y : SSet.{0}) (n m : ℕ) :
    complexizeSimplicialChainComponent X Y n m 0 = 0 := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_complexizeSimplicialChainComponent]
  ext
  simp

lemma complexizeSimplicialChainComponent_add
    (X Y : SSet.{0}) (n m : ℕ)
    (f g : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    complexizeSimplicialChainComponent X Y n m (f + g) =
      complexizeSimplicialChainComponent X Y n m f +
        complexizeSimplicialChainComponent X Y n m g := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_complexizeSimplicialChainComponent, Preadditive.comp_add,
    iota_complexizeSimplicialChainComponent,
    iota_complexizeSimplicialChainComponent]
  ext
  simp

lemma complexizeSimplicialChainComponent_neg
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    complexizeSimplicialChainComponent X Y n m (-f) =
      -complexizeSimplicialChainComponent X Y n m f := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_complexizeSimplicialChainComponent, Preadditive.comp_neg,
    iota_complexizeSimplicialChainComponent]
  ext
  simp

/-- The integral-to-complex coefficient map commutes with the simplicial differential. -/
lemma integralToComplexChainComponent_comm_d (X : SSet.{0}) (n : ℕ) :
    integralToComplexChainComponent X (n + 1) ≫
        complexForget.map ((ComplexSimplicialChainComplex X).d (n + 1) n) =
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        integralToComplexChainComponent X n := by
  refine (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) (n + 1)).hom_ext fun x ↦ ?_
  change X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (integralToComplexChainComponent X (n + 1) ≫
        complexForget.map ((ComplexSimplicialChainComplex X).d (n + 1) n)) =
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      ((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        integralToComplexChainComponent X n)
  rw [← Category.assoc, iota_integralToComplexChainComponent, Category.assoc,
    ← Functor.map_comp, SSet.ιChainComplex_d, ← Category.assoc, SSet.ιChainComplex_d,
    Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, iota_integralToComplexChainComponent]
  simp only [Functor.map_sum, Functor.map_zsmul]
  rw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul]

/-- Complexization sends the integral simplicial differential to the complex differential. -/
lemma complexizeSimplicialChainComponent_d (X : SSet.{0}) (n : ℕ) :
    complexizeSimplicialChainComponent X X (n + 1) n
        ((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n) =
      (ComplexSimplicialChainComplex X).d (n + 1) n := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_complexizeSimplicialChainComponent]
  ext
  change (LinearMap.toSpanSingleton ℂ _ _) 1 = _
  rw [LinearMap.toSpanSingleton_apply_one]
  simp only [ConcreteCategory.comp_apply]
  change (integralToComplexChainComponent X n).hom
      (((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)) =
    ((ComplexSimplicialChainComplex X).d (n + 1) n).hom
      ((X.ιChainComplex (R := ModuleCat.of ℂ ℂ) x).hom 1)
  have h := ConcreteCategory.congr_hom
    (integralToComplexChainComponent_comm_d X n)
    ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)
  have hx := ConcreteCategory.congr_hom
    (iota_integralToComplexChainComponent X (n + 1) x) 1
  simp only [ConcreteCategory.comp_apply] at h hx ⊢
  rw [hx] at h
  simpa [complexForget] using h.symm

/-- Complexization of a chain map between integral simplicial chains. -/
def complexizeSimplicialChainMap (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    ComplexSimplicialChainComplex X ⟶ ComplexSimplicialChainComplex Y where
  f n := complexizeSimplicialChainComponent X Y n n (f.f n)
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst i
    rw [← complexizeSimplicialChainComponent_d Y j,
      ← complexizeSimplicialChainComponent_comp, f.comm,
      complexizeSimplicialChainComponent_comp,
      complexizeSimplicialChainComponent_d]

@[simp]
lemma complexizeSimplicialChainMap_f (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) (n : ℕ) :
    (complexizeSimplicialChainMap X Y f).f n =
      complexizeSimplicialChainComponent X Y n n (f.f n) :=
  rfl

lemma complexizeSimplicialChainMap_id (X : SSet.{0}) :
    complexizeSimplicialChainMap X X (𝟙 _) = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun n ↦ complexizeSimplicialChainComponent_id X n

lemma complexizeSimplicialChainMap_comp (X Y Z : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ))
    (g : Y.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Z.chainComplex (AddCommGrpCat.of ℤ)) :
    complexizeSimplicialChainMap X Z (f ≫ g) =
      complexizeSimplicialChainMap X Y f ≫
        complexizeSimplicialChainMap Y Z g :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    complexizeSimplicialChainComponent_comp X Y Z n n n (f.f n) (g.f n)

lemma complexizeSimplicialChainMap_add (X Y : SSet.{0})
    (f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    complexizeSimplicialChainMap X Y (f + g) =
      complexizeSimplicialChainMap X Y f +
        complexizeSimplicialChainMap X Y g :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    complexizeSimplicialChainComponent_add X Y n n (f.f n) (g.f n)

lemma complexizeSimplicialChainMap_zero (X Y : SSet.{0}) :
    complexizeSimplicialChainMap X Y 0 = 0 :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    complexizeSimplicialChainComponent_zero X Y n n

/-- Complexization preserves a chain homotopy between integral simplicial chain maps. -/
def complexizeSimplicialChainHomotopy (X Y : SSet.{0})
    {f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)} (h : Homotopy f g) :
    Homotopy (complexizeSimplicialChainMap X Y f)
      (complexizeSimplicialChainMap X Y g) where
  hom i j := complexizeSimplicialChainComponent X Y i j (h.hom i j)
  zero i j hij := by
    rw [h.zero i j hij, complexizeSimplicialChainComponent_zero]
  comm i := by
    cases i with
    | zero =>
        have hh := congrArg
          (complexizeSimplicialChainComponent X Y 0 0) (h.comm 0)
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex] at hh ⊢
        simp only [complexizeSimplicialChainComponent_add,
          complexizeSimplicialChainComponent_comp,
          complexizeSimplicialChainComponent_d, zero_add] at hh
        change complexizeSimplicialChainComponent X Y 0 0 (f.f 0) =
          0 + complexizeSimplicialChainComponent X Y 0 1 (h.hom 0 1) ≫
            (ComplexSimplicialChainComplex Y).d 1 0 +
              complexizeSimplicialChainComponent X Y 0 0 (g.f 0)
        simpa only [zero_add] using hh
    | succ n =>
        have hh := congrArg
          (complexizeSimplicialChainComponent X Y (n + 1) (n + 1))
            (h.comm (n + 1))
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex] at hh ⊢
        simp only [complexizeSimplicialChainComponent_add,
          complexizeSimplicialChainComponent_comp,
          complexizeSimplicialChainComponent_d] at hh
        exact hh

/-- Complexization preserves a chain-homotopy equivalence of simplicial chain complexes. -/
def complexizeSimplicialChainHomotopyEquiv (X Y : SSet.{0})
    (e : HomotopyEquiv (X.chainComplex (AddCommGrpCat.of ℤ))
      (Y.chainComplex (AddCommGrpCat.of ℤ))) :
    HomotopyEquiv (ComplexSimplicialChainComplex X)
      (ComplexSimplicialChainComplex Y) where
  hom := complexizeSimplicialChainMap X Y e.hom
  inv := complexizeSimplicialChainMap Y X e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (complexizeSimplicialChainMap_comp X Y X e.hom e.inv).symm).trans
      ((complexizeSimplicialChainHomotopy X X e.homotopyHomInvId).trans
        (Homotopy.ofEq (complexizeSimplicialChainMap_id X)))
  homotopyInvHomId :=
    (Homotopy.ofEq (complexizeSimplicialChainMap_comp Y X Y e.inv e.hom).symm).trans
      ((complexizeSimplicialChainHomotopy Y Y e.homotopyInvHomId).trans
        (Homotopy.ofEq (complexizeSimplicialChainMap_id Y)))

/-- Complexization of an integral chain map induced by a simplicial map is the corresponding
complex chain map. -/
lemma complexizeSimplicialChainComponent_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ) :
    complexizeSimplicialChainComponent X Y n n
        ((SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n) =
      (SSet.chainComplexMap f (ModuleCat.of ℂ ℂ)).f n := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_complexizeSimplicialChainComponent,
    SSet.ι_chainComplexMap_f]
  ext
  change (LinearMap.toSpanSingleton ℂ _ _) 1 = _
  rw [LinearMap.toSpanSingleton_apply_one]
  change (integralToComplexChainComponent Y n).hom
      (((SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)) =
    (Y.ιChainComplex (R := ModuleCat.of ℂ ℂ) (f.app _ x)).hom 1
  have hf := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f X Y f (AddCommGrpCat.of ℤ) x) 1
  have hcoeff := ConcreteCategory.congr_hom
    (iota_integralToComplexChainComponent Y n (f.app _ x)) 1
  simp only [ConcreteCategory.comp_apply] at hf hcoeff
  rw [hf]
  simpa [complexForget] using hcoeff

lemma complexizeSimplicialChainMap_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    complexizeSimplicialChainMap X Y
        (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)) =
      SSet.chainComplexMap f (ModuleCat.of ℂ ℂ) :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    complexizeSimplicialChainComponent_chainComplexMap f n

section ComplexSmallChains

variable {ι : Type} (X : TopCat.{0}) (U : ι → Set X)

/-- Complex chains generated by singular simplices subordinate to one member of a cover. -/
abbrev CoverSmallComplexSingularChainComplex :
    ChainComplex (ModuleCat ℂ) ℕ :=
  (coverSmallSingularSubcomplex X U : SSet).chainComplex (ModuleCat.of ℂ ℂ)

/-- Inclusion of cover-small complex singular chains into all complex singular chains. -/
def coverSmallComplexSingularChainInclusion :
    CoverSmallComplexSingularChainComplex X U ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℂ ℂ) :=
  SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (ModuleCat.of ℂ ℂ)

instance coverSmallComplexSingularChainInclusion_mono :
    Mono (coverSmallComplexSingularChainInclusion X U) := by
  dsimp [coverSmallComplexSingularChainInclusion, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

/-- The all-open-cover small-chain theorem with complex coefficients. -/
def CoverSmallComplexChainApproximation : Prop :=
  HomologicalComplex.homotopyEquivalences (ModuleCat ℂ) (ComplexShape.down ℕ)
    (coverSmallComplexSingularChainInclusion X U)

/-- The proven integral subdivision-and-prism homotopy transports to complex coefficients. -/
theorem coverSmallComplexChainApproximation_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    CoverSmallComplexChainApproximation X U := by
  let hZ := coverSmallChainApproximation_of_openCover X U hUopen hUcover
  let eZ := coverSmallChainHomotopyEquiv X U hZ
  refine ⟨complexizeSimplicialChainHomotopyEquiv
    (coverSmallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X) eZ, ?_⟩
  change complexizeSimplicialChainMap
      (coverSmallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X) eZ.hom =
    coverSmallComplexSingularChainInclusion X U
  rw [show eZ.hom = coverSmallIntegralSingularChainInclusion X U from
    coverSmallChainHomotopyEquiv_hom X U hZ]
  exact complexizeSimplicialChainMap_chainComplexMap
    (coverSmallSingularSubcomplex X U).ι

/-- A selected complex small-chain homotopy equivalence for an open cover. -/
def coverSmallComplexChainHomotopyEquiv_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv (CoverSmallComplexSingularChainComplex X U)
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℂ ℂ)) :=
  (coverSmallComplexChainApproximation_of_openCover X U hUopen hUcover).choose

lemma coverSmallComplexChainHomotopyEquiv_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coverSmallComplexChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom =
      coverSmallComplexSingularChainInclusion X U :=
  (coverSmallComplexChainApproximation_of_openCover X U hUopen hUcover).choose_spec

/-- Complex small-chain inclusion induces an isomorphism on homology in every degree. -/
def coverSmallComplexSingularHomologyIso_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (CoverSmallComplexSingularChainComplex X U).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℂ ℂ)).homology n :=
  (coverSmallComplexChainHomotopyEquiv_of_openCover X U hUopen hUcover).toHomologyIso n

lemma coverSmallComplexSingularHomologyIso_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (coverSmallComplexSingularHomologyIso_of_openCover X U hUopen hUcover n).hom =
      HomologicalComplex.homologyMap
        (coverSmallComplexSingularChainInclusion X U) n := by
  dsimp [coverSmallComplexSingularHomologyIso_of_openCover]
  change HomologicalComplex.homologyMap
      (coverSmallComplexChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom n = _
  rw [coverSmallComplexChainHomotopyEquiv_of_openCover_hom]

end ComplexSmallChains

end AlgebraicTopology.Singular
