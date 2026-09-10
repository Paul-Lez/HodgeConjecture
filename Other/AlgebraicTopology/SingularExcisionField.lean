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

public import Other.AlgebraicTopology.SingularExcisionScalar

/-!
# Small singular chains with rational coefficients

This file transports the integral subdivision homotopy to rational simplicial chains.  The
transport is constructed directly from the universal bases of the two simplicial chain
complexes.  In particular, it does not assume a universal-coefficient theorem.

The construction is carried out for an arbitrary commutative ring of coefficients in
`Other.AlgebraicTopology.SingularExcisionScalar` (names `Scalar…`/`scalarize…`); this file
records the rational specialisation `R := ℚ` under its original names.  The types and the
small-chain inclusion are stated with their original bodies (so that `RationalSimplicialChainComplex
X` still unfolds to `X.chainComplex (ModuleCat.of ℚ ℚ)` and
`coverSmallRationalSingularChainInclusion X U` still unfolds to
`SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (ModuleCat.of ℚ ℚ)`); every other
declaration is definitionally the `ℚ`-instance of the corresponding general one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- Rational chains on a simplicial set. -/
abbrev RationalSimplicialChainComplex (X : SSet.{0}) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  X.chainComplex (ModuleCat.of ℚ ℚ)

/-- The underlying additive group of a rational module. -/
abbrev rationalForget := forget₂ (ModuleCat ℚ) AddCommGrpCat

@[simp]
lemma moduleCat_toSpanSingleton_apply_one (M : ModuleCat ℚ) (v : M) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ M v)).hom 1 = v :=
  moduleCat_toSpanSingleton_hom_apply_one ℚ M v

/-- The coefficient map from integral to rational chains in one degree. -/
def integralToRationalChainComponent (X : SSet.{0}) (n : ℕ) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      rationalForget.obj ((RationalSimplicialChainComplex X).X n) :=
  integralToScalarChainComponent ℚ X n

@[reassoc]
lemma iota_integralToRationalChainComponent (X : SSet.{0}) (n : ℕ)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x ≫
        integralToRationalChainComponent X n =
      AddCommGrpCat.ofHom (Int.castAddHom ℚ) ≫
        rationalForget.map (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x) :=
  iota_integralToScalarChainComponent ℚ X n x

/-- Extend an integral map between free simplicial-chain groups rational-linearly. -/
def rationalizeSimplicialChainComponent (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    (RationalSimplicialChainComplex X).X n ⟶
      (RationalSimplicialChainComplex Y).X m :=
  scalarizeSimplicialChainComponent ℚ X Y n m f

@[reassoc]
lemma iota_rationalizeSimplicialChainComponent
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x ≫
        rationalizeSimplicialChainComponent X Y n m f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ <|
        (show (RationalSimplicialChainComplex Y).X m from
          (integralToRationalChainComponent Y m).hom
            (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)))) :=
  iota_scalarizeSimplicialChainComponent ℚ X Y n m f x

lemma integralToRationalChainComponent_naturality
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    integralToRationalChainComponent X n ≫
        rationalForget.map (rationalizeSimplicialChainComponent X Y n m f) =
      f ≫ integralToRationalChainComponent Y m :=
  integralToScalarChainComponent_naturality ℚ X Y n m f

lemma rationalizeSimplicialChainComponent_comp
    (X Y Z : SSet.{0}) (n m k : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (g : (Y.chainComplex (AddCommGrpCat.of ℤ)).X m ⟶
      (Z.chainComplex (AddCommGrpCat.of ℤ)).X k) :
    rationalizeSimplicialChainComponent X Z n k (f ≫ g) =
      rationalizeSimplicialChainComponent X Y n m f ≫
        rationalizeSimplicialChainComponent Y Z m k g :=
  scalarizeSimplicialChainComponent_comp ℚ X Y Z n m k f g

lemma rationalizeSimplicialChainComponent_id (X : SSet.{0}) (n : ℕ) :
    rationalizeSimplicialChainComponent X X n n (𝟙 _) = 𝟙 _ :=
  scalarizeSimplicialChainComponent_id ℚ X n

lemma rationalizeSimplicialChainComponent_zero
    (X Y : SSet.{0}) (n m : ℕ) :
    rationalizeSimplicialChainComponent X Y n m 0 = 0 :=
  scalarizeSimplicialChainComponent_zero ℚ X Y n m

lemma rationalizeSimplicialChainComponent_add
    (X Y : SSet.{0}) (n m : ℕ)
    (f g : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    rationalizeSimplicialChainComponent X Y n m (f + g) =
      rationalizeSimplicialChainComponent X Y n m f +
        rationalizeSimplicialChainComponent X Y n m g :=
  scalarizeSimplicialChainComponent_add ℚ X Y n m f g

lemma rationalizeSimplicialChainComponent_neg
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    rationalizeSimplicialChainComponent X Y n m (-f) =
      -rationalizeSimplicialChainComponent X Y n m f :=
  scalarizeSimplicialChainComponent_neg ℚ X Y n m f

/-- The integral-to-rational coefficient map commutes with the simplicial differential. -/
lemma integralToRationalChainComponent_comm_d (X : SSet.{0}) (n : ℕ) :
    integralToRationalChainComponent X (n + 1) ≫
        rationalForget.map ((RationalSimplicialChainComplex X).d (n + 1) n) =
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        integralToRationalChainComponent X n :=
  integralToScalarChainComponent_comm_d ℚ X n

/-- Rationalization sends the integral simplicial differential to the rational differential. -/
lemma rationalizeSimplicialChainComponent_d (X : SSet.{0}) (n : ℕ) :
    rationalizeSimplicialChainComponent X X (n + 1) n
        ((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n) =
      (RationalSimplicialChainComplex X).d (n + 1) n :=
  scalarizeSimplicialChainComponent_d ℚ X n

/-- Rationalization of a chain map between integral simplicial chains. -/
def rationalizeSimplicialChainMap (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    RationalSimplicialChainComplex X ⟶ RationalSimplicialChainComplex Y :=
  scalarizeSimplicialChainMap ℚ X Y f

@[simp]
lemma rationalizeSimplicialChainMap_f (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) (n : ℕ) :
    (rationalizeSimplicialChainMap X Y f).f n =
      rationalizeSimplicialChainComponent X Y n n (f.f n) :=
  rfl

lemma rationalizeSimplicialChainMap_id (X : SSet.{0}) :
    rationalizeSimplicialChainMap X X (𝟙 _) = 𝟙 _ :=
  scalarizeSimplicialChainMap_id ℚ X

lemma rationalizeSimplicialChainMap_comp (X Y Z : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ))
    (g : Y.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Z.chainComplex (AddCommGrpCat.of ℤ)) :
    rationalizeSimplicialChainMap X Z (f ≫ g) =
      rationalizeSimplicialChainMap X Y f ≫
        rationalizeSimplicialChainMap Y Z g :=
  scalarizeSimplicialChainMap_comp ℚ X Y Z f g

lemma rationalizeSimplicialChainMap_add (X Y : SSet.{0})
    (f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    rationalizeSimplicialChainMap X Y (f + g) =
      rationalizeSimplicialChainMap X Y f +
        rationalizeSimplicialChainMap X Y g :=
  scalarizeSimplicialChainMap_add ℚ X Y f g

lemma rationalizeSimplicialChainMap_zero (X Y : SSet.{0}) :
    rationalizeSimplicialChainMap X Y 0 = 0 :=
  scalarizeSimplicialChainMap_zero ℚ X Y

/-- Rationalization preserves a chain homotopy between integral simplicial chain maps. -/
def rationalizeSimplicialChainHomotopy (X Y : SSet.{0})
    {f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)} (h : Homotopy f g) :
    Homotopy (rationalizeSimplicialChainMap X Y f)
      (rationalizeSimplicialChainMap X Y g) :=
  scalarizeSimplicialChainHomotopy ℚ X Y h

/-- Rationalization preserves a chain-homotopy equivalence of simplicial chain complexes. -/
def rationalizeSimplicialChainHomotopyEquiv (X Y : SSet.{0})
    (e : HomotopyEquiv (X.chainComplex (AddCommGrpCat.of ℤ))
      (Y.chainComplex (AddCommGrpCat.of ℤ))) :
    HomotopyEquiv (RationalSimplicialChainComplex X)
      (RationalSimplicialChainComplex Y) :=
  scalarizeSimplicialChainHomotopyEquiv ℚ X Y e

/-- Rationalization of an integral chain map induced by a simplicial map is the corresponding
rational chain map. -/
lemma rationalizeSimplicialChainComponent_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ) :
    rationalizeSimplicialChainComponent X Y n n
        ((SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n) =
      (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n :=
  scalarizeSimplicialChainComponent_chainComplexMap ℚ f n

lemma rationalizeSimplicialChainMap_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    rationalizeSimplicialChainMap X Y
        (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)) =
      SSet.chainComplexMap f (ModuleCat.of ℚ ℚ) :=
  scalarizeSimplicialChainMap_chainComplexMap ℚ f

section RationalSmallChains

variable {ι : Type} (X : TopCat.{0}) (U : ι → Set X)

/-- Rational chains generated by singular simplices subordinate to one member of a cover. -/
abbrev CoverSmallRationalSingularChainComplex :
    ChainComplex (ModuleCat ℚ) ℕ :=
  (coverSmallSingularSubcomplex X U : SSet).chainComplex (ModuleCat.of ℚ ℚ)

/-- Inclusion of cover-small rational singular chains into all rational singular chains.

This is definitionally `coverSmallScalarSingularChainInclusion ℚ X U`; it is stated with the
explicit body so that unfolding it exposes `SSet.chainComplexMap` directly. -/
def coverSmallRationalSingularChainInclusion :
    CoverSmallRationalSingularChainComplex X U ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (ModuleCat.of ℚ ℚ)

instance coverSmallRationalSingularChainInclusion_mono :
    Mono (coverSmallRationalSingularChainInclusion X U) :=
  coverSmallScalarSingularChainInclusion_mono ℚ X U

/-- The proven integral subdivision-and-prism homotopy transports to rational coefficients:
the all-open-cover small-chain theorem with rational coefficients. -/
theorem coverSmallRationalChainApproximation_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat ℚ) (ComplexShape.down ℕ)
      (coverSmallRationalSingularChainInclusion X U) :=
  coverSmallScalarChainApproximation_of_openCover ℚ X U hUopen hUcover

/-- A selected rational small-chain homotopy equivalence for an open cover. -/
def coverSmallRationalChainHomotopyEquiv_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv (CoverSmallRationalSingularChainComplex X U)
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)) :=
  coverSmallScalarChainHomotopyEquiv_of_openCover ℚ X U hUopen hUcover

lemma coverSmallRationalChainHomotopyEquiv_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coverSmallRationalChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom =
      coverSmallRationalSingularChainInclusion X U :=
  coverSmallScalarChainHomotopyEquiv_of_openCover_hom ℚ X U hUopen hUcover

/-- Rational small-chain inclusion induces an isomorphism on homology in every degree. -/
def coverSmallRationalSingularHomologyIso_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (CoverSmallRationalSingularChainComplex X U).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).homology n :=
  coverSmallScalarSingularHomologyIso_of_openCover ℚ X U hUopen hUcover n

lemma coverSmallRationalSingularHomologyIso_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (coverSmallRationalSingularHomologyIso_of_openCover X U hUopen hUcover n).hom =
      HomologicalComplex.homologyMap
        (coverSmallRationalSingularChainInclusion X U) n :=
  coverSmallScalarSingularHomologyIso_of_openCover_hom ℚ X U hUopen hUcover n

end RationalSmallChains

end AlgebraicTopology.Singular
