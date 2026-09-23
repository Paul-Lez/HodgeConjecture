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

public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.Constant
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Sheaves.Abelian

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Contractible
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import Mathlib.Topology.Sheaves.Sheafify

/-!
# The singular-cochain sheaf

This file constructs the singular cochain presheaf on a topological space. In degree `n`, its
sections over an open set `U` are the linear dual of the singular `n`-chains of `U`. Restriction is
dual to the chain map induced by an inclusion of open sets. The singular boundary dualizes to the
coboundary, giving a cochain complex. Degreewise sheafification gives the singular-cochain sheaf
complex.

These constructions are prerequisites for comparing singular cohomology with constant-sheaf
cohomology. The comparison is proved in degree zero on locally path-connected spaces. In
positive degrees, an explicit neighborhood-wise primitive condition is shown to imply it.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [CommRing R] (X : TopCat.{u})

/-- Let `R` be a commutative ring and `X` a topological space. This functor sends an open subset `U`
to its singular chain complex `C_*(U; R)`, freely generated in degree `n` by continuous singular
`n`-simplices. Inclusions of opens induce the chain maps. -/
def openSingularChainComplexFunctor :
    Opens X ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  Opens.toTopCat X ⋙
    (singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)

/-- Let `R` be a commutative ring and `X` a topological space. For an open subset `U` and a natural
number `n`, this is `C_n(U; R)`, the free `R`-module on continuous maps from the standard
`n`-simplex to `U`. -/
abbrev OpenChains (U : (Opens X)ᵒᵖ) (n : ℕ) :=
  (openSingularChainComplexFunctor R X).obj U.unop |>.X n

/-- Let `R` be a commutative ring and `X` a topological space. For an open subset `U` and a natural
number `n`, this is the module `Hom_R(C_n(U; R), R)` of singular cochains, or equivalently all
functions assigning an element of `R` to each singular `n`-simplex in `U`. -/
abbrev OpenCochains (U : (Opens X)ᵒᵖ) (n : ℕ) :=
  Module.Dual R (OpenChains R X U n)

/-- Let `R` be a commutative ring and `X` a topological space. For a natural number `n`, this
presheaf of abelian groups sends an open `U` to `C^n(U; R) = Hom_R(C_n(U; R), R)`. Restrictions
precompose cochains with the chain maps induced by inclusions of opens. -/
def singularCochainPresheaf (n : ℕ) : TopCat.Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of (OpenCochains R X U n)
  map {U V} i := AddCommGrpCat.ofHom <|
    (((openSingularChainComplexFunctor R X).map i.unop).f n).hom.dualMap.toAddMonoidHom
  map_id U := by
    change AddCommGrpCat.ofHom
        (((((openSingularChainComplexFunctor R X).map (𝟙 U.unop)).f n).hom.dualMap)
          |>.toAddMonoidHom) = 𝟙 _
    rw [(openSingularChainComplexFunctor R X).map_id]
    rfl
  map_comp {U V W} i j := by
    rw [show (i ≫ j).unop = j.unop ≫ i.unop by rfl,
      (openSingularChainComplexFunctor R X).map_comp]
    rfl

/-- Let `R` be a commutative ring and `X` a topological space. This morphism of presheaves sends a
singular `n`-cochain `φ` on an open `U` to the `(n+1)`-cochain `φ ∘ ∂`, where `∂` is the
alternating sum of the simplex face maps. -/
def singularCochainCoboundary (n : ℕ) :
    singularCochainPresheaf R X n ⟶ singularCochainPresheaf R X (n + 1) where
  app U := AddCommGrpCat.ofHom <|
    ((((openSingularChainComplexFunctor R X).obj U.unop).d
      (n + 1) n).hom.dualMap).toAddMonoidHom
  naturality {U V} i := by
    ext φ
    change OpenCochains R X U n at φ
    apply LinearMap.ext
    intro c
    change φ
        (((((openSingularChainComplexFunctor R X).map i.unop).f n).hom)
          (((openSingularChainComplexFunctor R X).obj V.unop).d (n + 1) n |>.hom c)) =
      φ
        ((((openSingularChainComplexFunctor R X).obj U.unop).d (n + 1) n |>.hom)
          (((openSingularChainComplexFunctor R X).map i.unop).f (n + 1) |>.hom c))
    calc
      _ = φ (ModuleCat.Hom.hom
          (((openSingularChainComplexFunctor R X).obj V.unop).d (n + 1) n ≫
            ((openSingularChainComplexFunctor R X).map i.unop).f n) c) := rfl
      _ = φ (ModuleCat.Hom.hom
          (((openSingularChainComplexFunctor R X).map i.unop).f (n + 1) ≫
            ((openSingularChainComplexFunctor R X).obj U.unop).d (n + 1) n) c) :=
        congrArg (fun f ↦ φ (ModuleCat.Hom.hom f c))
          (((openSingularChainComplexFunctor R X).map i.unop).comm (n + 1) n).symm
      _ = _ := rfl

/-- Consecutive singular coboundaries compose to zero. -/
lemma singularCochainCoboundary_comp (n : ℕ) :
    singularCochainCoboundary R X n ≫ singularCochainCoboundary R X (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  ext φ
  change OpenCochains R X U n at φ
  apply LinearMap.ext
  intro c
  let K := (openSingularChainComplexFunctor R X).obj U.unop
  have h := K.d_comp_d (n + 2) (n + 1) n
  calc
    _ = φ (ModuleCat.Hom.hom
        (K.d (n + 2) (n + 1) ≫ K.d (n + 1) n) c) := rfl
    _ = φ (ModuleCat.Hom.hom (0 : K.X (n + 2) ⟶ K.X n) c) :=
      congrArg (fun f ↦ φ (ModuleCat.Hom.hom f c)) h
    _ = φ 0 := rfl
    _ = 0 := φ.map_zero

/-- Let `R` be a commutative ring and `X` a topological space. This nonnegative complex of
presheaves has `U ↦ Hom_R(C_n(U; R), R)` in degree `n`, with restrictions induced by inclusions
of opens and coboundary `φ ↦ φ ∘ ∂`. -/
def singularCochainPresheafComplex :
    CochainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ :=
  CochainComplex.of
    (singularCochainPresheaf R X)
    (singularCochainCoboundary R X)
    (singularCochainCoboundary_comp R X)

@[simp]
lemma singularCochainPresheafComplex_d (n : ℕ) :
    (singularCochainPresheafComplex R X).d n (n + 1) =
      singularCochainCoboundary R X n := by
  simp [singularCochainPresheafComplex]

/-- Let `R` be a commutative ring and `X` a topological space. For a natural number `n`, this is the
sheafification, as abelian groups, of `U ↦ C^n(U; R)`. Its sections are locally represented by
singular cochains, with representatives identified if they agree on smaller neighborhoods. -/
def singularCochainSheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat X :=
  let J := Opens.grothendieckTopology X
  (presheafToSheaf J AddCommGrpCat).obj (singularCochainPresheaf R X n)

/-- Let `R` be a commutative ring and `X` a topological space. Sheafifying the singular coboundary
`φ ↦ φ ∘ ∂` gives this morphism from the sheaf of degree-`n` singular cochains to that of
degree-`n+1` cochains. -/
def singularCochainSheafCoboundary (n : ℕ) :
    singularCochainSheaf R X n ⟶ singularCochainSheaf R X (n + 1) :=
  let J := Opens.grothendieckTopology X
  (presheafToSheaf J AddCommGrpCat).map (singularCochainCoboundary R X n)

/-- Let `R` be a commutative ring and `X` a topological space. This nonnegative complex of sheaves
of abelian groups is obtained by sheafifying `U ↦ C^n(U; R)` in every degree. Its differential
is induced by the singular coboundary `φ ↦ φ ∘ ∂`. -/
def singularCochainSheafComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℕ :=
  let J := Opens.grothendieckTopology X
  ((presheafToSheaf J AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (singularCochainPresheafComplex R X)

@[simp]
lemma singularCochainSheafComplex_d (n : ℕ) :
    (singularCochainSheafComplex R X).d n (n + 1) =
      singularCochainSheafCoboundary R X n := by
  change (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).map
        ((singularCochainPresheafComplex R X).d n (n + 1)) = _
  rw [singularCochainPresheafComplex_d]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let `R` be a commutative ring and `X` a topological space. This map from the singular cochain
presheaf complex to its degreewise sheafification sends each cochain on an open set to the
section represented by its local germs. It commutes with singular coboundaries. -/
noncomputable def singularCochainSheafificationUnit :
    singularCochainPresheafComplex R X ⟶
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapHomologicalComplex
        (ComplexShape.up ℕ) |>.obj (singularCochainSheafComplex R X) where
  f n := toSheafify (Opens.grothendieckTopology X)
    (singularCochainPresheaf R X n)
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, singularCochainPresheafComplex_d,
      singularCochainSheafComplex_d]
    dsimp [singularCochainSheafCoboundary, singularCochainSheaf]
    exact (toSheafify_naturality (Opens.grothendieckTopology X)
      (singularCochainCoboundary R X i)).symm

/-- Let `R` be a commutative ring and `S` a simplicial set. This linear map from the free module of
zero-chains on `S` to `R` sums coefficients, sending every vertex to `1`. -/
def simplicialZeroAugmentation (S : SSet.{u}) :
    (S.chainComplex (ModuleCat.of R R)).X 0 ⟶ ModuleCat.of R R :=
  Limits.Sigma.desc (fun _ ↦ 𝟙 _)

@[reassoc (attr := simp)]
lemma ιChainComplex_comp_simplicialZeroAugmentation (S : SSet.{u})
    (σ : S.obj (.op ⟨0⟩)) :
    S.ιChainComplex σ ≫ simplicialZeroAugmentation R S = 𝟙 _ :=
  Limits.Sigma.ι_desc (fun _ ↦ 𝟙 (ModuleCat.of R R)) σ

/-- The zero-chain augmentation is natural in the simplicial set. -/
lemma simplicialZeroAugmentation_naturality {S T : SSet.{u}} (f : S ⟶ T) :
    (SSet.chainComplexMap f (ModuleCat.of R R)).f 0 ≫
      simplicialZeroAugmentation R T = simplicialZeroAugmentation R S := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    ιChainComplex_comp_simplicialZeroAugmentation,
    ιChainComplex_comp_simplicialZeroAugmentation]

/-- The simplicial boundary of a one-chain has augmentation zero. -/
private lemma simplicialBoundary_comp_zeroAugmentation (S : SSet.{u}) :
    (S.chainComplex (ModuleCat.of R R)).d 1 0 ≫
      simplicialZeroAugmentation R S = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp

/-- Let `R` be a commutative ring and `X` a topological space. For an open `U`, this map `C_0(U; R)
→ R` sends every point of `U`, regarded as a singular zero-simplex, to `1` and sums coefficients
on finite chains. -/
def openZeroAugmentation (U : (Opens X)ᵒᵖ) :
    OpenChains R X U 0 ⟶ ModuleCat.of R R :=
  simplicialZeroAugmentation R <|
    TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)

/-- Restriction of open subsets commutes with the zero-chain augmentation. -/
lemma openZeroAugmentation_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ((openSingularChainComplexFunctor R X).map i.unop).f 0 ≫
      openZeroAugmentation R X U = openZeroAugmentation R X V :=
  simplicialZeroAugmentation_naturality R
    (TopCat.toSSet.map ((Opens.toTopCat X).map i.unop))

/-- The boundary of an open singular one-chain has augmentation zero. -/
private lemma openBoundary_comp_zeroAugmentation (U : (Opens X)ᵒᵖ) :
    ((openSingularChainComplexFunctor R X).obj U.unop).d 1 0 ≫
      openZeroAugmentation R X U = 0 :=
  simplicialBoundary_comp_zeroAugmentation R
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop))

/-- Let `R` be a commutative ring and `X` a topological space. For an open `U`, this linear map
sends `r ∈ R` to the singular zero-cochain on `U` with constant value `r` on every point. -/
def constantSingularZeroCochain (U : (Opens X)ᵒᵖ) :
    R →+ OpenCochains R X U 0 where
  toFun r := r • (openZeroAugmentation R X U).hom
  map_zero' := LinearMap.ext fun c ↦ by simp
  map_add' r s := LinearMap.ext fun c ↦ by simp [add_smul]

/-- Let `R` be a commutative ring and `X` a topological space. This presheaf morphism sends an
element `r` of the constant presheaf `R` on each open `U` to the singular zero-cochain whose
value is `r` at every point of `U`. -/
def constantsToSingularCochainZero :
    𝓒ᵖ(X; R) ⟶ singularCochainPresheaf R X 0 where
  app U := AddCommGrpCat.ofHom (constantSingularZeroCochain R X U)
  naturality {U V} i := by
    ext r
    change R at r
    apply LinearMap.ext
    intro c
    dsimp [TopCat.Presheaf.const, constantSingularZeroCochain,
      singularCochainPresheaf]
    exact congrArg (r * ·) <| congrArg (fun f ↦ f.hom c) <|
      (openZeroAugmentation_naturality R X i).symm

/-- Constant zero-cochains have zero coboundary. -/
lemma constantsToSingularCochainZero_comp_coboundary :
    constantsToSingularCochainZero R X ≫ singularCochainCoboundary R X 0 = 0 := by
  apply NatTrans.ext
  funext U
  ext r
  change R at r
  apply LinearMap.ext
  intro c
  change r * (openZeroAugmentation R X U).hom
      ((((openSingularChainComplexFunctor R X).obj U.unop).d 1 0).hom c) = 0
  have hc : (openZeroAugmentation R X U).hom
      ((((openSingularChainComplexFunctor R X).obj U.unop).d 1 0).hom c) = 0 := by
    calc
      _ = ModuleCat.Hom.hom
          (((openSingularChainComplexFunctor R X).obj U.unop).d 1 0 ≫
            openZeroAugmentation R X U) c := rfl
      _ = ModuleCat.Hom.hom
          (0 : OpenChains R X U 1 ⟶ ModuleCat.of R R) c :=
        congrArg (fun f ↦ f.hom c) (openBoundary_comp_zeroAugmentation R X U)
      _ = 0 := rfl
  rw [hc, mul_zero]

/-- Let `R` be a commutative ring and `X` a topological space. This sheaf morphism from the constant
sheaf `R_X` to the sheafification of singular zero-cochains sends a locally constant function to
its germs as a zero-cochain. -/
def constantsToSingularCochainZeroSheaf :
    𝓒(X; R) ⟶ singularCochainSheaf R X 0 :=
  let J := Opens.grothendieckTopology X
  (presheafToSheaf J AddCommGrpCat).map (constantsToSingularCochainZero R X)

/-- Constant sections have zero sheafified singular coboundary. -/
lemma constantsToSingularCochainZeroSheaf_comp_coboundary :
    constantsToSingularCochainZeroSheaf R X ≫
      singularCochainSheafCoboundary R X 0 = 0 := by
  let J := Opens.grothendieckTopology X
  change (presheafToSheaf J AddCommGrpCat).map
      (constantsToSingularCochainZero R X) ≫
    (presheafToSheaf J AddCommGrpCat).map
      (singularCochainCoboundary R X 0) = 0
  rw [← Functor.map_comp, constantsToSingularCochainZero_comp_coboundary,
    Functor.map_zero]

/-- Let `R` be a commutative ring and `X` a topological space. This map from the constant sheaf
`R_X` in degree zero to the sheafified singular cochain complex includes locally constant
functions as zero-cochains. All positive-degree components of the source are zero. -/
def constantsToSingularCochainSheafComplex :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat X)).obj
        𝓒(X; R) ⟶ singularCochainSheafComplex R X :=
  (CochainComplex.fromSingle₀Equiv (singularCochainSheafComplex R X)
    𝓒(X; R)).symm
      ⟨constantsToSingularCochainZeroSheaf R X, by
        rw [singularCochainSheafComplex_d]
        exact constantsToSingularCochainZeroSheaf_comp_coboundary R X⟩

end AlgebraicTopology.Singular
