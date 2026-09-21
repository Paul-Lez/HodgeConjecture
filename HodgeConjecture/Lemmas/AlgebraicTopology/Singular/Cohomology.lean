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

public import HodgeConjecture.Mathlib.AlgebraicTopology.SimplicialSet.ChainComplexSplit
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Cohomology

import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Singular cohomology over a commutative ring

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Singular.Cohomology`.

Cohomology is the homology of the dual cochain complex, so the pairing of a cohomology class
against a homology class is mediated by the universal-coefficient equivalence
`cohomologyEquivDualHomology`. The `_apply` lemmas below record that this pairing is natural.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

/-- The singular chain map induced by a continuous map. -/
abbrev singularChainComplexMap (R : Type u) [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SingularChainComplex R X ⟶ SingularChainComplex R Y :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map f

/-- Let `X` be a topological space and `R` a commutative ring. The singular cochain complex
`C^•(X;R)` has degree-`n` term `Hom_R(C_n(X;R),R)`, where `C_n` is the free module on singular
`n`-simplices. Its coboundary sends `φ` to `φ ∘ ∂`, with `∂` the singular boundary. -/
abbrev SingularCochainComplex (R : Type u) [CommRing R] (X : TopCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (SingularChainComplex R X).linearDualCochainComplex

/-- `C^n(X; R)` is the module of singular `n`-cochains of `X` with coefficients in `R`. -/
scoped notation:max "C^" n:max "(" Y "; " R ")" =>
  HomologicalComplex.X (SingularCochainComplex R Y) n

/-- The singular cochain map induced by a continuous map, obtained by dualising the chain map. -/
abbrev singularCochainComplexMap (R : Type u) [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SingularCochainComplex R Y ⟶ SingularCochainComplex R X :=
  HomologicalComplex.linearDualMap (singularChainComplexMap R f)

/-- Let `X` be a topological space and `R` a commutative ring. Singular cohomology `H^n(X;R)` is
`ker(δ : C^n → C^{n+1}) / im(δ : C^{n-1} → C^n)`, where `C^n = Hom_R(C_n(X;R),R)` and `δφ = φ ∘
∂`. In degree zero the denominator is zero. -/
abbrev Cohomology (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  (SingularCochainComplex R X).homology n

/-- `H^n(X; R)` is singular cohomology of `X` in degree `n` with coefficients in `R`. -/
scoped notation:max "H^" n:max "(" X "; " R ")" => Cohomology R X n

/-- Pullback in singular cohomology, induced by the dualised chain map. -/
def cohomologyMap (R : Type u) [CommRing R] {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) :
    Cohomology R Y n →ₗ[R] Cohomology R X n :=
  (HomologicalComplex.homologyMap (singularCochainComplexMap R f) n).hom

/-- Let `X` be a topological space and `R` a field. This linear equivalence `H^n(X;R) ≅
Hom_R(H_n(X;R),R)` sends a singular cohomology class `[φ]` to the functional `[c] ↦ φ(c)` on
homology classes. It is the universal coefficient isomorphism over a field. -/
def cohomologyEquivDualHomology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) :
    Cohomology R X n ≃ₗ[R] Module.Dual R (Homology R X n) :=
  (SingularChainComplex R X).linearDualHomologyEquiv n

/-- The map on relative homology induced by a map of pairs. -/
def relativeHomologyMap (R : Type u) [CommRing R] {X Y : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) : RelativeHomology R X n →ₗ[R] RelativeHomology R Y n :=
  ((relativeHomologyFunctor R n).map f).hom

/-- The quotient map from absolute homology to relative homology. -/
def relativeHomologyProjection (R : Type u) [CommRing R] (X : TopPair.{u}) (n : ℕ) :
    Homology R X.fst n ⟶ RelativeHomology R X n :=
  HomologicalComplex.homologyMap (relativeChainProjection R X) n

/-- The canonical map from relative cohomology to absolute cohomology, induced by the dual of
the projection from absolute chains to relative chains. -/
def relativeCohomologyToAbsolute (R : Type u) [CommRing R] (X : TopPair.{u}) (n : ℕ) :
    RelativeCohomology R X n →ₗ[R] Cohomology R X.fst n :=
  (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (relativeChainProjection R X)) n).hom

/-- Let `X` be a topological space, `R` a commutative ring, and `Z ⊆ X` a closed subset. Singular
cohomology with support in `Z` is `H_Z^n(X;R) = H^n(X,X \ Z;R)`. It is the degree-`n` cohomology
of the linear dual of `C_*(X;R)/C_*(X \ Z;R)`. The same formula defines this object for an
arbitrary subset `Z`. -/
abbrev CohomologyWithSupport (R : Type u) [CommRing R] (X : TopCat.{u})
    (Z : Set X) (n : ℕ) : ModuleCat.{u} R :=
  RelativeCohomology R (TopPair.ofSubset Zᶜ) n

/-- `H_[Z]^n(X; R)` is singular cohomology of `X` with support in `Z`, in degree `n` with
coefficients in `R`. -/
scoped notation:max "H_[" Z "]^" n:max "(" X "; " R ")" => CohomologyWithSupport R X Z n

/-- Forget support in `Z`, mapping a supported class to ordinary singular cohomology. -/
def forgetSupport (R : Type u) [CommRing R] (X : TopCat.{u}) (Z : Set X) (n : ℕ) :
    CohomologyWithSupport R X Z n →ₗ[R] Cohomology R X n :=
  relativeCohomologyToAbsolute R (TopPair.ofSubset Zᶜ) n

/-- A continuous map, regarded as a map of pairs for a closed support and its preimage. -/
def preimageSupportPairMap {X Y : TopCat.{u}} (f : X ⟶ Y) (Z : Set Y) :
    TopPair.ofSubset (f ⁻¹' Z)ᶜ ⟶ TopPair.ofSubset Zᶜ :=
  TopPair.ofHom f
    (TopCat.ofHom ⟨fun x => ⟨f x.1, x.2⟩,
      Continuous.subtype_mk (f.hom.continuous.comp continuous_subtype_val) _⟩)
    (by ext x; rfl)

/-- Pull back a supported cohomology class. Its support pulls back along the continuous map. -/
def cohomologyWithSupportMap (R : Type u) [CommRing R] {X Y : TopCat.{u}}
    (n : ℕ) (f : X ⟶ Y) (Z : Set Y) :
    CohomologyWithSupport R Y Z n →ₗ[R]
      CohomologyWithSupport R X (f ⁻¹' Z) n :=
  relativeCohomologyMap R n (preimageSupportPairMap f Z)

/-- The identity map as a map of pairs for an inclusion of supports `Z ⊆ W`. -/
def supportInclusionPairMap (X : TopCat.{u}) {Z W : Set X} (h : Z ⊆ W) :
    TopPair.ofSubset Wᶜ ⟶ TopPair.ofSubset Zᶜ :=
  TopPair.ofHom (𝟙 X)
    (TopCat.ofHom ⟨fun x => ⟨x.1, fun hx => x.2 (h hx)⟩, by fun_prop⟩)
    (by ext x; rfl)

/-- Enlarge the allowed support of a supported cohomology class. -/
def enlargeSupport (R : Type u) [CommRing R] (X : TopCat.{u}) {Z W : Set X}
    (h : Z ⊆ W) (n : ℕ) :
    CohomologyWithSupport R X Z n →ₗ[R] CohomologyWithSupport R X W n :=
  relativeCohomologyMap R n (supportInclusionPairMap X h)

end AlgebraicTopology.Singular

end

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

@[simp]
lemma homologyMap_id (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    homologyMap R n (𝟙 X) = LinearMap.id := by
  calc
    _ = ModuleCat.Hom.hom (𝟙 (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj X)) := congrArg ModuleCat.Hom.hom
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map_id X)
    _ = LinearMap.id := rfl

@[simp]
lemma homologyMap_comp (R : Type u) [CommRing R] {X Y Z : TopCat.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homologyMap R n (f ≫ g) = (homologyMap R n g).comp (homologyMap R n f) := by
  calc
    _ = ((((singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).map f) ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj
            (ModuleCat.of R R)).map g).hom := congrArg ModuleCat.Hom.hom
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map_comp f g)
    _ = _ := rfl

/-- Pulling a cohomology class back and then pairing it with a homology class is the same as
pushing the homology class forward and pairing there: the universal-coefficient equivalence is
natural. -/
@[simp]
lemma cohomologyEquivDualHomology_cohomologyMap (R : Type u) [Field R] {X Y : TopCat.{u}}
    (n : ℕ) (f : X ⟶ Y) (α : Cohomology R Y n) (z : Homology R X n) :
    cohomologyEquivDualHomology R X n (cohomologyMap R n f α) z =
      cohomologyEquivDualHomology R Y n α (homologyMap R n f z) :=
  HomologicalComplex.linearDualHomologyEquiv_naturality (singularChainComplexMap R f) n α z

@[simp]
lemma cohomologyMap_id (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    cohomologyMap R n (𝟙 X) = LinearMap.id := by
  simp [cohomologyMap, singularCochainComplexMap]

@[simp]
lemma cohomologyMap_comp (R : Type u) [CommRing R] {X Y Z : TopCat.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    cohomologyMap R n (f ≫ g) =
      (cohomologyMap R n f).comp (cohomologyMap R n g) := by
  simp [cohomologyMap, singularCochainComplexMap, HomologicalComplex.homologyMap_comp]

@[simp]
lemma relativeHomologyMap_id (R : Type u) [CommRing R] (X : TopPair.{u}) (n : ℕ) :
    relativeHomologyMap R n (𝟙 X) = LinearMap.id := by
  calc
    _ = ModuleCat.Hom.hom (𝟙 ((relativeHomologyFunctor R n).obj X)) :=
      congrArg ModuleCat.Hom.hom ((relativeHomologyFunctor R n).map_id X)
    _ = LinearMap.id := rfl

@[simp]
lemma relativeHomologyMap_comp (R : Type u) [CommRing R] {X Y Z : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativeHomologyMap R n (f ≫ g) =
      (relativeHomologyMap R n g).comp (relativeHomologyMap R n f) := by
  calc
    _ = (((relativeHomologyFunctor R n).map f) ≫
        (relativeHomologyFunctor R n).map g).hom :=
      congrArg ModuleCat.Hom.hom ((relativeHomologyFunctor R n).map_comp f g)
    _ = _ := rfl

/-- The universal-coefficient equivalence for pairs is natural in the pair. -/
@[simp]
lemma relativeCohomologyEquivDualHomology_relativeCohomologyMap (R : Type u) [Field R]
    {X Y : TopPair.{u}} (n : ℕ) (f : X ⟶ Y) (α : RelativeCohomology R Y n)
    (z : RelativeHomology R X n) :
    relativeCohomologyEquivDualHomology R X n (relativeCohomologyMap R n f α) z =
      relativeCohomologyEquivDualHomology R Y n α (relativeHomologyMap R n f z) :=
  HomologicalComplex.linearDualHomologyEquiv_naturality ((relativeChainFunctor R).map f) n α z

@[simp]
lemma relativeCohomologyMap_id (R : Type u) [CommRing R] (X : TopPair.{u}) (n : ℕ) :
    relativeCohomologyMap R n (𝟙 X) = LinearMap.id := by
  simp [relativeCohomologyMap, relativeCochainComplexMap]

@[simp]
lemma relativeCohomologyMap_comp (R : Type u) [CommRing R] {X Y Z : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativeCohomologyMap R n (f ≫ g) =
      (relativeCohomologyMap R n f).comp (relativeCohomologyMap R n g) := by
  simp [relativeCohomologyMap, relativeCochainComplexMap,
    HomologicalComplex.homologyMap_comp]

@[reassoc (attr := simp)]
lemma subspaceChainMap_relativeChainProjection (R : Type u) [CommRing R]
    (X : TopPair.{u}) :
    ((chainPairFunctor R).obj X).hom ≫ relativeChainProjection R X = 0 :=
  cokernel.condition _

/-- The short exact sequence of subspace, ambient, and relative singular chains. -/
def relativeChainShortComplex (R : Type u) [CommRing R] (X : TopPair.{u}) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk ((chainPairFunctor R).obj X).hom
    (relativeChainProjection R X)
    (subspaceChainMap_relativeChainProjection R X)

/-- The singular-chain map of a topological-pair inclusion is a monomorphism. -/
lemma relativeChainMap_mono (R : Type u) [CommRing R] (X : TopPair.{u}) :
    Mono ((chainPairFunctor R).obj X).hom := by
  let : Mono X.hom :=
    (TopCat.mono_iff_injective X.hom).mpr X.prop.injective
  change Mono (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).map X.hom)
  apply Functor.map_mono

/-- The singular-chain map of a topological-pair inclusion is a split monomorphism in every
degree. -/
lemma relativeChainMap_isSplitMono (R : Type u) [CommRing R] (X : TopPair.{u}) (n : ℕ) :
    IsSplitMono (((chainPairFunctor R).obj X).hom.f n) :=
  let _ : Mono X.hom := (TopCat.mono_iff_injective X.hom).mpr X.prop.injective
  AlgebraicTopology.isSplitMono_singularChainComplexFunctor_map_f X.hom (ModuleCat.of R R) n

/-- Singular chains of a pair form a short exact sequence.

See mathlib PR https://github.com/leanprover-community/mathlib4/pull/37659. -/
lemma relativeChainShortComplex_shortExact (R : Type u) [CommRing R] (X : TopPair.{u}) :
    (relativeChainShortComplex R X).ShortExact := by
  let : Mono ((chainPairFunctor R).obj X).hom := relativeChainMap_mono R X
  exact
    { exact := ShortComplex.exact_cokernel ((chainPairFunctor R).obj X).hom
      mono_f := by
        dsimp [relativeChainShortComplex]
        infer_instance
      epi_g := by
        dsimp [relativeChainShortComplex, relativeChainProjection]
        exact coequalizer.π_epi }

/-- Forgetting that a class is relative and then pairing it with an absolute homology class is
the same as projecting the homology class to relative homology and pairing there. -/
@[simp]
lemma cohomologyEquivDualHomology_relativeCohomologyToAbsolute (R : Type u) [Field R]
    (X : TopPair.{u}) (n : ℕ) (α : RelativeCohomology R X n) (z : Homology R X.fst n) :
    cohomologyEquivDualHomology R X.fst n (relativeCohomologyToAbsolute R X n α) z =
      relativeCohomologyEquivDualHomology R X n α ((relativeHomologyProjection R X n).hom z) :=
  HomologicalComplex.linearDualHomologyEquiv_naturality (relativeChainProjection R X) n α z

@[simp]
lemma cohomologyEquivDualHomology_forgetSupport (R : Type u) [Field R] (X : TopCat.{u})
    (Z : Set X) (n : ℕ) (α : CohomologyWithSupport R X Z n) (z : Homology R X n) :
    cohomologyEquivDualHomology R X n (forgetSupport R X Z n α) z =
      relativeCohomologyEquivDualHomology R (TopPair.ofSubset Zᶜ) n α
        ((relativeHomologyProjection R (TopPair.ofSubset Zᶜ) n).hom z) :=
  cohomologyEquivDualHomology_relativeCohomologyToAbsolute R (TopPair.ofSubset Zᶜ) n α z

@[simp]
lemma preimageSupportPairMap_id (X : TopCat.{u}) (Z : Set X) :
    preimageSupportPairMap (𝟙 X) Z = 𝟙 (TopPair.ofSubset Zᶜ) := rfl

@[simp]
lemma cohomologyWithSupportMap_id (R : Type u) [CommRing R] (X : TopCat.{u})
    (Z : Set X) (n : ℕ) :
    cohomologyWithSupportMap R n (𝟙 X) Z = LinearMap.id := by
  unfold cohomologyWithSupportMap
  exact relativeCohomologyMap_id R (TopPair.ofSubset Zᶜ) n

@[simp]
lemma supportInclusionPairMap_rfl (X : TopCat.{u}) (Z : Set X) :
    supportInclusionPairMap X (Set.Subset.rfl : Z ⊆ Z) = 𝟙 (TopPair.ofSubset Zᶜ) := rfl

lemma supportInclusionPairMap_trans (X : TopCat.{u}) {Z W U : Set X}
    (hZW : Z ⊆ W) (hWU : W ⊆ U) :
    supportInclusionPairMap X (hZW.trans hWU) =
      supportInclusionPairMap X hWU ≫ supportInclusionPairMap X hZW := rfl

@[simp]
lemma enlargeSupport_rfl (R : Type u) [CommRing R] (X : TopCat.{u}) (Z : Set X) (n : ℕ) :
    enlargeSupport R X (Set.Subset.rfl : Z ⊆ Z) n = LinearMap.id := by
  rw [enlargeSupport, supportInclusionPairMap_rfl, relativeCohomologyMap_id]

/-- If relative homology is a subsingleton, so is relative cohomology, by the
universal-coefficient equivalence. -/
lemma relativeCohomology_subsingleton (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ)
    (h : Subsingleton (RelativeHomology R X n)) :
    Subsingleton (RelativeCohomology R X n) :=
  have : Subsingleton (Module.Dual R (RelativeHomology R X n)) :=
    ⟨fun φ ψ => LinearMap.ext fun x => by rw [h.elim x 0, map_zero, map_zero]⟩
  (relativeCohomologyEquivDualHomology R X n).toEquiv.subsingleton

/-- If relative homology is a zero object, so is relative cohomology. -/
lemma relativeCohomology_isZero (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ)
    (h : IsZero (RelativeHomology R X n)) : IsZero (RelativeCohomology R X n) :=
  have := relativeCohomology_subsingleton R X n (ModuleCat.subsingleton_of_isZero h)
  ModuleCat.isZero_of_subsingleton _

end AlgebraicTopology.Singular
