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

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Cohomology

import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Singular cohomology over a field

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Singular.Cohomology`.

Because cohomology is the homology of the dual cochain complex rather than the dual of homology,
the pairing of a cohomology class against a homology class is not definitional: it is mediated by
the universal-coefficient equivalence `cohomologyEquivDualHomology`. The `_apply` lemmas below
record that this pairing is natural, which is what the old definitional `rfl` lemmas expressed.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

/-- The singular chain map induced by a continuous map. -/
abbrev singularChainComplexMap (R : Type u) [Field R] {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SingularChainComplex R X ⟶ SingularChainComplex R Y :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map f

/-- The singular cochain complex `C^*(X; R)`, the degreewise `R`-linear dual of the singular
chain complex. -/
abbrev SingularCochainComplex (R : Type u) [Field R] (X : TopCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (SingularChainComplex R X).linearDualCochainComplex

/-- The singular cochain map induced by a continuous map, obtained by dualising the chain map. -/
abbrev singularCochainComplexMap (R : Type u) [Field R] {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SingularCochainComplex R Y ⟶ SingularCochainComplex R X :=
  HomologicalComplex.linearDualMap (singularChainComplexMap R f)

/-- Singular cohomology with coefficients in a field, defined as the homology of the singular
cochain complex — that is, by dualising the chain complex, not by dualising homology. -/
abbrev Cohomology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  (SingularCochainComplex R X).homology n

/-- Pullback in singular cohomology, induced by the dualised chain map. -/
def cohomologyMap (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) :
    Cohomology R Y n →ₗ[R] Cohomology R X n :=
  (HomologicalComplex.homologyMap (singularCochainComplexMap R f) n).hom

/-- Universal coefficients over a field: singular cohomology, defined by dualising the chain
complex, is canonically the linear dual of singular homology. This is a theorem here, not the
definition of cohomology. -/
def cohomologyEquivDualHomology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) :
    Cohomology R X n ≃ₗ[R] Module.Dual R (Homology R X n) :=
  (SingularChainComplex R X).linearDualHomologyEquiv n

/-- The map on relative homology induced by a map of pairs. -/
def relativeHomologyMap (R : Type u) [Field R] {X Y : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) : RelativeHomology R X n →ₗ[R] RelativeHomology R Y n :=
  ((relativeHomologyFunctor R n).map f).hom

/-- The quotient map from absolute homology to relative homology. -/
def relativeHomologyProjection (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    Homology R X.fst n ⟶ RelativeHomology R X n :=
  HomologicalComplex.homologyMap (relativeChainProjection R X) n

/-- The canonical map from relative cohomology to absolute cohomology, induced by the dual of
the projection from absolute chains to relative chains. -/
def relativeCohomologyToAbsolute (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    RelativeCohomology R X n →ₗ[R] Cohomology R X.fst n :=
  (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (relativeChainProjection R X)) n).hom

/-- Singular cohomology of `X` with support in `Z`, defined as `H^n(X, X ∖ Z)`. -/
abbrev CohomologyWithSupport (R : Type u) [Field R] (X : TopCat.{u})
    (Z : Set X) (n : ℕ) : ModuleCat.{u} R :=
  RelativeCohomology R (TopPair.ofSubset Zᶜ) n

/-- Forget support in `Z`, mapping a supported class to ordinary singular cohomology. -/
def forgetSupport (R : Type u) [Field R] (X : TopCat.{u}) (Z : Set X) (n : ℕ) :
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
def cohomologyWithSupportMap (R : Type u) [Field R] {X Y : TopCat.{u}}
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
def enlargeSupport (R : Type u) [Field R] (X : TopCat.{u}) {Z W : Set X}
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
lemma homologyMap_id (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) :
    homologyMap R n (𝟙 X) = LinearMap.id := by
  change (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
    (ModuleCat.of R R)).map (𝟙 X)).hom = LinearMap.id
  calc
    _ = ModuleCat.Hom.hom (𝟙 (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj X)) := congrArg ModuleCat.Hom.hom
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map_id X)
    _ = LinearMap.id := rfl

@[simp]
lemma homologyMap_comp (R : Type u) [Field R] {X Y Z : TopCat.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homologyMap R n (f ≫ g) = (homologyMap R n g).comp (homologyMap R n f) := by
  change (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
    (ModuleCat.of R R)).map (f ≫ g)).hom = _
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
lemma cohomologyMap_id (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) :
    cohomologyMap R n (𝟙 X) = LinearMap.id := by
  simp [cohomologyMap, singularCochainComplexMap]

@[simp]
lemma cohomologyMap_comp (R : Type u) [Field R] {X Y Z : TopCat.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    cohomologyMap R n (f ≫ g) =
      (cohomologyMap R n f).comp (cohomologyMap R n g) := by
  simp [cohomologyMap, singularCochainComplexMap, HomologicalComplex.homologyMap_comp]

@[simp]
lemma relativeHomologyMap_id (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    relativeHomologyMap R n (𝟙 X) = LinearMap.id := by
  change ((relativeHomologyFunctor R n).map (𝟙 X)).hom = LinearMap.id
  calc
    _ = ModuleCat.Hom.hom (𝟙 ((relativeHomologyFunctor R n).obj X)) :=
      congrArg ModuleCat.Hom.hom ((relativeHomologyFunctor R n).map_id X)
    _ = LinearMap.id := rfl

@[simp]
lemma relativeHomologyMap_comp (R : Type u) [Field R] {X Y Z : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativeHomologyMap R n (f ≫ g) =
      (relativeHomologyMap R n g).comp (relativeHomologyMap R n f) := by
  change ((relativeHomologyFunctor R n).map (f ≫ g)).hom = _
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
lemma relativeCohomologyMap_id (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    relativeCohomologyMap R n (𝟙 X) = LinearMap.id := by
  simp [relativeCohomologyMap, relativeCochainComplexMap]

@[simp]
lemma relativeCohomologyMap_comp (R : Type u) [Field R] {X Y Z : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativeCohomologyMap R n (f ≫ g) =
      (relativeCohomologyMap R n f).comp (relativeCohomologyMap R n g) := by
  simp [relativeCohomologyMap, relativeCochainComplexMap,
    HomologicalComplex.homologyMap_comp]

@[reassoc (attr := simp)]
lemma subspaceChainMap_relativeChainProjection (R : Type u) [Field R]
    (X : TopPair.{u}) :
    ((chainPairFunctor R).obj X).hom ≫ relativeChainProjection R X = 0 :=
  cokernel.condition _

/-- The short exact sequence of subspace, ambient, and relative singular chains. -/
def relativeChainShortComplex (R : Type u) [Field R] (X : TopPair.{u}) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk ((chainPairFunctor R).obj X).hom
    (relativeChainProjection R X)
    (subspaceChainMap_relativeChainProjection R X)

/-- The singular-chain map of a topological-pair inclusion is a monomorphism. -/
lemma relativeChainMap_mono (R : Type u) [Field R] (X : TopPair.{u}) :
    Mono ((chainPairFunctor R).obj X).hom := by
  let : Mono X.hom :=
    (TopCat.mono_iff_injective X.hom).mpr X.prop.injective
  change Mono (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).map X.hom)
  apply Functor.map_mono

/-- Singular chains of a pair form a short exact sequence.

See mathlib PR https://github.com/leanprover-community/mathlib4/pull/37659. -/
lemma relativeChainShortComplex_shortExact (R : Type u) [Field R] (X : TopPair.{u}) :
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
    preimageSupportPairMap (𝟙 X) Z = 𝟙 (TopPair.ofSubset Zᶜ) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

lemma preimageSupportPairMap_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : Set Z) :
    preimageSupportPairMap (f ≫ g) W =
      preimageSupportPairMap f (g ⁻¹' W) ≫ preimageSupportPairMap g W := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

@[simp]
lemma cohomologyWithSupportMap_id (R : Type u) [Field R] (X : TopCat.{u})
    (Z : Set X) (n : ℕ) :
    cohomologyWithSupportMap R n (𝟙 X) Z = LinearMap.id := by
  unfold cohomologyWithSupportMap
  rw [preimageSupportPairMap_id]
  exact relativeCohomologyMap_id R (TopPair.ofSubset Zᶜ) n

lemma cohomologyWithSupportMap_comp (R : Type u) [Field R]
    {X Y Z : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) (W : Set Z) :
    cohomologyWithSupportMap R n (f ≫ g) W =
      (cohomologyWithSupportMap R n f (g ⁻¹' W)).comp
        (cohomologyWithSupportMap R n g W) := by
  rw [cohomologyWithSupportMap, cohomologyWithSupportMap, cohomologyWithSupportMap,
    preimageSupportPairMap_comp, relativeCohomologyMap_comp]

@[simp]
lemma supportInclusionPairMap_rfl (X : TopCat.{u}) (Z : Set X) :
    supportInclusionPairMap X (Set.Subset.rfl : Z ⊆ Z) = 𝟙 (TopPair.ofSubset Zᶜ) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

lemma supportInclusionPairMap_trans (X : TopCat.{u}) {Z W U : Set X}
    (hZW : Z ⊆ W) (hWU : W ⊆ U) :
    supportInclusionPairMap X (hZW.trans hWU) =
      supportInclusionPairMap X hWU ≫ supportInclusionPairMap X hZW := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

@[simp]
lemma enlargeSupport_rfl (R : Type u) [Field R] (X : TopCat.{u}) (Z : Set X) (n : ℕ) :
    enlargeSupport R X (Set.Subset.rfl : Z ⊆ Z) n = LinearMap.id := by
  rw [enlargeSupport, supportInclusionPairMap_rfl, relativeCohomologyMap_id]

lemma enlargeSupport_trans (R : Type u) [Field R] (X : TopCat.{u}) {Z W U : Set X}
    (hZW : Z ⊆ W) (hWU : W ⊆ U) (n : ℕ) :
    enlargeSupport R X (hZW.trans hWU) n =
      (enlargeSupport R X hWU n).comp (enlargeSupport R X hZW n) := by
  rw [enlargeSupport, enlargeSupport, enlargeSupport, supportInclusionPairMap_trans,
    relativeCohomologyMap_comp]

/-- Over a field a continuous map is determined on cohomology by its effect on homology:
universal coefficients is natural, and an injective equivalence. -/
lemma cohomologyMap_eq_of_homologyMap_eq (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ)
    {f g : X ⟶ Y} (h : homologyMap R n f = homologyMap R n g) :
    cohomologyMap R n f = cohomologyMap R n g := by
  ext α
  refine (cohomologyEquivDualHomology R X n).injective (LinearMap.ext fun z => ?_)
  rw [cohomologyEquivDualHomology_cohomologyMap, cohomologyEquivDualHomology_cohomologyMap,
    h]

/-- Over a field a map of pairs is determined on relative cohomology by its effect on relative
homology. -/
lemma relativeCohomologyMap_eq_of_relativeHomologyMap_eq (R : Type u) [Field R]
    {X Y : TopPair.{u}} (n : ℕ) {f g : X ⟶ Y}
    (h : relativeHomologyMap R n f = relativeHomologyMap R n g) :
    relativeCohomologyMap R n f = relativeCohomologyMap R n g := by
  ext α
  refine (relativeCohomologyEquivDualHomology R X n).injective (LinearMap.ext fun z => ?_)
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap, h]

/-- Relative cohomology vanishes wherever relative homology does: the two are linked by the
universal-coefficient equivalence. -/
lemma relativeCohomology_subsingleton (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ)
    (h : Subsingleton (RelativeHomology R X n)) :
    Subsingleton (RelativeCohomology R X n) :=
  have : Subsingleton (Module.Dual R (RelativeHomology R X n)) :=
    ⟨fun φ ψ => LinearMap.ext fun x => by rw [h.elim x 0, map_zero, map_zero]⟩
  (relativeCohomologyEquivDualHomology R X n).toEquiv.subsingleton

/-- Relative cohomology is zero wherever relative homology is. -/
lemma relativeCohomology_isZero (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ)
    (h : IsZero (RelativeHomology R X n)) : IsZero (RelativeCohomology R X n) :=
  have := relativeCohomology_subsingleton R X n (ModuleCat.subsingleton_of_isZero h)
  ModuleCat.isZero_of_subsingleton _

end AlgebraicTopology.Singular
