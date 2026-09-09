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

public import Other.AlgebraicTopology.ChartLocalFundamentalClass
public import Other.AlgebraicTopology.EuclideanLocalHomology
public import Other.AlgebraicTopology.SingularHomologyVanishing
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Lifting local homology classes to global fundamental classes

For a pair `A ⊆ X`, the long exact sequence contains

`H_{n+1}(A) ⟶ H_{n+1}(X) ⟶ H_{n+1}(X,A) ⟶ H_n(A)`.

This file packages the exact consequences needed in the construction of a global fundamental
class. A relative class whose boundary vanishes has a global lift; if the homology of `A` in
degree `n + 1` vanishes, that lift is unique. When the entire boundary map vanishes, the
absolute-to-relative map is a canonical linear equivalence.

Specializing to `A = M ∖ {x}` gives a construction of a global class from one prescribed local
homology class. In the manifold application the remaining geometric input is not hidden in this
definition: one must prove

* `H_{n+1}(M ∖ {x}; ℚ) = 0` (top homology of the punctured, hence noncompact, manifold), and
* that the boundary of the locally coherent orientation class at `x` vanishes.

Those are precisely the local-to-global orientation theorems normally proved by relative
Mayer–Vietoris. Neither a singular Mayer–Vietoris sequence nor a triangulation theorem is
currently available in Mathlib. In particular, this file does not assume an `∃!` global class
or store a fundamental class as data.  The last section reduces both geometric inputs further:

* boundary vanishing follows from injectivity of puncture inclusion one degree lower; and
* top homology vanishing follows from a bounded chain model quasi-isomorphic to the punctured
  space.

Thus the remaining missing primitive is exactly a dimension-controlled locally finite
good-cover or triangulation comparison for manifolds, not any fundamental-class datum.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
/-- If `H_{n+1}(A; ℚ)` vanishes, the map `H_{n+1}(X; ℚ) ⟶ H_{n+1}(X,A; ℚ)` is
injective. This is the left half of the long exact sequence criterion for a unique global lift.
-/
public theorem relativeHomologyProjection_injective_of_isZero_subspace
    (X : TopPair) (n : ℕ) (hA : IsZero (Homology ℚ X.snd (n + 1))) :
    Function.Injective (relativeHomologyProjection ℚ X (n + 1)).hom := by
  intro z z' hzz'
  have hker :
      (relativeHomologyProjection ℚ X (n + 1)).hom (z - z') = 0 := by
    rw [map_sub, hzz', sub_self]
  have hexact :=
    (ShortComplex.moduleCat_exact_iff _).mp
      (relativeSingular_homology_exact_ambient X (n + 1))
  obtain ⟨a, ha⟩ := hexact (z - z') hker
  have ha0 : a = 0 := (ModuleCat.subsingleton_of_isZero hA).elim _ _
  have hsub : z - z' = 0 := ha.symm.trans (by simp [ha0])
  exact sub_eq_zero.mp hsub

set_option backward.isDefEq.respectTransparency false in
/-- Degree-unrestricted form of the left exact-sequence criterion: if the subspace has no
homology in degree `n`, absolute-to-relative homology is injective in degree `n`. -/
public theorem relativeHomologyProjection_injective_of_isZero_subspace_degree
    (X : TopPair) (n : ℕ) (hA : IsZero (Homology ℚ X.snd n)) :
    Function.Injective (relativeHomologyProjection ℚ X n).hom := by
  intro z z' hzz'
  have hker : (relativeHomologyProjection ℚ X n).hom (z - z') = 0 := by
    rw [map_sub, hzz', sub_self]
  have hexact :=
    (ShortComplex.moduleCat_exact_iff _).mp
      (relativeSingular_homology_exact_ambient X n)
  obtain ⟨a, ha⟩ := hexact (z - z') hker
  have ha0 : a = 0 := (ModuleCat.subsingleton_of_isZero hA).elim _ _
  have hsub : z - z' = 0 := ha.symm.trans (by simp [ha0])
  exact sub_eq_zero.mp hsub

/-- If the connecting morphism vanishes, every relative class in degree `n + 1` has a global
lift. This is the right half of the long exact sequence criterion. -/
public theorem relativeHomologyProjection_surjective_of_boundary_eq_zero
    (X : TopPair) (n : ℕ) (hδ : relativeSingularBoundary X n = 0) :
    Function.Surjective (relativeHomologyProjection ℚ X (n + 1)).hom := by
  have hexact :=
    (ShortComplex.moduleCat_exact_iff _).mp
      (relativeSingular_homology_exact_relative X n)
  intro c
  apply hexact c
  simpa using ConcreteCategory.congr_hom hδ c

/-- A relative class with zero boundary has an absolute lift. This is a consequence of the
long exact sequence, rather than an existence assumption. -/
public theorem exists_absoluteClass_of_boundary_eq_zero
    (X : TopPair) (n : ℕ) (c : RelativeHomology ℚ X (n + 1))
    (hc : (relativeSingularBoundary X n).hom c = 0) :
    ∃ z : Homology ℚ X.fst (n + 1),
      (relativeHomologyProjection ℚ X (n + 1)).hom z = c :=
  (ShortComplex.moduleCat_exact_iff _).mp
    (relativeSingular_homology_exact_relative X n) c hc

/-- A linear map out of a cyclic relative homology group vanishes as soon as it vanishes on the
specified generator. Applied to the connecting morphism, this turns the boundary calculation
for the oriented local generator into surjectivity of global-to-local restriction. -/
public theorem relativeSingularBoundary_eq_zero_of_span_eq_top
    (X : TopPair) (n : ℕ) (c : RelativeHomology ℚ X (n + 1))
    (hspan : Submodule.span ℚ {c} = ⊤)
    (hc : (relativeSingularBoundary X n).hom c = 0) :
    relativeSingularBoundary X n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro z hz
  rw [Set.mem_singleton_iff.mp hz]
  exact hc

set_option backward.isDefEq.respectTransparency false in
/-- If inclusion of the subspace into the ambient space is injective on homology in degree `n`,
then the connecting morphism of the pair vanishes.  This is the exact-sequence formulation of
the geometric boundary calculation and makes no reference to a chosen relative class. -/
public theorem relativeSingularBoundary_eq_zero_of_injective_subspaceMap
    (X : TopPair) (n : ℕ)
    (hinjective : Function.Injective
      (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).obj X).hom n).hom) :
    relativeSingularBoundary X n = 0 := by
  let i := HomologicalComplex.homologyMap ((chainPairFunctor ℚ).obj X).hom n
  let : Mono i := (ModuleCat.mono_iff_injective i).mpr hinjective
  have hcomp : relativeSingularBoundary X n ≫ i = 0 :=
    (relativeSingularChainShortComplex_shortExact X).δ_comp
      (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))
  apply (cancel_mono i).mp
  rw [hcomp, zero_comp]

/-- The absolute lift supplied by exactness for a relative cycle. The existence proof is the
long exact sequence theorem above; the lift is not passed as data. -/
public def absoluteClassOfBoundaryCycle
    (X : TopPair) (n : ℕ) (c : RelativeHomology ℚ X (n + 1))
    (hc : (relativeSingularBoundary X n).hom c = 0) :
    Homology ℚ X.fst (n + 1) :=
  Classical.choose (exists_absoluteClass_of_boundary_eq_zero X n c hc)

@[simp]
public theorem relativeHomologyProjection_absoluteClassOfBoundaryCycle
    (X : TopPair) (n : ℕ) (c : RelativeHomology ℚ X (n + 1))
    (hc : (relativeSingularBoundary X n).hom c = 0) :
    (relativeHomologyProjection ℚ X (n + 1)).hom
      (absoluteClassOfBoundaryCycle X n c hc) = c :=
  Classical.choose_spec (exists_absoluteClass_of_boundary_eq_zero X n c hc)

/-- A lift of a relative class is unique when the subspace has no homology in the same degree.
-/
public theorem absoluteClass_unique_of_isZero_subspace
    (X : TopPair) (n : ℕ) (hA : IsZero (Homology ℚ X.snd (n + 1)))
    {z z' : Homology ℚ X.fst (n + 1)}
    (h : (relativeHomologyProjection ℚ X (n + 1)).hom z =
      (relativeHomologyProjection ℚ X (n + 1)).hom z') : z = z' :=
  relativeHomologyProjection_injective_of_isZero_subspace X n hA h

/-- If the adjacent obstruction group and map in the pair sequence vanish, absolute and
relative homology are canonically linearly equivalent via the quotient map. -/
public def relativeHomologyProjectionLinearEquiv
    (X : TopPair) (n : ℕ) (hA : IsZero (Homology ℚ X.snd (n + 1)))
    (hδ : relativeSingularBoundary X n = 0) :
    Homology ℚ X.fst (n + 1) ≃ₗ[ℚ] RelativeHomology ℚ X (n + 1) :=
  LinearEquiv.ofBijective (relativeHomologyProjection ℚ X (n + 1)).hom
    ⟨relativeHomologyProjection_injective_of_isZero_subspace X n hA,
      relativeHomologyProjection_surjective_of_boundary_eq_zero X n hδ⟩

/-- Generator-level form of `relativeHomologyProjectionLinearEquiv`: it is enough to calculate
that the connecting map kills one spanning local orientation class. -/
public def relativeHomologyProjectionLinearEquivOfGenerator
    (X : TopPair) (n : ℕ) (hA : IsZero (Homology ℚ X.snd (n + 1)))
    (c : RelativeHomology ℚ X (n + 1)) (hspan : Submodule.span ℚ {c} = ⊤)
    (hc : (relativeSingularBoundary X n).hom c = 0) :
    Homology ℚ X.fst (n + 1) ≃ₗ[ℚ] RelativeHomology ℚ X (n + 1) :=
  relativeHomologyProjectionLinearEquiv X n hA
    (relativeSingularBoundary_eq_zero_of_span_eq_top X n c hspan hc)

@[simp]
public theorem relativeHomologyProjectionLinearEquiv_apply
    (X : TopPair) (n : ℕ) (hA : IsZero (Homology ℚ X.snd (n + 1)))
    (hδ : relativeSingularBoundary X n = 0)
    (z : Homology ℚ X.fst (n + 1)) :
    relativeHomologyProjectionLinearEquiv X n hA hδ z =
      (relativeHomologyProjection ℚ X (n + 1)).hom z :=
  rfl

section PointComplement

variable {M : Type} [TopologicalSpace M]

/-- Restrict an absolute homology class to local homology at a point. -/
public abbrev pointLocalHomologyRestriction (n : ℕ) (x : M) :
    Homology ℚ (TopCat.of M) n →ₗ[ℚ]
      RelativeHomology ℚ (pointComplementPair x) n :=
  (relativeHomologyProjection ℚ (pointComplementPair x) n).hom

/-- Inclusion of the point complement into the ambient space, on rational homology. -/
public abbrev pointComplementHomologyInclusion (n : ℕ) (x : M) :
    Homology ℚ (pointComplementPair x).snd n →ₗ[ℚ]
      Homology ℚ (TopCat.of M) n :=
  (HomologicalComplex.homologyMap
    ((chainPairFunctor ℚ).obj (pointComplementPair x)).hom n).hom

/-- Injectivity of point-complement inclusion one degree below a local class forces its
connecting boundary to vanish.  This is the canonical map property supplied by the usual
punctured-manifold Mayer--Vietoris argument. -/
public theorem pointRelativeSingularBoundary_eq_zero_of_injective_complementInclusion
    (n : ℕ) (x : M)
    (hinjective : Function.Injective (pointComplementHomologyInclusion n x)) :
    relativeSingularBoundary (pointComplementPair x) n = 0 :=
  relativeSingularBoundary_eq_zero_of_injective_subspaceMap
    (pointComplementPair x) n hinjective

/-- Construct a global class with prescribed local value at `x`, when that local value has zero
boundary in the punctured space. The global class is supplied by exactness, not passed as data.
-/
public def globalClassOfPointLocalClass (n : ℕ) (x : M)
    (c : RelativeHomology ℚ (pointComplementPair x) (n + 1))
    (hc : (relativeSingularBoundary (pointComplementPair x) n).hom c = 0) :
    Homology ℚ (TopCat.of M) (n + 1) :=
  absoluteClassOfBoundaryCycle (pointComplementPair x) n c hc

/-- Construct the global lift from injectivity of puncture inclusion one degree lower.  Unlike
`globalClassOfPointLocalClass`, this formulation does not ask for a boundary calculation on the
chosen local class. -/
public def globalClassOfPointLocalClassOfInjectiveComplementInclusion
    (n : ℕ) (x : M)
    (hinjective : Function.Injective (pointComplementHomologyInclusion n x))
    (c : RelativeHomology ℚ (pointComplementPair x) (n + 1)) :
    Homology ℚ (TopCat.of M) (n + 1) :=
  globalClassOfPointLocalClass n x c <| by
    have hδ := pointRelativeSingularBoundary_eq_zero_of_injective_complementInclusion
      n x hinjective
    simpa using ConcreteCategory.congr_hom hδ c

@[simp]
public theorem pointLocalHomologyRestriction_globalClassOfPointLocalClass
    (n : ℕ) (x : M)
    (c : RelativeHomology ℚ (pointComplementPair x) (n + 1))
    (hc : (relativeSingularBoundary (pointComplementPair x) n).hom c = 0) :
    pointLocalHomologyRestriction (n + 1) x
      (globalClassOfPointLocalClass n x c hc) = c :=
  relativeHomologyProjection_absoluteClassOfBoundaryCycle
    (pointComplementPair x) n c hc

@[simp]
public theorem pointLocalHomologyRestriction_globalClassOfPointLocalClassOfInjectiveComplementInclusion
    (n : ℕ) (x : M)
    (hinjective : Function.Injective (pointComplementHomologyInclusion n x))
    (c : RelativeHomology ℚ (pointComplementPair x) (n + 1)) :
    pointLocalHomologyRestriction (n + 1) x
      (globalClassOfPointLocalClassOfInjectiveComplementInclusion n x hinjective c) = c := by
  unfold globalClassOfPointLocalClassOfInjectiveComplementInclusion
  apply pointLocalHomologyRestriction_globalClassOfPointLocalClass

set_option backward.isDefEq.respectTransparency false in
/-- The constructed class is the unique global class with the prescribed local value. -/
public theorem eq_globalClassOfPointLocalClass_of_restrict_eq
    (n : ℕ) (x : M)
    (hpunctured : IsZero (Homology ℚ (pointComplementPair x).snd (n + 1)))
    (c : RelativeHomology ℚ (pointComplementPair x) (n + 1))
    (hc : (relativeSingularBoundary (pointComplementPair x) n).hom c = 0)
    (z : Homology ℚ (TopCat.of M) (n + 1))
    (hz : pointLocalHomologyRestriction (n + 1) x z = c) :
    z = globalClassOfPointLocalClass n x c hc := by
  apply relativeHomologyProjection_injective_of_isZero_subspace
    (pointComplementPair x) n hpunctured
  exact hz.trans (pointLocalHomologyRestriction_globalClassOfPointLocalClass n x c hc).symm

/-- A bounded chain model for the punctured space supplies the top-homology vanishing needed
for uniqueness of a global lift. -/
public theorem pointComplementHomology_isZero_of_bounded_chainModel
    (n : ℕ) (x : M) (C : ChainComplex (ModuleCat ℚ) ℕ)
    (f : C ⟶ ((singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj (pointComplementPair x).snd)
    [QuasiIso f] (hC : IsZero (C.X n)) :
    IsZero (Homology ℚ (pointComplementPair x).snd n) :=
  homology_isZero_of_bounded_quasiIso_chainModel
    (pointComplementPair x).snd C f n hC

set_option backward.isDefEq.respectTransparency false in
/-- The construction from puncture-inclusion injectivity is unique when the punctured space has
a bounded chain model in top degree.  These are the two standard outputs of a
dimension-controlled manifold triangulation or good-cover comparison. -/
public theorem eq_globalClassOfPointLocalClassOfInjectiveComplementInclusion_of_bounded_chainModel
    (n : ℕ) (x : M)
    (hinjective : Function.Injective (pointComplementHomologyInclusion n x))
    (c : RelativeHomology ℚ (pointComplementPair x) (n + 1))
    (C : ChainComplex (ModuleCat ℚ) ℕ)
    (f : C ⟶ ((singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj (pointComplementPair x).snd)
    [QuasiIso f] (hC : IsZero (C.X (n + 1)))
    (z : Homology ℚ (TopCat.of M) (n + 1))
    (hz : pointLocalHomologyRestriction (n + 1) x z = c) :
    z = globalClassOfPointLocalClassOfInjectiveComplementInclusion n x hinjective c := by
  apply relativeHomologyProjection_injective_of_isZero_subspace
    (pointComplementPair x) n
    (pointComplementHomology_isZero_of_bounded_chainModel (n + 1) x C f hC)
  exact hz.trans
    (pointLocalHomologyRestriction_globalClassOfPointLocalClassOfInjectiveComplementInclusion
      n x hinjective c).symm

end PointComplement

end AlgebraicTopology.Singular
