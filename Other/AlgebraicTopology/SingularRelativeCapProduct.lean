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

public import Other.AlgebraicTopology.SingularCapProduct

/-!
# The relative singular cap product

This file carries the simplicial cap product over to singular chains of a topological pair. A
relative cochain, meaning one vanishing on the subspace, caps a relative chain to give an
absolute chain, well defined because the two chains that differ by a chain of the subspace are
capped to the same thing.

Descent to homology in both variables is proved separately: in the chain variable by the signed
boundary formula, and in the cochain variable by showing that the cap product with a relative
coboundary is a boundary. What comes out is the same-pair relative cap product on homology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial
open scoped Simplicial

universe u

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
  ext c
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
  ext c
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
      ((relativeChainProjection R X).f n).hom (Simplicial.boundary R n c) :=
  ConcreteCategory.congr_hom
    ((relativeChainProjection R X).comm (n + 1) n) c

/-- The pullback of a relative cochain to the subspace is zero. -/
lemma cochainMap_relativeCochainToAbsolute_eq_zero (X : TopPair.{u}) (n : ℕ)
    (phi : RelativeCochain R X n) :
    Simplicial.cochainMap R (TopCat.toSSet.map X.map) n
      (relativeCochainToAbsolute R X n phi) = 0 := by
  ext c
  have hz := congrArg (fun f ↦ f.f n)
    (subspaceChainMap_relativeChainProjection R X)
  have hc := ConcreteCategory.congr_hom hz c
  change phi (((relativeChainProjection R X).f n).hom
    ((((chainPairFunctor R).obj X).hom.f n).hom c)) = 0
  rw [show ((relativeChainProjection R X).f n).hom
    ((((chainPairFunctor R).obj X).hom.f n).hom c) = 0 from hc]
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
  refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
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
        exact h)) :=
  CokernelCofork.mapIsColimit _
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
      ModuleCat.ofHom (relativeCapLift R X p q phi) :=
  (Cofork.IsColimit.π_desc
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
  exact ModuleCat.hom_ext (relativeCapLift_add R X p q phi psi)

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
  exact ModuleCat.hom_ext (relativeCapLift_smul R X p q a phi)

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
      relativeCapLift R X p q phi c :=
  ConcreteCategory.congr_hom
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
  ext z
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
  · refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
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
  · refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
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
  · exact ModuleCat.hom_ext (boundary_relativeCap_eq_of_cocycle R X p q phi hphi)

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
        (Simplicial.reassocChain R p q c) :=
  ConcreteCategory.congr_hom
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
  ext z
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
  exact ModuleCat.hom_ext (relativeCap_coboundary_eq R X p q phi)

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
      (relativeCoboundary_relativeCoboundary R X p phi) = 0 :=
  congrArg ModuleCat.Hom.hom
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
  have hdeta : phi - psi = deta := Subtype.ext h
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
    ext c
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
  refine Subtype.ext (LinearMap.ext fun c => ?_)
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
        ext c
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
