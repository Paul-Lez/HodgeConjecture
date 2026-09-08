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

public import HodgeConjecture.Other.AlgebraicTopology.SingularCapProduct
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# A relative cap product for a topological triad

For subsets `A B ⊆ X`, the ordinary chain-level triad cap product has the form

`C^p(X, A) ⊗ C_{p+q}(X, A ∪ B) ⟶ C_q(X, B)`.

This file constructs the part of this pairing which does not require an excision theorem.  Its
source is the honest cokernel

`C_*^{sum}(X; A, B) := coker(C_*(A) ⊕ C_*(B) ⟶ C_*(X))`.

The cap product vanishes on both summands: on `A` because the cochain is relative to `A`, and
on `B` because its value is a chain in `B`, which vanishes after projection to `C_*(X, B)`.
Consequently it descends to a chain map (with the usual grading sign), and then to homology.

We deliberately do **not** identify this sum quotient with `C_*(X, A ∪ B)`.  Such an
identification needs the small-chain/subdivision proof of excision for the cover of `A ∪ B`
by `A` and `B`; it is not a formal cokernel identity.  The definitions here therefore expose the
exact comparison boundary needed to obtain the customary triad pairing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

/-- The map `C_*(A) ⊕ C_*(B) ⟶ C_*(X)` induced by the two subset inclusions. -/
noncomputable def triadSubspaceChainMap (X : TopCat.{u}) (A B : Set X) :
    (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
          (TopPair.ofSubset A).snd ⊞
        ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
          (TopPair.ofSubset B).snd) ⟶
      ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X :=
  biprod.desc ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom
    ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom

/-- The sum-relative chain complex
`coker(C_*(A) ⊕ C_*(B) ⟶ C_*(X))`.

This is a chain model for the source of the triad cap product.  No comparison with
`C_*(X, A ∪ B)` is built into the definition. -/
noncomputable def triadRelativeChainComplex (X : TopCat.{u}) (A B : Set X) :
    ChainCategory R :=
  cokernel (triadSubspaceChainMap R X A B)

/-- Projection from ambient chains to the sum-relative triad chain complex. -/
noncomputable def triadRelativeChainProjection (X : TopCat.{u}) (A B : Set X) :
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X ⟶
      triadRelativeChainComplex R X A B :=
  cokernel.π (triadSubspaceChainMap R X A B)

@[reassoc (attr := simp)]
lemma triadSubspaceChainMap_triadRelativeChainProjection
    (X : TopCat.{u}) (A B : Set X) :
    triadSubspaceChainMap R X A B ≫ triadRelativeChainProjection R X A B = 0 :=
  cokernel.condition _

/-- Chains in a fixed degree of the sum-relative triad chain complex. -/
abbrev TriadRelativeChainGroup (X : TopCat.{u}) (A B : Set X) (n : ℕ) :
    ModuleCat.{u} R :=
  (triadRelativeChainComplex R X A B).X n

/-- Homology of the sum-relative triad chain complex. -/
abbrev TriadRelativeHomology (X : TopCat.{u}) (A B : Set X) (n : ℕ) :
    ModuleCat.{u} R :=
  (triadRelativeChainComplex R X A B).homology n

/-- The boundary on the sum-relative triad chain complex. -/
def triadRelativeBoundary (X : TopCat.{u}) (A B : Set X) (n : ℕ) :
    TriadRelativeChainGroup R X A B (n + 1) →ₗ[R]
      TriadRelativeChainGroup R X A B n :=
  ((triadRelativeChainComplex R X A B).d (n + 1) n).hom

/-! ## Descent of cap product through both subspaces -/

/-- Cap a cochain relative to `A` with an ambient chain, then project the result modulo
chains in `B`. -/
def triadCapLiftHom (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).obj X).X (p + q) ⟶
      ((relativeChainFunctor R).obj (TopPair.ofSubset B)).X q :=
  ModuleCat.ofHom (relativeCapLift R (TopPair.ofSubset A) p q phi) ≫
    (relativeChainProjection R (TopPair.ofSubset B)).f q

/-- The lifted triad cap product as a linear map. -/
def triadCapLift (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    Simplicial.ChainGroup R (TopCat.toSSet.obj X) (p + q) →ₗ[R]
      RelativeChainGroup R (TopPair.ofSubset B) q :=
  (triadCapLiftHom R X A B p q phi).hom

set_option backward.isDefEq.respectTransparency false in
/-- The ambient lift vanishes on chains in `A`, because the cochain is relative to `A`. -/
lemma subspaceAChainMap_triadCapLiftHom_eq_zero
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom.f (p + q) ≫
      triadCapLiftHom R X A B p q phi = 0 := by
  rw [triadCapLiftHom, ← Category.assoc,
    subspaceChainMap_relativeCapLift_eq_zero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The ambient lift vanishes on chains in `B`: naturality says the cap is again a chain
in `B`, and the target projection kills such chains. -/
lemma subspaceBChainMap_triadCapLiftHom_eq_zero
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom.f (p + q) ≫
      triadCapLiftHom R X A B p q phi = 0 := by
  change (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map)
      (ModuleCat.of R R)).f (p + q) ≫
    ModuleCat.ofHom (relativeCapLift R (TopPair.ofSubset A) p q phi) ≫
      (relativeChainProjection R (TopPair.ofSubset B)).f q = 0
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hcap := Simplicial.cap_naturality R
    (TopCat.toSSet.map (TopPair.ofSubset B).map) p q
    (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi) c
  have hprojection := congrArg (fun f ↦ f.f q)
    (subspaceChainMap_relativeChainProjection R (TopPair.ofSubset B))
  have hprojection' :
      (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map)
          (ModuleCat.of R R)).f q ≫
        (relativeChainProjection R (TopPair.ofSubset B)).f q = 0 := by
    change (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map)
        (ModuleCat.of R R)).f q ≫
      (relativeChainProjection R (TopPair.ofSubset B)).f q = 0 at hprojection
    exact hprojection
  have hzero' := ConcreteCategory.congr_hom hprojection'
    (Simplicial.cap R p q
      (Simplicial.cochainMap R (TopCat.toSSet.map (TopPair.ofSubset B).map) p
        (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi)) c)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] at hzero'
  have hprojected := congrArg
    (fun z ↦ ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom z) hcap
  change ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
    (Simplicial.cap R p q (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi)
      (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map)
        (ModuleCat.of R R)).f (p + q)).hom c)) = 0
  exact hprojected.symm.trans hzero'

set_option backward.isDefEq.respectTransparency false in
/-- The map `C_*(A) ⊕ C_*(B) ⟶ C_*(X)` is annihilated by the lifted triad cap
product. -/
lemma triadSubspaceChainMap_triadCapLiftHom_eq_zero
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (triadSubspaceChainMap R X A B).f (p + q) ≫
      triadCapLiftHom R X A B p q phi = 0 := by
  change (biprod.desc
      ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom
      ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom).f (p + q) ≫
        triadCapLiftHom R X A B p q phi = 0
  apply HomologicalComplex.biprodX_ext_from
  · rw [← Category.assoc, HomologicalComplex.biprod_inl_desc_f,
      subspaceAChainMap_triadCapLiftHom_eq_zero]
    simp
  · rw [← Category.assoc, HomologicalComplex.biprod_inr_desc_f,
      subspaceBChainMap_triadCapLiftHom_eq_zero]
    simp

/-- Each component of the triad projection has the defining cokernel universal property. -/
noncomputable def triadRelativeChainProjectionComponentIsCokernel
    (X : TopCat.{u}) (A B : Set X) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (f := (triadSubspaceChainMap R X A B).f n)
      ((triadRelativeChainProjection R X A B).f n) (by
        have h := congrArg (fun f ↦ f.f n)
          (triadSubspaceChainMap_triadRelativeChainProjection R X A B)
        exact h)) := by
  exact CokernelCofork.mapIsColimit _
    (cokernelIsCokernel (triadSubspaceChainMap R X A B))
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)

/-- The triad cap product, descended through the sum-relative quotient in the chain
variable. -/
noncomputable def triadCapHom (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    TriadRelativeChainGroup R X A B (p + q) ⟶
      RelativeChainGroup R (TopPair.ofSubset B) q :=
  (triadRelativeChainProjectionComponentIsCokernel R X A B (p + q)).desc
    (CokernelCofork.ofπ (triadCapLiftHom R X A B p q phi)
      (triadSubspaceChainMap_triadCapLiftHom_eq_zero R X A B p q phi))

/-- The descended triad cap product as a linear map. -/
noncomputable def triadCap (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    TriadRelativeChainGroup R X A B (p + q) →ₗ[R]
      RelativeChainGroup R (TopPair.ofSubset B) q :=
  (triadCapHom R X A B p q phi).hom

/-- Capping a projected ambient representative agrees with the lifted triad cap product. -/
@[reassoc]
lemma triadRelativeChainProjection_triadCapHom
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (triadRelativeChainProjection R X A B).f (p + q) ≫
      triadCapHom R X A B p q phi = triadCapLiftHom R X A B p q phi := by
  exact (Cofork.IsColimit.π_desc
    (triadRelativeChainProjectionComponentIsCokernel R X A B (p + q))
    (t := CokernelCofork.ofπ (triadCapLiftHom R X A B p q phi)
      (triadSubspaceChainMap_triadCapLiftHom_eq_zero R X A B p q phi))).trans
    (CokernelCofork.π_ofπ _ _ _)

@[simp]
lemma triadCap_projection_apply
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) (p + q)) :
    triadCap R X A B p q phi
        ((triadRelativeChainProjection R X A B).f (p + q) c) =
      triadCapLift R X A B p q phi c := by
  exact ConcreteCategory.congr_hom
    (triadRelativeChainProjection_triadCapHom R X A B p q phi) c

set_option backward.isDefEq.respectTransparency false in
lemma triadCapLiftHom_add
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi psi : RelativeCochain R (TopPair.ofSubset A) p) :
    triadCapLiftHom R X A B p q (phi + psi) =
      triadCapLiftHom R X A B p q phi +
        triadCapLiftHom R X A B p q psi := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
      (relativeCapLift R (TopPair.ofSubset A) p q (phi + psi) c) =
    ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
        (relativeCapLift R (TopPair.ofSubset A) p q phi c) +
      ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
        (relativeCapLift R (TopPair.ofSubset A) p q psi c)
  rw [LinearMap.congr_fun
    (relativeCapLift_add R (TopPair.ofSubset A) p q phi psi) c,
    LinearMap.add_apply, map_add]

set_option backward.isDefEq.respectTransparency false in
lemma triadCapLiftHom_smul
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) (a : R)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    triadCapLiftHom R X A B p q (a • phi) =
      a • triadCapLiftHom R X A B p q phi := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
      (relativeCapLift R (TopPair.ofSubset A) p q (a • phi) c) =
    a • ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
      (relativeCapLift R (TopPair.ofSubset A) p q phi c)
  rw [LinearMap.congr_fun
    (relativeCapLift_smul R (TopPair.ofSubset A) p q a phi) c,
    LinearMap.smul_apply, map_smul]

set_option backward.isDefEq.respectTransparency false in
lemma triadCapHom_add
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi psi : RelativeCochain R (TopPair.ofSubset A) p) :
    triadCapHom R X A B p q (phi + psi) =
      triadCapHom R X A B p q phi + triadCapHom R X A B p q psi := by
  apply Cofork.IsColimit.hom_ext
    (triadRelativeChainProjectionComponentIsCokernel R X A B (p + q))
  change (triadRelativeChainProjection R X A B).f (p + q) ≫
      triadCapHom R X A B p q (phi + psi) =
    (triadRelativeChainProjection R X A B).f (p + q) ≫
      (triadCapHom R X A B p q phi + triadCapHom R X A B p q psi)
  rw [triadRelativeChainProjection_triadCapHom, Preadditive.comp_add,
    triadRelativeChainProjection_triadCapHom,
    triadRelativeChainProjection_triadCapHom, triadCapLiftHom_add]

set_option backward.isDefEq.respectTransparency false in
lemma triadCapHom_smul
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) (a : R)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    triadCapHom R X A B p q (a • phi) =
      a • triadCapHom R X A B p q phi := by
  apply Cofork.IsColimit.hom_ext
    (triadRelativeChainProjectionComponentIsCokernel R X A B (p + q))
  change (triadRelativeChainProjection R X A B).f (p + q) ≫
      triadCapHom R X A B p q (a • phi) =
    (triadRelativeChainProjection R X A B).f (p + q) ≫
      (a • triadCapHom R X A B p q phi)
  rw [triadRelativeChainProjection_triadCapHom, Linear.comp_smul,
    triadRelativeChainProjection_triadCapHom,
    triadCapLiftHom_smul]

/-- Triad cap product, bilinear in a relative cochain and a sum-relative chain. -/
noncomputable def triadCapLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    RelativeCochain R (TopPair.ofSubset A) p →ₗ[R]
      (TriadRelativeChainGroup R X A B (p + q) →ₗ[R]
        RelativeChainGroup R (TopPair.ofSubset B) q) where
  toFun phi := triadCap R X A B p q phi
  map_add' phi psi := congrArg ModuleCat.Hom.hom
    (triadCapHom_add R X A B p q phi psi)
  map_smul' a phi := congrArg ModuleCat.Hom.hom
    (triadCapHom_smul R X A B p q a phi)

@[simp]
lemma triadCapLinear_apply
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    triadCapLinear R X A B p q phi = triadCap R X A B p q phi :=
  rfl

/-- The triad quotient boundary of a projected ambient chain is the projection of its
ambient boundary. -/
lemma triadRelativeBoundary_projection
    (X : TopCat.{u}) (A B : Set X) (n : ℕ)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) (n + 1)) :
    triadRelativeBoundary R X A B n
        (((triadRelativeChainProjection R X A B).f (n + 1)).hom c) =
      ((triadRelativeChainProjection R X A B).f n).hom
        (Simplicial.boundary R n c) := by
  exact ConcreteCategory.congr_hom
    ((triadRelativeChainProjection R X A B).comm (n + 1) n) c

set_option backward.isDefEq.respectTransparency false in
/-- For a relative cocycle, the lifted triad cap product satisfies the signed boundary
identity before quotienting the chain variable. -/
theorem boundary_triadCapLift_eq_of_cocycle
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    (relativeBoundary R (TopPair.ofSubset B) q).comp
        (triadCapLift R X A B p (q + 1) phi) =
      (-1 : R) ^ p •
        (triadCapLift R X A B p q phi).comp
          (Simplicial.boundary R (p + q)) := by
  apply LinearMap.ext
  intro c
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  have hboundary := ConcreteCategory.congr_hom
    ((relativeChainProjection R (TopPair.ofSubset B)).comm (q + 1) q)
    (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)
  have habsolute := LinearMap.congr_fun
    (boundary_relativeCapLift_eq_of_cocycle R (TopPair.ofSubset A) p q phi hphi) c
  have hprojected := congrArg
    (fun z ↦ ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom z) habsolute
  change relativeBoundary R (TopPair.ofSubset B) q
      (((relativeChainProjection R (TopPair.ofSubset B)).f (q + 1)).hom
        (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) = _
  calc
    _ = ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
        (Simplicial.boundary R q
          (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) := hboundary
    _ = ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
        ((-1 : R) ^ p • relativeCapLift R (TopPair.ofSubset A) p q phi
          (Simplicial.boundary R (p + q) c)) := hprojected
    _ = _ := by rw [map_smul]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a relative cocycle, the descended triad cap product intertwines the source and
target boundaries up to the conventional sign. -/
theorem boundary_triadCap_eq_of_cocycle
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    (relativeBoundary R (TopPair.ofSubset B) q).comp
        (triadCap R X A B p (q + 1) phi) =
      (-1 : R) ^ p •
        (triadCap R X A B p q phi).comp
          (triadRelativeBoundary R X A B (p + q)) := by
  apply LinearMap.ext
  intro z
  let π := (triadRelativeChainProjection R X A B).f (p + q + 1)
  let _ : Epi π := Cofork.IsColimit.epi
    (triadRelativeChainProjectionComponentIsCokernel R X A B (p + q + 1))
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance z
  dsimp only [π]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  erw [triadCap_projection_apply R X A B p (q + 1) phi c,
    triadRelativeBoundary_projection R X A B (p + q) c,
    triadCap_projection_apply R X A B p q phi
      (Simplicial.boundary R (p + q) c)]
  exact LinearMap.congr_fun
    (boundary_triadCapLift_eq_of_cocycle R X A B p q phi hphi) c

/-! ## The sum-relative triad cap product on homology -/

/-- The explicit triad cap morphism ending in degree zero. -/
noncomputable def triadCapShortComplexHomZero
    (X : TopCat.{u}) (A B : Set X) (p : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    (triadRelativeChainComplex R X A B).sc' (p + 1) p
        ((ComplexShape.down ℕ).next p) ⟶
      ((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc' 1 0 0 := by
  let s : R := (-1 : R) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine
    { τ₁ := ModuleCat.ofHom (s • triadCap R X A B p 1 phi)
      τ₂ := triadCapHom R X A B p 0 phi
      τ₃ := 0
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change relativeBoundary R (TopPair.ofSubset B) 0
        (s • triadCap R X A B p 1 phi c) =
      triadCap R X A B p 0 phi (triadRelativeBoundary R X A B p c)
    rw [map_smul]
    have h := LinearMap.congr_fun
      (boundary_triadCap_eq_of_cocycle R X A B p 0 phi hphi) c
    change relativeBoundary R (TopPair.ofSubset B) 0
        (triadCap R X A B p 1 phi c) =
      s • triadCap R X A B p 0 phi
        (triadRelativeBoundary R X A B p c) at h
    simpa [s, hs, smul_smul] using congrArg (fun z ↦ s • z) h
  · change triadCapHom R X A B p 0 phi ≫
        ((relativeChainFunctor R).obj (TopPair.ofSubset B)).d 0 0 =
      (triadRelativeChainComplex R X A B).d p
          ((ComplexShape.down ℕ).next p) ≫ 0
    rw [(((relativeChainFunctor R).obj (TopPair.ofSubset B)).shape 0 0 (by simp)),
      comp_zero, comp_zero]

/-- The explicit triad cap morphism ending in a positive degree. -/
noncomputable def triadCapShortComplexHomSucc
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    (triadRelativeChainComplex R X A B).sc'
        (p + ((q + 1) + 1)) (p + (q + 1)) (p + q) ⟶
      ((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc'
        ((q + 1) + 1) (q + 1) q := by
  let s : R := (-1 : R) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine
    { τ₁ := ModuleCat.ofHom (s • triadCap R X A B p ((q + 1) + 1) phi)
      τ₂ := triadCapHom R X A B p (q + 1) phi
      τ₃ := ModuleCat.ofHom (s • triadCap R X A B p q phi)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change relativeBoundary R (TopPair.ofSubset B) (q + 1)
        (s • triadCap R X A B p ((q + 1) + 1) phi c) =
      triadCap R X A B p (q + 1) phi
        (triadRelativeBoundary R X A B (p + (q + 1)) c)
    rw [map_smul]
    have h := LinearMap.congr_fun
      (boundary_triadCap_eq_of_cocycle R X A B p (q + 1) phi hphi) c
    change relativeBoundary R (TopPair.ofSubset B) (q + 1)
        (triadCap R X A B p ((q + 1) + 1) phi c) =
      s • triadCap R X A B p (q + 1) phi
        (triadRelativeBoundary R X A B (p + (q + 1)) c) at h
    simpa [s, hs, smul_smul] using congrArg (fun z ↦ s • z) h
  · apply ModuleCat.hom_ext
    exact boundary_triadCap_eq_of_cocycle R X A B p q phi hphi

/-- The short-complex morphism underlying the sum-relative triad cap product. -/
noncomputable def triadCapShortComplexHom
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    (triadRelativeChainComplex R X A B).sc (p + q) ⟶
      ((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc q := by
  let Ktriad := triadRelativeChainComplex R X A B
  let KrelB := (relativeChainFunctor R).obj (TopPair.ofSubset B)
  cases q with
  | zero =>
      exact
        (Ktriad.isoSc' (p + 1) p ((ComplexShape.down ℕ).next p)
            (ChainComplex.prev ℕ p) rfl).hom ≫
          triadCapShortComplexHomZero R X A B p phi hphi ≫
          (KrelB.isoSc' 1 0 0 (ChainComplex.prev ℕ 0)
            ChainComplex.next_nat_zero).inv
  | succ q =>
      exact
        (Ktriad.isoSc' (p + ((q + 1) + 1)) (p + (q + 1)) (p + q)
            (by rw [ChainComplex.prev]; omega)
            (by rw [show p + (q + 1) = (p + q) + 1 by omega,
              ChainComplex.next_nat_succ])).hom ≫
          triadCapShortComplexHomSucc R X A B p q phi hphi ≫
          (KrelB.isoSc' ((q + 1) + 1) (q + 1) q
            (by rw [ChainComplex.prev]) (ChainComplex.next_nat_succ q)).inv

@[simp]
lemma triadCapShortComplexHom_τ₂
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    (triadCapShortComplexHom R X A B p q phi hphi).τ₂ =
      triadCapHom R X A B p q phi := by
  cases q <;> simp [triadCapShortComplexHom, triadCapShortComplexHomZero,
    triadCapShortComplexHomSucc] <;> cat_disch

/-- Additivity of the homology map induced by the triad cap product. -/
lemma triadCapShortComplexHom_homologyMap_add
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi psi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0)
    (hpsi : relativeCoboundary R (TopPair.ofSubset A) p psi = 0)
    (hadd : relativeCoboundary R (TopPair.ofSubset A) p (phi + psi) = 0) :
    ShortComplex.homologyMap
        (triadCapShortComplexHom R X A B p q (phi + psi) hadd) =
      ShortComplex.homologyMap (triadCapShortComplexHom R X A B p q phi hphi) +
        ShortComplex.homologyMap
          (triadCapShortComplexHom R X A B p q psi hpsi) := by
  rw [← ShortComplex.homologyMap_add]
  apply Simplicial.homologyMap_eq_of_τ₂_eq
  simp [triadCapShortComplexHom_τ₂, triadCapHom_add]
  rfl

/-- Scalar compatibility of the homology map induced by the triad cap product. -/
lemma triadCapShortComplexHom_homologyMap_smul
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) (a : R)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0)
    (hsmul : relativeCoboundary R (TopPair.ofSubset A) p (a • phi) = 0) :
    ShortComplex.homologyMap
        (triadCapShortComplexHom R X A B p q (a • phi) hsmul) =
      a • ShortComplex.homologyMap
        (triadCapShortComplexHom R X A B p q phi hphi) := by
  rw [← ShortComplex.homologyMap_smul]
  apply Simplicial.homologyMap_eq_of_τ₂_eq
  simp [triadCapShortComplexHom_τ₂, triadCapHom_smul]
  rfl

/-- Cap product with a relative cocycle, descended in the chain variable to sum-relative
triad homology and valued in homology relative to `B`. -/
noncomputable def triadCapHomologyMap
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    TriadRelativeHomology R X A B (p + q) →ₗ[R]
      RelativeHomology R (TopPair.ofSubset B) q :=
  (ShortComplex.homologyMap
    (triadCapShortComplexHom R X A B p q phi hphi)).hom

/-- The sum-relative triad cap product is linear in relative cocycles. -/
noncomputable def triadCapCocycleHomologyLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    RelativeCocycle R (TopPair.ofSubset A) p →ₗ[R]
      (TriadRelativeHomology R X A B (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset B) q) where
  toFun phi := triadCapHomologyMap R X A B p q phi.1 phi.2
  map_add' phi psi := congrArg ModuleCat.Hom.hom
    (triadCapShortComplexHom_homologyMap_add R X A B p q
      phi.1 psi.1 phi.2 psi.2 (phi + psi).2)
  map_smul' a phi := congrArg ModuleCat.Hom.hom
    (triadCapShortComplexHom_homologyMap_smul R X A B p q
      a phi.1 phi.2 (a • phi).2)

@[simp]
lemma triadCapCocycleHomologyLinear_apply
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCocycle R (TopPair.ofSubset A) p) :
    triadCapCocycleHomologyLinear R X A B p q phi =
      triadCapHomologyMap R X A B p q phi.1 phi.2 :=
  rfl

/-! ## Independence of the relative cocycle representative -/

/-- Reassociate a sum-relative triad chain degree from `p + q + 1` to `(p + 1) + q`. -/
noncomputable def triadRelativeReassocChain
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    TriadRelativeChainGroup R X A B (p + q + 1) →ₗ[R]
      TriadRelativeChainGroup R X A B (p + 1 + q) :=
  (((triadRelativeChainComplex R X A B).XIsoOfEq (by omega)).hom).hom

/-- Reassociation commutes with projection from ambient to sum-relative triad chains. -/
lemma triadRelativeChainProjection_reassoc_apply
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) (p + q + 1)) :
    triadRelativeReassocChain R X A B p q
        (((triadRelativeChainProjection R X A B).f (p + q + 1)).hom c) =
      ((triadRelativeChainProjection R X A B).f (p + 1 + q)).hom
        (Simplicial.reassocChain R p q c) := by
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.XIsoOfEq_hom_naturality
      (triadRelativeChainProjection R X A B) (by omega)) c

set_option backward.isDefEq.respectTransparency false in
/-- Cap product by a relative coboundary is chain-null-homotopic on the sum-relative
triad quotient. -/
theorem triadCap_coboundary_eq
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (triadCap R X A B (p + 1) q
        (relativeCoboundary R (TopPair.ofSubset A) p phi)).comp
        (triadRelativeReassocChain R X A B p q) =
      (triadCap R X A B p q phi).comp
          (triadRelativeBoundary R X A B (p + q)) -
        (-1 : R) ^ p •
          (relativeBoundary R (TopPair.ofSubset B) q).comp
            (triadCap R X A B p (q + 1) phi) := by
  apply LinearMap.ext
  intro z
  let π := (triadRelativeChainProjection R X A B).f (p + q + 1)
  let _ : Epi π := Cofork.IsColimit.epi
    (triadRelativeChainProjectionComponentIsCokernel R X A B (p + q + 1))
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance z
  dsimp only [π]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  erw [triadRelativeChainProjection_reassoc_apply R X A B p q c,
    triadCap_projection_apply R X A B (p + 1) q
      (relativeCoboundary R (TopPair.ofSubset A) p phi)
      (Simplicial.reassocChain R p q c),
    triadRelativeBoundary_projection R X A B (p + q) c,
    triadCap_projection_apply R X A B p q phi
      (Simplicial.boundary R (p + q) c),
    triadCap_projection_apply R X A B p (q + 1) phi c]
  have habsolute := LinearMap.congr_fun
    (Simplicial.cap_coboundary_eq R p q
      (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi)) c
  rw [← relativeCochainToAbsolute_coboundary] at habsolute
  have hprojected := congrArg
    (fun z ↦ ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom z)
    habsolute
  have hboundary := ConcreteCategory.congr_hom
    ((relativeChainProjection R (TopPair.ofSubset B)).comm (q + 1) q)
    (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)
  have hboundary' :
      ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
          (Simplicial.boundary R q
            (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) =
        relativeBoundary R (TopPair.ofSubset B) q
          (((relativeChainProjection R (TopPair.ofSubset B)).f (q + 1)).hom
            (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) := by
    change relativeBoundary R (TopPair.ofSubset B) q
        (((relativeChainProjection R (TopPair.ofSubset B)).f (q + 1)).hom
          (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) =
      ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
        (Simplicial.boundary R q
          (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) at hboundary
    exact hboundary.symm
  change ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
      (Simplicial.cap R (p + 1) q
        (relativeCochainToAbsolute R (TopPair.ofSubset A) (p + 1)
          (relativeCoboundary R (TopPair.ofSubset A) p phi))
        (Simplicial.reassocChain R p q c)) = _
  calc
    _ = ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
        (Simplicial.cap R p q
            (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi)
            (Simplicial.boundary R (p + q) c) -
          (-1 : R) ^ p •
            Simplicial.boundary R q
              (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) := hprojected
    _ = ((relativeChainProjection R (TopPair.ofSubset B)).f q).hom
          (relativeCapLift R (TopPair.ofSubset A) p q phi
            (Simplicial.boundary R (p + q) c)) -
        (-1 : R) ^ p •
          relativeBoundary R (TopPair.ofSubset B) q
            (((relativeChainProjection R (TopPair.ofSubset B)).f (q + 1)).hom
              (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) := by
      rw [map_sub, map_smul]
      apply congrArg₂ (fun x y ↦ x - (-1 : R) ^ p • y)
      · rfl
      · exact hboundary'

/-- Reassociation of source degree as an isomorphism of triad homology short complexes. -/
noncomputable def triadRelativeReassocShortComplexIso
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    (triadRelativeChainComplex R X A B).sc (p + q + 1) ≅
      (triadRelativeChainComplex R X A B).sc (p + 1 + q) :=
  eqToIso (congrArg (fun n ↦ (triadRelativeChainComplex R X A B).sc n)
    (by omega : p + q + 1 = p + 1 + q))

lemma triadRelativeReassocShortComplexIso_hom_τ₂
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    (triadRelativeReassocShortComplexIso R X A B p q).hom.τ₂ =
      ModuleCat.ofHom (triadRelativeReassocChain R X A B p q) := by
  let K := triadRelativeChainComplex R X A B
  have eqToIso_sc_hom_τ₂ {m n : ℕ} (h : m = n) :
      (eqToIso (congrArg (fun i ↦ K.sc i) h)).hom.τ₂ = (K.XIsoOfEq h).hom := by
    subst n
    rfl
  exact eqToIso_sc_hom_τ₂ (by omega)

/-- The short-complex map obtained by capping with a relative coboundary, with its source
degree canonically reassociated. -/
noncomputable def triadCapCoboundaryShortComplexHom
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (triadRelativeChainComplex R X A B).sc (p + q + 1) ⟶
      ((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc q :=
  (triadRelativeReassocShortComplexIso R X A B p q).hom ≫
    triadCapShortComplexHom R X A B (p + 1) q
      (relativeCoboundary R (TopPair.ofSubset A) p phi)
      (relativeCoboundary_relativeCoboundary R (TopPair.ofSubset A) p phi)

lemma triadCapCoboundaryShortComplexHom_τ₂
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (triadCapCoboundaryShortComplexHom R X A B p q phi).τ₂ =
      ModuleCat.ofHom
        ((triadCap R X A B (p + 1) q
          (relativeCoboundary R (TopPair.ofSubset A) p phi)).comp
            (triadRelativeReassocChain R X A B p q)) := by
  simp [triadCapCoboundaryShortComplexHom,
    triadRelativeReassocShortComplexIso_hom_τ₂, triadCapShortComplexHom_τ₂]
  congr 1

/-- The middle component of the triad coboundary cap map is the difference in its chain
homotopy formula. -/
lemma triadCapCoboundaryShortComplexHom_τ₂_eq
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (triadCapCoboundaryShortComplexHom R X A B p q phi).τ₂ =
      (triadRelativeChainComplex R X A B).d (p + q + 1) (p + q) ≫
          triadCapHom R X A B p q phi -
        (-1 : R) ^ p •
          (triadCapHom R X A B p (q + 1) phi ≫
            ((relativeChainFunctor R).obj (TopPair.ofSubset B)).d (q + 1) q) := by
  rw [triadCapCoboundaryShortComplexHom_τ₂]
  apply ModuleCat.hom_ext
  exact triadCap_coboundary_eq R X A B p q phi

set_option backward.isDefEq.respectTransparency false in
/-- Cap product by a relative coboundary induces zero on sum-relative triad homology. -/
theorem triadCapCoboundary_homologyMap_eq_zero
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    ShortComplex.homologyMap
      (triadCapCoboundaryShortComplexHom R X A B p q phi) = 0 := by
  rw [← cancel_epi ((triadRelativeChainComplex R X A B).sc
    (p + q + 1)).homologyπ]
  rw [← cancel_mono
    (((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc q).homologyι]
  simp only [Category.assoc, zero_comp, comp_zero]
  rw [ShortComplex.π_homologyMap_ι,
    triadCapCoboundaryShortComplexHom_τ₂_eq]
  have hsource :
      ((triadRelativeChainComplex R X A B).sc (p + q + 1)).iCycles ≫
        (triadRelativeChainComplex R X A B).d (p + q + 1) (p + q) = 0 :=
    (triadRelativeChainComplex R X A B).iCycles_d (p + q + 1) (p + q)
  have htarget :
      ((relativeChainFunctor R).obj (TopPair.ofSubset B)).d (q + 1) q ≫
        (((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc q).pOpcycles = 0 :=
    ((relativeChainFunctor R).obj (TopPair.ofSubset B)).d_pOpcycles (q + 1) q
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
    Linear.comp_smul]
  simp only [← Category.assoc, hsource, zero_comp]
  simp only [Category.assoc, htarget, comp_zero, smul_zero, sub_zero]

/-- Without the degree reassociation, cap product by a relative coboundary still induces
zero on triad homology. -/
theorem triadCapShortComplexHom_coboundary_homologyMap_eq_zero
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    ShortComplex.homologyMap
      (triadCapShortComplexHom R X A B (p + 1) q
        (relativeCoboundary R (TopPair.ofSubset A) p phi)
        (relativeCoboundary_relativeCoboundary R (TopPair.ofSubset A) p phi)) = 0 := by
  rw [← cancel_epi (ShortComplex.homologyMap
    (triadRelativeReassocShortComplexIso R X A B p q).hom)]
  rw [← ShortComplex.homologyMap_comp, comp_zero]
  exact triadCapCoboundary_homologyMap_eq_zero R X A B p q phi

/-- A relative coboundary acts trivially on triad homology by cap product. -/
@[simp]
theorem triadCapHomologyMap_coboundary
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    triadCapHomologyMap R X A B (p + 1) q
      (relativeCoboundary R (TopPair.ofSubset A) p phi)
      (relativeCoboundary_relativeCoboundary R (TopPair.ofSubset A) p phi) = 0 := by
  exact congrArg ModuleCat.Hom.hom
    (triadCapShortComplexHom_coboundary_homologyMap_eq_zero R X A B p q phi)

/-- Relative cocycles differing by a relative coboundary induce the same triad cap map. -/
theorem triadCapCocycleHomologyLinear_eq_of_sub_eq_coboundary
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi psi : RelativeCocycle R (TopPair.ofSubset A) (p + 1))
    (eta : RelativeCochain R (TopPair.ofSubset A) p)
    (h : phi.1 - psi.1 = relativeCoboundary R (TopPair.ofSubset A) p eta) :
    triadCapCocycleHomologyLinear R X A B (p + 1) q phi =
      triadCapCocycleHomologyLinear R X A B (p + 1) q psi := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  let deta : RelativeCocycle R (TopPair.ofSubset A) (p + 1) :=
    ⟨relativeCoboundary R (TopPair.ofSubset A) p eta,
      relativeCoboundary_relativeCoboundary R (TopPair.ofSubset A) p eta⟩
  have hdeta : phi - psi = deta := by
    apply Subtype.ext
    exact h
  rw [hdeta]
  exact triadCapHomologyMap_coboundary R X A B p q eta

/-! ## Descent in the cohomology variable -/

/-- Triad cap product on explicit dual cycles in the relative cochain short complex. -/
noncomputable def triadRelativeCohomologyCycleCapLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    LinearMap.ker
        ((((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual.g.hom) →ₗ[R]
      (TriadRelativeHomology R X A B (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset B) q) :=
  (triadCapCocycleHomologyLinear R X A B p q).comp
    (relativeCohomologyCycleToCocycle R (TopPair.ofSubset A) p)

/-- Triad cap product on dual cycles annihilates the boundaries in the explicit relative
cohomology quotient. -/
lemma triadRelativeCohomologyCycleCapLinear_vanishes_on_boundaries
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
    LinearMap.range T.moduleCatToCycles ≤
      LinearMap.ker (triadRelativeCohomologyCycleCapLinear R X A B p q) := by
  dsimp only
  rintro _ ⟨eta, rfl⟩
  cases p with
  | zero =>
      change triadRelativeCohomologyCycleCapLinear R X A B 0 q
        (((((relativeChainFunctor R).obj
          (TopPair.ofSubset A)).sc 0).linearDual.moduleCatToCycles) eta) = 0
      let K := (relativeChainFunctor R).obj (TopPair.ofSubset A)
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
      exact map_zero (triadRelativeCohomologyCycleCapLinear R X A B 0 q)
  | succ p =>
      change triadRelativeCohomologyCycleCapLinear R X A B (p + 1) q
        (((((relativeChainFunctor R).obj
          (TopPair.ofSubset A)).sc (p + 1)).linearDual.moduleCatToCycles) eta) = 0
      rw [triadRelativeCohomologyCycleCapLinear, LinearMap.comp_apply,
        relativeCohomologyCycleToCocycle_moduleCatToCycles_succ,
        triadCapCocycleHomologyLinear_apply, triadCapHomologyMap_coboundary]

/-- Triad cap product on the explicit quotient of relative cocycles by relative
coboundaries. -/
noncomputable def triadCapCohomologyExplicitLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
    T.moduleCatLeftHomologyData.H →ₗ[R]
      (TriadRelativeHomology R X A B (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset B) q) :=
  let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
  (LinearMap.range T.moduleCatToCycles).liftQ
    (triadRelativeCohomologyCycleCapLinear R X A B p q)
    (triadRelativeCohomologyCycleCapLinear_vanishes_on_boundaries R X A B p q)

/-- Sum-relative triad cap product on algebraic relative cochain cohomology. -/
noncomputable def triadCapCochainCohomologyLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    RelativeCochainCohomology R (TopPair.ofSubset A) p →ₗ[R]
      (TriadRelativeHomology R X A B (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset B) q) :=
  let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
  (triadCapCohomologyExplicitLinear R X A B p q).comp
    T.moduleCatHomologyIso.hom.hom

/-- On the class of an explicit relative dual cycle, the triad cochain-cohomology cap
product agrees with the cocycle-level construction. -/
@[simp]
lemma triadCapCochainCohomologyLinear_on_cycle
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : LinearMap.ker
      ((((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual.g.hom)) :
    let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
    triadCapCochainCohomologyLinear R X A B p q
        (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
      triadRelativeCohomologyCycleCapLinear R X A B p q phi := by
  dsimp only
  let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
  change triadCapCohomologyExplicitLinear R X A B p q
      (T.moduleCatHomologyIso.hom.hom
        (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))) = _
  have h := ConcreteCategory.congr_hom T.moduleCatHomologyIso.inv_hom_id
    (Submodule.Quotient.mk phi)
  change T.moduleCatHomologyIso.hom.hom
      (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
    Submodule.Quotient.mk phi at h
  rw [h]
  rfl

/-- The sum-relative triad cap product on the repository's standard relative cohomology
and homology objects:

`H^p(X,A) → (H_{p+q}^{sum}(X;A,B) → H_q(X,B))`.

Replacing the sum-relative source by `H_{p+q}(X,A ∪ B)` requires a separately proved
excision comparison. -/
noncomputable def triadCapCohomologyLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    RelativeCohomology R (TopPair.ofSubset A) p →ₗ[R]
      (TriadRelativeHomology R X A B (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset B) q) :=
  (triadCapCochainCohomologyLinear R X A B p q).comp
    (((relativeChainFunctor R).obj
      (TopPair.ofSubset A)).sc p).linearDualHomologyEquiv.symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- On the standard relative cohomology class represented by an explicit relative
cocycle, the triad cap product agrees with the cocycle-level map. -/
@[simp]
lemma triadCapCohomologyLinear_on_cycle
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : LinearMap.ker
      ((((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual.g.hom)) :
    let S := ((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p
    triadCapCohomologyLinear R X A B p q
        (S.linearDualHomologyEquiv
          (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))) =
      triadRelativeCohomologyCycleCapLinear R X A B p q phi := by
  dsimp only
  rw [triadCapCohomologyLinear, LinearMap.comp_apply]
  let S := ((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p
  have h := S.linearDualHomologyEquiv.symm_apply_apply
    (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))
  change triadCapCochainCohomologyLinear R X A B p q
      (S.linearDualHomologyEquiv.symm
        (S.linearDualHomologyEquiv
          (S.linearDual.moduleCatHomologyIso.inv.hom
            (Submodule.Quotient.mk phi)))) = _
  rw [h]
  exact triadCapCochainCohomologyLinear_on_cycle R X A B p q phi

/-! ## The comparison with the ordinary union-relative complex

There is always a canonical map from the sum-relative quotient to `C_*(X, A ∪ B)`.  We
construct that map here.  We make no claim that it is a quasi-isomorphism: proving that is exactly
the subdivision/excision step which cannot be replaced by a formal cokernel calculation. -/

/-- Inclusion of `A` into the subspace `A ∪ B`. -/
def subsetToUnionLeft (X : TopCat.{u}) (A B : Set X) :
    (TopPair.ofSubset A).snd ⟶ (TopPair.ofSubset (A ∪ B)).snd :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, Or.inl x.2⟩, by fun_prop⟩

/-- Inclusion of `B` into the subspace `A ∪ B`. -/
def subsetToUnionRight (X : TopCat.{u}) (A B : Set X) :
    (TopPair.ofSubset B).snd ⟶ (TopPair.ofSubset (A ∪ B)).snd :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, Or.inr x.2⟩, by fun_prop⟩

@[reassoc]
lemma subsetToUnionLeft_comp_unionMap
    (X : TopCat.{u}) (A B : Set X) :
    subsetToUnionLeft X A B ≫ (TopPair.ofSubset (A ∪ B)).map =
      (TopPair.ofSubset A).map := by
  ext x
  rfl

@[reassoc]
lemma subsetToUnionRight_comp_unionMap
    (X : TopCat.{u}) (A B : Set X) :
    subsetToUnionRight X A B ≫ (TopPair.ofSubset (A ∪ B)).map =
      (TopPair.ofSubset B).map := by
  ext x
  rfl

/-- The chain map induced by `A ⊆ A ∪ B`. -/
noncomputable def subsetToUnionLeftChainMap
    (X : TopCat.{u}) (A B : Set X) :
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).obj (TopPair.ofSubset A).snd ⟶
      ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).obj (TopPair.ofSubset (A ∪ B)).snd :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).map (subsetToUnionLeft X A B)

/-- The chain map induced by `B ⊆ A ∪ B`. -/
noncomputable def subsetToUnionRightChainMap
    (X : TopCat.{u}) (A B : Set X) :
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).obj (TopPair.ofSubset B).snd ⟶
      ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).obj (TopPair.ofSubset (A ∪ B)).snd :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).map (subsetToUnionRight X A B)

set_option backward.isDefEq.respectTransparency false in
lemma subsetToUnionLeftChainMap_comp_unionChainMap
    (X : TopCat.{u}) (A B : Set X) :
    subsetToUnionLeftChainMap R X A B ≫
        ((chainPairFunctor R).obj (TopPair.ofSubset (A ∪ B))).hom =
      ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom := by
  change ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map (subsetToUnionLeft X A B) ≫
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map (TopPair.ofSubset (A ∪ B)).map =
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map (TopPair.ofSubset A).map
  let F := (singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  exact (F.map_comp (subsetToUnionLeft X A B)
    (TopPair.ofSubset (A ∪ B)).map).symm.trans
      (congrArg F.map (subsetToUnionLeft_comp_unionMap X A B))

set_option backward.isDefEq.respectTransparency false in
lemma subsetToUnionRightChainMap_comp_unionChainMap
    (X : TopCat.{u}) (A B : Set X) :
    subsetToUnionRightChainMap R X A B ≫
        ((chainPairFunctor R).obj (TopPair.ofSubset (A ∪ B))).hom =
      ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom := by
  change ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map (subsetToUnionRight X A B) ≫
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map (TopPair.ofSubset (A ∪ B)).map =
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map (TopPair.ofSubset B).map
  let F := (singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  exact (F.map_comp (subsetToUnionRight X A B)
    (TopPair.ofSubset (A ∪ B)).map).symm.trans
      (congrArg F.map (subsetToUnionRight_comp_unionMap X A B))

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of `A` into `X` is killed by projection modulo `A ∪ B`. -/
lemma subspaceAChainMap_unionRelativeChainProjection_eq_zero
    (X : TopCat.{u}) (A B : Set X) :
    ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom ≫
      relativeChainProjection R (TopPair.ofSubset (A ∪ B)) = 0 := by
  calc
    _ = (subsetToUnionLeftChainMap R X A B ≫
          ((chainPairFunctor R).obj (TopPair.ofSubset (A ∪ B))).hom) ≫
        relativeChainProjection R (TopPair.ofSubset (A ∪ B)) := by
      rw [subsetToUnionLeftChainMap_comp_unionChainMap]
    _ = subsetToUnionLeftChainMap R X A B ≫
        (((chainPairFunctor R).obj (TopPair.ofSubset (A ∪ B))).hom ≫
          relativeChainProjection R (TopPair.ofSubset (A ∪ B))) :=
      Category.assoc _ _ _
    _ = 0 := by rw [subspaceChainMap_relativeChainProjection, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of `B` into `X` is killed by projection modulo `A ∪ B`. -/
lemma subspaceBChainMap_unionRelativeChainProjection_eq_zero
    (X : TopCat.{u}) (A B : Set X) :
    ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom ≫
      relativeChainProjection R (TopPair.ofSubset (A ∪ B)) = 0 := by
  calc
    _ = (subsetToUnionRightChainMap R X A B ≫
          ((chainPairFunctor R).obj (TopPair.ofSubset (A ∪ B))).hom) ≫
        relativeChainProjection R (TopPair.ofSubset (A ∪ B)) := by
      rw [subsetToUnionRightChainMap_comp_unionChainMap]
    _ = subsetToUnionRightChainMap R X A B ≫
        (((chainPairFunctor R).obj (TopPair.ofSubset (A ∪ B))).hom ≫
          relativeChainProjection R (TopPair.ofSubset (A ∪ B))) :=
      Category.assoc _ _ _
    _ = 0 := by rw [subspaceChainMap_relativeChainProjection, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The two-summand subspace map is killed by projection modulo `A ∪ B`. -/
lemma triadSubspaceChainMap_unionRelativeChainProjection_eq_zero
    (X : TopCat.{u}) (A B : Set X) :
    triadSubspaceChainMap R X A B ≫
      relativeChainProjection R (TopPair.ofSubset (A ∪ B)) = 0 := by
  change biprod.desc
      ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom
      ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom ≫
    relativeChainProjection R (TopPair.ofSubset (A ∪ B)) = 0
  apply HomologicalComplex.hom_ext
  intro n
  change (biprod.desc
      ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom
      ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom).f n ≫
        (relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f n = 0
  apply HomologicalComplex.biprodX_ext_from
  · rw [← Category.assoc, HomologicalComplex.biprod_inl_desc_f]
    have h := congrArg (fun f ↦ f.f n)
      (subspaceAChainMap_unionRelativeChainProjection_eq_zero R X A B)
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at h
    rw [h]
    simp
  · rw [← Category.assoc, HomologicalComplex.biprod_inr_desc_f]
    have h := congrArg (fun f ↦ f.f n)
      (subspaceBChainMap_unionRelativeChainProjection_eq_zero R X A B)
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at h
    rw [h]
    simp

/-- The canonical chain map
`C_*^{sum}(X;A,B) ⟶ C_*(X,A ∪ B)`.

This map exists formally.  Its being a quasi-isomorphism is the non-formal excision theorem. -/
noncomputable def triadToUnionRelativeChainMap
    (X : TopCat.{u}) (A B : Set X) :
    triadRelativeChainComplex R X A B ⟶
      (relativeChainFunctor R).obj (TopPair.ofSubset (A ∪ B)) :=
  (cokernelIsCokernel (triadSubspaceChainMap R X A B)).desc
    (CokernelCofork.ofπ
      (relativeChainProjection R (TopPair.ofSubset (A ∪ B)))
      (triadSubspaceChainMap_unionRelativeChainProjection_eq_zero R X A B))

/-- The comparison map is induced by the identity on ambient chains. -/
@[reassoc]
lemma triadRelativeChainProjection_triadToUnionRelativeChainMap
    (X : TopCat.{u}) (A B : Set X) :
    triadRelativeChainProjection R X A B ≫
      triadToUnionRelativeChainMap R X A B =
        relativeChainProjection R (TopPair.ofSubset (A ∪ B)) := by
  exact (Cofork.IsColimit.π_desc
    (cokernelIsCokernel (triadSubspaceChainMap R X A B))
    (t := CokernelCofork.ofπ
      (relativeChainProjection R (TopPair.ofSubset (A ∪ B)))
      (triadSubspaceChainMap_unionRelativeChainProjection_eq_zero R X A B))).trans
    (CokernelCofork.π_ofπ _ _ _)

/-- The canonical map from sum-relative triad homology to ordinary homology relative to
`A ∪ B`. -/
noncomputable def triadToUnionRelativeHomologyMap
    (X : TopCat.{u}) (A B : Set X) (n : ℕ) :
    TriadRelativeHomology R X A B n →ₗ[R]
      RelativeHomology R (TopPair.ofSubset (A ∪ B)) n :=
  (HomologicalComplex.homologyMap (triadToUnionRelativeChainMap R X A B) n).hom

/-! ## The customary triad pairing, conditional on the excision comparison

The only hypothesis in this section is that the canonical chain comparison constructed above is a
quasi-isomorphism.  Thus the equivalence below is derived from the excision statement itself; no
equivalence between unrelated homology groups is supplied as data. -/

/-- The homology equivalence induced by the canonical comparison from the sum-relative model to
the ordinary union-relative complex.

The named `hExcision` hypothesis is precisely the still-required small-chain/excision theorem. -/
noncomputable def triadUnionExcisionHomologyEquiv
    (X : TopCat.{u}) (A B : Set X) (n : ℕ)
    (hExcision : QuasiIso (triadToUnionRelativeChainMap R X A B)) :
    TriadRelativeHomology R X A B n ≃ₗ[R]
      RelativeHomology R (TopPair.ofSubset (A ∪ B)) n := by
  letI := hExcision
  exact (isoOfQuasiIsoAt
    (triadToUnionRelativeChainMap R X A B) n).toLinearEquiv

@[simp]
lemma triadUnionExcisionHomologyEquiv_apply
    (X : TopCat.{u}) (A B : Set X) (n : ℕ)
    (hExcision : QuasiIso (triadToUnionRelativeChainMap R X A B))
    (z : TriadRelativeHomology R X A B n) :
    triadUnionExcisionHomologyEquiv R X A B n hExcision z =
      triadToUnionRelativeHomologyMap R X A B n z :=
  rfl

/-- The customary triad cap product

`H^p(X,A) → (H_{p+q}(X,A ∪ B) → H_q(X,B))`,

obtained by transporting the constructed sum-relative cap product along the homology equivalence
induced by the canonical excision comparison. -/
noncomputable def unionRelativeTriadCapCohomologyLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (hExcision : QuasiIso (triadToUnionRelativeChainMap R X A B)) :
    RelativeCohomology R (TopPair.ofSubset A) p →ₗ[R]
      (RelativeHomology R (TopPair.ofSubset (A ∪ B)) (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset B) q) where
  toFun alpha := (triadCapCohomologyLinear R X A B p q alpha).comp
    (triadUnionExcisionHomologyEquiv R X A B (p + q) hExcision).symm.toLinearMap
  map_add' alpha beta := by
    apply LinearMap.ext
    intro z
    simp
  map_smul' a alpha := by
    apply LinearMap.ext
    intro z
    simp

/-- Evaluation of the customary triad cap product is evaluation of the sum-relative product on
the inverse image under the excision equivalence. -/
@[simp]
lemma unionRelativeTriadCapCohomologyLinear_apply
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (hExcision : QuasiIso (triadToUnionRelativeChainMap R X A B))
    (alpha : RelativeCohomology R (TopPair.ofSubset A) p)
    (z : RelativeHomology R (TopPair.ofSubset (A ∪ B)) (p + q)) :
    unionRelativeTriadCapCohomologyLinear R X A B p q hExcision alpha z =
      triadCapCohomologyLinear R X A B p q alpha
        ((triadUnionExcisionHomologyEquiv R X A B (p + q) hExcision).symm z) :=
  rfl

/-- On a class coming from the sum-relative model through the canonical comparison, the customary
triad pairing agrees with the originally constructed pairing. -/
@[simp]
lemma unionRelativeTriadCapCohomologyLinear_on_comparison
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (hExcision : QuasiIso (triadToUnionRelativeChainMap R X A B))
    (alpha : RelativeCohomology R (TopPair.ofSubset A) p)
    (z : TriadRelativeHomology R X A B (p + q)) :
    unionRelativeTriadCapCohomologyLinear R X A B p q hExcision alpha
        (triadToUnionRelativeHomologyMap R X A B (p + q) z) =
      triadCapCohomologyLinear R X A B p q alpha z := by
  rw [unionRelativeTriadCapCohomologyLinear_apply]
  have hz :
      (triadUnionExcisionHomologyEquiv R X A B (p + q) hExcision).symm
          (triadToUnionRelativeHomologyMap R X A B (p + q) z) = z := by
    calc
      _ = (triadUnionExcisionHomologyEquiv R X A B (p + q) hExcision).symm
          (triadUnionExcisionHomologyEquiv R X A B (p + q) hExcision z) :=
        congrArg (triadUnionExcisionHomologyEquiv R X A B
          (p + q) hExcision).symm
          (triadUnionExcisionHomologyEquiv_apply R X A B
            (p + q) hExcision z).symm
      _ = z := (triadUnionExcisionHomologyEquiv R X A B
        (p + q) hExcision).symm_apply_apply z
  exact congrArg (triadCapCohomologyLinear R X A B p q alpha) hz

end AlgebraicTopology.Singular
