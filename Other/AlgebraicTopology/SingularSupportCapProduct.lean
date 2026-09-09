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

public import Other.AlgebraicTopology.SingularTriadCapProduct

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

/-! ## The support-valued relative cap product

The Alexander--Whitney convention used above also gives the complementary relative
pairing

`C^p(X,A) ⊗ C_{p+q}(X,B) ⟶ C_q(X,A ∪ B)`.

No opposite cap product is needed.  Naturality says that capping a chain in `B` gives
another chain in `B`, so projection modulo `A ∪ B` kills it.  Thus the ambient cap
descends directly through the ordinary relative-chain quotient by `B`.  In contrast to
the customary triad pairing constructed above, this direction needs no comparison with
the sum-relative complex and hence no excision hypothesis.
-/

/-- Cap a cochain relative to `A` with an ambient chain and project the result modulo
`A ∪ B`. -/
def supportCapLiftHom (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).obj X).X (p + q) ⟶
      RelativeChainGroup R (TopPair.ofSubset (A ∪ B)) q :=
  ModuleCat.ofHom (relativeCapLift R (TopPair.ofSubset A) p q phi) ≫
    (relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q

/-- The ambient lift of the support-valued cap product as a linear map. -/
def supportCapLift (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    Simplicial.ChainGroup R (TopCat.toSSet.obj X) (p + q) →ₗ[R]
      RelativeChainGroup R (TopPair.ofSubset (A ∪ B)) q :=
  (supportCapLiftHom R X A B p q phi).hom

set_option backward.isDefEq.respectTransparency false in
/-- Naturality on the supported subspace before the target projection is used. -/
lemma supportCapLift_naturality_on_B
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (c : Simplicial.ChainGroup R
      (TopCat.toSSet.obj (TopPair.ofSubset B).snd) (p + q)) :
    supportCapLift R X A B p q phi
        ((((chainPairFunctor R).obj (TopPair.ofSubset B)).hom.f (p + q)).hom c) =
      ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
        ((((SSet.chainComplexMap
          (TopCat.toSSet.map (TopPair.ofSubset B).map)
          (ModuleCat.of R R)).f q).hom
            (Simplicial.cap R p q
              (Simplicial.cochainMap R
                (TopCat.toSSet.map (TopPair.ofSubset B).map) p
                (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi)) c))) := by
  have h := Simplicial.cap_naturality R
    (TopCat.toSSet.map (TopPair.ofSubset B).map) p q
    (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi) c
  exact congrArg
    (fun z ↦ ((relativeChainProjection R
      (TopPair.ofSubset (A ∪ B))).f q).hom z) h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The support-valued lift kills chains in `B`; this is the exact factorization
boundary which makes the source `C_*(X,B)`. -/
lemma subspaceBChainMap_supportCapLiftHom_eq_zero
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    ((chainPairFunctor R).obj (TopPair.ofSubset B)).hom.f (p + q) ≫
      supportCapLiftHom R X A B p q phi = 0 := by
  ext c
  have hcap := Simplicial.cap_naturality R
    (TopCat.toSSet.map (TopPair.ofSubset B).map) p q
    (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi) c
  have hprojection := congrArg (fun f ↦ f.f q)
    (subspaceBChainMap_unionRelativeChainProjection_eq_zero R X A B)
  have hprojection' :
      (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map)
          (ModuleCat.of R R)).f q ≫
        (relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q = 0 := hprojection
  have hzero := ConcreteCategory.congr_hom hprojection'
    (Simplicial.cap R p q
      (Simplicial.cochainMap R
        (TopCat.toSSet.map (TopPair.ofSubset B).map) p
        (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi)) c)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] at hzero
  have hprojected := congrArg
    (fun z ↦ ((relativeChainProjection R
      (TopPair.ofSubset (A ∪ B))).f q).hom z) hcap
  change ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
    (Simplicial.cap R p q
      (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi)
      (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map)
        (ModuleCat.of R R)).f (p + q)).hom c)) = 0
  exact hprojected.symm.trans hzero

/-- The support-valued cap product, descended through the ordinary quotient by `B` in
the chain variable. -/
noncomputable def supportCapHom (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    RelativeChainGroup R (TopPair.ofSubset B) (p + q) ⟶
      RelativeChainGroup R (TopPair.ofSubset (A ∪ B)) q :=
  (relativeChainProjectionComponentIsCokernelForCap R
    (TopPair.ofSubset B) (p + q)).desc
      (CokernelCofork.ofπ (supportCapLiftHom R X A B p q phi)
        (subspaceBChainMap_supportCapLiftHom_eq_zero R X A B p q phi))

/-- The support-valued cap product as a linear map in the relative-chain variable. -/
noncomputable def supportCap (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    RelativeChainGroup R (TopPair.ofSubset B) (p + q) →ₗ[R]
      RelativeChainGroup R (TopPair.ofSubset (A ∪ B)) q :=
  (supportCapHom R X A B p q phi).hom

/-- Capping a projected ambient representative agrees with the lifted support-valued
cap product. -/
@[reassoc]
lemma relativeChainProjection_supportCapHom
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (relativeChainProjection R (TopPair.ofSubset B)).f (p + q) ≫
      supportCapHom R X A B p q phi =
        supportCapLiftHom R X A B p q phi :=
  (Cofork.IsColimit.π_desc
    (relativeChainProjectionComponentIsCokernelForCap R
      (TopPair.ofSubset B) (p + q))
    (t := CokernelCofork.ofπ (supportCapLiftHom R X A B p q phi)
      (subspaceBChainMap_supportCapLiftHom_eq_zero R X A B p q phi))).trans
    (CokernelCofork.π_ofπ _ _ _)

@[simp]
lemma supportCap_projection_apply
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) (p + q)) :
    supportCap R X A B p q phi
        (((relativeChainProjection R (TopPair.ofSubset B)).f (p + q)).hom c) =
      supportCapLift R X A B p q phi c :=
  ConcreteCategory.congr_hom
    (relativeChainProjection_supportCapHom R X A B p q phi) c

set_option backward.isDefEq.respectTransparency false in
lemma supportCapLiftHom_add
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi psi : RelativeCochain R (TopPair.ofSubset A) p) :
    supportCapLiftHom R X A B p q (phi + psi) =
      supportCapLiftHom R X A B p q phi +
        supportCapLiftHom R X A B p q psi := by
  ext c
  change ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
      (relativeCapLift R (TopPair.ofSubset A) p q (phi + psi) c) =
    ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
        (relativeCapLift R (TopPair.ofSubset A) p q phi c) +
      ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
        (relativeCapLift R (TopPair.ofSubset A) p q psi c)
  rw [LinearMap.congr_fun
    (relativeCapLift_add R (TopPair.ofSubset A) p q phi psi) c,
    LinearMap.add_apply, map_add]

set_option backward.isDefEq.respectTransparency false in
lemma supportCapLiftHom_smul
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) (a : R)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    supportCapLiftHom R X A B p q (a • phi) =
      a • supportCapLiftHom R X A B p q phi := by
  ext c
  change ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
      (relativeCapLift R (TopPair.ofSubset A) p q (a • phi) c) =
    a • ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
      (relativeCapLift R (TopPair.ofSubset A) p q phi c)
  rw [LinearMap.congr_fun
    (relativeCapLift_smul R (TopPair.ofSubset A) p q a phi) c,
    LinearMap.smul_apply, map_smul]

set_option backward.isDefEq.respectTransparency false in
lemma supportCapHom_add
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi psi : RelativeCochain R (TopPair.ofSubset A) p) :
    supportCapHom R X A B p q (phi + psi) =
      supportCapHom R X A B p q phi + supportCapHom R X A B p q psi := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap R
      (TopPair.ofSubset B) (p + q))
  change (relativeChainProjection R (TopPair.ofSubset B)).f (p + q) ≫
      supportCapHom R X A B p q (phi + psi) =
    (relativeChainProjection R (TopPair.ofSubset B)).f (p + q) ≫
      (supportCapHom R X A B p q phi + supportCapHom R X A B p q psi)
  rw [relativeChainProjection_supportCapHom, Preadditive.comp_add,
    relativeChainProjection_supportCapHom,
    relativeChainProjection_supportCapHom, supportCapLiftHom_add]

set_option backward.isDefEq.respectTransparency false in
lemma supportCapHom_smul
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) (a : R)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    supportCapHom R X A B p q (a • phi) =
      a • supportCapHom R X A B p q phi := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap R
      (TopPair.ofSubset B) (p + q))
  change (relativeChainProjection R (TopPair.ofSubset B)).f (p + q) ≫
      supportCapHom R X A B p q (a • phi) =
    (relativeChainProjection R (TopPair.ofSubset B)).f (p + q) ≫
      (a • supportCapHom R X A B p q phi)
  rw [relativeChainProjection_supportCapHom, Linear.comp_smul,
    relativeChainProjection_supportCapHom, supportCapLiftHom_smul]

/-- Support-valued cap product, bilinear in a relative cochain and a chain relative to
`B`, with values in chains relative to the explicit union `A ∪ B`. -/
noncomputable def supportCapLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    RelativeCochain R (TopPair.ofSubset A) p →ₗ[R]
      (RelativeChainGroup R (TopPair.ofSubset B) (p + q) →ₗ[R]
        RelativeChainGroup R (TopPair.ofSubset (A ∪ B)) q) where
  toFun phi := supportCap R X A B p q phi
  map_add' phi psi := congrArg ModuleCat.Hom.hom
    (supportCapHom_add R X A B p q phi psi)
  map_smul' a phi := congrArg ModuleCat.Hom.hom
    (supportCapHom_smul R X A B p q a phi)

@[simp]
lemma supportCapLinear_apply
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    supportCapLinear R X A B p q phi = supportCap R X A B p q phi :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a relative cocycle, the lifted support-valued cap product satisfies the signed
boundary identity before quotienting the chain variable. -/
theorem boundary_supportCapLift_eq_of_cocycle
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    (relativeBoundary R (TopPair.ofSubset (A ∪ B)) q).comp
        (supportCapLift R X A B p (q + 1) phi) =
      (-1 : R) ^ p •
        (supportCapLift R X A B p q phi).comp
          (Simplicial.boundary R (p + q)) := by
  ext c
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  have hboundary := ConcreteCategory.congr_hom
    ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).comm (q + 1) q)
    (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)
  have habsolute := LinearMap.congr_fun
    (boundary_relativeCapLift_eq_of_cocycle R
      (TopPair.ofSubset A) p q phi hphi) c
  have hprojected := congrArg
    (fun z ↦ ((relativeChainProjection R
      (TopPair.ofSubset (A ∪ B))).f q).hom z) habsolute
  change relativeBoundary R (TopPair.ofSubset (A ∪ B)) q
      (((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f (q + 1)).hom
        (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) = _
  calc
    _ = ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
        (Simplicial.boundary R q
          (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) := hboundary
    _ = ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
        ((-1 : R) ^ p • relativeCapLift R (TopPair.ofSubset A) p q phi
          (Simplicial.boundary R (p + q) c)) := hprojected
    _ = _ := by rw [map_smul]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a relative cocycle, support-valued cap product intertwines the ordinary relative
boundaries of `(X,B)` and `(X,A ∪ B)`, up to the standard sign. -/
theorem boundary_supportCap_eq_of_cocycle
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    (relativeBoundary R (TopPair.ofSubset (A ∪ B)) q).comp
        (supportCap R X A B p (q + 1) phi) =
      (-1 : R) ^ p •
        (supportCap R X A B p q phi).comp
          (relativeBoundary R (TopPair.ofSubset B) (p + q)) := by
  ext z
  let π := (relativeChainProjection R (TopPair.ofSubset B)).f (p + q + 1)
  let : Epi π := Cofork.IsColimit.epi
    (relativeChainProjectionComponentIsCokernelForCap R
      (TopPair.ofSubset B) (p + q + 1))
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance z
  dsimp only [π]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  erw [supportCap_projection_apply R X A B p (q + 1) phi c,
    relativeBoundary_projection R (TopPair.ofSubset B) (p + q) c,
    supportCap_projection_apply R X A B p q phi
      (Simplicial.boundary R (p + q) c)]
  exact LinearMap.congr_fun
    (boundary_supportCapLift_eq_of_cocycle R X A B p q phi hphi) c

/-! ### Descent in the homology variable -/

/-- The explicit support-valued cap morphism ending in degree zero. -/
noncomputable def supportCapShortComplexHomZero
    (X : TopCat.{u}) (A B : Set X) (p : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    ((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc'
        (p + 1) p ((ComplexShape.down ℕ).next p) ⟶
      ((relativeChainFunctor R).obj (TopPair.ofSubset (A ∪ B))).sc' 1 0 0 := by
  let s : R := (-1 : R) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine
    { τ₁ := ModuleCat.ofHom (s • supportCap R X A B p 1 phi)
      τ₂ := supportCapHom R X A B p 0 phi
      τ₃ := 0
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · ext c
    change relativeBoundary R (TopPair.ofSubset (A ∪ B)) 0
        (s • supportCap R X A B p 1 phi c) =
      supportCap R X A B p 0 phi
        (relativeBoundary R (TopPair.ofSubset B) p c)
    rw [map_smul]
    have h := LinearMap.congr_fun
      (boundary_supportCap_eq_of_cocycle R X A B p 0 phi hphi) c
    change relativeBoundary R (TopPair.ofSubset (A ∪ B)) 0
        (supportCap R X A B p 1 phi c) =
      s • supportCap R X A B p 0 phi
        (relativeBoundary R (TopPair.ofSubset B) p c) at h
    simpa [s, hs, smul_smul] using congrArg (fun z ↦ s • z) h
  · change supportCapHom R X A B p 0 phi ≫
        ((relativeChainFunctor R).obj (TopPair.ofSubset (A ∪ B))).d 0 0 =
      ((relativeChainFunctor R).obj (TopPair.ofSubset B)).d p
          ((ComplexShape.down ℕ).next p) ≫ 0
    rw [(((relativeChainFunctor R).obj
      (TopPair.ofSubset (A ∪ B))).shape 0 0 (by simp)), comp_zero, comp_zero]

/-- The explicit support-valued cap morphism ending in a positive degree. -/
noncomputable def supportCapShortComplexHomSucc
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    ((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc'
        (p + ((q + 1) + 1)) (p + (q + 1)) (p + q) ⟶
      ((relativeChainFunctor R).obj (TopPair.ofSubset (A ∪ B))).sc'
        ((q + 1) + 1) (q + 1) q := by
  let s : R := (-1 : R) ^ p
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  refine
    { τ₁ := ModuleCat.ofHom (s • supportCap R X A B p ((q + 1) + 1) phi)
      τ₂ := supportCapHom R X A B p (q + 1) phi
      τ₃ := ModuleCat.ofHom (s • supportCap R X A B p q phi)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · ext c
    change relativeBoundary R (TopPair.ofSubset (A ∪ B)) (q + 1)
        (s • supportCap R X A B p ((q + 1) + 1) phi c) =
      supportCap R X A B p (q + 1) phi
        (relativeBoundary R (TopPair.ofSubset B) (p + (q + 1)) c)
    rw [map_smul]
    have h := LinearMap.congr_fun
      (boundary_supportCap_eq_of_cocycle R X A B p (q + 1) phi hphi) c
    change relativeBoundary R (TopPair.ofSubset (A ∪ B)) (q + 1)
        (supportCap R X A B p ((q + 1) + 1) phi c) =
      s • supportCap R X A B p (q + 1) phi
        (relativeBoundary R (TopPair.ofSubset B) (p + (q + 1)) c) at h
    simpa [s, hs, smul_smul] using congrArg (fun z ↦ s • z) h
  · exact ModuleCat.hom_ext (boundary_supportCap_eq_of_cocycle R X A B p q phi hphi)

/-- The short-complex morphism underlying the support-valued cap product. -/
noncomputable def supportCapShortComplexHom
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    ((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc (p + q) ⟶
      ((relativeChainFunctor R).obj (TopPair.ofSubset (A ∪ B))).sc q := by
  let KB := (relativeChainFunctor R).obj (TopPair.ofSubset B)
  let Kunion := (relativeChainFunctor R).obj (TopPair.ofSubset (A ∪ B))
  cases q with
  | zero =>
      exact
        (KB.isoSc' (p + 1) p ((ComplexShape.down ℕ).next p)
            (ChainComplex.prev ℕ p) rfl).hom ≫
          supportCapShortComplexHomZero R X A B p phi hphi ≫
          (Kunion.isoSc' 1 0 0 (ChainComplex.prev ℕ 0)
            ChainComplex.next_nat_zero).inv
  | succ q =>
      exact
        (KB.isoSc' (p + ((q + 1) + 1)) (p + (q + 1)) (p + q)
            (by rw [ChainComplex.prev]; omega)
            (by rw [show p + (q + 1) = (p + q) + 1 by omega,
              ChainComplex.next_nat_succ])).hom ≫
          supportCapShortComplexHomSucc R X A B p q phi hphi ≫
          (Kunion.isoSc' ((q + 1) + 1) (q + 1) q
            (by rw [ChainComplex.prev]) (ChainComplex.next_nat_succ q)).inv

@[simp]
lemma supportCapShortComplexHom_τ₂
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    (supportCapShortComplexHom R X A B p q phi hphi).τ₂ =
      supportCapHom R X A B p q phi := by
  cases q <;> simp [supportCapShortComplexHom, supportCapShortComplexHomZero,
    supportCapShortComplexHomSucc] <;> cat_disch

lemma supportCapShortComplexHom_homologyMap_add
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi psi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0)
    (hpsi : relativeCoboundary R (TopPair.ofSubset A) p psi = 0)
    (hadd : relativeCoboundary R (TopPair.ofSubset A) p (phi + psi) = 0) :
    ShortComplex.homologyMap
        (supportCapShortComplexHom R X A B p q (phi + psi) hadd) =
      ShortComplex.homologyMap
          (supportCapShortComplexHom R X A B p q phi hphi) +
        ShortComplex.homologyMap
          (supportCapShortComplexHom R X A B p q psi hpsi) := by
  rw [← ShortComplex.homologyMap_add]
  apply Simplicial.homologyMap_eq_of_τ₂_eq
  simp [supportCapShortComplexHom_τ₂, supportCapHom_add]
  rfl

lemma supportCapShortComplexHom_homologyMap_smul
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) (a : R)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0)
    (hsmul : relativeCoboundary R (TopPair.ofSubset A) p (a • phi) = 0) :
    ShortComplex.homologyMap
        (supportCapShortComplexHom R X A B p q (a • phi) hsmul) =
      a • ShortComplex.homologyMap
        (supportCapShortComplexHom R X A B p q phi hphi) := by
  rw [← ShortComplex.homologyMap_smul]
  apply Simplicial.homologyMap_eq_of_τ₂_eq
  simp [supportCapShortComplexHom_τ₂, supportCapHom_smul]
  rfl

/-- Cap product with a relative cocycle, descended to the support-valued relative
homology groups. -/
noncomputable def supportCapHomologyMap
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p)
    (hphi : relativeCoboundary R (TopPair.ofSubset A) p phi = 0) :
    RelativeHomology R (TopPair.ofSubset B) (p + q) →ₗ[R]
      RelativeHomology R (TopPair.ofSubset (A ∪ B)) q :=
  (ShortComplex.homologyMap
    (supportCapShortComplexHom R X A B p q phi hphi)).hom

/-- The support-valued cap product is linear in relative cocycles. -/
noncomputable def supportCapCocycleHomologyLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    RelativeCocycle R (TopPair.ofSubset A) p →ₗ[R]
      (RelativeHomology R (TopPair.ofSubset B) (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset (A ∪ B)) q) where
  toFun phi := supportCapHomologyMap R X A B p q phi.1 phi.2
  map_add' phi psi := congrArg ModuleCat.Hom.hom
    (supportCapShortComplexHom_homologyMap_add R X A B p q
      phi.1 psi.1 phi.2 psi.2 (phi + psi).2)
  map_smul' a phi := congrArg ModuleCat.Hom.hom
    (supportCapShortComplexHom_homologyMap_smul R X A B p q
      a phi.1 phi.2 (a • phi).2)

@[simp]
lemma supportCapCocycleHomologyLinear_apply
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCocycle R (TopPair.ofSubset A) p) :
    supportCapCocycleHomologyLinear R X A B p q phi =
      supportCapHomologyMap R X A B p q phi.1 phi.2 :=
  rfl

/-! ### Independence of the relative cocycle representative -/

set_option backward.isDefEq.respectTransparency false in
/-- Cap product by a relative coboundary is chain-null-homotopic for the support-valued
pairing.  Both the source boundary modulo `B` and target boundary modulo `A ∪ B` are
shown explicitly. -/
theorem supportCap_coboundary_eq
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (supportCap R X A B (p + 1) q
        (relativeCoboundary R (TopPair.ofSubset A) p phi)).comp
        (relativeReassocChain R (TopPair.ofSubset B) p q) =
      (supportCap R X A B p q phi).comp
          (relativeBoundary R (TopPair.ofSubset B) (p + q)) -
        (-1 : R) ^ p •
          (relativeBoundary R (TopPair.ofSubset (A ∪ B)) q).comp
            (supportCap R X A B p (q + 1) phi) := by
  ext z
  let π := (relativeChainProjection R (TopPair.ofSubset B)).f (p + q + 1)
  let : Epi π := Cofork.IsColimit.epi
    (relativeChainProjectionComponentIsCokernelForCap R
      (TopPair.ofSubset B) (p + q + 1))
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance z
  dsimp only [π]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  erw [relativeChainProjection_reassoc_apply R (TopPair.ofSubset B) p q c,
    supportCap_projection_apply R X A B (p + 1) q
      (relativeCoboundary R (TopPair.ofSubset A) p phi)
      (Simplicial.reassocChain R p q c),
    relativeBoundary_projection R (TopPair.ofSubset B) (p + q) c,
    supportCap_projection_apply R X A B p q phi
      (Simplicial.boundary R (p + q) c),
    supportCap_projection_apply R X A B p (q + 1) phi c]
  have habsolute := LinearMap.congr_fun
    (Simplicial.cap_coboundary_eq R p q
      (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi)) c
  rw [← relativeCochainToAbsolute_coboundary] at habsolute
  have hprojected := congrArg
    (fun z ↦ ((relativeChainProjection R
      (TopPair.ofSubset (A ∪ B))).f q).hom z) habsolute
  have hboundary := ConcreteCategory.congr_hom
    ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).comm (q + 1) q)
    (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)
  have hboundary' :
      ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
          (Simplicial.boundary R q
            (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) =
        relativeBoundary R (TopPair.ofSubset (A ∪ B)) q
          (((relativeChainProjection R
            (TopPair.ofSubset (A ∪ B))).f (q + 1)).hom
              (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) := hboundary.symm
  change ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
      (Simplicial.cap R (p + 1) q
        (relativeCochainToAbsolute R (TopPair.ofSubset A) (p + 1)
          (relativeCoboundary R (TopPair.ofSubset A) p phi))
        (Simplicial.reassocChain R p q c)) = _
  calc
    _ = ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
        (Simplicial.cap R p q
            (relativeCochainToAbsolute R (TopPair.ofSubset A) p phi)
            (Simplicial.boundary R (p + q) c) -
          (-1 : R) ^ p •
            Simplicial.boundary R q
              (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) := hprojected
    _ = ((relativeChainProjection R (TopPair.ofSubset (A ∪ B))).f q).hom
          (relativeCapLift R (TopPair.ofSubset A) p q phi
            (Simplicial.boundary R (p + q) c)) -
        (-1 : R) ^ p •
          relativeBoundary R (TopPair.ofSubset (A ∪ B)) q
            (((relativeChainProjection R
              (TopPair.ofSubset (A ∪ B))).f (q + 1)).hom
                (relativeCapLift R (TopPair.ofSubset A) p (q + 1) phi c)) := by
      rw [map_sub, map_smul]
      exact congrArg₂ (fun x y ↦ x - (-1 : R) ^ p • y) rfl hboundary'

/-- The short-complex map obtained by capping with a relative coboundary. -/
noncomputable def supportCapCoboundaryShortComplexHom
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    ((relativeChainFunctor R).obj (TopPair.ofSubset B)).sc (p + q + 1) ⟶
      ((relativeChainFunctor R).obj (TopPair.ofSubset (A ∪ B))).sc q :=
  (relativeReassocShortComplexIso R (TopPair.ofSubset B) p q).hom ≫
    supportCapShortComplexHom R X A B (p + 1) q
      (relativeCoboundary R (TopPair.ofSubset A) p phi)
      (relativeCoboundary_relativeCoboundary R (TopPair.ofSubset A) p phi)

lemma supportCapCoboundaryShortComplexHom_τ₂
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (supportCapCoboundaryShortComplexHom R X A B p q phi).τ₂ =
      ModuleCat.ofHom
        ((supportCap R X A B (p + 1) q
          (relativeCoboundary R (TopPair.ofSubset A) p phi)).comp
            (relativeReassocChain R (TopPair.ofSubset B) p q)) := by
  simp [supportCapCoboundaryShortComplexHom,
    relativeReassocShortComplexIso_hom_τ₂, supportCapShortComplexHom_τ₂]
  congr 1

/-- The middle component of the coboundary cap map is the explicit chain-homotopy
difference. -/
lemma supportCapCoboundaryShortComplexHom_τ₂_eq
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    (supportCapCoboundaryShortComplexHom R X A B p q phi).τ₂ =
      ((relativeChainFunctor R).obj (TopPair.ofSubset B)).d
          (p + q + 1) (p + q) ≫ supportCapHom R X A B p q phi -
        (-1 : R) ^ p •
          (supportCapHom R X A B p (q + 1) phi ≫
            ((relativeChainFunctor R).obj
              (TopPair.ofSubset (A ∪ B))).d (q + 1) q) := by
  rw [supportCapCoboundaryShortComplexHom_τ₂]
  exact ModuleCat.hom_ext (supportCap_coboundary_eq R X A B p q phi)

set_option backward.isDefEq.respectTransparency false in
/-- Cap product by a relative coboundary induces zero on support-valued relative
homology. -/
theorem supportCapCoboundary_homologyMap_eq_zero
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    ShortComplex.homologyMap
      (supportCapCoboundaryShortComplexHom R X A B p q phi) = 0 := by
  rw [← cancel_epi (((relativeChainFunctor R).obj
      (TopPair.ofSubset B)).sc (p + q + 1)).homologyπ,
    ← cancel_mono (((relativeChainFunctor R).obj
      (TopPair.ofSubset (A ∪ B))).sc q).homologyι]
  simp only [Category.assoc, zero_comp, comp_zero]
  rw [ShortComplex.π_homologyMap_ι,
    supportCapCoboundaryShortComplexHom_τ₂_eq]
  have hsource :
      (((relativeChainFunctor R).obj
          (TopPair.ofSubset B)).sc (p + q + 1)).iCycles ≫
        ((relativeChainFunctor R).obj
          (TopPair.ofSubset B)).d (p + q + 1) (p + q) = 0 :=
    ((relativeChainFunctor R).obj
      (TopPair.ofSubset B)).iCycles_d (p + q + 1) (p + q)
  have htarget :
      ((relativeChainFunctor R).obj
          (TopPair.ofSubset (A ∪ B))).d (q + 1) q ≫
        (((relativeChainFunctor R).obj
          (TopPair.ofSubset (A ∪ B))).sc q).pOpcycles = 0 :=
    ((relativeChainFunctor R).obj
      (TopPair.ofSubset (A ∪ B))).d_pOpcycles (q + 1) q
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
    Linear.comp_smul]
  simp only [← Category.assoc, hsource, zero_comp]
  simp only [Category.assoc, htarget, comp_zero, smul_zero, sub_zero]

/-- Without degree reassociation, cap product by a relative coboundary still induces
the zero map on homology. -/
theorem supportCapShortComplexHom_coboundary_homologyMap_eq_zero
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    ShortComplex.homologyMap
      (supportCapShortComplexHom R X A B (p + 1) q
        (relativeCoboundary R (TopPair.ofSubset A) p phi)
        (relativeCoboundary_relativeCoboundary R
          (TopPair.ofSubset A) p phi)) = 0 := by
  rw [← cancel_epi (ShortComplex.homologyMap
      (relativeReassocShortComplexIso R (TopPair.ofSubset B) p q).hom),
    ← ShortComplex.homologyMap_comp, comp_zero]
  exact supportCapCoboundary_homologyMap_eq_zero R X A B p q phi

/-- A relative coboundary acts trivially on support-valued relative homology. -/
@[simp]
theorem supportCapHomologyMap_coboundary
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : RelativeCochain R (TopPair.ofSubset A) p) :
    supportCapHomologyMap R X A B (p + 1) q
      (relativeCoboundary R (TopPair.ofSubset A) p phi)
      (relativeCoboundary_relativeCoboundary R
        (TopPair.ofSubset A) p phi) = 0 :=
  congrArg ModuleCat.Hom.hom
    (supportCapShortComplexHom_coboundary_homologyMap_eq_zero
      R X A B p q phi)

/-! ### Descent in the cohomology variable -/

/-- Support-valued cap product on explicit dual cycles in the relative cochain short
complex. -/
noncomputable def supportRelativeCohomologyCycleCapLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    LinearMap.ker
        ((((relativeChainFunctor R).obj
          (TopPair.ofSubset A)).sc p).linearDual.g.hom) →ₗ[R]
      (RelativeHomology R (TopPair.ofSubset B) (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset (A ∪ B)) q) :=
  (supportCapCocycleHomologyLinear R X A B p q).comp
    (relativeCohomologyCycleToCocycle R (TopPair.ofSubset A) p)

/-- Support-valued cap product on dual cycles annihilates the boundaries in the explicit
relative cohomology quotient. -/
lemma supportRelativeCohomologyCycleCapLinear_vanishes_on_boundaries
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
    LinearMap.range T.moduleCatToCycles ≤
      LinearMap.ker (supportRelativeCohomologyCycleCapLinear R X A B p q) := by
  dsimp only
  rintro _ ⟨eta, rfl⟩
  cases p with
  | zero =>
      change supportRelativeCohomologyCycleCapLinear R X A B 0 q
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
        ext c
        let etaF : Module.Dual R (K.sc 0).X₃ := eta
        change etaF (0 : (K.sc 0).X₃) = 0
        exact map_zero etaF
      rw [hz]
      exact map_zero (supportRelativeCohomologyCycleCapLinear R X A B 0 q)
  | succ p =>
      change supportRelativeCohomologyCycleCapLinear R X A B (p + 1) q
        (((((relativeChainFunctor R).obj
          (TopPair.ofSubset A)).sc (p + 1)).linearDual.moduleCatToCycles) eta) = 0
      rw [supportRelativeCohomologyCycleCapLinear, LinearMap.comp_apply,
        relativeCohomologyCycleToCocycle_moduleCatToCycles_succ,
        supportCapCocycleHomologyLinear_apply, supportCapHomologyMap_coboundary]

/-- Support-valued cap product on the explicit quotient of relative cocycles by relative
coboundaries. -/
noncomputable def supportCapCohomologyExplicitLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
    T.moduleCatLeftHomologyData.H →ₗ[R]
      (RelativeHomology R (TopPair.ofSubset B) (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset (A ∪ B)) q) :=
  let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
  (LinearMap.range T.moduleCatToCycles).liftQ
    (supportRelativeCohomologyCycleCapLinear R X A B p q)
    (supportRelativeCohomologyCycleCapLinear_vanishes_on_boundaries
      R X A B p q)

/-- Support-valued cap product on algebraic relative cochain cohomology. -/
noncomputable def supportCapCochainCohomologyLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    RelativeCochainCohomology R (TopPair.ofSubset A) p →ₗ[R]
      (RelativeHomology R (TopPair.ofSubset B) (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset (A ∪ B)) q) :=
  let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
  (supportCapCohomologyExplicitLinear R X A B p q).comp
    T.moduleCatHomologyIso.hom.hom

@[simp]
lemma supportCapCochainCohomologyLinear_on_cycle
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : LinearMap.ker
      ((((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual.g.hom)) :
    let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
    supportCapCochainCohomologyLinear R X A B p q
        (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
      supportRelativeCohomologyCycleCapLinear R X A B p q phi := by
  dsimp only
  let T := (((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual
  change supportCapCohomologyExplicitLinear R X A B p q
      (T.moduleCatHomologyIso.hom.hom
        (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))) = _
  have h := ConcreteCategory.congr_hom T.moduleCatHomologyIso.inv_hom_id
    (Submodule.Quotient.mk phi)
  change T.moduleCatHomologyIso.hom.hom
      (T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
    Submodule.Quotient.mk phi at h
  rw [h]
  rfl

/-- The support-valued cap product on the repository's standard relative cohomology and
homology objects:

`H^p(X,A) → (H_{p+q}(X,B) → H_q(X,A ∪ B))`.

This is the convention needed to cap a class supported away from `A` with a class
relative to a compactification boundary `B`.  Its target is the ordinary union-relative
homology object, without an arbitrary equivalence or an excision hypothesis. -/
noncomputable def supportCapCohomologyLinear
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ) :
    RelativeCohomology R (TopPair.ofSubset A) p →ₗ[R]
      (RelativeHomology R (TopPair.ofSubset B) (p + q) →ₗ[R]
        RelativeHomology R (TopPair.ofSubset (A ∪ B)) q) :=
  (supportCapCochainCohomologyLinear R X A B p q).comp
    (((relativeChainFunctor R).obj
      (TopPair.ofSubset A)).sc p).linearDualHomologyEquiv.symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma supportCapCohomologyLinear_on_cycle
    (X : TopCat.{u}) (A B : Set X) (p q : ℕ)
    (phi : LinearMap.ker
      ((((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p).linearDual.g.hom)) :
    let S := ((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p
    supportCapCohomologyLinear R X A B p q
        (S.linearDualHomologyEquiv
          (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))) =
      supportRelativeCohomologyCycleCapLinear R X A B p q phi := by
  dsimp only
  rw [supportCapCohomologyLinear, LinearMap.comp_apply]
  let S := ((relativeChainFunctor R).obj (TopPair.ofSubset A)).sc p
  have h := S.linearDualHomologyEquiv.symm_apply_apply
    (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))
  change supportCapCochainCohomologyLinear R X A B p q
      (S.linearDualHomologyEquiv.symm
        (S.linearDualHomologyEquiv
          (S.linearDual.moduleCatHomologyIso.inv.hom
            (Submodule.Quotient.mk phi)))) = _
  rw [h]
  exact supportCapCochainCohomologyLinear_on_cycle R X A B p q phi

end AlgebraicTopology.Singular
