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

public import Other.AlgebraicTopology.SingularRelativeCapProduct
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
public import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-!
# Naturality of cap product on homology

The chain-level Alexander--Whitney formula induces the projection formula
`f_* (f^* φ ⌢ c) = φ ⌢ f_* c` for every cocycle `φ` and homology class `c`.
Both maps are the actual maps induced on singular chains. No orientation, duality equivalence,
or compatibility theorem is passed as data.

This is a prerequisite for geometric duality, not a proof that capping with an orientation
class is an equivalence or that a global orientation class exists.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicTopology.Simplicial

variable (R : Type u) [Field R]

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of simplicial cochains commutes with coboundary. -/
lemma coboundary_cochainMap {X Y : SSet.{u}} (f : X ⟶ Y) (p : ℕ)
    (phi : Cochain R Y p) :
    coboundary R p (cochainMap R f p phi) =
      cochainMap R f (p + 1) (coboundary R p phi) := by
  ext c
  change phi (((SSet.chainComplexMap f (ModuleCat.of R R)).f p).hom
      (((X.chainComplex (ModuleCat.of R R)).d (p + 1) p).hom c)) =
    phi (((Y.chainComplex (ModuleCat.of R R)).d (p + 1) p).hom
      (((SSet.chainComplexMap f (ModuleCat.of R R)).f (p + 1)).hom c))
  exact congrArg phi (ConcreteCategory.congr_hom
    ((SSet.chainComplexMap f (ModuleCat.of R R)).comm (p + 1) p) c).symm

/-- The actual cochain pullback restricted to cocycles. -/
def cocycleMap {X Y : SSet.{u}} (f : X ⟶ Y) (p : ℕ) :
    Cocycle R Y p →ₗ[R] Cocycle R X p :=
  (cochainMap R f p).restrict
    (fun phi hphi ↦ by
      change coboundary R p (cochainMap R f p phi) = 0
      rw [coboundary_cochainMap, show coboundary R p phi = 0 from hphi, map_zero])

@[simp]
lemma cocycleMap_val {X Y : SSet.{u}} (f : X ⟶ Y) (p : ℕ)
    (phi : Cocycle R Y p) :
    (cocycleMap R f p phi).1 = cochainMap R f p phi.1 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the cap product after descent in the homology variable. -/
theorem capHomologyMap_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (p q : ℕ)
    (phi : Cocycle R Y p) :
    (HomologicalComplex.homologyMap (SSet.chainComplexMap f (ModuleCat.of R R)) q).hom.comp
        (capHomologyMap R p q (cocycleMap R f p phi).1
          (cocycleMap R f p phi).2) =
      (capHomologyMap R p q phi.1 phi.2).comp
        (HomologicalComplex.homologyMap
          (SSet.chainComplexMap f (ModuleCat.of R R)) (p + q)).hom := by
  let F := SSet.chainComplexMap f (ModuleCat.of R R)
  let Fpq := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) (p + q)).map F
  let Fq := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) q).map F
  have h :
      ShortComplex.homologyMap
        (capShortComplexHom R p q (cocycleMap R f p phi).1
          (cocycleMap R f p phi).2 ≫ Fq) =
      ShortComplex.homologyMap (Fpq ≫ capShortComplexHom R p q phi.1 phi.2) := by
    apply homologyMap_eq_of_τ₂_eq
    simp only [ShortComplex.comp_τ₂, capShortComplexHom_τ₂]
    exact ModuleCat.hom_ext (LinearMap.ext fun c => cap_naturality R f p q phi.1 c)
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h
  exact congrArg ModuleCat.Hom.hom h

/-- Pullback on cochain cohomology, induced by the actual dual chain map. -/
def cochainCohomologyMap {X Y : SSet.{u}} (f : X ⟶ Y) (p : ℕ) :
    CochainCohomology R Y p →ₗ[R] CochainCohomology R X p :=
  (ShortComplex.homologyMap (ShortComplex.linearDualMap
    ((HomologicalComplex.shortComplexFunctor
      (ModuleCat.{u} R) (ComplexShape.down ℕ) p).map
        (SSet.chainComplexMap f (ModuleCat.of R R))))).hom

set_option backward.isDefEq.respectTransparency false in
/-- Naturality after descent in both the cochain and chain variables. -/
theorem capCohomologyLinear_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (p q : ℕ)
    (alpha : CochainCohomology R Y p) :
    (HomologicalComplex.homologyMap (SSet.chainComplexMap f (ModuleCat.of R R)) q).hom.comp
        (capCohomologyLinear R p q (cochainCohomologyMap R f p alpha)) =
      (capCohomologyLinear R p q alpha).comp
        (HomologicalComplex.homologyMap
          (SSet.chainComplexMap f (ModuleCat.of R R)) (p + q)).hom := by
  let S := (X.chainComplex (ModuleCat.of R R)).sc p
  let T := (Y.chainComplex (ModuleCat.of R R)).sc p
  let F := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) p).map
      (SSet.chainComplexMap f (ModuleCat.of R R))
  obtain ⟨phi, rfl⟩ := T.linearDual.moduleCatHomologyClass_surjective alpha
  change (HomologicalComplex.homologyMap
      (SSet.chainComplexMap f (ModuleCat.of R R)) q).hom.comp (capCohomologyLinear R p q
      ((ShortComplex.homologyMap (ShortComplex.linearDualMap F)).hom
        (T.linearDual.moduleCatHomologyClass phi))) = _
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  change (HomologicalComplex.homologyMap
      (SSet.chainComplexMap f (ModuleCat.of R R)) q).hom.comp (capCohomologyLinear R p q
      (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk _))) =
    (capCohomologyLinear R p q
      (T.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))).comp _
  rw [capCohomologyLinear_on_cycle, capCohomologyLinear_on_cycle]
  exact capHomologyMap_naturality R f p q (cohomologyCycleToCocycle R p phi)

end AlgebraicTopology.Simplicial

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

/-- Pullback of singular cocycles along the actual continuous map. -/
def cocycleMap {X Y : TopCat.{u}} (f : X ⟶ Y) (p : ℕ) :
    Cocycle R Y p →ₗ[R] Cocycle R X p :=
  Simplicial.cocycleMap R (TopCat.toSSet.map f) p

/-- The cap projection formula for a continuous map, a cocycle, and a homology class. -/
theorem capHomologyMap_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (p q : ℕ)
    (phi : Cocycle R Y p) (c : Homology R X (p + q)) :
    homologyMap R q f (capHomologyMap R X p q (cocycleMap R f p phi) c) =
      capHomologyMap R Y p q phi (homologyMap R (p + q) f c) :=
  LinearMap.congr_fun
    (Simplicial.capHomologyMap_naturality R (TopCat.toSSet.map f) p q phi) c

/-- The pullback on singular cochain cohomology induced by the continuous map. -/
def cochainCohomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y) (p : ℕ) :
    CochainCohomology R Y p →ₗ[R] CochainCohomology R X p :=
  Simplicial.cochainCohomologyMap R (TopCat.toSSet.map f) p

/-- The universal-coefficient comparison respects the actual pullback maps. -/
theorem cochainCohomologyEquiv_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (p : ℕ)
    (alpha : CochainCohomology R Y p) :
    cochainCohomologyEquiv R X p (cochainCohomologyMap R f p alpha) =
      cohomologyMap R p f (cochainCohomologyEquiv R Y p alpha) := by
  set eX := (ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex R X) p)).toLinearEquiv
  set eY := (ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex R Y) p)).toLinearEquiv
  have hnat := congrArg (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map
    (HomologicalComplex.linearDualCochainComplexScIso_naturality (singularChainComplexMap R f) p)
  rw [Functor.map_comp, Functor.map_comp] at hnat
  have ha : eX (cohomologyMap R p f (eY.symm alpha)) =
      cochainCohomologyMap R f p (eY (eY.symm alpha)) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hnat) (eY.symm alpha)
  rw [eY.apply_symm_apply] at ha
  exact eX.symm_apply_eq.2 ha.symm

/-- The singular cap projection formula is independent of both representatives. -/
theorem capCohomologyLinear_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (p q : ℕ)
    (alpha : CochainCohomology R Y p) (c : Homology R X (p + q)) :
    homologyMap R q f
        (capCohomologyLinear R X p q (cochainCohomologyMap R f p alpha) c) =
      capCohomologyLinear R Y p q alpha (homologyMap R (p + q) f c) :=
  LinearMap.congr_fun
    (Simplicial.capCohomologyLinear_naturality R (TopCat.toSSet.map f) p q alpha) c

/-- Cap product in the repository's standard, homology-dual model of singular cohomology.
The comparison is the constructed universal-coefficient map. -/
def standardCapCohomologyLinear (X : TopCat.{u}) (p q : ℕ) :
    Cohomology R X p →ₗ[R] (Homology R X (p + q) →ₗ[R] Homology R X q) :=
  (capCohomologyLinear R X p q).comp (cochainCohomologyEquiv R X p).symm.toLinearMap

/-- Naturality for the standard singular cohomology and homology APIs. -/
theorem standardCapCohomologyLinear_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (p q : ℕ)
    (alpha : Cohomology R Y p) (c : Homology R X (p + q)) :
    homologyMap R q f
        (standardCapCohomologyLinear R X p q (cohomologyMap R p f alpha) c) =
      standardCapCohomologyLinear R Y p q alpha (homologyMap R (p + q) f c) := by
  have hpull :
      (cochainCohomologyEquiv R X p).symm (cohomologyMap R p f alpha) =
        cochainCohomologyMap R f p ((cochainCohomologyEquiv R Y p).symm alpha) := by
    apply (cochainCohomologyEquiv R X p).injective
    rw [LinearEquiv.apply_symm_apply, cochainCohomologyEquiv_naturality,
      LinearEquiv.apply_symm_apply]
  change homologyMap R q f
      (capCohomologyLinear R X p q
        ((cochainCohomologyEquiv R X p).symm (cohomologyMap R p f alpha)) c) = _
  rw [hpull]
  exact capCohomologyLinear_naturality R f p q
    ((cochainCohomologyEquiv R Y p).symm alpha) c

/-- Pullback of relative cochains along a continuous map of pairs. -/
def relativeCochainMap {X Y : TopPair.{u}} (f : X ⟶ Y) (p : ℕ) :
    RelativeCochain R Y p →ₗ[R] RelativeCochain R X p :=
  (((relativeChainFunctor R).map f).f p).hom.dualMap

set_option backward.isDefEq.respectTransparency false in
/-- Relative cochain pullback commutes with coboundary. -/
lemma relativeCoboundary_relativeCochainMap {X Y : TopPair.{u}} (f : X ⟶ Y) (p : ℕ)
    (phi : RelativeCochain R Y p) :
    relativeCoboundary R X p (relativeCochainMap R f p phi) =
      relativeCochainMap R f (p + 1) (relativeCoboundary R Y p phi) := by
  ext c
  exact congrArg phi (ConcreteCategory.congr_hom
    (((relativeChainFunctor R).map f).comm (p + 1) p) c).symm

/-- Relative cocycles pull back along maps of pairs. -/
def relativeCocycleMap {X Y : TopPair.{u}} (f : X ⟶ Y) (p : ℕ) :
    RelativeCocycle R Y p →ₗ[R] RelativeCocycle R X p :=
  (relativeCochainMap R f p).restrict
    (fun phi hphi ↦ by
      change relativeCoboundary R X p (relativeCochainMap R f p phi) = 0
      rw [relativeCoboundary_relativeCochainMap,
        show relativeCoboundary R Y p phi = 0 from hphi, map_zero])

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting that a cochain is relative commutes with pullback. -/
lemma relativeCochainToAbsolute_relativeCochainMap {X Y : TopPair.{u}}
    (f : X ⟶ Y) (p : ℕ) (phi : RelativeCochain R Y p) :
    relativeCochainToAbsolute R X p (relativeCochainMap R f p phi) =
      Simplicial.cochainMap R (TopCat.toSSet.map (TopPair.Hom.fst f)) p
        (relativeCochainToAbsolute R Y p phi) := by
  ext c
  exact congrArg phi (ConcreteCategory.congr_hom
    (congrArg (fun g ↦ g.f p)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := R) f)) c)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the relative-to-absolute cap product on chains. -/
lemma relativeCapHom_naturality {X Y : TopPair.{u}} (f : X ⟶ Y) (p q : ℕ)
    (phi : RelativeCochain R Y p) :
    relativeCapHom R X p q (relativeCochainMap R f p phi) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
          (ModuleCat.of R R)).f q =
      ((relativeChainFunctor R).map f).f (p + q) ≫ relativeCapHom R Y p q phi := by
  apply CategoryTheory.Limits.Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap R X (p + q))
  change (relativeChainProjection R X).f (p + q) ≫
      (relativeCapHom R X p q (relativeCochainMap R f p phi) ≫ _) =
    (relativeChainProjection R X).f (p + q) ≫
      (((relativeChainFunctor R).map f).f (p + q) ≫ _)
  rw [← Category.assoc, relativeChainProjection_relativeCapHom, ← Category.assoc]
  have hnat := congrArg (fun g ↦ g.f (p + q))
    (TopPair.Homotopy.relativeChainProjection_naturality (R := R) f)
  change (relativeChainProjection R X).f (p + q) ≫
      ((relativeChainFunctor R).map f).f (p + q) =
    (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
      (ModuleCat.of R R)).f (p + q) ≫ (relativeChainProjection R Y).f (p + q) at hnat
  rw [hnat, Category.assoc, relativeChainProjection_relativeCapHom]
  refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
  change ((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
      (ModuleCat.of R R)).f q).hom (Simplicial.cap R p q
      (relativeCochainToAbsolute R X p (relativeCochainMap R f p phi)) c) =
    Simplicial.cap R p q (relativeCochainToAbsolute R Y p phi)
      (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
        (ModuleCat.of R R)).f (p + q)).hom c)
  rw [relativeCochainToAbsolute_relativeCochainMap]
  exact Simplicial.cap_naturality R (TopCat.toSSet.map (TopPair.Hom.fst f)) p q
    (relativeCochainToAbsolute R Y p phi) c

set_option backward.isDefEq.respectTransparency false in
/-- The relative cap projection formula on homology. Its output is ordinary homology
of the ambient space, as in the existing same-pair cap product. -/
theorem relativeCapHomologyMap_naturality {X Y : TopPair.{u}} (f : X ⟶ Y) (p q : ℕ)
    (phi : RelativeCocycle R Y p) (c : RelativeHomology R X (p + q)) :
    homologyMap R q (TopPair.Hom.fst f)
        (relativeCapHomologyMap R X p q (relativeCocycleMap R f p phi).1
          (relativeCocycleMap R f p phi).2 c) =
      relativeCapHomologyMap R Y p q phi.1 phi.2
        (relativeHomologyMap R (p + q) f c) := by
  let Frel := (relativeChainFunctor R).map f
  let Fabs := SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
    (ModuleCat.of R R)
  let Fpq := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) (p + q)).map Frel
  let Fq := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) q).map Fabs
  have h :
      ShortComplex.homologyMap
        (relativeCapShortComplexHom R X p q (relativeCocycleMap R f p phi).1
          (relativeCocycleMap R f p phi).2 ≫ Fq) =
      ShortComplex.homologyMap
        (Fpq ≫ relativeCapShortComplexHom R Y p q phi.1 phi.2) := by
    apply Simplicial.homologyMap_eq_of_τ₂_eq
    simp only [ShortComplex.comp_τ₂, relativeCapShortComplexHom_τ₂]
    exact relativeCapHom_naturality R f p q phi.1
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

end AlgebraicTopology.Singular
