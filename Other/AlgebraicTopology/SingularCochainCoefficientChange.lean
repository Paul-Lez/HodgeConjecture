/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SimplicialCochainCoefficientChange
public import Other.AlgebraicTopology.SingularSubdivisionCochainSheaf
public import Other.AlgebraicGeometry.BettiGlobalSectionsComparison
public import Other.AlgebraicGeometry.ComplexSingularComparison
public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration

/-!
# Change of coefficients on singular-cochain sheaves

A ring homomorphism `f : R →+* S` induces, by postcomposition on the function model of
cochains, a morphism between the singular-cochain presheaf complexes with coefficients in `R`
and `S`. This file records that morphism, its degreewise sheafification, and its compatibility
with the augmentation from constants, with the extension by zero to integer degrees on the
analytic space of a complex scheme, with the comparison between top-open cochains and global
sections of the sheafified complex, and with the identification of ordinary singular cohomology
with the cohomology of top-open cochains.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (X : TopCat.{u})

/-- The singular simplicial set of an open subset of `X`. -/
abbrev openSSet (U : (Opens X)ᵒᵖ) : SSet.{u} :=
  TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)

/-- Change of coefficients on the singular cochains of an open subset. -/
def openCochainCoefficientChange (U : (Opens X)ᵒᵖ) (n : ℕ) :
    OpenCochains R X U n →+ OpenCochains S X U n :=
  SSet.dualCoefficientChange f (openSSet X U) n

set_option backward.isDefEq.respectTransparency false in
/-- Change of coefficients on the singular cochain presheaf in a fixed degree. -/
def singularCochainPresheafMap (n : ℕ) :
    singularCochainPresheaf R X n ⟶ singularCochainPresheaf S X n where
  app U := AddCommGrpCat.ofHom (openCochainCoefficientChange f X U n)
  naturality {U V} i := by
    ext φ
    change OpenCochains R X U n at φ
    change openCochainCoefficientChange f X V n
        ((((openSingularChainComplexFunctor R X).map i.unop).f n).hom.dualMap φ) =
      (((openSingularChainComplexFunctor S X).map i.unop).f n).hom.dualMap
        (openCochainCoefficientChange f X U n φ)
    exact SSet.dualCoefficientChange_dualMap f (openSSet X V)
      (TopCat.toSSet.map ((Opens.toTopCat X).map i.unop)) n φ

@[simp]
lemma singularCochainPresheafMap_app (n : ℕ) (U : (Opens X)ᵒᵖ) :
    (singularCochainPresheafMap f X n).app U =
      AddCommGrpCat.ofHom (openCochainCoefficientChange f X U n) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Change of coefficients commutes with the singular coboundary. -/
lemma singularCochainCoboundary_comp_presheafMap (n : ℕ) :
    singularCochainCoboundary R X n ≫ singularCochainPresheafMap f X (n + 1) =
      singularCochainPresheafMap f X n ≫ singularCochainCoboundary S X n := by
  apply NatTrans.ext
  funext U
  ext φ
  change OpenCochains R X U n at φ
  change openCochainCoefficientChange f X U (n + 1)
      ((((openSingularChainComplexFunctor R X).obj U.unop).d (n + 1) n).hom.dualMap φ) =
    (((openSingularChainComplexFunctor S X).obj U.unop).d (n + 1) n).hom.dualMap
      (openCochainCoefficientChange f X U n φ)
  exact SSet.dualCoefficientChange_dualMap_d f (openSSet X U) n φ

/-- Change of coefficients on the singular cochain presheaf complex. -/
def singularCochainPresheafComplexMap :
    singularCochainPresheafComplex R X ⟶ singularCochainPresheafComplex S X where
  f n := singularCochainPresheafMap f X n
  comm' i j hij := by
    obtain rfl := hij
    rw [singularCochainPresheafComplex_d, singularCochainPresheafComplex_d]
    exact (singularCochainCoboundary_comp_presheafMap f X i).symm

@[simp]
lemma singularCochainPresheafComplexMap_f (n : ℕ) :
    (singularCochainPresheafComplexMap f X).f n = singularCochainPresheafMap f X n :=
  rfl

/-- Change of coefficients on the degreewise sheafified singular cochain complex. -/
def singularCochainSheafComplexMap :
    singularCochainSheafComplex R X ⟶ singularCochainSheafComplex S X :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularCochainPresheafComplexMap f X)

/-- Change of coefficients on the constant presheaf. -/
def constantCoefficientPresheafMap :
    constantCoefficientPresheaf R X ⟶ constantCoefficientPresheaf S X :=
  (Functor.const (Opens X)ᵒᵖ).map (AddCommGrpCat.ofHom f.toAddMonoidHom)

/-- Change of coefficients on the constant sheaf. -/
def constantCoefficientSheafMap :
    constantCoefficientSheaf R X ⟶ constantCoefficientSheaf S X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (AddCommGrpCat.ofHom f.toAddMonoidHom)

set_option backward.isDefEq.respectTransparency false in
/-- Change of coefficients sends the constant zero-cochain with value `r` to the constant
zero-cochain with value `f r`. -/
lemma openCochainCoefficientChange_constantSingularZeroCochain (U : (Opens X)ᵒᵖ) (r : R) :
    openCochainCoefficientChange f X U 0 (constantSingularZeroCochain R X U r) =
      constantSingularZeroCochain S X U (f r) := by
  apply SSet.dualToFun_injective S (openSSet X U) 0
  change SSet.dualToFun S (openSSet X U) 0
      (SSet.dualCoefficientChange f (openSSet X U) 0 (constantSingularZeroCochain R X U r)) = _
  rw [SSet.dualToFun_dualCoefficientChange]
  funext x
  have hR : (simplicialZeroAugmentation R (openSSet X U)).hom
      (SSet.chainOfSimplex R (openSSet X U) 0 x) = 1 :=
    congrArg (fun g ↦ g.hom 1)
      (ιChainComplex_comp_simplicialZeroAugmentation R (openSSet X U) x)
  have hS : (simplicialZeroAugmentation S (openSSet X U)).hom
      (SSet.chainOfSimplex S (openSSet X U) 0 x) = 1 :=
    congrArg (fun g ↦ g.hom 1)
      (ιChainComplex_comp_simplicialZeroAugmentation S (openSSet X U) x)
  simp only [Function.comp_apply, SSet.dualToFun_apply]
  change f ((r • (openZeroAugmentation R X U).hom) (SSet.chainOfSimplex R (openSSet X U) 0 x)) =
    (f r • (openZeroAugmentation S X U).hom) (SSet.chainOfSimplex S (openSSet X U) 0 x)
  rw [LinearMap.smul_apply, LinearMap.smul_apply]
  change f (r • (simplicialZeroAugmentation R (openSSet X U)).hom
      (SSet.chainOfSimplex R (openSSet X U) 0 x)) =
    f r • (simplicialZeroAugmentation S (openSSet X U)).hom
      (SSet.chainOfSimplex S (openSSet X U) 0 x)
  rw [hR, hS, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf-level augmentation from constants is compatible with change of
coefficients. -/
lemma constantsToSingularCochainZero_comp_presheafMap :
    constantsToSingularCochainZero R X ≫ singularCochainPresheafMap f X 0 =
      constantCoefficientPresheafMap f X ≫ constantsToSingularCochainZero S X := by
  apply NatTrans.ext
  funext U
  ext r
  change R at r
  exact openCochainCoefficientChange_constantSingularZeroCochain f X U r

/-- The sheaf-level augmentation from constants is compatible with change of coefficients. -/
lemma constantsToSingularCochainZeroSheaf_comp_map :
    constantsToSingularCochainZeroSheaf R X ≫ (singularCochainSheafComplexMap f X).f 0 =
      constantCoefficientSheafMap f X ≫ constantsToSingularCochainZeroSheaf S X := by
  let J := Opens.grothendieckTopology X
  change (presheafToSheaf J AddCommGrpCat).map (constantsToSingularCochainZero R X) ≫
      (presheafToSheaf J AddCommGrpCat).map (singularCochainPresheafMap f X 0) =
    (presheafToSheaf J AddCommGrpCat).map (constantCoefficientPresheafMap f X) ≫
      (presheafToSheaf J AddCommGrpCat).map (constantsToSingularCochainZero S X)
  rw [← Functor.map_comp, ← Functor.map_comp, constantsToSingularCochainZero_comp_presheafMap]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma constantsToSingularCochainSheafComplex_f_zero :
    (constantsToSingularCochainSheafComplex R X).f 0 =
      constantsToSingularCochainZeroSheaf R X := by
  unfold constantsToSingularCochainSheafComplex
  rw [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison from the constant sheaf complex to the singular-cochain sheaf complex is
natural in the coefficient ring. -/
lemma constantsToSingularCochainSheafComplex_comp_map :
    constantsToSingularCochainSheafComplex R X ≫ singularCochainSheafComplexMap f X =
      (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat X)).map
          (constantCoefficientSheafMap f X) ≫
        constantsToSingularCochainSheafComplex S X := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    constantsToSingularCochainSheafComplex_f_zero,
    constantsToSingularCochainSheafComplex_f_zero,
    HomologicalComplex.single_map_f_self]
  simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  exact constantsToSingularCochainZeroSheaf_comp_map f X

/-- Change of coefficients on the raw singular cochain complex evaluated on the top open
subset. -/
def globalRawSingularCochainComplexMap :
    globalRawSingularCochainComplex R X ⟶ globalRawSingularCochainComplex S X :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularCochainPresheafComplexMap f X)

@[simp]
lemma globalRawSingularCochainComplexMap_f (n : ℕ) :
    (globalRawSingularCochainComplexMap f X).f n =
      (singularCochainPresheafMap f X n).app (.op ⊤) :=
  rfl

/-- Change of coefficients on the underlying presheaf complex of the singular-cochain sheaf
complex. -/
def forgottenSingularCochainSheafComplexMap :
    forgottenSingularCochainSheafComplex R X ⟶ forgottenSingularCochainSheafComplex S X :=
  ((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (singularCochainSheafComplexMap f X)

/-- Change of coefficients on global sections of the singular-cochain sheaf complex. -/
def globalSingularCochainSheafComplexMap :
    globalSingularCochainSheafComplex R X ⟶ globalSingularCochainSheafComplex S X :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (forgottenSingularCochainSheafComplexMap f X)

set_option backward.isDefEq.respectTransparency false in
/-- The double-plus comparison to the chosen sheafification is natural in the coefficient
ring, at the level of presheaf complexes. -/
lemma singularCochainToPlusPlus_comp_isoSheafComplex_comp_map :
    singularCochainToPlusPlusPresheafComplex R X ≫
        (singularCochainPlusPlusPresheafComplexIsoSheafComplex R X).hom ≫
          forgottenSingularCochainSheafComplexMap f X =
      singularCochainPresheafComplexMap f X ≫
        singularCochainToPlusPlusPresheafComplex S X ≫
          (singularCochainPlusPlusPresheafComplexIsoSheafComplex S X).hom := by
  let J := Opens.grothendieckTopology X
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, singularCochainToPlusPlusPresheafComplex_f]
  change J.toSheafify (singularCochainPresheaf R X n) ≫
      (plusPlusIsoSheafify J AddCommGrpCat (singularCochainPresheaf R X n)).hom ≫
        sheafifyMap J (singularCochainPresheafMap f X n) =
    singularCochainPresheafMap f X n ≫ J.toSheafify (singularCochainPresheaf S X n) ≫
      (plusPlusIsoSheafify J AddCommGrpCat (singularCochainPresheaf S X n)).hom
  rw [toSheafify_plusPlusIsoSheafify_hom_assoc, toSheafify_plusPlusIsoSheafify_hom,
    toSheafify_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison from top-open cochains to global sections of the singular-cochain sheaf
complex is natural in the coefficient ring. -/
lemma topOpenToGlobalSingularCochainSheafComplex_comp_map :
    topOpenToGlobalSingularCochainSheafComplex R X ≫
        globalSingularCochainSheafComplexMap f X =
      globalRawSingularCochainComplexMap f X ≫
        topOpenToGlobalSingularCochainSheafComplex S X := by
  let E := ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  change (E.map (singularCochainToPlusPresheafComplex R X) ≫
      E.map (singularCochainPlusToPlusPlusPresheafComplex R X)) ≫
    E.map (singularCochainPlusPlusPresheafComplexIsoSheafComplex R X).hom ≫
      E.map (forgottenSingularCochainSheafComplexMap f X) =
    E.map (singularCochainPresheafComplexMap f X) ≫
      (E.map (singularCochainToPlusPresheafComplex S X) ≫
        E.map (singularCochainPlusToPlusPlusPresheafComplex S X)) ≫
      E.map (singularCochainPlusPlusPresheafComplexIsoSheafComplex S X).hom
  simp only [← Functor.map_comp]
  congr 1
  have h := singularCochainToPlusPlus_comp_isoSheafComplex_comp_map f X
  simpa only [singularCochainToPlusPlusPresheafComplex, Category.assoc] using h

variable (R) in
/-- The ordinary singular cochain complex of `X`, with its scalar structure forgotten. -/
abbrev ordinaryForgottenSingularCochainComplex : CochainComplex AddCommGrpCat ℕ :=
  ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (SingularChainComplex R X).linearDualCochainComplex

variable (R) in
/-- Forgetting scalar multiplication commutes with taking the homology of the ordinary singular
cochain complex. -/
def ordinaryForgottenSingularCochainHomologyIso (n : ℕ) :
    (ordinaryForgottenSingularCochainComplex R X).homology n ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat).obj (OrdinarySingularCohomology R X n) :=
  ShortComplex.mapHomologyIso ((SingularChainComplex R X).linearDualCochainComplex.sc n)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat)

set_option backward.isDefEq.respectTransparency false in
/-- Change of coefficients on the forgotten ordinary singular cochain complex. -/
def ordinaryForgottenSingularCochainCoefficientChange :
    ordinaryForgottenSingularCochainComplex R X ⟶ ordinaryForgottenSingularCochainComplex S X :=
  SSet.linearDualCoefficientChange f (TopCat.toSSet.obj X)

set_option backward.isDefEq.respectTransparency false in
/-- Change of coefficients on the forgotten top-open singular cochain complex. -/
def topOpenForgottenSingularCochainCoefficientChange :
    topOpenForgottenSingularCochainComplex R X ⟶ topOpenForgottenSingularCochainComplex S X :=
  SSet.linearDualCoefficientChange f (TopCat.toSSet.obj ((Opens.toTopCat X).obj ⊤))

set_option backward.isDefEq.respectTransparency false in
/-- Change of coefficients on ordinary singular cohomology. -/
def ordinarySingularCohomologyCoefficientChange (n : ℕ) :
    OrdinarySingularCohomology R X n →+ OrdinarySingularCohomology S X n :=
  ((ordinaryForgottenSingularCochainHomologyIso R X n).inv ≫
    HomologicalComplex.homologyMap (ordinaryForgottenSingularCochainCoefficientChange f X) n ≫
      (ordinaryForgottenSingularCochainHomologyIso S X n).hom).hom

set_option backward.isDefEq.respectTransparency false in
/-- The identification of raw global cochains with forgotten top-open cochains is compatible
with change of coefficients. -/
lemma globalRawSingularCochainComplexIso_hom_comp_coefficientChange :
    (globalRawSingularCochainComplexIso R X).hom ≫
        topOpenForgottenSingularCochainCoefficientChange f X =
      globalRawSingularCochainComplexMap f X ≫
        (globalRawSingularCochainComplexIso S X).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identification of ordinary with top-open cochains is compatible with change of
coefficients. -/
lemma singularCochainComplexIsoTopOpen_hom_comp_coefficientChange :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (singularCochainComplexIsoTopOpen R X).hom ≫
        topOpenForgottenSingularCochainCoefficientChange f X =
      ordinaryForgottenSingularCochainCoefficientChange f X ≫
        ((forget₂ (ModuleCat.{u} S) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (singularCochainComplexIsoTopOpen S X).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  ext ψ
  change Module.Dual R (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n) at ψ
  change SSet.dualCoefficientChange f (TopCat.toSSet.obj ((Opens.toTopCat X).obj ⊤)) n
      (((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusionTopIso X).hom)
        (ModuleCat.of R R)).f n).hom.dualMap ψ) =
    ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusionTopIso X).hom)
        (ModuleCat.of S S)).f n).hom.dualMap
      (SSet.dualCoefficientChange f (TopCat.toSSet.obj X) n ψ)
  exact SSet.dualCoefficientChange_dualMap f _ _ n ψ

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the comparison between homology after forgetting scalars and the forgotten
homology, for morphisms of cochain complexes of modules. -/
lemma homologyMap_mapHomologicalComplex_comp_mapHomologyIso_hom
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (ψ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).map ψ) n ≫
        (ShortComplex.mapHomologyIso (L.sc n) (forget₂ (ModuleCat.{u} R) AddCommGrpCat)).hom =
      (ShortComplex.mapHomologyIso (K.sc n) (forget₂ (ModuleCat.{u} R) AddCommGrpCat)).hom ≫
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat).map (HomologicalComplex.homologyMap ψ n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map ψ)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat)

set_option backward.isDefEq.respectTransparency false in
/-- The forgotten top-open coefficient change, transported to raw global cochains, is the
evaluation of the presheaf coefficient change. -/
lemma topOpenForgottenSingularCochainCoefficientChange_comp_inv :
    topOpenForgottenSingularCochainCoefficientChange f X ≫
        (globalRawSingularCochainComplexIso S X).inv =
      (globalRawSingularCochainComplexIso R X).inv ≫ globalRawSingularCochainComplexMap f X := by
  rw [Iso.comp_inv_eq, Category.assoc,
    ← globalRawSingularCochainComplexIso_hom_comp_coefficientChange, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The composite identification of ordinary singular cohomology with raw global cochain
cohomology is compatible with change of coefficients, as an equation of morphisms. -/
lemma ordinarySingularCohomologyCoefficientChange_comm_hom (n : ℕ) :
    (ordinaryForgottenSingularCochainHomologyIso R X n).inv ≫
      HomologicalComplex.homologyMap
        (ordinaryForgottenSingularCochainCoefficientChange f X) n ≫
      (ordinaryForgottenSingularCochainHomologyIso S X n).hom ≫
      (forget₂ (ModuleCat.{u} S) AddCommGrpCat).map
        (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen S X).hom n) ≫
      (topOpenForgottenSingularCochainHomologyIso S X n).inv ≫
      HomologicalComplex.homologyMap (globalRawSingularCochainComplexIso S X).inv n =
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat).map
        (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen R X).hom n) ≫
      (topOpenForgottenSingularCochainHomologyIso R X n).inv ≫
      HomologicalComplex.homologyMap (globalRawSingularCochainComplexIso R X).inv n ≫
      HomologicalComplex.homologyMap (globalRawSingularCochainComplexMap f X) n := by
  have hR : (forget₂ (ModuleCat.{u} R) AddCommGrpCat).map
      (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen R X).hom n) =
      (ordinaryForgottenSingularCochainHomologyIso R X n).inv ≫
        HomologicalComplex.homologyMap
          (((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (singularCochainComplexIsoTopOpen R X).hom) n ≫
        (topOpenForgottenSingularCochainHomologyIso R X n).hom := by
    rw [Iso.eq_inv_comp]
    exact (homologyMap_mapHomologicalComplex_comp_mapHomologyIso_hom
      (singularCochainComplexIsoTopOpen R X).hom n).symm
  have hS : (forget₂ (ModuleCat.{u} S) AddCommGrpCat).map
      (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen S X).hom n) =
      (ordinaryForgottenSingularCochainHomologyIso S X n).inv ≫
        HomologicalComplex.homologyMap
          (((forget₂ (ModuleCat.{u} S) AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (singularCochainComplexIsoTopOpen S X).hom) n ≫
        (topOpenForgottenSingularCochainHomologyIso S X n).hom := by
    rw [Iso.eq_inv_comp]
    exact (homologyMap_mapHomologicalComplex_comp_mapHomologyIso_hom
      (singularCochainComplexIsoTopOpen S X).hom n).symm
  rw [hR, hS]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  congr 1
  simp only [← HomologicalComplex.homologyMap_comp]
  congr 1
  rw [← Category.assoc, ← singularCochainComplexIsoTopOpen_hom_comp_coefficientChange,
    Category.assoc, topOpenForgottenSingularCochainCoefficientChange_comp_inv]

set_option backward.isDefEq.respectTransparency false in
/-- Change of coefficients on ordinary singular cohomology corresponds, under the identification
with raw global cochain cohomology, to the map induced by the presheaf coefficient change. -/
lemma ordinarySingularCohomologyEquivGlobalRaw_coefficientChange (n : ℕ)
    (a : OrdinarySingularCohomology R X n) :
    ordinarySingularCohomologyEquivGlobalRaw S X n
        (ordinarySingularCohomologyCoefficientChange f X n a) =
      HomologicalComplex.homologyMap (globalRawSingularCochainComplexMap f X) n
        (ordinarySingularCohomologyEquivGlobalRaw R X n a) := by
  have h := congrArg (fun g ↦ g.hom a)
    (ordinarySingularCohomologyCoefficientChange_comm_hom f X n)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at h
  simp only [ordinarySingularCohomologyEquivGlobalRaw, AddEquiv.trans_apply,
    Iso.addCommGroupIsoToAddEquiv_apply, ordinarySingularCohomologyCoefficientChange,
    AddCommGrpCat.hom_comp, Iso.symm_hom, HomologicalComplex.homologyMapIso_inv]
  exact h

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

/-- Change of coefficients on the integer-indexed singular-cochain sheaf complex. -/
def singularCochainSheafComplexIntMap :
    singularCochainSheafComplexInt X R ⟶ singularCochainSheafComplexInt X S :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.Singular.singularCochainSheafComplexMap f (TopCat.of (ComplexPoint X)))
    ComplexShape.embeddingUpNat

/-- Change of coefficients on the integer-indexed constant sheaf complex. -/
def constantCoefficientSheafComplexIntMap :
    constantCoefficientSheafComplexInt X R ⟶ constantCoefficientSheafComplexInt X S :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).map
      (AlgebraicTopology.Singular.constantCoefficientSheafMap f (TopCat.of (ComplexPoint X))))
    ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
/-- The integer-indexed constant-to-singular comparison is natural in the coefficient ring. -/
lemma constantsToSingularCochainComplexInt_comp_map :
    constantsToSingularCochainComplexInt X R ≫ singularCochainSheafComplexIntMap X f =
      constantCoefficientSheafComplexIntMap X f ≫
        constantsToSingularCochainComplexInt X S := by
  unfold constantsToSingularCochainComplexInt singularCochainSheafComplexIntMap
    constantCoefficientSheafComplexIntMap
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex_comp_map]

set_option backward.isDefEq.respectTransparency false in
/-- Change of coefficients along `ℤ → ℚ` on constant sheaf complexes is the canonical
integer-to-rational comparison with scalar `1`. -/
lemma constantCoefficientSheafComplexIntMap_intCast :
    constantCoefficientSheafComplexIntMap X (Int.castRingHom ℚ) =
      integerToFieldConstantSheafComplexInt ℚ X 1 := by
  have h : AddCommGrpCat.ofHom (integerMultipleAddHom ℚ 1) =
      AddCommGrpCat.ofHom (Int.castRingHom ℚ).toAddMonoidHom := by
    congr 1
    ext
    simp [integerMultipleAddHom]
  change _ = HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        AddCommGrpCat).map
          (AddCommGrpCat.ofHom (integerMultipleAddHom ℚ 1)))) ComplexShape.embeddingUpNat
  rw [h]
  rfl

end AlgebraicGeometry.ComplexPoint
