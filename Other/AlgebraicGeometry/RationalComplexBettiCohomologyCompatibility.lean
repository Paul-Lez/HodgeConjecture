/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Other.AlgebraicGeometry.RationalComplexBettiCompatibility
import Other.AlgebraicGeometry.PlainHypercohomologyGlobalSectionsNaturality
import Other.Algebra.Homology.MapExtendNaturality
import Other.AlgebraicTopology.SingularProductCoefficientChange
import Other.AlgebraicTopology.LinearDualHomologyNaturality

/-!
# Rational-to-complex compatibility of the Betti comparison

This file identifies extension of coefficients on constant-sheaf hypercohomology with the
usual rational-to-complex map on ordinary singular cohomology.  The proof follows the actual
cochain representatives through global sections, extension from natural to integer degrees,
sheafification, and the universal-coefficient equivalence.
-/

@[expose] noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace HomologicalComplex

universe u v

variable {C D : Type u} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  {i i' : Type v} {c : ComplexShape i} {c' : ComplexShape i'}

set_option backward.isDefEq.respectTransparency false in
theorem mapExtendIso_hom_naturality
    (F : Functor C D) [F.Additive] {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    (F.mapHomologicalComplex c').map (extendMap f e) ≫ (mapExtendIso F L e).hom =
      (mapExtendIso F K e).hom ≫ extendMap ((F.mapHomologicalComplex c).map f) e := by
  rw [← cancel_epi (mapExtendIso F K e).inv]
  rw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc,
    ← mapExtendIso_inv_naturality]
  simp

end HomologicalComplex

namespace HomologicalComplex

universe u v

variable {C D E : Type u}
  [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  {ι : Type v} {ι' : Type v} {c : ComplexShape ι} {c' : ComplexShape ι'}

theorem mapExtendCompIso_naturality
    (F : C ⥤ D) [F.Additive] (E₁ : D ⥤ E) [E₁.Additive]
    (G : C ⥤ E) [G.Additive] (eComp : F ⋙ E₁ ≅ G)
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    (G.mapHomologicalComplex c').map (extendMap f e) ≫
        (mapExtendIso (c' := c') G L e).hom ≫
        extendMap
          ((Functor.mapHomologicalComplexCompIso eComp c).inv.app L) e =
      (mapExtendIso (c' := c') G K e).hom ≫
        extendMap
          ((Functor.mapHomologicalComplexCompIso eComp c).inv.app K) e ≫
        extendMap
          ((E₁.mapHomologicalComplex c).map
            ((F.mapHomologicalComplex c).map f)) e := by
  rw [← Category.assoc, mapExtendIso_hom_naturality]
  simp only [Category.assoc]
  rw [← extendMap_comp, ← extendMap_comp]
  rw [(Functor.mapHomologicalComplexCompIso eComp c).inv.naturality]
  rfl

end HomologicalComplex

namespace AlgebraicTopology.Singular

variable (Y : TopCat.{0})

local instance qToCCompatibilityOpenChainsModule
    (U : (Opens Y)ᵒᵖ) (n : Nat) :
    Module Rat (OpenChains Complex Y U n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCCompatibilityOpenChainsScalarTower
    (U : (Opens Y)ᵒᵖ) (n : Nat) :
    IsScalarTower Rat Complex (OpenChains Complex Y U n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance qToCOrdinaryModuleCochains (n : ℕ) :
    Module ℚ ((SingularChainComplex ℂ Y).linearDualCochainComplex.X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance qToCOrdinaryScalarTowerCochains (n : ℕ) :
    IsScalarTower ℚ ℂ
      ((SingularChainComplex ℂ Y).linearDualCochainComplex.X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- Complex singular cochains regarded as a cochain complex of rational modules. -/
abbrev restrictedCOrdinarySingularCochains :
    CochainComplex (ModuleCat ℚ) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
      (SingularChainComplex ℂ Y).linearDualCochainComplex

/-- Coefficient extension on whole-space cochains before forgetting additive structure. -/
def qToCOrdinarySingularCochainComplexRestricted :
    (SingularChainComplex ℚ Y).linearDualCochainComplex ⟶
      restrictedCOrdinarySingularCochains Y where
  f n := ModuleCat.ofHom (qToCSingularCochain Y n)
  comm' i j hij := by
    obtain rfl := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    simp only [Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.linearDualCochainComplex_d]
    change ((SingularChainComplex ℂ Y).d (i + 1) i).hom.dualMap
        (qToCSingularCochain Y i φ) =
      qToCSingularCochain Y (i + 1)
        (((SingularChainComplex ℚ Y).d (i + 1) i).hom.dualMap φ)
    exact (qToCSingularCochain_coboundary Y i φ).symm

/-- Restriction of scalars commutes with cohomology of the complex singular cochain complex. -/
def restrictedCOrdinarySingularCochainsHomologyIso (n : ℕ) :
    (restrictedCOrdinarySingularCochains Y).homology n ≅
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj
        ((SingularChainComplex ℂ Y).linearDualCochainComplex.homology n) :=
  ShortComplex.mapHomologyIso
    ((SingularChainComplex ℂ Y).linearDualCochainComplex.sc n)
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ))

/-- Coefficient extension on the ordinary whole-space singular cochain complexes,
with scalar structures forgotten. -/
def qToCOrdinarySingularCochainComplex :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (SingularChainComplex ℚ Y).linearDualCochainComplex ⟶
      ((forget₂ (ModuleCat ℂ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (SingularChainComplex ℂ Y).linearDualCochainComplex where
  f n := AddCommGrpCat.ofHom (qToCSingularCochain Y n).toAddMonoidHom
  comm' i j hij := by
    obtain rfl := hij
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    simp only [ConcreteCategory.comp_apply,
      Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.linearDualCochainComplex_d]
    change ((SingularChainComplex ℂ Y).d (i + 1) i).hom.dualMap
        (qToCSingularCochain Y i φ) =
      qToCSingularCochain Y (i + 1)
        (((SingularChainComplex ℚ Y).d (i + 1) i).hom.dualMap φ)
    exact (qToCSingularCochain_coboundary Y i φ).symm

/-- Coefficient extension on the raw global singular-cochain complexes. -/
def qToCGlobalRawSingularCochainComplex :
    globalRawSingularCochainComplex ℚ Y ⟶
      globalRawSingularCochainComplex ℂ Y :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (qToCSingularCochainPresheafComplex Y)

/-- Coefficient extension on global sections of singular-cochain sheaves. -/
def qToCGlobalSingularCochainSheafComplex :
    globalSingularCochainSheafComplex ℚ Y ⟶
      globalSingularCochainSheafComplex ℂ Y :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (qToCSingularCochainSheafComplex Y))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem topOpenToGlobal_qToC_naturality :
    topOpenToGlobalSingularCochainSheafComplex ℚ Y ≫
        qToCGlobalSingularCochainSheafComplex Y =
      qToCGlobalRawSingularCochainComplex Y ≫
        topOpenToGlobalSingularCochainSheafComplex ℂ Y := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    topOpenToGlobalSingularCochainSheafComplex_f,
    topOpenToGlobalSingularCochainSheafComplex_f]
  change (toSheafify (Opens.grothendieckTopology Y)
      (singularCochainPresheaf ℚ Y n)).app (.op ⊤) ≫
      ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
        (qToCSingularCochainPresheaf Y n)).hom.app (.op ⊤) =
    (qToCSingularCochainPresheaf Y n).app (.op ⊤) ≫
      (toSheafify (Opens.grothendieckTopology Y)
        (singularCochainPresheaf ℂ Y n)).app (.op ⊤)
  simpa only [NatTrans.comp_app] using (congrArg (fun f => f.app (.op ⊤))
    (toSheafify_naturality (Opens.grothendieckTopology Y)
      (qToCSingularCochainPresheaf Y n))).symm

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular

universe u

variable (R : Type u) [Field R] (Y : TopCat.{u})

/-- Transport an ordinary singular cocycle to the raw top-open cochain complex. -/
def ordinarySingularCochainCyclesToGlobalRaw (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat).obj
        ((SingularChainComplex R Y).linearDualCochainComplex.cycles n) ⟶
      (globalRawSingularCochainComplex R Y).cycles n :=
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  let T := (TopOpenSingularChainComplex R Y).linearDualCochainComplex
  F.map (HomologicalComplex.cyclesMap
      (singularCochainComplexIsoTopOpen R Y).hom n) ≫
    ((T.sc n).mapCyclesIso F).inv ≫
    HomologicalComplex.cyclesMap
      (globalRawSingularCochainComplexIso R Y).inv n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma ordinarySingularCohomologyEquivGlobalRaw_homologyπ
    (n : ℕ)
    (phi : (SingularChainComplex R Y).linearDualCochainComplex.cycles n) :
    ordinarySingularCohomologyEquivGlobalRaw R Y n
        ((SingularChainComplex R Y).linearDualCochainComplex.homologyπ n phi) =
      (globalRawSingularCochainComplex R Y).homologyπ n
        (ordinarySingularCochainCyclesToGlobalRaw R Y n phi) := by
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  let K := (SingularChainComplex R Y).linearDualCochainComplex
  let T := (TopOpenSingularChainComplex R Y).linearDualCochainComplex
  let eT := singularCochainComplexIsoTopOpen R Y
  let eG := globalRawSingularCochainComplexIso R Y
  let eC := (T.sc n).mapCyclesIso F
  let eH := (T.sc n).mapHomologyIso F
  have hpres :
      ((T.sc n).map F).homologyπ ≫ eH.hom =
        eC.hom ≫ F.map ((T.sc n).homologyπ) := by
    let h := (T.sc n).homologyData.left
    change ((T.sc n).map F).homologyπ ≫
        ((T.sc n).mapHomologyIso F).hom =
      ((T.sc n).mapCyclesIso F).hom ≫
        F.map (T.sc n).homologyπ
    rw [h.mapCyclesIso_eq, h.mapHomologyIso_eq]
    simp only [Iso.trans_hom, Category.assoc]
    rw [← Category.assoc,
      (h.map F).homologyπ_comp_homologyIso_hom]
    simp only [Category.assoc]
    rw [cancel_epi]
    change F.map (h.π ≫ h.homologyIso.inv) =
      F.map (h.cyclesIso.inv ≫ (T.sc n).homologyπ)
    rw [h.π_comp_homologyIso_inv]
  have hinv :
      F.map ((T.sc n).homologyπ) ≫ eH.inv =
        eC.inv ≫
          ((T.sc n).map F).homologyπ := by
    rw [← cancel_epi eC.hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← hpres]
    simp
  dsimp only [ordinarySingularCohomologyEquivGlobalRaw,
    ordinarySingularCochainCyclesToGlobalRaw, AddEquiv.trans_apply]
  simp only [Iso.addCommGroupIsoToAddEquiv_apply,
    Iso.addCommGroupIsoToAddEquiv_symm_apply,
    Functor.mapIso_hom, HomologicalComplex.homologyMapIso_hom,
    HomologicalComplex.homologyMapIso_inv]
  change
    (F.map (K.homologyπ n) ≫
      F.map (HomologicalComplex.homologyMap eT.hom n) ≫
      eH.inv ≫ HomologicalComplex.homologyMap eG.inv n) phi =
    ((F.map (HomologicalComplex.cyclesMap eT.hom n) ≫
      eC.inv ≫ HomologicalComplex.cyclesMap eG.inv n) ≫
      (globalRawSingularCochainComplex R Y).homologyπ n) phi
  simp only [← ConcreteCategory.comp_apply]
  apply ConcreteCategory.congr_hom
  have htop := HomologicalComplex.homologyπ_naturality
    (φ := eT.hom) n
  have htopF := congrArg F.map htop
  simp only [Functor.map_comp] at htopF
  have htopF' :
      F.map (K.homologyπ n) ≫
          F.map (HomologicalComplex.homologyMap eT.hom n) =
        F.map (HomologicalComplex.cyclesMap eT.hom n) ≫
          F.map ((T.sc n).homologyπ) := by
    exact htopF
  have hraw' :
      ((T.sc n).map F).homologyπ ≫
          HomologicalComplex.homologyMap eG.inv n =
        HomologicalComplex.cyclesMap eG.inv n ≫
          (globalRawSingularCochainComplex R Y).homologyπ n := by
    exact HomologicalComplex.homologyπ_naturality
      (φ := eG.inv) n
  rw [← Category.assoc, htopF']
  calc
    _ = F.map (HomologicalComplex.cyclesMap eT.hom n) ≫
        (F.map ((T.sc n).homologyπ) ≫ eH.inv) ≫
        HomologicalComplex.homologyMap eG.inv n := by
      simp only [Category.assoc]
    _ = F.map (HomologicalComplex.cyclesMap eT.hom n) ≫
        (eC.inv ≫ ((T.sc n).map F).homologyπ) ≫
        HomologicalComplex.homologyMap eG.inv n := by
      rw [hinv]
    _ = F.map (HomologicalComplex.cyclesMap eT.hom n) ≫ eC.inv ≫
        (((T.sc n).map F).homologyπ ≫
          HomologicalComplex.homologyMap eG.inv n) := by
      simp only [Category.assoc]
    _ = F.map (HomologicalComplex.cyclesMap eT.hom n) ≫ eC.inv ≫
        (HomologicalComplex.cyclesMap eG.inv n ≫
          (globalRawSingularCochainComplex R Y).homologyπ n) := by
      rw [hraw']
    _ = _ := by simp only [Category.assoc]

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec (.of ℂ)))

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem globalSectionsSingularCochainComplexIntIsoExtend_qToC_naturality :
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (rationalToComplexSingularCochainComplexInt X) ≫
        (globalSectionsComplexSingularCochainComplexIntIsoExtend X).hom =
      (globalSectionsSingularCochainComplexIntIsoExtend X).hom ≫
        HomologicalComplex.extendMap
          (AlgebraicTopology.Singular.qToCGlobalSingularCochainSheafComplex
            (TopCat.of (ComplexPoint X)))
          ComplexShape.embeddingUpNat := by
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let SQ := AlgebraicTopology.Singular.singularCochainSheafComplex ℚ Y
  let SC := AlgebraicTopology.Singular.singularCochainSheafComplex ℂ Y
  let q := AlgebraicTopology.Singular.qToCSingularCochainSheafComplex Y
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : E.Additive := by dsimp [E]; infer_instance
  letI : Γ.Additive := by dsimp [Γ]; infer_instance
  let eComp : F ⋙ E ≅ Γ := Iso.refl _
  change
    (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap q ComplexShape.embeddingUpNat) ≫
      (HomologicalComplex.mapExtendIso Γ SC ComplexShape.embeddingUpNat).hom ≫
        HomologicalComplex.extendMap
          ((Functor.mapHomologicalComplexCompIso eComp
            (ComplexShape.up ℕ)).inv.app SC) ComplexShape.embeddingUpNat =
    (HomologicalComplex.mapExtendIso Γ SQ ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap
        ((Functor.mapHomologicalComplexCompIso eComp
          (ComplexShape.up ℕ)).inv.app SQ) ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap
        ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map q))
        ComplexShape.embeddingUpNat
  exact HomologicalComplex.mapExtendCompIso_naturality
    F E Γ eComp q ComplexShape.embeddingUpNat

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular

variable (Y : TopCat.{0})

local instance qToCCompatibilityOpenChainsModule'
    (U : (Opens Y)ᵒᵖ) (n : Nat) :
    Module Rat (OpenChains Complex Y U n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCCompatibilityOpenChainsScalarTower'
    (U : (Opens Y)ᵒᵖ) (n : Nat) :
    IsScalarTower Rat Complex (OpenChains Complex Y U n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance qToCOrdinaryModuleCochains' (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).linearDualCochainComplex.X n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCOrdinaryScalarTowerCochains' (n : Nat) :
    IsScalarTower Rat Complex
      ((SingularChainComplex Complex Y).linearDualCochainComplex.X n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance qToCOrdinaryModuleCohomology (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).linearDualCochainComplex.homology n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCOrdinaryScalarTowerCohomology (n : Nat) :
    IsScalarTower Rat Complex
      ((SingularChainComplex Complex Y).linearDualCochainComplex.homology n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance qToCOrdinaryModuleCochainCycles (n : Nat) :
    Module Rat
      ((SingularChainComplex Complex Y).linearDualCochainComplex.cycles n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCOrdinaryScalarTowerCochainCycles (n : Nat) :
    IsScalarTower Rat Complex
      ((SingularChainComplex Complex Y).linearDualCochainComplex.cycles n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance qToCOrdinaryModuleChainCycles (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).cycles n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCOrdinaryScalarTowerChainCycles (n : Nat) :
    IsScalarTower Rat Complex ((SingularChainComplex Complex Y).cycles n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance qToCOrdinaryModuleHomology (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).homology n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCOrdinaryScalarTowerHomology (n : Nat) :
    IsScalarTower Rat Complex ((SingularChainComplex Complex Y).homology n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance qToCRepositoryModuleHomology (n : Nat) :
    Module Rat ((CChains Y).homology n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCRepositoryScalarTowerHomology (n : Nat) :
    IsScalarTower Rat Complex ((CChains Y).homology n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance qToCOrdinaryModuleRawChainCycles (n : Nat) :
    Module Rat
      (((SingularChainComplex Complex Y).sc n).homologyData.left.K) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCOrdinaryScalarTowerRawChainCycles (n : Nat) :
    IsScalarTower Rat Complex
      (((SingularChainComplex Complex Y).sc n).homologyData.left.K) :=
  IsScalarTower.of_compHom Rat Complex _

local instance qToCOrdinaryModuleShortChainCycles (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).sc n).cycles :=
  Module.compHom _ (algebraMap Rat Complex)

local instance qToCOrdinaryScalarTowerShortChainCycles (n : Nat) :
    IsScalarTower Rat Complex ((SingularChainComplex Complex Y).sc n).cycles :=
  IsScalarTower.of_compHom Rat Complex _

def restrictedCOrdinarySingularCochainsCyclesIso (n : Nat) :
    (restrictedCOrdinarySingularCochains Y).cycles n ≅
      (ModuleCat.restrictScalars (algebraMap Rat Complex)).obj
        ((SingularChainComplex Complex Y).linearDualCochainComplex.cycles n) :=
  ((SingularChainComplex Complex Y).linearDualCochainComplex.sc n).mapCyclesIso
    (ModuleCat.restrictScalars (algebraMap Rat Complex))

def qToCOrdinaryCochainCycles (n : Nat) :
    (SingularChainComplex Rat Y).linearDualCochainComplex.cycles n →ₗ[Rat]
      (SingularChainComplex Complex Y).linearDualCochainComplex.cycles n :=
  (restrictedCOrdinarySingularCochainsCyclesIso Y n).hom.hom.comp
    (HomologicalComplex.cyclesMap
      (qToCOrdinarySingularCochainComplexRestricted Y) n).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma restrictedCOrdinarySingularCochains_homologyπ_iso (n : Nat) :
    (restrictedCOrdinarySingularCochains Y).homologyπ n ≫
        (restrictedCOrdinarySingularCochainsHomologyIso Y n).hom =
      (restrictedCOrdinarySingularCochainsCyclesIso Y n).hom ≫
        (ModuleCat.restrictScalars (algebraMap Rat Complex)).map
          ((SingularChainComplex Complex Y).linearDualCochainComplex.homologyπ n) := by
  let S := (SingularChainComplex Complex Y).linearDualCochainComplex.sc n
  let F := ModuleCat.restrictScalars (algebraMap Rat Complex)
  let h := S.homologyData.left
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [h.mapCyclesIso_eq, h.mapHomologyIso_eq]
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc,
    (h.map F).homologyπ_comp_homologyIso_hom]
  simp only [Category.assoc]
  rw [cancel_epi]
  change F.map (h.π ≫ h.homologyIso.inv) =
    F.map (h.cyclesIso.inv ≫ S.homologyπ)
  rw [h.π_comp_homologyIso_inv]

lemma iCycles_comp_qToCOrdinaryCochainCycles (n : Nat) :
    (qToCSingularCochain Y n).comp
        ((SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n).hom =
      (((SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n).hom.restrictScalars Rat).comp
        (qToCOrdinaryCochainCycles Y n) := by
  apply LinearMap.ext
  intro phi
  have h1 := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.cyclesMap_i
        (qToCOrdinarySingularCochainComplexRestricted Y) n).symm) phi
  have h2 := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (ShortComplex.mapCyclesIso_hom_iCycles
        ((SingularChainComplex Complex Y).linearDualCochainComplex.sc n)
        (ModuleCat.restrictScalars (algebraMap Rat Complex))))
    ((HomologicalComplex.cyclesMap
      (qToCOrdinarySingularCochainComplexRestricted Y) n).hom phi)
  change qToCSingularCochain Y n
      (((SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n).hom phi) =
    ((SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n).hom
      (qToCOrdinaryCochainCycles Y n phi)
  exact h1.trans h2.symm

/-- The class-level map induced by literal coefficient extension on singular cochains. -/
def qToCOrdinaryCochainCohomologyMap (n : Nat) :
    OrdinarySingularCohomology Rat Y n →ₗ[Rat]
      OrdinarySingularCohomology Complex Y n :=
  (restrictedCOrdinarySingularCochainsHomologyIso Y n).hom.hom.comp
    (HomologicalComplex.homologyMap
      (qToCOrdinarySingularCochainComplexRestricted Y) n).hom

lemma qToCOrdinaryCochainCohomologyMap_homologyπ (n : Nat)
    (phi : (SingularChainComplex Rat Y).linearDualCochainComplex.cycles n) :
    qToCOrdinaryCochainCohomologyMap Y n
        ((SingularChainComplex Rat Y).linearDualCochainComplex.homologyπ n phi) =
      (SingularChainComplex Complex Y).linearDualCochainComplex.homologyπ n
        (qToCOrdinaryCochainCycles Y n phi) := by
  let KQ := (SingularChainComplex Rat Y).linearDualCochainComplex
  let KC := (SingularChainComplex Complex Y).linearDualCochainComplex
  let KR := restrictedCOrdinarySingularCochains Y
  let q := qToCOrdinarySingularCochainComplexRestricted Y
  let eC := restrictedCOrdinarySingularCochainsCyclesIso Y n
  let eH := restrictedCOrdinarySingularCochainsHomologyIso Y n
  let F := ModuleCat.restrictScalars (algebraMap Rat Complex)
  have h : KQ.homologyπ n ≫ HomologicalComplex.homologyMap q n ≫ eH.hom =
      HomologicalComplex.cyclesMap q n ≫ eC.hom ≫ F.map (KC.homologyπ n) := by
    rw [HomologicalComplex.homologyπ_naturality_assoc,
      restrictedCOrdinarySingularCochains_homologyπ_iso]
  exact ConcreteCategory.congr_hom h phi

def qToCOrdinaryChainCycles (n : Nat) :
    (SingularChainComplex Rat Y).cycles n →ₗ[Rat]
      (SingularChainComplex Complex Y).cycles n :=
  (((SingularChainComplex Complex Y).sc n).homologyData.left.cyclesIso.inv.hom
    |>.restrictScalars Rat).comp (qToCCycles Y n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma iCycles_qToCOrdinaryChainCycles (n : Nat)
    (z : (SingularChainComplex Rat Y).cycles n) :
    (SingularChainComplex Complex Y).iCycles n
        (qToCOrdinaryChainCycles Y n z) =
      qToCChainGroup Y n ((SingularChainComplex Rat Y).iCycles n z) := by
  let h := ((SingularChainComplex Complex Y).sc n).homologyData.left
  have hq := DFunLike.congr_fun (iCycles_comp_qToCChainGroup Y n) z
  have hc := ConcreteCategory.congr_hom h.cyclesIso_inv_comp_iCycles
    (qToCCycles Y n z)
  change ((SingularChainComplex Complex Y).sc n).iCycles.hom
      (h.cyclesIso.inv.hom (qToCCycles Y n z)) =
    qToCChainGroup Y n
      (((SingularChainComplex Rat Y).sc n).iCycles.hom z)
  exact hc.trans hq.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma qToCHomology_homologyπ (n : Nat)
    (z : (SingularChainComplex Rat Y).cycles n) :
    qToCHomology Y n
        ((SingularChainComplex Rat Y).homologyπ n z) =
      (SingularChainComplex Complex Y).homologyπ n
        (qToCOrdinaryChainCycles Y n z) := by
  let S := (SingularChainComplex Complex Y).sc n
  let h := S.homologyData.left
  have hq := ConcreteCategory.congr_hom
    (homologyπ_comp_qToCHomology Y n) z
  have hc := ConcreteCategory.congr_hom h.π_comp_homologyIso_inv
    (qToCCycles Y n z)
  have hi : h.homologyIso.inv = 𝟙 _ := by
    simp only [ShortComplex.LeftHomologyData.homologyIso, Iso.trans_inv,
      Iso.symm_inv]
    change S.leftHomologyIso.inv ≫ S.leftHomologyIso.hom = 𝟙 _
    simp
  change qToCHomology Y n
      ((SingularChainComplex Rat Y).homologyπ n z) =
    S.homologyπ.hom (h.cyclesIso.inv.hom (qToCCycles Y n z))
  change qToCHomology Y n
      ((SingularChainComplex Rat Y).homologyπ n z) =
    h.π.hom (qToCCycles Y n z) at hq
  rw [hi] at hc
  simp only [Category.comp_id, ConcreteCategory.comp_apply] at hc
  exact hq.trans hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma linearDualHomologyEquiv_homologyπ_apply
    {R : Type} [Field R] (K : ChainComplex (ModuleCat R) Nat) (n : Nat)
    (phi : K.linearDualCochainComplex.cycles n) (z : K.cycles n) :
    HomologicalComplex.linearDualHomologyEquiv K n
        (K.linearDualCochainComplex.homologyπ n phi)
        (K.homologyπ n z) =
      (show Module.Dual R (K.X n) from
        K.linearDualCochainComplex.iCycles n phi) (K.iCycles n z) := by
  change (K.sc n).linearDualHomologyEquiv
      ((ShortComplex.homologyMap
        (HomologicalComplex.linearDualCochainComplexScIso K n).hom).hom
        ((K.linearDualCochainComplex.sc n).homologyπ.hom phi))
      ((K.sc n).homologyπ z) = _
  rw [← ConcreteCategory.comp_apply,
    ShortComplex.homologyπ_naturality]
  change (K.sc n).linearDualHomologyEquiv
      ((K.sc n).linearDual.homologyπ.hom
        ((ShortComplex.cyclesMap
          (HomologicalComplex.linearDualCochainComplexScIso K n).hom).hom phi))
      ((K.sc n).homologyπ.hom z) = _
  rw [ShortComplex.linearDualHomologyEquiv_homologyπ_apply]
  have hi := ConcreteCategory.congr_hom
    (ShortComplex.cyclesMap_i
      (HomologicalComplex.linearDualCochainComplexScIso K n).hom) phi
  have he :
      (HomologicalComplex.linearDualCochainComplexScIso K n).hom.τ₂ = 𝟙 _ := by
    simp [HomologicalComplex.linearDualCochainComplexScIso,
      HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor]
  rw [he] at hi
  simp only [Category.comp_id, ConcreteCategory.comp_apply] at hi
  have hi' :
      (show Module.Dual R (K.X n) from
        (K.sc n).linearDual.iCycles.hom
          ((ShortComplex.cyclesMap
            (HomologicalComplex.linearDualCochainComplexScIso K n).hom).hom phi)) =
      (show Module.Dual R (K.X n) from
        K.linearDualCochainComplex.iCycles n phi) := by
    exact hi
  exact congrArg (fun f : Module.Dual R (K.X n) ↦ f (K.iCycles n z)) hi'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma qToCOrdinaryCochain_uct_pairing (n : Nat)
    (a : OrdinarySingularCohomology Rat Y n)
    (z : (SingularChainComplex Rat Y).homology n) :
    HomologicalComplex.linearDualHomologyEquiv (SingularChainComplex Complex Y) n
        (qToCOrdinaryCochainCohomologyMap Y n a)
        (qToCHomology Y n z) =
      algebraMap Rat Complex
        (HomologicalComplex.linearDualHomologyEquiv
          (SingularChainComplex Rat Y) n a z) := by
  let KQ := (SingularChainComplex Rat Y).linearDualCochainComplex
  let KC := (SingularChainComplex Complex Y).linearDualCochainComplex
  obtain ⟨phi, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (KQ.homologyπ n)).mp inferInstance a
  obtain ⟨c, rfl⟩ :=
    (ModuleCat.epi_iff_surjective
      ((SingularChainComplex Rat Y).homologyπ n)).mp inferInstance z
  rw [qToCOrdinaryCochainCohomologyMap_homologyπ,
    qToCHomology_homologyπ,
    linearDualHomologyEquiv_homologyπ_apply,
    linearDualHomologyEquiv_homologyπ_apply]
  have hphi := DFunLike.congr_fun
    (iCycles_comp_qToCOrdinaryCochainCycles Y n) phi
  have hc := iCycles_qToCOrdinaryChainCycles Y n c
  change (show Module.Dual Complex
      ((SingularChainComplex Complex Y).X n) from
      (SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n
        (qToCOrdinaryCochainCycles Y n phi))
      ((SingularChainComplex Complex Y).iCycles n
        (qToCOrdinaryChainCycles Y n c)) =
    algebraMap Rat Complex
      ((show Module.Dual Rat ((SingularChainComplex Rat Y).X n) from
        (SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi)
        ((SingularChainComplex Rat Y).iCycles n c))
  have hphi' :
      (show Module.Dual Complex
        ((SingularChainComplex Complex Y).X n) from
        (SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n
          (qToCOrdinaryCochainCycles Y n phi)) =
      qToCSingularCochain Y n
        (show Module.Dual Rat ((SingularChainComplex Rat Y).X n) from
          (SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi) := by
    change qToCSingularCochain Y n
        (show Module.Dual Rat ((SingularChainComplex Rat Y).X n) from
          (SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi) =
      (show Module.Dual Complex
        ((SingularChainComplex Complex Y).X n) from
        (SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n
          (qToCOrdinaryCochainCycles Y n phi)) at hphi
    exact hphi.symm
  calc
    _ = qToCSingularCochain Y n
        (show Module.Dual Rat ((SingularChainComplex Rat Y).X n) from
          (SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi)
        (qToCChainGroup Y n
          ((SingularChainComplex Rat Y).iCycles n c)) := by
      rw [hphi', hc]
      rfl
    _ = _ := qToCSingularCochain_apply_qToCChain Y n _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma qToCOrdinaryCohomology_uct (n : Nat)
    (a : OrdinarySingularCohomology Rat Y n) :
    ordinarySingularCohomologyEquivCohomology Complex Y n
        (qToCOrdinaryCochainCohomologyMap Y n a) =
      rationalToComplexCohomologyMap Y n
        (ordinarySingularCohomologyEquivCohomology Rat Y n a) := by
  apply LinearMap.ext
  intro w
  apply (qToCHomology_isBaseChange Y n).inductionOn w
    (fun w =>
      ordinarySingularCohomologyEquivCohomology Complex Y n
          (qToCOrdinaryCochainCohomologyMap Y n a) w =
        rationalToComplexCohomologyMap Y n
          (ordinarySingularCohomologyEquivCohomology Rat Y n a) w)
  · simp
  · intro z
    exact (qToCOrdinaryCochain_uct_pairing Y n a z).trans
      ((qToCHomology_isBaseChange Y n).toDual_comp_apply
        (ordinarySingularCohomologyEquivCohomology Rat Y n a) z).symm
  · intro c z hz
    simp [hz]
  · intro x y hx hy
    simp [hx, hy]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma ordinarySingularCochainCyclesToGlobalRaw_iCycles
    {R : Type} [Field R] (n : Nat)
    (phi : (SingularChainComplex R Y).linearDualCochainComplex.cycles n) :
    (globalRawSingularCochainComplex R Y).iCycles n
        (ordinarySingularCochainCyclesToGlobalRaw R Y n phi) =
      (singularCochainComplexIsoTopOpen R Y).hom.f n
        ((SingularChainComplex R Y).linearDualCochainComplex.iCycles n phi) := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let T := (TopOpenSingularChainComplex R Y).linearDualCochainComplex
  let eC := (T.sc n).mapCyclesIso F
  have heC : eC.inv ≫ ((T.sc n).map F).iCycles =
      F.map ((T.sc n).iCycles) := by
    rw [← cancel_epi eC.hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (ShortComplex.mapCyclesIso_hom_iCycles (T.sc n) F).symm
  have heC' : eC.inv ≫
      (topOpenForgottenSingularCochainComplex R Y).iCycles n =
        F.map (T.iCycles n) := by
    exact heC
  have heG : (globalRawSingularCochainComplexIso R Y).inv.f n = 𝟙 _ := by
    ext x
    rfl
  have hcycle :
      F.map (HomologicalComplex.cyclesMap
          (singularCochainComplexIsoTopOpen R Y).hom n) ≫
          F.map (T.iCycles n) =
        F.map
          ((SingularChainComplex R Y).linearDualCochainComplex.iCycles n ≫
            (singularCochainComplexIsoTopOpen R Y).hom.f n) := by
    have h := HomologicalComplex.cyclesMap_i
      (φ := (singularCochainComplexIsoTopOpen R Y).hom) n
    have hF := congrArg F.map h
    simpa only [Functor.map_comp] using hF
  dsimp only [ordinarySingularCochainCyclesToGlobalRaw]
  change _ = (F.map
    ((SingularChainComplex R Y).linearDualCochainComplex.iCycles n ≫
      (singularCochainComplexIsoTopOpen R Y).hom.f n)) phi
  simp only [← ConcreteCategory.comp_apply]
  apply ConcreteCategory.congr_hom
  simp only [Category.assoc]
  rw [HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc eC.inv
    ((topOpenForgottenSingularCochainComplex R Y).iCycles n)
    ((globalRawSingularCochainComplexIso R Y).inv.f n)]
  rw [heC']
  rw [heG, Category.comp_id]
  exact hcycle

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma ordinarySingularCochainCyclesToGlobalRaw_qToC
    (n : Nat)
    (phi : (SingularChainComplex Rat Y).linearDualCochainComplex.cycles n) :
    HomologicalComplex.cyclesMap
        (qToCGlobalRawSingularCochainComplex Y) n
        (ordinarySingularCochainCyclesToGlobalRaw Rat Y n phi) =
      ordinarySingularCochainCyclesToGlobalRaw Complex Y n
        (qToCOrdinaryCochainCycles Y n phi) := by
  apply (AddCommGrpCat.mono_iff_injective
    ((globalRawSingularCochainComplex Complex Y).iCycles n)).mp inferInstance
  rw [← ConcreteCategory.comp_apply,
    HomologicalComplex.cyclesMap_i]
  simp only [ConcreteCategory.comp_apply]
  rw [
    ordinarySingularCochainCyclesToGlobalRaw_iCycles,
    ordinarySingularCochainCyclesToGlobalRaw_iCycles]
  have hphi := DFunLike.congr_fun
    (iCycles_comp_qToCOrdinaryCochainCycles Y n) phi
  have hphi' :
      (SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n
          (qToCOrdinaryCochainCycles Y n phi) =
        qToCSingularCochain Y n
          ((SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi) := by
    exact hphi.symm
  rw [hphi']
  change qToCOpenCochains Y (.op (⊤ : Opens Y)) n
      ((singularCochainComplexIsoTopOpen Rat Y).hom.f n
        ((SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi)) =
    (singularCochainComplexIsoTopOpen Complex Y).hom.f n
      (qToCSingularCochain Y n
        ((SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi))
  letI : Module Rat (OpenChains Complex Y (.op (⊤ : Opens Y)) n) :=
    Module.compHom _ (algebraMap Rat Complex)
  letI : IsScalarTower Rat Complex
      (OpenChains Complex Y (.op (⊤ : Opens Y)) n) :=
    IsScalarTower.of_compHom Rat Complex _
  apply (fieldToFieldOpenChainGroup_isBaseChange Rat Complex Y
    (.op (⊤ : Opens Y)) n).algHom_ext
  intro c
  rw [qToCOpenCochains_apply_qToCChain]
  let psi : Simplicial.Cochain Rat (TopCat.toSSet.obj Y) n :=
    (SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi
  change algebraMap Rat Complex
      (psi (((topOpenSingularChainComplexIso Rat Y).hom.f n).hom c)) =
    (qToCSingularCochain Y n psi)
      (((topOpenSingularChainComplexIso Complex Y).hom.f n).hom
        (fieldToFieldChainGroup Rat Complex
          ((Opens.toTopCat Y).obj ⊤) n c))
  have hsquare := fieldToFieldChainGroup_naturality Rat Complex
    (Opens.inclusionTopIso Y).hom n
  have hc := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hsquare) c
  simp only [ConcreteCategory.comp_apply] at hc
  have hc' :
      ((topOpenSingularChainComplexIso Complex Y).hom.f n).hom
          (fieldToFieldChainGroup Rat Complex
            ((Opens.toTopCat Y).obj ⊤) n c) =
        fieldToFieldChainGroup Rat Complex Y n
          (((topOpenSingularChainComplexIso Rat Y).hom.f n).hom c) := by
    exact hc
  let cY : Simplicial.ChainGroup Rat (TopCat.toSSet.obj Y) n :=
    ((topOpenSingularChainComplexIso Rat Y).hom.f n).hom c
  have hc'' :
      ((topOpenSingularChainComplexIso Complex Y).hom.f n).hom
          (fieldToFieldChainGroup Rat Complex
            ((Opens.toTopCat Y).obj ⊤) n c) =
        qToCChainGroup Y n cY := by
    exact hc'
  rw [hc'', qToCSingularCochain_apply_qToCChain]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma ordinarySingularCohomologyEquivGlobalRaw_qToC
    (n : Nat) (a : OrdinarySingularCohomology Rat Y n) :
    HomologicalComplex.homologyMap
        (qToCGlobalRawSingularCochainComplex Y) n
        (ordinarySingularCohomologyEquivGlobalRaw Rat Y n a) =
      ordinarySingularCohomologyEquivGlobalRaw Complex Y n
        (qToCOrdinaryCochainCohomologyMap Y n a) := by
  let KQ := (SingularChainComplex Rat Y).linearDualCochainComplex
  obtain ⟨phi, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (KQ.homologyπ n)).mp inferInstance a
  rw [qToCOrdinaryCochainCohomologyMap_homologyπ,
    ordinarySingularCohomologyEquivGlobalRaw_homologyπ,
    ordinarySingularCohomologyEquivGlobalRaw_homologyπ,
    ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality]
  simp only [ConcreteCategory.comp_apply]
  rw [ordinarySingularCochainCyclesToGlobalRaw_qToC]

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular.HereditarilyParacompact

variable (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma ordinarySingularCohomologyEquivGlobalSections_qToC
    (n : Nat) (a : OrdinarySingularCohomology Rat Y n) :
    ordinaryComplexSingularCohomologyEquivGlobalSections Y n
        (qToCOrdinaryCochainCohomologyMap Y n a) =
      HomologicalComplex.homologyMap
        (qToCGlobalSingularCochainSheafComplex Y) n
        (ordinaryRationalSingularCohomologyEquivGlobalSections Y n a) := by
  dsimp only [ordinaryComplexSingularCohomologyEquivGlobalSections,
    ordinaryRationalSingularCohomologyEquivGlobalSections, AddEquiv.trans_apply]
  rw [← ordinarySingularCohomologyEquivGlobalRaw_qToC]
  simp only [Iso.addCommGroupIsoToAddEquiv_apply]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (topOpenToGlobal_qToC_naturality Y)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact (ConcreteCategory.congr_hom h
    (ordinarySingularCohomologyEquivGlobalRaw Rat Y n a)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma singularCohomologyEquivGlobalSections_qToC
    (n : Nat) (a : AlgebraicTopology.Singular.Cohomology Rat Y n) :
    complexSingularCohomologyEquivGlobalSections Y n
        (rationalToComplexCohomologyMap Y n a) =
      HomologicalComplex.homologyMap
        (qToCGlobalSingularCochainSheafComplex Y) n
        (rationalSingularCohomologyEquivGlobalSections Y n a) := by
  let eQ := ordinarySingularCohomologyEquivCohomology Rat Y n
  let eC := ordinarySingularCohomologyEquivCohomology Complex Y n
  have huct :
      eC.symm (rationalToComplexCohomologyMap Y n a) =
        qToCOrdinaryCochainCohomologyMap Y n (eQ.symm a) := by
    apply eC.injective
    rw [eC.apply_symm_apply, qToCOrdinaryCohomology_uct,
      eQ.apply_symm_apply]
  dsimp only [complexSingularCohomologyEquivGlobalSections,
    rationalSingularCohomologyEquivGlobalSections, AddEquiv.trans_apply]
  change ordinaryComplexSingularCohomologyEquivGlobalSections Y n
      (eC.symm (rationalToComplexCohomologyMap Y n a)) = _
  rw [huct]
  exact ordinarySingularCohomologyEquivGlobalSections_qToC Y n (eQ.symm a)

end AlgebraicTopology.Singular.HereditarilyParacompact

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec (.of Complex)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma rationalToComplexSingularCochainHypercohomologyEquivGlobalSections_naturality
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : Int) (a : RationalSingularCochainHypercohomology X n) :
    complexSingularCochainHypercohomologyEquivGlobalSections X n
        (hypercohomologyMap X
          (rationalToComplexSingularCochainComplexInt X) n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up Int)).map
            (rationalToComplexSingularCochainComplexInt X)) n
        (rationalSingularCochainHypercohomologyEquivGlobalSections X n a) := by
  let SQ := singularCochainSheafComplexInt X Rat
  let SC := singularCochainSheafComplexInt X Complex
  let hQ : ∀ q, (SQ.X q).IsFlasque :=
    fun q ↦ singularCochainSheafComplexInt_isFlasque X q
  let hC : ∀ q, (SC.X q).IsFlasque :=
    fun q ↦ complexSingularCochainSheafComplexInt_isFlasque X q
  letI : SQ.IsStrictlyGE 0 := by
    dsimp [SQ, singularCochainSheafComplexInt]
    infer_instance
  letI : SC.IsStrictlyGE 0 := by
    dsimp [SC, singularCochainSheafComplexInt]
    infer_instance
  change hypercohomologyEquivGlobalSections X SC 0 hC n
      (hypercohomologyMap X
        (rationalToComplexSingularCochainComplexInt X) n a) = _
  change _ = HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up Int)).map
          (rationalToComplexSingularCochainComplexInt X)) n
      (hypercohomologyEquivGlobalSections X SQ 0 hQ n a)
  exact plainHypercohomologyEquivGlobalSections_naturality X
    SQ SC 0 hQ hC (rationalToComplexSingularCochainComplexInt X) n a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma rationalToComplexSingularCochainHypercohomologyEquivCohomology_naturality
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : Nat) (a : RationalSingularCochainHypercohomology X (n : Int)) :
    complexSingularCochainHypercohomologyEquivCohomology X n
        (hypercohomologyMap X
          (rationalToComplexSingularCochainComplexInt X) (n : Int) a) =
      AlgebraicTopology.Singular.rationalToComplexCohomologyMap
        (TopCat.of (ComplexPoint X)) n
        (rationalSingularCochainHypercohomologyEquivCohomology X n a) := by
  dsimp only [complexSingularCochainHypercohomologyEquivCohomology,
    rationalSingularCochainHypercohomologyEquivCohomology, Equiv.trans_apply]
  rw [rationalToComplexSingularCochainHypercohomologyEquivGlobalSections_naturality]
  let Y := TopCat.of (ComplexPoint X)
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  let KQ := AlgebraicTopology.Singular.globalSingularCochainSheafComplex Rat Y
  let KC := AlgebraicTopology.Singular.globalSingularCochainSheafComplex Complex Y
  let qNat := AlgebraicTopology.Singular.qToCGlobalSingularCochainSheafComplex Y
  let qInt :=
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
      ).mapHomologicalComplex (.up Int)).map
        (rationalToComplexSingularCochainComplexInt X)
  let eQ := globalSectionsSingularCochainComplexIntIsoExtend X
  let eC := globalSectionsComplexSingularCochainComplexIntIsoExtend X
  let EQ := AlgebraicTopology.Singular.HereditarilyParacompact.rationalSingularCohomologyEquivGlobalSections
    Y n
  let EC := AlgebraicTopology.Singular.HereditarilyParacompact.complexSingularCohomologyEquivGlobalSections
    Y n
  have hn : ComplexShape.embeddingUpNat.f n = (n : Int) := rfl
  let b := rationalSingularCochainHypercohomologyEquivGlobalSections X (n : Int) a
  let bQ : KQ.homology n :=
    (KQ.extendHomologyIso ComplexShape.embeddingUpNat
      (j := n) (j' := (n : Int)) hn).hom.hom
      (HomologicalComplex.homologyMap eQ.hom (n : Int) b)
  let bC : KC.homology n :=
    (KC.extendHomologyIso ComplexShape.embeddingUpNat
      (j := n) (j' := (n : Int)) hn).hom.hom
      (HomologicalComplex.homologyMap eC.hom (n : Int)
        (HomologicalComplex.homologyMap qInt (n : Int) b))
  have hglobal := congrArg
    (fun f => HomologicalComplex.homologyMap f (n : Int))
    (globalSectionsSingularCochainComplexIntIsoExtend_qToC_naturality X)
  simp only [HomologicalComplex.homologyMap_comp] at hglobal
  have hglobal_b := ConcreteCategory.congr_hom hglobal b
  have hext := HomologicalComplex.extendHomologyIso_hom_naturality
    qNat ComplexShape.embeddingUpNat (j := n) (j' := (n : Int)) hn
  have hext_b := ConcreteCategory.congr_hom hext
    (HomologicalComplex.homologyMap eQ.hom (n : Int) b)
  simp only [ConcreteCategory.comp_apply] at hglobal_b hext_b
  have hglobal_b' :
      HomologicalComplex.homologyMap eC.hom (n : Int)
          (HomologicalComplex.homologyMap qInt (n : Int) b) =
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap qNat ComplexShape.embeddingUpNat)
          (n : Int)
          (HomologicalComplex.homologyMap eQ.hom (n : Int) b) := by
    exact hglobal_b
  have hstage :
      bC = HomologicalComplex.homologyMap qNat n bQ := by
    dsimp only [bC, bQ]
    rw [hglobal_b']
    exact hext_b
  have hbetti :
      EC.symm (HomologicalComplex.homologyMap qNat n bQ) =
        AlgebraicTopology.Singular.rationalToComplexCohomologyMap Y n
          (EQ.symm bQ) := by
    apply EC.injective
    rw [EC.apply_symm_apply]
    rw [AlgebraicTopology.Singular.HereditarilyParacompact.singularCohomologyEquivGlobalSections_qToC]
    rw [EQ.apply_symm_apply]
  change EC.symm bC =
    AlgebraicTopology.Singular.rationalToComplexCohomologyMap Y n (EQ.symm bQ)
  rw [hstage, hbetti]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem complexCohomologyEquivSingularCohomology_fieldToComplexCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : Nat) (a : FieldCohomology Rat X (n : Int)) :
    complexCohomologyEquivSingularCohomology X n
        (fieldToComplexCohomology Rat X (n : Int) a) =
      AlgebraicTopology.Singular.rationalToComplexCohomologyMap
        (TopCat.of (ComplexPoint X)) n
        (rationalCohomologyAddEquivSingularCohomology X n a) := by
  change complexSingularCochainHypercohomologyEquivCohomology X n
      (hypercohomologyMap X (complexToSingularCochainComplexInt X) (n : Int)
        (fieldToComplexCohomology Rat X (n : Int) a)) =
    AlgebraicTopology.Singular.rationalToComplexCohomologyMap
      (TopCat.of (ComplexPoint X)) n
      (rationalSingularCochainHypercohomologyAddEquivCohomology X n
        (hypercohomologyMap X (rationalToSingularCochainComplexInt X)
          (n : Int) a))
  rw [fieldToComplexCohomology_singularCochain_square]
  exact rationalToComplexSingularCochainHypercohomologyEquivCohomology_naturality
    X n (hypercohomologyMap X (rationalToSingularCochainComplexInt X)
      (n : Int) a)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem deRhamCohomologyEquivComplexSingularCohomology_fieldToDeRhamCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : Nat) (a : FieldCohomology Rat X (n : Int)) :
    deRhamCohomologyEquivComplexSingularCohomology X n
        (fieldToDeRhamCohomology Rat X (n : Int) a) =
      AlgebraicTopology.Singular.rationalToComplexCohomologyMap
        (TopCat.of (ComplexPoint X)) n
        (rationalCohomologyAddEquivSingularCohomology X n a) := by
  let e := complexConstantCohomologyDeRhamEquiv X inferInstance (n : Int)
  have hDR :
      e.symm (fieldToDeRhamCohomology Rat X (n : Int) a) =
        fieldToComplexCohomology Rat X (n : Int) a := by
    rw [fieldToDeRhamCohomology_factor]
    change e.symm
        (e (fieldToComplexCohomology Rat X (n : Int) a)) = _
    exact e.symm_apply_apply _
  change complexCohomologyEquivSingularCohomology X n
      (e.symm (fieldToDeRhamCohomology Rat X (n : Int) a)) = _
  rw [hDR]
  exact complexCohomologyEquivSingularCohomology_fieldToComplexCohomology X n a

end AlgebraicGeometry.ComplexPoint
