/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexBettiGlobalSectionsAdditivity
public import Other.AlgebraicGeometry.PlainHypercohomologyGlobalSectionsNaturality
public import Other.AlgebraicGeometry.SingularCochainMapNaturality
public import Other.AlgebraicGeometry.HolomorphicFunctionPullback
public import Other.Algebra.Homology.MapExtendCompositeNaturality

/-!
# Naturality of the complex singular-cohomology comparison

This file proves that the comparison from hypercohomology of the complex
singular-cochain resolution to ordinary complex singular cohomology commutes
with the map induced by an algebraic self-map.
-/

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology

variable (X : Over (Spec (.of ℂ)))

def singularRestrictionSheafComplexInt
    {U Y : TopCat.{0}} (j : U ⟶ Y) (R : Type) [Field R] :
    (Singular.singularCochainSheafComplex R Y).extend
        ComplexShape.embeddingUpNat ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        ((Singular.singularCochainSheafComplex R U).extend
          ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap
      (Singular.singularRestrictionSheafComplex R j)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.pushforward AddCommGrpCat j)
      (Singular.singularCochainSheafComplex R U)
      ComplexShape.embeddingUpNat).inv

lemma pushforwardComplexSingularCochainSheafComplexInt_isFlasque
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (f : X ⟶ X) (q : ℤ) :
    TopCat.Sheaf.IsFlasque
      ((((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X X f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (singularCochainSheafComplexInt X ℂ)).X q) := by
  change TopCat.Sheaf.IsFlasque
    ((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X X f)).obj
      ((singularCochainSheafComplexInt X ℂ).X q))
  letI : TopCat.Sheaf.IsFlasque
      ((singularCochainSheafComplexInt X ℂ).X q) :=
    complexSingularCochainSheafComplexInt_isFlasque X q
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque
    ((singularCochainSheafComplexInt X ℂ).X q)
    (analyticMapTopCat X X f)

instance pushforwardComplexSingularCochainSheafComplexInt_isStrictlyGE
    (f : X ⟶ X) :
    CochainComplex.IsStrictlyGE
      (((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X X f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (singularCochainSheafComplexInt X ℂ)) 0 := by
  let K := singularCochainSheafComplexInt X ℂ
  letI : CochainComplex.IsStrictlyGE K 0 := by
    dsimp [K, singularCochainSheafComplexInt]
    infer_instance
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  change IsZero ((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticMapTopCat X X f)).obj (K.X i))
  exact Functor.map_isZero
    (TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X X f))
    (K.isZero_of_isStrictlyGE 0 i hi)

set_option backward.isDefEq.respectTransparency false in
lemma complexSingularHypercohomology_naturality_to_pushforward
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (f : X ⟶ X) (n : ℤ)
    (a : ComplexSingularCochainHypercohomology X n) :
    hypercohomologyEquivGlobalSections X
        (((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X X f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (singularCochainSheafComplexInt X ℂ)) 0
        (pushforwardComplexSingularCochainSheafComplexInt_isFlasque X f) n
        (hypercohomologyMap X
          (singularRestrictionSheafComplexInt
            (analyticMapTopCat X X f) ℂ) n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex
            (.up ℤ)).map
          (singularRestrictionSheafComplexInt
            (analyticMapTopCat X X f) ℂ)) n
        (complexSingularCochainHypercohomologyEquivGlobalSections X n a) := by
  let K := singularCochainSheafComplexInt X ℂ
  let L := ((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X X f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K
  let g : K ⟶ L := singularRestrictionSheafComplexInt
    (analyticMapTopCat X X f) ℂ
  letI : K.IsStrictlyGE 0 := by
    dsimp [K, singularCochainSheafComplexInt]
    infer_instance
  letI : CochainComplex.IsStrictlyGE L 0 := by
    exact pushforwardComplexSingularCochainSheafComplexInt_isStrictlyGE X f
  have hK : ∀ q, (K.X q).IsFlasque :=
    complexSingularCochainSheafComplexInt_isFlasque X
  have hL : ∀ q, (L.X q).IsFlasque :=
    pushforwardComplexSingularCochainSheafComplexInt_isFlasque X f
  exact plainHypercohomologyEquivGlobalSections_naturality
    X K L 0 hK hL g n a

def globalSectionsPushforwardComplexSingularCochainComplexIntIsoExtend
    (f : X ⟶ X) :
    TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X X f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (singularCochainSheafComplexInt X ℂ)) ≅
      (AlgebraicTopology.Singular.globalPushforwardSingularCochainSheafComplex
        ℂ (analyticMapTopCat X X f)).extend
          ComplexShape.embeddingUpNat := by
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let G := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let P := TopCat.Sheaf.pushforward AddCommGrpCat (analyticMapTopCat X X f)
  let K := AlgebraicTopology.Singular.singularCochainSheafComplex ℂ Y
  let KP := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let : F.Additive := by dsimp [F]; infer_instance
  let : E.Additive := by dsimp [E]; infer_instance
  let eComp : F ⋙ E ≅ G := Iso.refl _
  exact
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (HomologicalComplex.mapExtendCanonicalIso P K
          ComplexShape.embeddingUpNat) ≪≫
      HomologicalComplex.mapExtendIso G KP ComplexShape.embeddingUpNat ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
        ((Functor.mapHomologicalComplexCompIso eComp
          (ComplexShape.up ℕ)).app KP).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma globalSectionsSingularRestrictionComplexInt_transport
    (f : X ⟶ X) :
    (globalSectionsComplexSingularCochainComplexIntIsoExtend X).hom ≫
        HomologicalComplex.extendMap
          (AlgebraicTopology.Singular.globalSingularSheafRestriction ℂ
            (analyticMapTopCat X X f))
          ComplexShape.embeddingUpNat =
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex
            (.up ℤ)).map
          (singularRestrictionSheafComplexInt
            (analyticMapTopCat X X f) ℂ)) ≫
        (globalSectionsPushforwardComplexSingularCochainComplexIntIsoExtend
          X f).hom := by
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let G := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let P := TopCat.Sheaf.pushforward AddCommGrpCat (analyticMapTopCat X X f)
  let K := AlgebraicTopology.Singular.singularCochainSheafComplex ℂ Y
  let KP := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let r := AlgebraicTopology.Singular.singularRestrictionSheafComplex ℂ
    (analyticMapTopCat X X f)
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : E.Additive := by dsimp [E]; infer_instance
  letI : G.Additive := by dsimp [G]; infer_instance
  let eComp : F ⋙ E ≅ G := Iso.refl _
  change
    (HomologicalComplex.mapExtendIso G K ComplexShape.embeddingUpNat).hom ≫
        HomologicalComplex.extendMap
          ((Functor.mapHomologicalComplexCompIso eComp
            (ComplexShape.up ℕ)).inv.app K) ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap
          ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map r))
          ComplexShape.embeddingUpNat =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap r ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.mapExtendCanonicalIso P K
              ComplexShape.embeddingUpNat).inv) ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapExtendCanonicalIso P K
            ComplexShape.embeddingUpNat).hom ≫
        (HomologicalComplex.mapExtendIso G KP
          ComplexShape.embeddingUpNat).hom ≫
        HomologicalComplex.extendMap
          ((Functor.mapHomologicalComplexCompIso eComp
            (ComplexShape.up ℕ)).inv.app KP) ComplexShape.embeddingUpNat
  rw [Functor.map_comp]
  let cIso := HomologicalComplex.mapExtendCanonicalIso P K
    ComplexShape.embeddingUpNat
  let tail := (HomologicalComplex.mapExtendIso G KP
      ComplexShape.embeddingUpNat).hom ≫
    HomologicalComplex.extendMap
      ((Functor.mapHomologicalComplexCompIso eComp
        (ComplexShape.up ℕ)).inv.app KP) ComplexShape.embeddingUpNat
  have hcancel :
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map cIso.inv ≫
          (G.mapHomologicalComplex (ComplexShape.up ℤ)).map cIso.hom ≫ tail = tail := by
    change ((G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso cIso).inv ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso cIso).hom ≫ tail = tail
    exact ((G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso cIso).inv_hom_id_assoc tail
  simp only [Category.assoc]
  rw [hcancel]
  exact
    (HomologicalComplex.mapExtendCompIso_naturality
      F E G eComp r ComplexShape.embeddingUpNat).symm

/-- Hypercohomology of the pushed singular-cochain resolution, evaluated back
on the source of the self-map. -/
def pushforwardComplexSingularHypercohomologyEquivGlobalSections
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (f : X ⟶ X) (n : ℕ) :
    Hypercohomology X
        (((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X X f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (singularCochainSheafComplexInt X ℂ)) (n : ℤ) ≃
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ
        (TopCat.of (ComplexPoint X))).homology n := by
  let KP := AlgebraicTopology.Singular.globalPushforwardSingularCochainSheafComplex
    ℂ (analyticMapTopCat X X f)
  exact (hypercohomologyEquivGlobalSections X
      (((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X X f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (singularCochainSheafComplexInt X ℂ)) 0
      (pushforwardComplexSingularCochainSheafComplexInt_isFlasque X f)
      (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsPushforwardComplexSingularCochainComplexIntIsoExtend
        X f) (n : ℤ)).addCommGroupIsoToAddEquiv.toEquiv |>.trans <|
      (KP.extendHomologyIso ComplexShape.embeddingUpNat rfl
        ).addCommGroupIsoToAddEquiv.toEquiv |>.trans <|
        (HomologicalComplex.homologyMapIso
          (AlgebraicTopology.Singular.globalPushforwardSingularCochainSheafComplexIsoGlobal
            ℂ (analyticMapTopCat X X f)) n).addCommGroupIsoToAddEquiv.toEquiv

def pushforwardComplexSingularHypercohomologyEquivCohomology
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (f : X ⟶ X) (n : ℕ) :
    Hypercohomology X
        (((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X X f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (singularCochainSheafComplexInt X ℂ)) (n : ℤ) ≃
      AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint X)) n := by
  let Y := TopCat.of (ComplexPoint X)
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  letI : QuasiIso
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex
        ℂ Y) :=
    AlgebraicTopology.Singular.HereditarilyParacompact.topOpenToGlobalSingularCochainSheafComplex_quasiIso_complex
  exact (pushforwardComplexSingularHypercohomologyEquivGlobalSections
    X f n).trans (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
      ℂ Y n).symm.toEquiv

def normalizedComplexSingularCochainHypercohomologyEquivGlobalSections
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    ComplexSingularCochainHypercohomology X (n : ℤ) ≃
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ
        (TopCat.of (ComplexPoint X))).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y
  exact (complexSingularCochainHypercohomologyEquivGlobalSections
      X (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsComplexSingularCochainComplexIntIsoExtend X)
        (n : ℤ)).addCommGroupIsoToAddEquiv.toEquiv |>.trans <|
      (K.extendHomologyIso ComplexShape.embeddingUpNat rfl
        ).addCommGroupIsoToAddEquiv.toEquiv

def normalizedComplexSingularCochainHypercohomologyEquivCohomology
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    ComplexSingularCochainHypercohomology X (n : ℤ) ≃
      AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint X)) n := by
  let Y := TopCat.of (ComplexPoint X)
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  letI : QuasiIso
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex
        ℂ Y) :=
    AlgebraicTopology.Singular.HereditarilyParacompact.topOpenToGlobalSingularCochainSheafComplex_quasiIso_complex
  exact (normalizedComplexSingularCochainHypercohomologyEquivGlobalSections X n).trans
    (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
      ℂ Y n).symm.toEquiv

lemma normalizedComplexSingularCochainHypercohomologyEquivCohomology_eq_standard
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) (a : ComplexSingularCochainHypercohomology X (n : ℤ)) :
    normalizedComplexSingularCochainHypercohomologyEquivCohomology X n a =
      complexSingularCochainHypercohomologyEquivCohomology X n a := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma complexSingularCochainHypercohomologyEquivCohomology_naturality
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (f : X ⟶ X) (n : ℕ)
    (a : ComplexSingularCochainHypercohomology X (n : ℤ)) :
    pushforwardComplexSingularHypercohomologyEquivCohomology X f n
        (hypercohomologyMap X
          (singularRestrictionSheafComplexInt
            (analyticMapTopCat X X f) ℂ) (n : ℤ) a) =
      AlgebraicTopology.Singular.cohomologyMap ℂ n
        (analyticMapTopCat X X f)
        (complexSingularCochainHypercohomologyEquivCohomology X n a) := by
  rw [← normalizedComplexSingularCochainHypercohomologyEquivCohomology_eq_standard X n a]
  let Y := TopCat.of (ComplexPoint X)
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  letI : QuasiIso
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex
        ℂ Y) :=
    AlgebraicTopology.Singular.HereditarilyParacompact.topOpenToGlobalSingularCochainSheafComplex_quasiIso_complex
  apply (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
    ℂ Y n).injective
  rw [AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections_naturality]
  simp only [pushforwardComplexSingularHypercohomologyEquivCohomology,
    normalizedComplexSingularCochainHypercohomologyEquivCohomology,
    Equiv.trans_apply]
  let b := pushforwardComplexSingularHypercohomologyEquivGlobalSections X f n
    (hypercohomologyMap X
      (singularRestrictionSheafComplexInt
        (analyticMapTopCat X X f) ℂ) (n : ℤ) a)
  let c := normalizedComplexSingularCochainHypercohomologyEquivGlobalSections X n a
  have htarget :
      (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
        ℂ Y n)
        ((AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
          ℂ (TopCat.of (ComplexPoint X)) n).symm.toEquiv b) = b := by
    change (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
      ℂ Y n).toEquiv
      ((AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
        ℂ Y n).toEquiv.symm b) = b
    exact (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
      ℂ Y n).toEquiv.apply_symm_apply b
  have hsource :
      (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
        ℂ (TopCat.of (ComplexPoint X)) n)
        ((AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
          ℂ (TopCat.of (ComplexPoint X)) n).symm.toEquiv c) = c := by
    exact (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
      ℂ (TopCat.of (ComplexPoint X)) n).toEquiv.apply_symm_apply c
  rw [htarget, hsource]
  dsimp [b, c, pushforwardComplexSingularHypercohomologyEquivGlobalSections,
    normalizedComplexSingularCochainHypercohomologyEquivGlobalSections]
  rw [HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply]
  apply congrArg (fun z ↦
    (HomologicalComplex.homologyMapIso
      (AlgebraicTopology.Singular.globalPushforwardSingularCochainSheafComplexIsoGlobal
        ℂ (analyticMapTopCat X X f)) n).addCommGroupIsoToAddEquiv z)
  rw [complexSingularHypercohomology_naturality_to_pushforward]
  have hglobal := congrArg
    (fun g ↦ HomologicalComplex.homologyMap g (n : ℤ))
    (globalSectionsSingularRestrictionComplexInt_transport X f)
  simp only [HomologicalComplex.homologyMap_comp] at hglobal
  have hglobal_a := ConcreteCategory.congr_hom hglobal
    (complexSingularCochainHypercohomologyEquivGlobalSections X (n : ℤ) a)
  simp only [ConcreteCategory.comp_apply] at hglobal_a
  have hglobal_ext := congrArg
    (fun z ↦ (HomologicalComplex.extendHomologyIso
      (AlgebraicTopology.Singular.globalPushforwardSingularCochainSheafComplex
      ℂ (analyticMapTopCat X X f)) ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl).addCommGroupIsoToAddEquiv z)
    hglobal_a.symm
  have hglobal_ext' :
      (HomologicalComplex.extendHomologyIso
          (AlgebraicTopology.Singular.globalPushforwardSingularCochainSheafComplex
            ℂ (analyticMapTopCat X X f)) ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).addCommGroupIsoToAddEquiv
        ((HomologicalComplex.homologyMapIso
            (globalSectionsPushforwardComplexSingularCochainComplexIntIsoExtend
              X f) (n : ℤ)).addCommGroupIsoToAddEquiv
          (HomologicalComplex.homologyMap
            (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
              (TopCat.of (ComplexPoint X))).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
              (singularRestrictionSheafComplexInt
                (analyticMapTopCat X X f) ℂ)) (n : ℤ)
            (complexSingularCochainHypercohomologyEquivGlobalSections
              X (n : ℤ) a))) =
        (HomologicalComplex.extendHomologyIso
          (AlgebraicTopology.Singular.globalPushforwardSingularCochainSheafComplex
            ℂ (analyticMapTopCat X X f)) ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).addCommGroupIsoToAddEquiv
        (HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap
            (AlgebraicTopology.Singular.globalSingularSheafRestriction ℂ
              (analyticMapTopCat X X f)) ComplexShape.embeddingUpNat)
          (n : ℤ)
          ((HomologicalComplex.homologyMapIso
            (globalSectionsComplexSingularCochainComplexIntIsoExtend X)
            (n : ℤ)).addCommGroupIsoToAddEquiv
            (complexSingularCochainHypercohomologyEquivGlobalSections
              X (n : ℤ) a))) := by
    exact hglobal_ext
  rw [hglobal_ext']
  have hext := HomologicalComplex.extendHomologyIso_hom_naturality
    (AlgebraicTopology.Singular.globalSingularSheafRestriction ℂ
    (analyticMapTopCat X X f))
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  have hext_a := ConcreteCategory.congr_hom hext
    (HomologicalComplex.homologyMap
      (globalSectionsComplexSingularCochainComplexIntIsoExtend X).hom
      (n : ℤ)
      (complexSingularCochainHypercohomologyEquivGlobalSections X (n : ℤ) a))
  simp only [ConcreteCategory.comp_apply] at hext_a
  change
    (HomologicalComplex.extendHomologyIso
      (AlgebraicTopology.Singular.globalPushforwardSingularCochainSheafComplex
        ℂ (analyticMapTopCat X X f)) ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl).hom.hom
      (HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (AlgebraicTopology.Singular.globalSingularSheafRestriction ℂ
            (analyticMapTopCat X X f)) ComplexShape.embeddingUpNat)
        (n : ℤ)
        ((HomologicalComplex.homologyMapIso
          (globalSectionsComplexSingularCochainComplexIntIsoExtend X)
          (n : ℤ)).hom.hom
          (complexSingularCochainHypercohomologyEquivGlobalSections
            X (n : ℤ) a))) =
      HomologicalComplex.homologyMap
        (AlgebraicTopology.Singular.globalSingularSheafRestriction ℂ
          (analyticMapTopCat X X f)) n
        ((HomologicalComplex.extendHomologyIso
          (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ
            (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).hom.hom
          ((HomologicalComplex.homologyMapIso
            (globalSectionsComplexSingularCochainComplexIntIsoExtend X)
            (n : ℤ)).hom.hom
            (complexSingularCochainHypercohomologyEquivGlobalSections
              X (n : ℤ) a)))
  exact hext_a

end AlgebraicGeometry.ComplexPoint
