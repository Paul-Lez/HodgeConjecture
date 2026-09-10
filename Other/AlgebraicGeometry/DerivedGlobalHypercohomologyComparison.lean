/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusInjectiveModel
public import Other.AlgebraicGeometry.BettiCohomologyWithSupportComparison
public import Other.AlgebraicGeometry.HypercohomologyGlobalSectionsNaturality
public import Other.AlgebraicTopology.DerivedSheafSupportForget
public import Other.AlgebraicTopology.DerivedSheafSupportTruncation

/-!
# Actual derived global sections and public hypercohomology

For a nonnegatively supported analytic sheaf complex, this file compares the
homology of the actual `D⁺` right-derived global-sections functor with the
repository's public `Hypercohomology` type.  Both sides are computed with one
fixed monic, bounded-below, termwise-injective replacement.  The construction
therefore also gives a strict lift of every coefficient-complex morphism and
will expose naturality without an additional comparison hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {A S I : CochainComplex C ℤ} (b : ℤ)
  [A.IsStrictlyGE b] [S.IsStrictlyGE b] [I.IsStrictlyGE b]
  (a : A ⟶ S) [Mono a] [QuasiIso a] (r : A ⟶ I)

/-- The injective-model lifting argument at an arbitrary common lower bound.
The pre-existing construction was specialized to lower bound zero. -/
def liftToInjectiveAt
    (hI : ∀ n : ℤ, Injective (I.X n)) : S ⟶ I := by
  let A' : Plus C := ⟨A, b, inferInstance⟩
  let S' : Plus C := ⟨S, b, inferInstance⟩
  let I' : Plus C := ⟨I, b, inferInstance⟩
  let a' : A' ⟶ S' := ObjectProperty.homMk a
  let r' : A' ⟶ I' := ObjectProperty.homMk r
  let Z' := ⊤_ Plus C
  let p : I' ⟶ Z' := terminal.from I'
  let c : S' ⟶ Z' := terminal.from S'
  let sq : CommSq r' a' p c := CommSq.mk (Subsingleton.elim _ _)
  letI : Mono a' := (Plus.mono_iff a').2 (inferInstance : Mono a)
  letI : WeakEquivalence a' :=
    (Plus.modelCategoryQuillen.weakEquivalence_iff a').2
      (inferInstance : QuasiIso a)
  letI : IsFibrant I' :=
    (Plus.modelCategoryQuillen.isFibrant_iff I').2 hI
  exact sq.lift.hom

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
omit [EnoughInjectives C] in
/-- The arbitrary-bound injective lift strictly extends its prescribed map. -/
@[reassoc (attr := simp)]
theorem comp_liftToInjectiveAt
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    a ≫ liftToInjectiveAt b a r hI = r := by
  let A' : Plus C := ⟨A, b, inferInstance⟩
  let S' : Plus C := ⟨S, b, inferInstance⟩
  let I' : Plus C := ⟨I, b, inferInstance⟩
  let a' : A' ⟶ S' := ObjectProperty.homMk a
  let r' : A' ⟶ I' := ObjectProperty.homMk r
  let Z' := ⊤_ Plus C
  let p : I' ⟶ Z' := terminal.from I'
  let c : S' ⟶ Z' := terminal.from S'
  let sq : CommSq r' a' p c := CommSq.mk (Subsingleton.elim _ _)
  letI : Mono a' := (Plus.mono_iff a').2 (inferInstance : Mono a)
  letI : WeakEquivalence a' :=
    (Plus.modelCategoryQuillen.weakEquivalence_iff a').2
      (inferInstance : QuasiIso a)
  letI : IsFibrant I' :=
    (Plus.modelCategoryQuillen.isFibrant_iff I').2 hI
  exact congrArg (fun f ↦ f.hom) sq.fac_left

end CochainComplex

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The injective-model computation of a bounded-below right-derived functor
is natural for a strict morphism between two injective models. -/
@[reassoc]
theorem rightDerivedFunctorPlusInjectiveModelIso_map_naturality
    (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex.Plus (InjectiveObject C)} (g : I ⟶ J) :
    DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map
            ((InjectiveObject.ι C).mapHomotopyCategoryPlus.map
              ((HomotopyCategory.Plus.quotient _).map g)))) ≫
      (F.rightDerivedFunctorPlusInjectiveModelIso J).hom =
    (F.rightDerivedFunctorPlusInjectiveModelIso I).hom ≫
      DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map
          (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).map g.hom)) := by
  let K : HomotopyCategory.Plus C :=
    (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.quotient _).obj I)
  let L : HomotopyCategory.Plus C :=
    (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.quotient _).obj J)
  let qg : K ⟶ L :=
    (InjectiveObject.ι C).mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.quotient _).map g)
  have hu : F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map qg) ≫
      CategoryTheory.inv (F.rightDerivedFunctorPlusUnit.app L) =
      CategoryTheory.inv (F.rightDerivedFunctorPlusUnit.app K) ≫
        DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map qg) := by
    apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app K)).1
    have hn := F.rightDerivedFunctorPlusUnit.naturality qg
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, IsIso.hom_inv_id_assoc]
  have hFg :
      DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Qh.map
            (F.mapHomotopyCategoryPlus.map qg)) =
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient D (.up ℤ)).map
            ((F.mapHomologicalComplex (.up ℤ)).map
              (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).map g.hom))) := by
    rfl
  dsimp only [Functor.rightDerivedFunctorPlusInjectiveModelIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv,
    Category.assoc]
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp, Category.assoc, hFg]
  congr 1
  exact (DerivedCategory.quotientCompQhIso D).hom.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map
      (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).map g.hom))

end CategoryTheory.Functor

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ)))

local instance derivedGlobalHypercohomologySheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance derivedGlobalHypercohomologyGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

variable (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
  [K.IsStrictlyGE 0]

/-- A fixed monic, quasi-isomorphic, termwise-injective replacement.  It is
allowed one extra zero term in degree `-1`, as supplied by the injective model
factorization. -/
def globalHypercohomologyInjectiveComplex :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  Classical.choose
    (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
      K (-1) 0)

/-- The fixed monic augmentation into the injective replacement. -/
def globalHypercohomologyInjectiveMap :
    K ⟶ globalHypercohomologyInjectiveComplex X K :=
  Classical.choose (Classical.choose_spec
    (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
      K (-1) 0))

instance globalHypercohomologyInjectiveMap_mono :
    Mono (globalHypercohomologyInjectiveMap X K) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
      K (-1) 0)))

instance globalHypercohomologyInjectiveMap_quasiIso :
    QuasiIso (globalHypercohomologyInjectiveMap X K) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
        K (-1) 0))))

instance globalHypercohomologyInjectiveComplex_injective (q : ℤ) :
    Injective ((globalHypercohomologyInjectiveComplex X K).X q) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
        K (-1) 0))))) q

instance globalHypercohomologyInjectiveComplex_isStrictlyGE :
    (globalHypercohomologyInjectiveComplex X K).IsStrictlyGE (-1) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
        K (-1) 0)))))

instance globalHypercohomologyInjectiveComplex_isKInjective :
    (globalHypercohomologyInjectiveComplex X K).IsKInjective :=
  CochainComplex.isKInjective_of_injective
    (globalHypercohomologyInjectiveComplex X K) (-1)

/-- The fixed injective replacement bundled in the exact shape expected by
the construction of the actual `D⁺` right-derived functor. -/
def globalHypercohomologyInjectivePlus :
    CochainComplex.Plus (InjectiveObject (AnalyticAdditiveSheaf X)) := by
  let I := globalHypercohomologyInjectiveComplex X K
  let J := HomologicalComplex.liftObjectProperty
    (Injective : AnalyticAdditiveSheaf X → Prop) I (fun _ ↦ inferInstance)
  have hJ : CochainComplex.IsStrictlyGE J (-1) := by
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      J (InjectiveObject.ι (AnalyticAdditiveSheaf X))]
    change CochainComplex.IsStrictlyGE I (-1)
    infer_instance
  exact ⟨J, -1, hJ⟩

variable {K}

/-- A coefficient-complex morphism lifted strictly between the two fixed
injective replacements. -/
def globalHypercohomologyInjectiveMapMap
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) :
    globalHypercohomologyInjectiveComplex X K ⟶
      globalHypercohomologyInjectiveComplex X L := by
  letI : K.IsStrictlyGE (-1) := K.isStrictlyGE_of_ge (-1) 0 (by omega)
  letI : L.IsStrictlyGE (-1) := L.isStrictlyGE_of_ge (-1) 0 (by omega)
  exact CochainComplex.liftToInjectiveAt (-1)
    (globalHypercohomologyInjectiveMap X K)
    (f ≫ globalHypercohomologyInjectiveMap X L) (fun _ ↦ inferInstance)

/-- The lifted map commutes strictly with both chosen augmentations. -/
@[reassoc (attr := simp)]
theorem globalHypercohomologyInjectiveMap_comp_map
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) :
    globalHypercohomologyInjectiveMap X K ≫
        globalHypercohomologyInjectiveMapMap X f =
      f ≫ globalHypercohomologyInjectiveMap X L := by
  letI : K.IsStrictlyGE (-1) := K.isStrictlyGE_of_ge (-1) 0 (by omega)
  letI : L.IsStrictlyGE (-1) := L.isStrictlyGE_of_ge (-1) 0 (by omega)
  exact CochainComplex.comp_liftToInjectiveAt (-1)
    (globalHypercohomologyInjectiveMap X K)
    (f ≫ globalHypercohomologyInjectiveMap X L) (fun _ ↦ inferInstance)

/-- The strict lifted map bundled between the injective `Plus` models. -/
def globalHypercohomologyInjectivePlusMap
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) :
    globalHypercohomologyInjectivePlus X K ⟶
      globalHypercohomologyInjectivePlus X L := by
  let g := globalHypercohomologyInjectiveMapMap X f
  refine ObjectProperty.homMk ?_
  dsimp only [globalHypercohomologyInjectivePlus,
    HomologicalComplex.liftObjectProperty]
  exact
    { f := fun n ↦ ObjectProperty.homMk (g.f n)
      comm' := fun i j _ ↦ by
        apply ObjectProperty.hom_ext
        exact g.comm i j }

@[simp]
theorem globalHypercohomologyInjectivePlusMap_underlying
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) :
    ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomologicalComplex
      (.up ℤ)).map (globalHypercohomologyInjectivePlusMap X f).hom =
        globalHypercohomologyInjectiveMapMap X f := by
  dsimp only [globalHypercohomologyInjectivePlusMap,
    globalHypercohomologyInjectivePlus,
    HomologicalComplex.liftObjectProperty]
  ext n
  rfl

/-- A morphism of nonnegative coefficient complexes, bundled in the
bounded-below derived category with lower bound zero. -/
def nonnegativeCoefficientPlusMap
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) :
    TopCat.Sheaf.supportCoefficientPlus
        (TopCat.of (ComplexPoint X)) K 0 ⟶
      TopCat.Sheaf.supportCoefficientPlus
        (TopCat.of (ComplexPoint X)) L 0 :=
  DerivedCategory.Plus.ι.preimage (DerivedCategory.Q.map f)

/-- The ambient derived morphism underlying `nonnegativeCoefficientPlusMap`
is the localization of the original coefficient morphism. -/
@[simp]
theorem nonnegativeCoefficientPlusMap_underlying
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (nonnegativeCoefficientPlusMap X f) =
      DerivedCategory.Q.map f := by
  exact Functor.map_preimage _ _

variable (K)

/-- The coefficient derived object is canonically isomorphic to the fixed
injective replacement through its actual augmentation. -/
def globalHypercohomologyCoefficientInjectiveIso :
    TopCat.Sheaf.supportCoefficientPlus
        (TopCat.of (ComplexPoint X)) K 0 ≅
      DerivedCategory.Plus.Qh.obj
        ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient _).obj
            (globalHypercohomologyInjectivePlus X K))) :=
  DerivedCategory.Plus.ι.preimageIso
    (asIso (DerivedCategory.Q.map
        (globalHypercohomologyInjectiveMap X K)) ≪≫
      (DerivedCategory.quotientCompQhIso
        (AnalyticAdditiveSheaf X)).symm.app _)

variable {K}

/-- The comparison from the coefficient object to its fixed injective model
is natural for coefficient-complex morphisms and their strict lifts. -/
@[reassoc]
theorem globalHypercohomologyCoefficientInjectiveIso_naturality
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) :
    nonnegativeCoefficientPlusMap X f ≫
        (globalHypercohomologyCoefficientInjectiveIso X L).hom =
      (globalHypercohomologyCoefficientInjectiveIso X K).hom ≫
        DerivedCategory.Plus.Qh.map
          (((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus).map
            (((HomotopyCategory.Plus.quotient
              (InjectiveObject (AnalyticAdditiveSheaf X))).map
                (globalHypercohomologyInjectivePlusMap X f)))) := by
  have hg :
      DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Qh.map
            (((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus).map
              (((HomotopyCategory.Plus.quotient
                (InjectiveObject (AnalyticAdditiveSheaf X))).map
                  (globalHypercohomologyInjectivePlusMap X f))))) =
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) := by
    rfl
  apply (DerivedCategory.Plus.ι.map_injective)
  dsimp only [nonnegativeCoefficientPlusMap,
    globalHypercohomologyCoefficientInjectiveIso]
  simp only [Functor.map_comp, Functor.map_preimage, Functor.preimageIso_hom,
    Iso.trans_hom, Category.assoc]
  rw [hg]
  change
    DerivedCategory.Q.map f ≫
        DerivedCategory.Q.map (globalHypercohomologyInjectiveMap X L) ≫
          (DerivedCategory.quotientCompQhIso
            (AnalyticAdditiveSheaf X)).inv.app
              (globalHypercohomologyInjectiveComplex X L) =
      DerivedCategory.Q.map (globalHypercohomologyInjectiveMap X K) ≫
        (DerivedCategory.quotientCompQhIso
          (AnalyticAdditiveSheaf X)).inv.app
            (globalHypercohomologyInjectiveComplex X K) ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (.up ℤ)).map
              (globalHypercohomologyInjectiveMapMap X f))
  have hq := (DerivedCategory.quotientCompQhIso
    (AnalyticAdditiveSheaf X)).inv.naturality
      (globalHypercohomologyInjectiveMapMap X f)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hq
  rw [← hq]
  simp only [← Category.assoc, ← Functor.map_comp,
    globalHypercohomologyInjectiveMap_comp_map]

variable (K)

/-- Actual derived global sections computed on the fixed injective model. -/
def derivedGlobalSectionsInjectiveModelIso :
    DerivedCategory.Plus.ι.obj
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).obj
            (TopCat.Sheaf.supportCoefficientPlus
              (TopCat.of (ComplexPoint X)) K 0)) ≅
      DerivedCategory.Q.obj
        (TopCat.Sheaf.globalSectionsComplexInt
          (TopCat.of (ComplexPoint X))
            (globalHypercohomologyInjectiveComplex X K)) :=
  DerivedCategory.Plus.ι.mapIso
    ((TopCat.Sheaf.derivedGlobalSections
      (TopCat.of (ComplexPoint X))).mapIso
        (globalHypercohomologyCoefficientInjectiveIso X K)) ≪≫
    Functor.rightDerivedFunctorPlusInjectiveModelIso
      (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤)
      (globalHypercohomologyInjectivePlus X K)

variable {K}

/-- The actual derived-global-sections injective-model comparison is natural
for coefficient-complex morphisms. -/
@[reassoc]
theorem derivedGlobalSectionsInjectiveModelIso_naturality
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (nonnegativeCoefficientPlusMap X f)) ≫
      (derivedGlobalSectionsInjectiveModelIso X L).hom =
    (derivedGlobalSectionsInjectiveModelIso X K).hom ≫
      DerivedCategory.Q.map
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) := by
  let F := TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤
  let g := globalHypercohomologyInjectivePlusMap X f
  have hi := F.rightDerivedFunctorPlusInjectiveModelIso_map_naturality g
  change
    DerivedCategory.Plus.ι.map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (DerivedCategory.Plus.Qh.map
              ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus.map
                ((HomotopyCategory.Plus.quotient
                  (InjectiveObject (AnalyticAdditiveSheaf X))).map
                    (globalHypercohomologyInjectivePlusMap X f))))) ≫
      ((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint X)) ⊤).rightDerivedFunctorPlusInjectiveModelIso
          (globalHypercohomologyInjectivePlus X L)).hom =
    ((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) ⊤).rightDerivedFunctorPlusInjectiveModelIso
        (globalHypercohomologyInjectivePlus X K)).hom ≫
      DerivedCategory.Q.map
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) at hi
  have hc := congrArg
    (fun q => (TopCat.Sheaf.derivedGlobalSections
      (TopCat.of (ComplexPoint X))).map q)
    (globalHypercohomologyCoefficientInjectiveIso_naturality X f)
  simp only [Functor.map_comp] at hc
  dsimp only [derivedGlobalSectionsInjectiveModelIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp, Category.assoc]
  exact congrArg
    (fun q => DerivedCategory.Plus.ι.map
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).map
          (globalHypercohomologyCoefficientInjectiveIso X K).hom) ≫ q) hi

variable (K)

/-- Homology of actual derived global sections, computed on the fixed
injective replacement. -/
def derivedGlobalSectionsAddEquivInjectiveHomology (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          (TopCat.Sheaf.supportCoefficientPlus
            (TopCat.of (ComplexPoint X)) K 0))) ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
          (globalHypercohomologyInjectiveComplex X K)).homology n :=
  ((DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
      (derivedGlobalSectionsInjectiveModelIso X K) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
          (globalHypercohomologyInjectiveComplex X K))).addCommGroupIsoToAddEquiv

variable {K}

set_option maxHeartbeats 800000 in
/-- The actual-derived-sections computation on the fixed injective model is
natural for coefficient-complex morphisms. -/
theorem derivedGlobalSectionsAddEquivInjectiveHomology_naturality
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) (n : ℤ)
    (a : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          (TopCat.Sheaf.supportCoefficientPlus
            (TopCat.of (ComplexPoint X)) K 0))) :
    derivedGlobalSectionsAddEquivInjectiveHomology X L n
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
          ((TopCat.Sheaf.derivedGlobalSections
            (TopCat.of (ComplexPoint X))).map
              (nonnegativeCoefficientPlusMap X f)) a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) n
        (derivedGlobalSectionsAddEquivInjectiveHomology X K n a) := by
  let H := DerivedCategory.homologyFunctor AddCommGrpCat n
  let Γg := ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
      (globalHypercohomologyInjectiveMapMap X f)
  have hm := congrArg
    (fun q => H.map q ≫
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app
        (TopCat.Sheaf.globalSectionsComplexInt
          (TopCat.of (ComplexPoint X))
            (globalHypercohomologyInjectiveComplex X L))).hom)
    (derivedGlobalSectionsInjectiveModelIso_naturality X f)
  simp only [Functor.map_comp, Category.assoc] at hm
  have hf := (DerivedCategory.homologyFunctorFactors
    AddCommGrpCat n).hom.naturality Γg
  have hm' := hm.trans (congrArg
    (fun q => H.map (derivedGlobalSectionsInjectiveModelIso X K).hom ≫ q) hf)
  exact ConcreteCategory.congr_hom hm' a

variable (K)

/-- Public hypercohomology, computed on the same fixed injective replacement. -/
def hypercohomologyAddEquivInjectiveHomology (n : ℤ) :
    Hypercohomology X K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
          (globalHypercohomologyInjectiveComplex X K)).homology n := by
  let e : Hypercohomology X K n ≃+
      Hypercohomology X
        (globalHypercohomologyInjectiveComplex X K) n :=
    { toEquiv := Localization.SmallShiftedHom.postcompEquiv
        (globalHypercohomologyInjectiveMap X K)
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
      map_add' a b := (hypercohomologyMap X
        (globalHypercohomologyInjectiveMap X K) n).map_add a b }
  exact e.trans (hypercohomologyAddEquivGlobalSectionsKInjective X
    (globalHypercohomologyInjectiveComplex X K) n)

set_option maxHeartbeats 800000 in
/-- The public-hypercohomology computation is natural for coefficient
morphisms, using their strict lifts between the fixed injective models. -/
theorem hypercohomologyAddEquivInjectiveHomology_naturality
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) (n : ℤ)
    (a : Hypercohomology X K n) :
    hypercohomologyAddEquivInjectiveHomology X L n
        (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) n
        (hypercohomologyAddEquivInjectiveHomology X K n a) := by
  let iK := globalHypercohomologyInjectiveMap X K
  let iL := globalHypercohomologyInjectiveMap X L
  let g := globalHypercohomologyInjectiveMapMap X f
  change hypercohomologyAddEquivGlobalSectionsKInjective X _ n
      (hypercohomologyMap X iL n (hypercohomologyMap X f n a)) = _
  rw [← hypercohomologyMap_comp_apply,
    ← globalHypercohomologyInjectiveMap_comp_map,
    hypercohomologyMap_comp_apply]
  exact hypercohomologyAddEquivGlobalSectionsKInjective_naturality
    X _ _ g n (hypercohomologyMap X iK n a)

/-- The canonical additive comparison from actual `D⁺` derived global
sections to the public Ext-valued hypercohomology API. -/
def derivedGlobalSectionsAddEquivHypercohomology (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          (TopCat.Sheaf.supportCoefficientPlus
            (TopCat.of (ComplexPoint X)) K 0))) ≃+
      Hypercohomology X K n :=
  (derivedGlobalSectionsAddEquivInjectiveHomology X K n).trans
    (hypercohomologyAddEquivInjectiveHomology X K n).symm

variable {K}

set_option maxHeartbeats 800000 in
/-- The canonical comparison from actual derived global sections to public
hypercohomology intertwines the maps induced by every morphism of
nonnegative coefficient complexes. -/
theorem derivedGlobalSectionsAddEquivHypercohomology_naturality
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [L.IsStrictlyGE 0] (f : K ⟶ L) (n : ℤ)
    (a : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          (TopCat.Sheaf.supportCoefficientPlus
            (TopCat.of (ComplexPoint X)) K 0))) :
    derivedGlobalSectionsAddEquivHypercohomology X L n
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
          ((TopCat.Sheaf.derivedGlobalSections
            (TopCat.of (ComplexPoint X))).map
              (nonnegativeCoefficientPlusMap X f)) a) =
      hypercohomologyMap X f n
        (derivedGlobalSectionsAddEquivHypercohomology X K n a) := by
  apply (hypercohomologyAddEquivInjectiveHomology X L n).injective
  dsimp only [derivedGlobalSectionsAddEquivHypercohomology,
    AddEquiv.trans_apply]
  rw [AddEquiv.apply_symm_apply]
  rw [derivedGlobalSectionsAddEquivInjectiveHomology_naturality,
    hypercohomologyAddEquivInjectiveHomology_naturality,
    AddEquiv.apply_symm_apply]

end AlgebraicGeometry.ComplexPoint
