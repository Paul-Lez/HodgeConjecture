import Other.AlgebraicGeometry.FilteredCycleComponentSupport
import Other.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusInjectiveModel
import Other.AlgebraicGeometry.BettiCohomologyWithSupportComparison

@[expose] noncomputable section
open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {A S I : CochainComplex C ℤ} (b : ℤ)
  [A.IsStrictlyGE b] [S.IsStrictlyGE b] [I.IsStrictlyGE b]
  (a : A ⟶ S) [Mono a] [QuasiIso a] (r : A ⟶ I)

noncomputable def testLiftToInjectiveAt
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
lemma testCompLiftToInjectiveAt
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    a ≫ testLiftToInjectiveAt b a r hI = r := by
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

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ)))

local instance : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _
local instance : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

variable (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (N : ℤ)
  [K.IsStrictlyGE N]

section MonoReplacement

variable [K.IsStrictlyGE 0]

def testMonoInjComplex : CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  Classical.choose
    (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
      K (-1) 0)

def testMonoInjMap : K ⟶ testMonoInjComplex X K :=
  Classical.choose (Classical.choose_spec
    (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
      K (-1) 0))

instance : Mono (testMonoInjMap X K) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
      K (-1) 0)))

instance : QuasiIso (testMonoInjMap X K) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
        K (-1) 0))))

instance (q : ℤ) : Injective ((testMonoInjComplex X K).X q) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
        K (-1) 0))))) q

instance : (testMonoInjComplex X K).IsStrictlyGE (-1) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
        K (-1) 0)))))

end MonoReplacement

def testInjComplex : CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  Classical.choose
    (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N)

def testInjMap : K ⟶ testInjComplex X K N :=
  Classical.choose (Classical.choose_spec
    (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N))

instance : QuasiIso (testInjMap X K N) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N)))

instance (q : ℤ) : Injective ((testInjComplex X K N).X q) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N)))) q

instance : (testInjComplex X K N).IsStrictlyGE N :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N))))

instance : (testInjComplex X K N).IsKInjective :=
  CochainComplex.isKInjective_of_injective (testInjComplex X K N) N

def testInjPlus : CochainComplex.Plus
    (InjectiveObject (AnalyticAdditiveSheaf X)) := by
  let I := testInjComplex X K N
  let J := HomologicalComplex.liftObjectProperty
    (Injective : AnalyticAdditiveSheaf X → Prop) I (fun _ => inferInstance)
  have hJ : CochainComplex.IsStrictlyGE J N := by
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      J (InjectiveObject.ι (AnalyticAdditiveSheaf X))]
    change CochainComplex.IsStrictlyGE I N
    infer_instance
  exact ⟨J, N, hJ⟩

def testDerivedIso :
    TopCat.Sheaf.supportCoefficientPlus
        (TopCat.of (ComplexPoint X)) K N ≅
      DerivedCategory.Plus.Qh.obj
        ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient _).obj (testInjPlus X K N))) :=
  DerivedCategory.Plus.ι.preimageIso
    (asIso (DerivedCategory.Q.map (testInjMap X K N)) ≪≫
      (DerivedCategory.quotientCompQhIso (AnalyticAdditiveSheaf X)).symm.app _)

def testGlobalIso :
    DerivedCategory.Plus.ι.obj
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).obj
            (TopCat.Sheaf.supportCoefficientPlus
              (TopCat.of (ComplexPoint X)) K N)) ≅
      DerivedCategory.Q.obj
        (TopCat.Sheaf.globalSectionsComplexInt
          (TopCat.of (ComplexPoint X)) (testInjComplex X K N)) :=
  DerivedCategory.Plus.ι.mapIso
    ((TopCat.Sheaf.derivedGlobalSections
      (TopCat.of (ComplexPoint X))).mapIso (testDerivedIso X K N)) ≪≫
    Functor.rightDerivedFunctorPlusInjectiveModelIso
      (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤)
      (testInjPlus X K N)

def testDerivedGlobalAddEquiv (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          (TopCat.Sheaf.supportCoefficientPlus
            (TopCat.of (ComplexPoint X)) K N))) ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) (testInjComplex X K N)).homology n :=
  ((DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
      (testGlobalIso X K N) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app _).addCommGroupIsoToAddEquiv

def testHyperAddEquiv (n : ℤ) :
    Hypercohomology X K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) (testInjComplex X K N)).homology n := by
  let e : Hypercohomology X K n ≃+
      Hypercohomology X (testInjComplex X K N) n :=
    { toEquiv := Localization.SmallShiftedHom.postcompEquiv
        (testInjMap X K N)
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
      map_add' a b := (hypercohomologyMap X (testInjMap X K N) n).map_add a b }
  exact e.trans (hypercohomologyAddEquivGlobalSectionsKInjective X
    (testInjComplex X K N) n)

def testGlobalHyperAddEquiv (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          (TopCat.Sheaf.supportCoefficientPlus
            (TopCat.of (ComplexPoint X)) K N))) ≃+
      Hypercohomology X K n :=
  (testDerivedGlobalAddEquiv X K N n).trans
    (testHyperAddEquiv X K N n).symm

end AlgebraicGeometry.ComplexPoint
