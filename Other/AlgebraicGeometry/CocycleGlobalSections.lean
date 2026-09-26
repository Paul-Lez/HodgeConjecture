/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.HypercohomologyNaturality
public import Other.AlgebraicGeometry.HypercohomologyFlasqueNaturality
public import Other.AlgebraicTopology.ConstantSheafGlobalSection

/-!
# Actual cocycle representatives under the global-sections comparison

The prescribed Hom-complex/global-sections isomorphism evaluates a cocycle on the
section defining its constant-integer input. For a K-injective target, the existing
derived comparison gives the cohomology class of that actual section cocycle.
All comparisons and constant-sheaf maps retain their original normalizations.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
namespace TopCat.Sheaf
variable (Y : TopCat.{0}) (F : Sheaf AddCommGrpCat Y)
lemma integerConstantHomEquivGlobalSections_id :
    integerConstantHomAddEquivGlobalSections (integerConstantSheaf Y) (𝟙 _) =
      integerOne (Y := Y) := by
  rfl
lemma integerConstantHomEquivGlobalSections_constHomOfSection
    (t : F.obj.obj (op ⊤)) :
    integerConstantHomAddEquivGlobalSections F (constHomOfSection F t) = t := by
  have h := integerConstantHomAddEquivGlobalSections_naturality
    (constHomOfSection F t) (𝟙 (integerConstantSheaf Y))
  rw [Category.id_comp, integerConstantHomEquivGlobalSections_id] at h
  refine h.trans ?_
  have hs := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app (op ⊤)) (toSheafify_constHomOfSection F t)) (1 : ℤ)
  change (constHomOfSection F t).hom.app (op ⊤) (integerOne (Y := Y)) = _ at hs
  have ht : F.obj.map (homOfLE (le_top : (⊤ : Opens Y) ≤ ⊤)).op t = t := by
    rw [show homOfLE (le_top : (⊤ : Opens Y) ≤ ⊤) = 𝟙 ⊤ from Subsingleton.elim _ _]
    simp
  exact hs.trans ((constPresheafHomOfSection_app_one F t (op ⊤)).trans ht)

/-- The prescribed Hom-complex/global-sections isomorphism evaluates a cochain
on the actual section defining its constant-sheaf input. -/
lemma homComplexSingleIntegerIsoGlobalSections_precomp_constHom
    (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ) (n : ℤ)
    (α : Cochain ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat Y) 0).obj F) K n)
    (t : F.obj.obj (op ⊤)) :
    (homComplexSingleIntegerIsoGlobalSections Y K).hom.f n
      ((Cochain.ofHom ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat Y) 0).map
        (constHomOfSection F t))).comp α (zero_add n)) =
    ((Cochain.fromSingleEquiv (zero_add n) α).hom.app (op ⊤)) t := by
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective α n (zero_add n)
  change integerConstantHomAddEquivGlobalSections (K.X n)
    (Cochain.fromSingleEquiv (zero_add n)
      ((Cochain.ofHom ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat Y) 0).map
        (constHomOfSection F t))).comp (Cochain.fromSingleMk a (zero_add n)) (zero_add n))) = _
  rw [← Cochain.fromSingleMk_precomp, Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]
  exact (integerConstantHomAddEquivGlobalSections_naturality a (constHomOfSection F t)).trans
    (congrArg (a.hom.app (op ⊤)) (integerConstantHomEquivGlobalSections_constHomOfSection Y F t))

end TopCat.Sheaf

namespace CochainComplex.HomComplex
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  (A K : CochainComplex C ℤ) (n : ℤ)
omit [HasZeroObject C] in
lemma homologyAddEquiv_symm_mk (z : Cocycle A K n) :
    (homologyAddEquiv A K n).symm (CohomologyClass.mk z) =
    (HomComplex A K).homologyπ n ((leftHomologyData A K n).cyclesIso.inv z) :=
  ConcreteCategory.congr_hom (ShortComplex.LeftHomologyData.π_comp_homologyIso_inv _
    (leftHomologyData A K n)) z
end CochainComplex.HomComplex

namespace TopCat.Sheaf
variable (Y : TopCat.{0}) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ) (n : ℤ)
/-- A cocycle out of the constant integer sheaf evaluated in the actual global
section complex through the prescribed Hom-complex comparison. -/
def integerCocycleGlobalSection (z : Cocycle (integerConstantSingleComplex Y) K n) :
    (globalSectionsComplexInt Y K).cycles n :=
  HomologicalComplex.cyclesMap (homComplexSingleIntegerIsoGlobalSections Y K).hom n
    ((leftHomologyData (integerConstantSingleComplex Y) K n).cyclesIso.inv z)

lemma iCycles_integerCocycleGlobalSection
    (z : Cocycle (integerConstantSingleComplex Y) K n) :
    (globalSectionsComplexInt Y K).iCycles n (integerCocycleGlobalSection Y K n z) =
    (homComplexSingleIntegerIsoGlobalSections Y K).hom.f n z.1 := by
  have hc := ConcreteCategory.congr_hom
    (ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles
      (leftHomologyData (integerConstantSingleComplex Y) K n)) z
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (homComplexSingleIntegerIsoGlobalSections Y K).hom n)
    ((leftHomologyData (integerConstantSingleComplex Y) K n).cyclesIso.inv z)
  exact hn.trans (congrArg ((homComplexSingleIntegerIsoGlobalSections Y K).hom.f n) hc)

lemma iCycles_integerCocycleGlobalSection_precomp_constHom
    (F : Sheaf AddCommGrpCat Y)
    (z : Cocycle ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat Y) 0).obj F) K n)
    (t : F.obj.obj (op ⊤)) :
    (globalSectionsComplexInt Y K).iCycles n
      (integerCocycleGlobalSection Y K n (z.precomp
        ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat Y) 0).map (constHomOfSection F t)))) =
    ((Cochain.fromSingleEquiv (zero_add n) z.1).hom.app (op ⊤)) t :=
  (iCycles_integerCocycleGlobalSection Y K n _).trans
    (homComplexSingleIntegerIsoGlobalSections_precomp_constHom Y F K n z.1 t)
end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ))
local instance cocycleGlobalSectionsDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _
lemma derivedHomAddEquivGlobalSectionsKInjective_cocycle
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective] (n : ℤ)
    (z : Cocycle (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) K n) :
    TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective (TopCat.of (ComplexPoint X)) K n
      (ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q) =
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) K).homologyπ n
      (TopCat.Sheaf.integerCocycleGlobalSection (TopCat.of (ComplexPoint X)) K n z) := by
  rw [← CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk]
  simp only [TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, homologyAddEquiv_symm_mk]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X)) K).hom n)
    ((leftHomologyData _ K n).cyclesIso.inv z)

/-- The existing flasque comparison agrees with the direct comparison when its
target complex is already K-injective. -/
lemma hypercohomologyAddEquivGlobalSections_eq_kInjective
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective]
    (N : ℤ) [K.IsStrictlyGE N] (hKflasque : ∀ q, (K.X q).IsFlasque) (n : ℤ)
    (a : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSections X K N hKflasque n a =
      hypercohomologyAddEquivGlobalSectionsKInjective X K n a := by
  have h := hypercohomologyAddEquivGlobalSections_naturality_to_kInjective
    X K K N hKflasque (𝟙 K) n a
  have hm : HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map (𝟙 K)) n = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  have hx : hypercohomologyMap X (𝟙 K) n a = a := by
    rw [hypercohomologyMap_id]
    rfl
  exact (ConcreteCategory.congr_hom hm
    (hypercohomologyAddEquivGlobalSections X K N hKflasque n a)).symm.trans
    (h.symm.trans (congrArg (hypercohomologyAddEquivGlobalSectionsKInjective X K n) hx))

/-- A cocycle, with the prescribed constant-complex source identification,
represents its actual section cocycle under the fixed hypercohomology comparison. -/
lemma hypercohomologyAddEquivGlobalSectionsKInjective_mk_cocycle
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective] (n : ℤ)
    (z : Cocycle (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) K n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X K n
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        ((constantIntegerSheafComplexIntIsoSingle X).hom ≫ Cocycle.equivHomShift.symm z)) =
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) K).homologyπ n
      (TopCat.Sheaf.integerCocycleGlobalSection (TopCat.of (ComplexPoint X)) K n z) := by
  change TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective (TopCat.of (ComplexPoint X)) K n
    ((DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv) ≫
      (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          ((constantIntegerSheafComplexIntIsoSingle X).hom ≫ Cocycle.equivHomShift.symm z)) ≫ 𝟙 _) = _
  rw [Localization.SmallShiftedHom.equiv_mk, Category.comp_id]
  have he : DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
      ShiftedHom.map ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
        Cocycle.equivHomShift.symm z) DerivedCategory.Q =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
    simp only [ShiftedHom.map, CategoryTheory.Functor.map_comp, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (congrArg (TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective (TopCat.of (ComplexPoint X)) K n) he).trans
    (derivedHomAddEquivGlobalSectionsKInjective_cocycle X K n z)
end AlgebraicGeometry.ComplexPoint
