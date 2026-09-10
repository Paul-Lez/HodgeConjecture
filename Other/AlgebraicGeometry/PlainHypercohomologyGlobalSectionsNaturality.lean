/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HypercohomologyFlasqueNaturality
public import Other.Algebra.Homology.HomComplexPostcompNaturality

/-!
# Naturality of the original hypercohomology/global-sections comparison

The repository's original comparison is an unbundled equivalence assembled directly in the
localized-Hom model.  This file proves that exact comparison natural in maps of bounded-below
termwise-flasque analytic sheaf complexes.
-/

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance plainHypercohomologyNaturalityHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

lemma constantIntegerSheafComplexIntIsoSingle_inv_analyticQuasiIso :
    HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ)
      (constantIntegerSheafComplexIntIsoSingle X).inv := by
  rw [HomologicalComplex.mem_quasiIso_iff]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma cohomologyClass_toSmallShiftedHom_postcompClass
    {K L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (f : L ⟶ M) (n : ℤ)
    (x : CochainComplex.HomComplex.CohomologyClass K L n) :
    (CochainComplex.HomComplex.postcompClass K f n x).toSmallShiftedHom =
      x.toSmallShiftedHom.comp
        (Localization.SmallShiftedHom.mk₀
          (analyticQuasiIsomorphisms X) 0 rfl f)
        (zero_add n) := by
  obtain ⟨z, rfl⟩ := x.mk_surjective
  apply (Localization.SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  simp only [CochainComplex.HomComplex.postcompClass_mk,
    CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk,
    Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk₀,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp]
  simp only [CategoryTheory.ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality,
    CategoryTheory.ShiftedHom.comp_mk₀]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma precompEquiv_hypercohomologyMap
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (f : K ⟶ L) (n : ℤ) (a : Hypercohomology X K n) :
    Localization.SmallShiftedHom.precompEquiv
        (constantIntegerSheafComplexIntIsoSingle X).inv
        (constantIntegerSheafComplexIntIsoSingle_inv_analyticQuasiIso X)
        (hypercohomologyMap X f n a) =
      (Localization.SmallShiftedHom.precompEquiv
          (constantIntegerSheafComplexIntIsoSingle X).inv
          (constantIntegerSheafComplexIntIsoSingle_inv_analyticQuasiIso X) a).comp
        (Localization.SmallShiftedHom.mk₀
          (analyticQuasiIsomorphisms X) 0 rfl f)
        (zero_add n) := by
  unfold hypercohomologyMap
  change
    (Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms X) 0 rfl
        (constantIntegerSheafComplexIntIsoSingle X).inv).comp
      (a.comp
        (Localization.SmallShiftedHom.mk₀
          (analyticQuasiIsomorphisms X) 0 rfl f) (zero_add n))
      (add_zero n) =
    ((Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms X) 0 rfl
        (constantIntegerSheafComplexIntIsoSingle X).inv).comp a
      (add_zero n)).comp
        (Localization.SmallShiftedHom.mk₀
          (analyticQuasiIsomorphisms X) 0 rfl f) (zero_add n)
  simpa only using
    (Localization.SmallShiftedHom.comp_assoc
      (analyticQuasiIsomorphisms X)
      (Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms X) 0 rfl
        (constantIntegerSheafComplexIntIsoSingle X).inv)
      a
      (Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms X) 0 rfl f)
      (add_zero n) (zero_add n) (by omega)).symm

/-- The old localization-model comparison, without a further injective replacement. -/
def plainHypercohomologyGlobalSectionsKInjective
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective]
    (n : ℤ) : Hypercohomology X K n →
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) K).homology n := by
  let A' := TopCat.Sheaf.integerConstantSingleComplex
    (TopCat.of (ComplexPoint X))
  let e := constantIntegerSheafComplexIntIsoSingle X
  have he : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) e.inv := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  exact fun a ↦
    (HomologicalComplex.homologyMapIso
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
        (TopCat.of (ComplexPoint X)) K) n).hom.hom
      ((CochainComplex.HomComplex.homologyAddEquiv A' K n).symm
        (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.symm
          (Localization.SmallShiftedHom.precompEquiv e.inv he a)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma plainHypercohomologyGlobalSectionsKInjective_naturality
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) (n : ℤ)
    (a : Hypercohomology X K n) :
    plainHypercohomologyGlobalSectionsKInjective X L n
        (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
        (plainHypercohomologyGlobalSectionsKInjective X K n a) := by
  let Y := TopCat.of (ComplexPoint X)
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let e := constantIntegerSheafComplexIntIsoSingle X
  have he : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) e.inv := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let x := CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.symm
    (Localization.SmallShiftedHom.precompEquiv e.inv he a)
  have hx_toSmallShiftedHom :
      x.toSmallShiftedHom =
        Localization.SmallShiftedHom.precompEquiv e.inv he a := by
    change CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective x = _
    exact Equiv.apply_symm_apply _ _
  have hx :
      CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.symm
          (Localization.SmallShiftedHom.precompEquiv e.inv he
            (hypercohomologyMap X f n a)) =
        CochainComplex.HomComplex.postcompClass A' f n x := by
    apply CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.injective
    rw [Equiv.apply_symm_apply]
    change Localization.SmallShiftedHom.precompEquiv e.inv he
        (hypercohomologyMap X f n a) =
      (CochainComplex.HomComplex.postcompClass A' f n x).toSmallShiftedHom
    rw [cohomologyClass_toSmallShiftedHom_postcompClass X]
    rw [hx_toSmallShiftedHom]
    exact precompEquiv_hypercohomologyMap X f n a
  let y := (CochainComplex.HomComplex.homologyAddEquiv A' K n).symm x
  have hy :
      (CochainComplex.HomComplex.homologyAddEquiv A' L n).symm
          (CochainComplex.HomComplex.postcompClass A' f n x) =
        HomologicalComplex.homologyMap
          (CochainComplex.HomComplex.postcompMap A' f) n y := by
    apply (CochainComplex.HomComplex.homologyAddEquiv A' L n).injective
    rw [AddEquiv.apply_symm_apply,
      CochainComplex.HomComplex.homologyAddEquiv_postcompMap]
    exact congrArg (CochainComplex.HomComplex.postcompClass A' f n)
      (AddEquiv.apply_symm_apply _ x).symm
  have hΓ := congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections_naturality Y f)
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hΓ
  have hΓy := ConcreteCategory.congr_hom hΓ y
  dsimp only [plainHypercohomologyGlobalSectionsKInjective]
  rw [hx, hy]
  exact hΓy

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma plainHypercohomologyEquivGlobalSectionsOfResolution_map
    (K I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : K ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map i)]
    (n : ℤ) (a : Hypercohomology X K n) :
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map i) n
      (hypercohomologyEquivGlobalSectionsOfResolution X K I i n a) =
        plainHypercohomologyGlobalSectionsKInjective X I n
          (hypercohomologyMap X i n a) := by
  let b := HomologicalComplex.homologyMap
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map i) n
  dsimp only [hypercohomologyEquivGlobalSectionsOfResolution,
    plainHypercohomologyGlobalSectionsKInjective, Equiv.trans_apply]
  change b ((inv b) _) = _
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma plainHypercohomologyEquivGlobalSectionsOfResolution_naturality_to_kInjective
    (K I L : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective] [L.IsKInjective]
    (i : K ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map i)]
    (f : K ⟶ L) (n : ℤ) (a : Hypercohomology X K n) :
    plainHypercohomologyGlobalSectionsKInjective X L n
        (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
        (hypercohomologyEquivGlobalSectionsOfResolution X K I i n a) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  obtain ⟨g, ⟨h⟩⟩ := CochainComplex.exists_homotopyLift_of_quasiIso_to_isKInjective i f
  have he : DerivedCategory.Q.map i ≫ DerivedCategory.Q.map g =
      DerivedCategory.Q.map f := by
    rw [← Functor.map_comp]
    exact DerivedCategory.Qh.congr_map
      (HomotopyCategory.eq_of_homotopy _ _ h)
  have ha : hypercohomologyMap X f n a =
      hypercohomologyMap X g n (hypercohomologyMap X i n a) := by
    apply (hypercohomologyAddEquivDerived X L n).injective
    simp only [hypercohomologyAddEquivDerived_naturality, Category.assoc,
      ← Functor.map_comp]
    rw [show DerivedCategory.Q.map (i ≫ g) = DerivedCategory.Q.map f from
      (DerivedCategory.Q.map_comp i g).trans he]
  rw [ha, plainHypercohomologyGlobalSectionsKInjective_naturality,
    ← plainHypercohomologyEquivGlobalSectionsOfResolution_map]
  have hh := (Γ.mapHomotopy h).homologyMap_eq n
  rw [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh
    (hypercohomologyEquivGlobalSectionsOfResolution X K I i n a)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma plainHypercohomologyEquivGlobalSections_naturality_to_kInjective
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [L.IsKInjective]
    (N : ℤ) [K.IsStrictlyGE N] (hKflasque : ∀ q, (K.X q).IsFlasque)
    (f : K ⟶ L) (n : ℤ) (a : Hypercohomology X K n) :
    plainHypercohomologyGlobalSectionsKInjective X L n
        (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
        (hypercohomologyEquivGlobalSections X K N hKflasque n a) := by
  let Y := TopCat.of (ComplexPoint X)
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N
  let I := Classical.choose hres
  let hresI := Classical.choose_spec hres
  let i := Classical.choose hresI
  let hresi := Classical.choose_spec hresI
  let hi : QuasiIso i := Classical.choose hresi
  let hresiHi := Classical.choose_spec hresi
  let hI : ∀ q : ℤ, Injective (I.X q) := Classical.choose hresiHi
  let hIge : I.IsStrictlyGE N := Classical.choose_spec hresiHi
  let : QuasiIso i := hi
  let : ∀ q : ℤ, Injective (I.X q) := hI
  let : I.IsStrictlyGE N := hIge
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I N
  have hIflasque : ∀ q, (I.X q).IsFlasque := by intro q; infer_instance
  let : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i N N hKflasque hIflasque
  exact
    plainHypercohomologyEquivGlobalSectionsOfResolution_naturality_to_kInjective
      X K I L i f n a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma plainHypercohomologyEquivGlobalSections_naturality
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (N : ℤ) [K.IsStrictlyGE N] [L.IsStrictlyGE N]
    (hKflasque : ∀ q, (K.X q).IsFlasque)
    (hLflasque : ∀ q, (L.X q).IsFlasque)
    (f : K ⟶ L) (n : ℤ) (a : Hypercohomology X K n) :
    hypercohomologyEquivGlobalSections X L N hLflasque n
        (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
        (hypercohomologyEquivGlobalSections X K N hKflasque n a) := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L N
  let I := Classical.choose hres
  let hresI := Classical.choose_spec hres
  let i := Classical.choose hresI
  let hresi := Classical.choose_spec hresI
  let hi : QuasiIso i := Classical.choose hresi
  let hresiHi := Classical.choose_spec hresi
  let hI : ∀ q : ℤ, Injective (I.X q) := Classical.choose hresiHi
  let hIge : I.IsStrictlyGE N := Classical.choose_spec hresiHi
  letI : QuasiIso i := hi
  letI : ∀ q : ℤ, Injective (I.X q) := hI
  letI : I.IsStrictlyGE N := hIge
  letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I N
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso ((Γ.mapHomologicalComplex (.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i N N hLflasque hIflasque
  let b := HomologicalComplex.homologyMap
    ((Γ.mapHomologicalComplex (.up ℤ)).map i) n
  apply ((asIso b).addCommGroupIsoToAddEquiv).injective
  change b (hypercohomologyEquivGlobalSectionsOfResolution X L I i n
      (hypercohomologyMap X f n a)) =
    b (HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex (.up ℤ)).map f) n
      (hypercohomologyEquivGlobalSections X K N hKflasque n a))
  rw [plainHypercohomologyEquivGlobalSectionsOfResolution_map X L I i]
  change plainHypercohomologyGlobalSectionsKInjective X I n
      (hypercohomologyMap X i n (hypercohomologyMap X f n a)) = _
  rw [← hypercohomologyMap_comp_apply]
  rw [plainHypercohomologyEquivGlobalSections_naturality_to_kInjective
    X K I N hKflasque (f ≫ i)]
  have hcomp :
      HomologicalComplex.homologyMap
          ((Γ.mapHomologicalComplex (.up ℤ)).map (f ≫ i)) n =
        HomologicalComplex.homologyMap
            ((Γ.mapHomologicalComplex (.up ℤ)).map f) n ≫ b := by
    rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]
  exact ConcreteCategory.congr_hom hcomp
    (hypercohomologyEquivGlobalSections X K N hKflasque n a)

end AlgebraicGeometry.ComplexPoint
