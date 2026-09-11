/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.HypercohomologyGlobalSectionsNaturality
public import HodgeConjecture.Lemmas.AlgebraicGeometry.HypercohomologyGlobalSectionsShift

/-!
# Naturality through actual flasque and injective resolution comparisons

The bounded-below flasque comparison uses a chosen injective resolution. Its
naturality must therefore be proved, rather than inferred from the literal
K-injective case. The arguments below compare actual maps through derived
localization and the genuine homotopies detected by K-injectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CochainComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A map to an actual K-injective complex lifts across a quasi-isomorphism up to
a genuine chain homotopy, by the proved fully faithful derived-category comparison. -/
theorem exists_homotopyLift_of_quasiIso_to_isKInjective
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K I L : CochainComplex C ℤ} [L.IsKInjective]
    (i : K ⟶ I) [QuasiIso i] (f : K ⟶ L) :
    ∃ g : I ⟶ L, Nonempty (Homotopy (i ≫ g) f) := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  obtain ⟨g, hg⟩ := (IsKInjective.Qh_map_bijective (Q.obj I) L).surjective
    (inv (DerivedCategory.Q.map i) ≫ DerivedCategory.Q.map f)
  obtain ⟨g, rfl⟩ := Q.map_surjective g
  change DerivedCategory.Q.map g = inv (DerivedCategory.Q.map i) ≫ DerivedCategory.Q.map f at hg
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq (i ≫ g) f ?_⟩⟩
  apply (IsKInjective.Qh_map_bijective (Q.obj K) L).injective
  change DerivedCategory.Q.map (i ≫ g) = DerivedCategory.Q.map f
  rw [Functor.map_comp, hg, IsIso.hom_inv_id_assoc]

end CochainComplex

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance hypercohomologyFlasqueNaturalitySheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The resolution comparison, followed by its actual global-section map, is precisely
the direct comparison after applying the resolution morphism in hypercohomology. -/
theorem hypercohomologyAddEquivGlobalSectionsOfResolution_map
    (K I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : K ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map i)]
    (n : ℤ) (a : Hypercohomology X K n) :
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map i) n
      (hypercohomologyAddEquivGlobalSectionsOfResolution X K I i n a) =
        hypercohomologyAddEquivGlobalSectionsKInjective X I n
          (hypercohomologyMap X i n a) := by
  let b := HomologicalComplex.homologyMap
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map i) n
  dsimp only [hypercohomologyAddEquivGlobalSectionsOfResolution,
    hypercohomologyAddEquivGlobalSectionsKInjective,
    derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply]
  rw [hypercohomologyAddEquivDerived_naturality]
  simp only [isoHomCongrAddEquiv_apply, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.mapIso_hom]
  change b ((inv b) _) = _
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id]
  rfl

/-- Naturality of the resolution comparison into any actual K-injective target.
No compatibility of chosen resolutions is an input: a homotopy lift is constructed. -/
theorem hypercohomologyAddEquivGlobalSectionsOfResolution_naturality_to_kInjective
    (K I L : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective] [L.IsKInjective]
    (i : K ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map i)]
    (f : K ⟶ L) (n : ℤ) (a : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X L n (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
        (hypercohomologyAddEquivGlobalSectionsOfResolution X K I i n a) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  obtain ⟨g, ⟨h⟩⟩ := CochainComplex.exists_homotopyLift_of_quasiIso_to_isKInjective i f
  have he : DerivedCategory.Q.map i ≫ DerivedCategory.Q.map g = DerivedCategory.Q.map f := by
    rw [← Functor.map_comp]
    exact DerivedCategory.Qh.congr_map (HomotopyCategory.eq_of_homotopy _ _ h)
  have ha : hypercohomologyMap X f n a = hypercohomologyMap X g n (hypercohomologyMap X i n a) := by
    apply (hypercohomologyAddEquivDerived X L n).injective
    simp only [hypercohomologyAddEquivDerived_naturality, Category.assoc,
      ← Functor.map_comp]
    rw [show DerivedCategory.Q.map (i ≫ g) = DerivedCategory.Q.map f from
      (DerivedCategory.Q.map_comp i g).trans he]
  rw [ha, hypercohomologyAddEquivGlobalSectionsKInjective_naturality,
    ← hypercohomologyAddEquivGlobalSectionsOfResolution_map]
  have hh := (Γ.mapHomotopy h).homologyMap_eq n
  rw [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh
    (hypercohomologyAddEquivGlobalSectionsOfResolution X K I i n a)

/-- The actual bounded-below flasque comparison is natural into K-injective targets,
independently of the injective replacement chosen in its definition. -/
theorem hypercohomologyAddEquivGlobalSections_naturality_to_kInjective
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [L.IsKInjective]
    (N : ℤ) [K.IsStrictlyGE N] (hKflasque : ∀ q, (K.X q).IsFlasque)
    (f : K ⟶ L) (n : ℤ) (a : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X L n (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
        (hypercohomologyAddEquivGlobalSections X K N hKflasque n a) := by
  let Y := TopCat.of (ComplexPoint X)
  -- This ladder mirrors the choices made inside `hypercohomologyAddEquivGlobalSections`
  -- term for term, which is what makes the two sides definitionally equal below. Replacing
  -- it with `choose` makes `I` and `i` opaque and breaks that defeq.
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
  exact hypercohomologyAddEquivGlobalSectionsOfResolution_naturality_to_kInjective
    X K I L i f n a

/-- The flasque comparison preserves actual shifted maps into K-injective targets,
including the exact cone-connecting sign used by support-forgetting. -/
theorem hypercohomologyAddEquivGlobalSections_shifted_naturality_to_kInjective
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [L.IsKInjective]
    (N : ℤ) [K.IsStrictlyGE N] (hKflasque : ∀ q, (K.X q).IsFlasque)
    (t n n' : ℤ) (h : n + t = n') (f : K ⟶ L⟦t⟧)
    (a : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X L n'
      (a.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X) f) (by omega)) =
      (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
        (ShiftedHom.map f
          ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ))) n n' (by omega)
        (hypercohomologyAddEquivGlobalSections X K N hKflasque n a) := by
  have hf : a.comp (Localization.SmallShiftedHom.mk
      (analyticQuasiIsomorphisms X) f) (show t + n = n' by omega) =
      (hypercohomologyMap X f n a).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom (L⟦t⟧) L t from 𝟙 (L⟦t⟧))) (by omega) := by
    apply (hypercohomologyAddEquivDerived X L n').injective
    rw [hypercohomologyAddEquivDerived_rightUnshift _ _ t n n' h,
      hypercohomologyAddEquivDerived_naturality]
    change Localization.SmallShiftedHom.equiv _ DerivedCategory.Q _ = _
    rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk]
    simp [ShiftedHom.map, ShiftedHom.comp, Category.assoc]
    rfl
  rw [hf, hypercohomologyAddEquivGlobalSectionsKInjective_rightUnshift _ _ t n n' h,
    hypercohomologyAddEquivGlobalSections_naturality_to_kInjective X K (L⟦t⟧) N hKflasque,
    TopCat.Sheaf.globalSectionsShiftShortComplex_homologyMap]
  simp only [Functor.shiftMap, ShiftedHom.map, Functor.map_comp, AddCommGrpCat.comp_apply]
  rfl

end AlgebraicGeometry.ComplexPoint
