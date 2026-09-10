/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HypercohomologyPushforwardHomeomorphism
public import Other.AlgebraicGeometry.PlainHypercohomologyGlobalSectionsNaturality

/-!
# Coherence of the two hypercohomology/global-section comparisons

The repository contains an older plain equivalence and a newer additive
version of the comparison between hypercohomology of a bounded-below
termwise-flasque complex and cohomology of global sections. This file proves
that their forward maps agree. It also gives the corresponding plain
normalization of direct image along a homeomorphism.
-/

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory Limits TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance hypercohomologyGlobalSectionsCoherenceHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

private lemma localizedEquiv_equivOfIsKInjective
    (A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsKInjective] (n : ℤ)
    (x : CochainComplex.HomComplex.CohomologyClass A K n) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective x) =
      (kInjectiveDerivedHomAddEquivCohomologyClass A K n).symm x := by
  obtain ⟨z, rfl⟩ := x.mk_surjective
  change (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (CochainComplex.HomComplex.CohomologyClass.mk z).toSmallShiftedHom = _
  rw [CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk,
    kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a K-injective complex, the additive and plain global-section
comparisons have the same underlying function. -/
theorem hypercohomologyAddEquivGlobalSectionsKInjective_eq_plain
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsKInjective] (n : ℤ) (a : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X K n a =
      plainHypercohomologyGlobalSectionsKInjective X K n a := by
  dsimp [hypercohomologyAddEquivGlobalSectionsKInjective,
    hypercohomologyAddEquivDerived, isoHomCongrAddEquiv,
    derivedHomAddEquivGlobalSectionsKInjective,
    plainHypercohomologyGlobalSectionsKInjective, AddEquiv.trans_apply]
  change (HomologicalComplex.homologyMapIso
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
        (TopCat.of (ComplexPoint X)) K) n).addCommGroupIsoToAddEquiv _ =
    (HomologicalComplex.homologyMapIso
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
        (TopCat.of (ComplexPoint X)) K) n).addCommGroupIsoToAddEquiv _
  congr 1
  congr 1
  apply CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.injective
  rw [Equiv.apply_symm_apply]
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [localizedEquiv_equivOfIsKInjective]
  rw [AddEquiv.symm_apply_apply]
  simp only [Localization.SmallShiftedHom.precompEquiv_apply,
    Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk₀]
  simp [Iso.homCongr, ShiftedHom.mk₀_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The additive and plain global-section comparisons agree for every
bounded-below termwise-flasque complex. -/
theorem hypercohomologyAddEquivGlobalSections_eq_plain
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsStrictlyGE 0]
    (hK : ∀ q, (K.X q).IsFlasque) (n : ℤ)
    (a : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSections X K 0 hK n a =
      hypercohomologyEquivGlobalSections X K 0 hK n a := by
  let I := globalHypercohomologyInjectiveComplex X K
  let i := globalHypercohomologyInjectiveMap X K
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  let Γi := (Γ.mapHomologicalComplex (.up ℤ)).map i
  have hI : ∀ q, (I.X q).IsFlasque := fun _ => inferInstance
  letI : QuasiIso Γi :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 (-1) hK hI
  apply AddCommGrpCat.injective_of_mono (HomologicalComplex.homologyMap Γi n)
  rw [← hypercohomologyAddEquivGlobalSections_naturality_to_kInjective
      X K I 0 hK i n a,
    ← plainHypercohomologyEquivGlobalSections_naturality_to_kInjective
      X K I 0 hK i n a]
  exact hypercohomologyAddEquivGlobalSectionsKInjective_eq_plain X I n
    (hypercohomologyMap X i n a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In the older plain comparison, the canonical direct-image identification
for a homeomorphism is also the identity on the whole-space global-section
complex. -/
theorem hypercohomologyPushforwardAddEquivOfIso_globalSections_plain
    (H : TopCat.of (ComplexPoint X) ≅ TopCat.of (ComplexPoint X))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsStrictlyGE 0]
    (hK : ∀ q, (K.X q).IsFlasque) (n : ℤ)
    (a : Hypercohomology X
      (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
        (.up ℤ)).obj K) n) :
    hypercohomologyEquivGlobalSections X K 0 hK n
        (hypercohomologyPushforwardAddEquivOfIso X H K n a) =
      hypercohomologyEquivGlobalSections X
        (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
          (.up ℤ)).obj K) 0
        (fun q => TopCat.Sheaf.IsFlasque.pushforward_isFlasque
          (K.X q) H.hom) n a := by
  rw [← hypercohomologyAddEquivGlobalSections_eq_plain X K hK,
    hypercohomologyPushforwardAddEquivOfIso_globalSections]
  exact hypercohomologyAddEquivGlobalSections_eq_plain X _ _ n a

end AlgebraicGeometry.ComplexPoint
