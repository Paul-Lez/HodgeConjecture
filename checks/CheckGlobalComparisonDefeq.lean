import Other.AlgebraicGeometry.HypercohomologyPushforwardHomeomorphism
import Other.AlgebraicGeometry.PlainHypercohomologyGlobalSectionsNaturality
import Other.AlgebraicGeometry.ComplexBettiGlobalSectionsComparison

open CategoryTheory Limits TopologicalSpace Topology
namespace AlgebraicGeometry.ComplexPoint
noncomputable section
variable (X : Over (Spec (.of ℂ)))
local instance : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _
lemma test_bridge
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
example (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsKInjective]
    (n : ℤ) (a : Hypercohomology X K n) :
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
  rw [test_bridge]
  rw [AddEquiv.symm_apply_apply]
  simp only [Localization.SmallShiftedHom.precompEquiv_apply,
    Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk₀]
  simp [Iso.homCongr, ShiftedHom.mk₀_comp]
example [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) (a : ComplexSingularCochainHypercohomology X n) :
    complexSingularCochainHypercohomologyEquivGlobalSections X n a =
      hypercohomologyEquivGlobalSections X
        (singularCochainSheafComplexInt X ℂ) 0
        (complexSingularCochainSheafComplexInt_isFlasque X) n a := by
  letI : CochainComplex.IsStrictlyGE
      (singularCochainSheafComplexInt X ℂ) 0 := by
    dsimp [singularCochainSheafComplexInt]
    infer_instance
  rfl
end
end AlgebraicGeometry.ComplexPoint
