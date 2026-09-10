import Other.AlgebraicGeometry.RationalComplexBettiCompatibility

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance : (singularCochainSheafComplexInt X ℚ).IsStrictlyGE 0 := by
  dsimp [singularCochainSheafComplexInt]
  infer_instance

example [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) (a : RationalSingularCochainHypercohomology X n) :
    rationalSingularCochainHypercohomologyEquivGlobalSections X n a =
      hypercohomologyEquivGlobalSections X
        (singularCochainSheafComplexInt X ℚ) 0
        (fun q => singularCochainSheafComplexInt_isFlasque X q) n a := by
  rfl

example (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsKInjective] (n : ℤ) (a : Hypercohomology X K n) :
    hypercohomologyEquivGlobalSectionsOfResolution X K K (𝟙 K) n a =
      hypercohomologyAddEquivGlobalSectionsKInjective X K n a := by
  dsimp only [hypercohomologyEquivGlobalSectionsOfResolution,
    hypercohomologyAddEquivGlobalSectionsKInjective,
    derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply,
    Equiv.trans_apply]
  simp only [Functor.map_id, HomologicalComplex.homologyMap_id]
  simp [isoHomCongrAddEquiv]
  have hinv (x : ((TopCat.Sheaf.globalSectionsComplexInt
      (TopCat.of (ComplexPoint X)) K).homology n)) :
      ((asIso (𝟙 ((TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) K).homology n))).symm
          |>.addCommGroupIsoToAddEquiv) x = x := by
    change (inv (𝟙 _)).hom x = x
    rw [IsIso.inv_id]
    rfl
  rw [hinv]
  apply (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
      (TopCat.of (ComplexPoint X)) K) n).addCommGroupIsoToAddEquiv.injective
  apply (CochainComplex.HomComplex.homologyAddEquiv
    (TopCat.Sheaf.integerConstantSingleComplex
      (TopCat.of (ComplexPoint X))) K n).symm.injective

end AlgebraicGeometry.ComplexPoint
