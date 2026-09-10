import Other.AlgebraicGeometry.PlainHypercohomologyGlobalSectionsNaturality
import Other.AlgebraicTopology.SheafPushforwardHomeomorphism
import Other.AlgebraicTopology.ClosedEmbeddingSheafExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

@[expose] noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance checkHyperPushHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

def kInjectiveHypercohomologyAddEquivGlobalSections
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective]
    (n : ℤ) : Hypercohomology X K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) K).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let A := constantIntegerSheafComplexInt X
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let e : A ≅ A' := constantIntegerSheafComplexIntIsoSingle X
  let e₀ := hypercohomologyAddEquivDerived X K n
  let e₂ : ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj K) n ≃+
      ShiftedHom (DerivedCategory.Q.obj A') (DerivedCategory.Q.obj K) n :=
    isoHomCongrAddEquiv (DerivedCategory.Q.mapIso e) (Iso.refl _)
  let e₃ := kInjectiveDerivedHomAddEquivCohomologyClass A' K n
  let e₄ := (CochainComplex.HomComplex.homologyAddEquiv A' K n).symm
  let e₅ := (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K) n)
      |>.addCommGroupIsoToAddEquiv
  exact e₀.trans <| e₂.trans <| e₃.trans <| e₄.trans e₅

def hypercohomologyPushforwardEquivOfIso
    (H : TopCat.of (ComplexPoint X) ≅ TopCat.of (ComplexPoint X))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (N : ℤ) [K.IsStrictlyGE N] (n : ℤ) :
    Hypercohomology X
        (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
          (.up ℤ)).obj K) n ≃
      Hypercohomology X K n := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat H.hom
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N
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
  letI : P.IsEquivalence :=
    TopCat.Sheaf.pushforward_isEquivalence_of_iso AddCommGrpCat H
  let PI := (P.mapHomologicalComplex (.up ℤ)).obj I
  let Pi := (P.mapHomologicalComplex (.up ℤ)).map i
  letI : QuasiIso Pi := by
    exact @TopCat.Sheaf.closedEmbeddingPushforward_map_quasiIso
      _ _ H.hom (TopCat.homeoOfIso H).isClosedEmbedding
      ℤ (.up ℤ) _ _ i hi
  letI : ∀ q : ℤ, Injective (PI.X q) := by
    intro q
    change Injective (P.obj (I.X q))
    infer_instance
  letI : CochainComplex.IsStrictlyGE PI N := by
    dsimp [PI]
    infer_instance
  letI : CochainComplex.IsKInjective PI :=
    CochainComplex.isKInjective_of_injective PI N
  let hqi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (.up ℤ) i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    exact hi
  let hqPi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (.up ℤ) Pi := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let eSource := (Localization.SmallShiftedHom.postcompEquiv
      (X := constantIntegerSheafComplexInt X)
      (Y := K) (Z := I) (a := n) i hqi).trans
    (kInjectiveHypercohomologyAddEquivGlobalSections X I n).toEquiv
  let PK := (P.mapHomologicalComplex (.up ℤ)).obj K
  let eTarget := (Localization.SmallShiftedHom.postcompEquiv
      (X := constantIntegerSheafComplexInt X)
      (Y := PK) (Z := PI) (a := n) Pi hqPi).trans
    (kInjectiveHypercohomologyAddEquivGlobalSections X PI n).toEquiv
  exact eTarget.trans eSource.symm

end AlgebraicGeometry.ComplexPoint
