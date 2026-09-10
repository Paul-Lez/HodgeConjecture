import Other.AlgebraicGeometry.AnalyticIteratedTransitionClass
import Other.AlgebraicGeometry.SheafExtHypercohomologyNaturality

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point Localization

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

/-- The single top-form sheaf maps canonically to the full de Rham complex. -/
def check_topHolomorphicFormSingleToDeRhamComplexInt :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) (dim X.left)).obj
        (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)) ⟶
      holomorphicDeRhamComplexInt X :=
  HomologicalComplex.mkHomFromSingle
    (((holomorphicDeRhamComplex X (dim X.left)).extendXIso
      ComplexShape.embeddingUpNat (i := dim X.left) rfl).inv) (by
      intro k hk
      have hk' : k = (dim X.left : ℤ) + 1 := by
        simpa [ComplexShape.up_Rel] using hk.symm
      subst k
      have hz : IsZero
          ((holomorphicDeRhamComplexInt X).X ((dim X.left : ℤ) + 1)) :=
        IsZero.of_iso
          (holomorphicDeRhamSheaf_isZero_of_lt X (dim X.left)
            (Nat.lt_succ_self _))
          (((holomorphicDeRhamComplex X (dim X.left)).extendXIso
            ComplexShape.embeddingUpNat (i := dim X.left + 1)
              (i' := (dim X.left : ℤ) + 1) (by simp)))
      exact hz.eq_of_tgt _ _)

theorem check_analyticClosedSectionToDeRhamComplexInt_top_eq
    (D : AnalyticIteratedCover X (dim X.left))
    (c : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj
      (.op (D.ambient ⟨dim X.left, Nat.lt_succ_self _⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) (dim X.left)).hom.app
      (.op (D.ambient ⟨dim X.left, Nat.lt_succ_self _⟩)) c = 0) :
    analyticClosedSectionToDeRhamComplexInt X D c hc =
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
          (dim X.left : ℤ)).map
          (analyticSectionSheafHom X
            (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)) _ c) ≫
        check_topHolomorphicFormSingleToDeRhamComplexInt X := by
  ext i
  by_cases hi : i = (dim X.left : ℤ)
  · subst i
    simp only [analyticClosedSectionToDeRhamComplexInt,
      check_topHolomorphicFormSingleToDeRhamComplexInt,
      HomologicalComplex.mkHomFromSingle_f, Category.comp_id,
      HomologicalComplex.comp_f]
    dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    rw [HomologicalComplex.single_map_f_self]
    simp
  · have hz := HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) (dim X.left : ℤ)
      (analyticOpenFreeAbelianSheaf X
        (D.ambient ⟨dim X.left, Nat.lt_succ_self _⟩)) i hi
    exact hz.eq_of_src _ _

theorem check_hypercohomologyMap_transport
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L)
    {i j : ℤ} (h : i = j) (a : Hypercohomology X K i) :
    h ▸ hypercohomologyMap X f i a =
      hypercohomologyMap X f j (h ▸ a) := by
  subst j
  rfl

theorem check_hypercohomology_transport_zero
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    {i j : ℤ} (h : i = j) :
    h ▸ (0 : Hypercohomology X K i) = 0 := by
  subst j
  rfl

theorem check_analyticIteratedTopTransitionExtClass_toDeRham
    (D : AnalyticIteratedCover X (dim X.left))
    (c : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj
      (.op (D.ambient ⟨dim X.left, Nat.lt_succ_self _⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) (dim X.left)).hom.app
      (.op (D.ambient ⟨dim X.left, Nat.lt_succ_self _⟩)) c = 0) :
    hypercohomologyMap X (check_topHolomorphicFormSingleToDeRhamComplexInt X)
        (2 * (dim X.left : ℤ))
        ((show (dim X.left : ℤ) + (dim X.left : ℤ) =
            2 * (dim X.left : ℤ) by omega) ▸
          sheafExtHypercohomologyEquiv X
            (holomorphicDeRhamSheaf X (dim X.left) (dim X.left))
            (dim X.left : ℤ) (dim X.left)
            (analyticIteratedTransitionExtClass X D
              (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)) c)) =
      analyticIteratedClosedSectionDeRhamClass X D c hc := by
  let s := analyticSectionSheafHom X
    (holomorphicDeRhamSheaf X (dim X.left) (dim X.left))
    (D.ambient ⟨dim X.left, Nat.lt_succ_self _⟩) c
  let α := sheafExtHypercohomologyEquiv X
    (analyticOpenFreeAbelianSheaf X
      (D.ambient ⟨dim X.left, Nat.lt_succ_self _⟩))
    (dim X.left : ℤ) (dim X.left) (D.boundaryExtClass X)
  have hbase :
      hypercohomologyMap X (check_topHolomorphicFormSingleToDeRhamComplexInt X)
          ((dim X.left : ℤ) + (dim X.left : ℤ))
          (sheafExtHypercohomologyEquiv X
            (holomorphicDeRhamSheaf X (dim X.left) (dim X.left))
            (dim X.left : ℤ) (dim X.left)
            (analyticIteratedTransitionExtClass X D
              (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)) c)) =
        hypercohomologyMap X
          (analyticClosedSectionToDeRhamComplexInt X D c hc)
          ((dim X.left : ℤ) + (dim X.left : ℤ)) α := by
    rw [analyticIteratedTransitionExtClass_eq_boundary_comp]
    rw [sheafExtHypercohomologyEquiv_naturality]
    rw [← hypercohomologyMap_comp_apply]
    rw [check_analyticClosedSectionToDeRhamComplexInt_top_eq]
  let hdeg : (dim X.left : ℤ) + (dim X.left : ℤ) =
      2 * (dim X.left : ℤ) := by omega
  have hcast := congrArg
    (fun z : DeRhamHypercohomology X
        ((dim X.left : ℤ) + (dim X.left : ℤ)) => hdeg ▸ z) hbase
  rw [check_hypercohomologyMap_transport,
    check_hypercohomologyMap_transport] at hcast
  unfold analyticIteratedClosedSectionDeRhamClass
  exact hcast

theorem check_analyticIteratedTopLogarithmicTransitionExtClass_toDeRham
    (D : AnalyticIteratedCover X (dim X.left))
    (u : Fin (dim X.left) →
      (OpenHolomorphicFunctions X (dim X.left)
        (.op (D.ambient ⟨dim X.left, Nat.lt_succ_self _⟩)))ˣ) :
    hypercohomologyMap X (check_topHolomorphicFormSingleToDeRhamComplexInt X)
        (2 * (dim X.left : ℤ))
        ((show (dim X.left : ℤ) + (dim X.left : ℤ) =
            2 * (dim X.left : ℤ) by omega) ▸
          sheafExtHypercohomologyEquiv X
            (holomorphicDeRhamSheaf X (dim X.left) (dim X.left))
            (dim X.left : ℤ) (dim X.left)
            (analyticIteratedLogarithmicTransitionExtClass X D u)) =
      analyticIteratedLogarithmicDeRhamClass X D u := by
  exact check_analyticIteratedTopTransitionExtClass_toDeRham X D
    (analyticIteratedLogarithmicFormSection X D u)
    (analyticIteratedLogarithmicFormSection_differential X D u)

theorem check_analyticIteratedTopLogarithmicTransitionExtClass_ne_zero_of_deRham
    (D : AnalyticIteratedCover X (dim X.left))
    (u : Fin (dim X.left) →
      (OpenHolomorphicFunctions X (dim X.left)
        (.op (D.ambient ⟨dim X.left, Nat.lt_succ_self _⟩)))ˣ)
    (h : analyticIteratedLogarithmicDeRhamClass X D u ≠ 0) :
    analyticIteratedLogarithmicTransitionExtClass X D u ≠ 0 := by
  intro hz
  have heq := check_analyticIteratedTopLogarithmicTransitionExtClass_toDeRham X D u
  rw [hz, sheafExtHypercohomologyEquiv_zero] at heq
  rw [check_hypercohomology_transport_zero] at heq
  have hmapzero :=
    (hypercohomologyMap X (check_topHolomorphicFormSingleToDeRhamComplexInt X)
      (2 * (dim X.left : ℤ))).map_zero
  rw [hmapzero] at heq
  exact h heq.symm

end AlgebraicGeometry.ComplexPoint
