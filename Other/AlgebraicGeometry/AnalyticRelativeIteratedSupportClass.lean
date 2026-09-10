/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticClosedOpenDeRhamSection
public import Other.AlgebraicGeometry.FilteredSupportLocalizationBoundary

/-!
# Iterated relative transition classes with closed support

A length-`q` chain of two-open covers inside an ambient open gives a degree-`q`
Yoneda boundary from the free sheaf on that ambient open to the free sheaf on
the deepest overlap.  A closed holomorphic `p`-form there adds cochain degree
`p`.  The resulting class in degree `q+p` on the ambient open is sent by the
actual localization boundary to a supported `F^p` de Rham class in degree
`q+p+1`.

Taking `q+1=p` gives the local degree-`2p` filtered class expected of a
codimension-`p` Thom class.  This construction uses actual derived support;
nonvanishing and comparison with the rational orientation are separate local
residue statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ)))

local instance relativeIteratedSupportSheafAbelian :
    Abelian (AnalyticAdditiveSheaf X) := CategoryTheory.sheafIsAbelian

local instance relativeIteratedSupportHasExt :
    HasExt.{1} (AnalyticAdditiveSheaf X) := analyticHasExt X

local instance relativeIteratedSupportSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

/-- A chain of relative two-open covers inside an arbitrary first ambient
open. -/
structure AnalyticRelativeIteratedCover (q : ℕ) where
  ambient : Fin (q + 1) → Opens (TopCat.of (ComplexPoint X))
  left : Fin q → Opens (TopCat.of (ComplexPoint X))
  right : Fin q → Opens (TopCat.of (ComplexPoint X))
  cover : ∀ i, left i ⊔ right i = ambient i.castSucc
  overlap : ∀ i, left i ⊓ right i = ambient i.succ

/-- The Mayer--Vietoris extension at one step of a relative iterated cover. -/
def AnalyticRelativeIteratedCover.stepExt {q : ℕ}
    (D : AnalyticRelativeIteratedCover X q) (i : Fin q) :
    Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf X (D.ambient i.castSucc))
      (analyticOpenFreeAbelianSheaf X (D.ambient i.succ)) 1 := by
  rw [← D.overlap i]
  exact (analyticRelativeCoverMayerVietorisSquare X (D.left i) (D.right i)
    (D.ambient i.castSucc)
    (by rw [← D.cover i]; exact le_sup_left)
    (by rw [← D.cover i]; exact le_sup_right)
    (D.cover i)).shortComplex_shortExact.extClass
      (C := AnalyticAdditiveSheaf X)

/-- Yoneda composition of the first `k` relative cover boundaries. -/
def AnalyticRelativeIteratedCover.boundaryUpTo {q : ℕ}
    (D : AnalyticRelativeIteratedCover X q) :
    (k : ℕ) → (hk : k ≤ q) →
      Abelian.Ext.{1}
        (analyticOpenFreeAbelianSheaf X (D.ambient 0))
        (analyticOpenFreeAbelianSheaf X
          (D.ambient ⟨k, Nat.lt_succ_of_le hk⟩)) k
  | 0, _ => Abelian.Ext.mk₀ (𝟙 _)
  | k + 1, hk =>
      (AnalyticRelativeIteratedCover.boundaryUpTo D k
        (Nat.le_trans (Nat.le_succ k) hk)).comp
        (AnalyticRelativeIteratedCover.stepExt (X := X) D ⟨k, by omega⟩)
        (by omega)

/-- The full iterated boundary from the first ambient open to the deepest
overlap. -/
def AnalyticRelativeIteratedCover.boundaryExtClass {q : ℕ}
    (D : AnalyticRelativeIteratedCover X q) :
    Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf X (D.ambient 0))
      (analyticOpenFreeAbelianSheaf X
        (D.ambient ⟨q, Nat.lt_succ_self q⟩)) q :=
  D.boundaryUpTo X q le_rfl

section Filtered

variable [IsIntegral X.left] [Smooth X.hom]

local instance relativeHodgeFilteredDeRhamComplex_isStrictlyGE_zero (p : ℕ) :
    (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE 0 := by
  letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE (p : ℤ) := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  exact (hodgeFilteredDeRhamComplex X (p : ℤ)).isStrictlyGE_of_ge
    0 (p : ℤ) (by omega)

/-- The derived degree-`p` morphism represented by a closed `p`-form on an
open, with target the fixed injective model of `F^p Ω^*`. -/
def analyticClosedOpenSectionFilteredShiftedHom
    (U : Opens (TopCat.of (ComplexPoint X))) {p : ℕ}
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj (.op U))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op U) c = 0) :
    ShiftedHom
      ((DerivedCategory.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (analyticOpenFreeAbelianSheaf X U))
      (DerivedCategory.Q.obj
        (globalHypercohomologyInjectiveComplex X
          (hodgeFilteredDeRhamComplex X (p : ℤ)))) (p : ℤ) := by
  let I := globalHypercohomologyInjectiveComplex X
    (hodgeFilteredDeRhamComplex X (p : ℤ))
  let f := analyticClosedOpenSectionToFilteredInjectiveDegree X U c hc
  let z : CochainComplex.HomComplex.Cocycle
      (analyticOpenFreeSingleComplex X U) I (p : ℤ) :=
    CochainComplex.HomComplex.Cocycle.fromSingleMk f
      (show 0 + (p : ℤ) = (p : ℤ) by omega)
      ((p : ℤ) + 1) rfl
      (analyticClosedOpenSectionToFilteredInjectiveDegree_closed X U c hc)
  let β₀ : ShiftedHom
      (DerivedCategory.Q.obj (analyticOpenFreeSingleComplex X U))
      (DerivedCategory.Q.obj I) (p : ℤ) :=
    (kInjectiveDerivedHomAddEquivCohomologyClass
      (analyticOpenFreeSingleComplex X U) I (p : ℤ)).symm
        (CochainComplex.HomComplex.CohomologyClass.mk z)
  let e := (DerivedCategory.singleFunctorIsoCompQ
    (AnalyticAdditiveSheaf X) 0).app (analyticOpenFreeAbelianSheaf X U)
  exact (ShiftedHom.mk₀ (0 : ℤ) rfl e.hom).comp β₀ (by omega)

/-- The relative iterated transition class followed by a closed `p`-form,
viewed as actual cohomology of the fixed injective model on the first ambient
open. -/
def analyticRelativeIteratedClosedSectionOpenClass
    {q p : ℕ} (D : AnalyticRelativeIteratedCover X q)
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)) c = 0) :
    (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) (D.ambient 0)).mapHomologicalComplex
        (.up ℤ)).obj
      (globalHypercohomologyInjectiveComplex X
        (hodgeFilteredDeRhamComplex X (p : ℤ)))).homology
          ((q : ℤ) + (p : ℤ)) := by
  let A := analyticOpenFreeAbelianSheaf X (D.ambient 0)
  let α := D.boundaryExtClass X
  let β := analyticClosedOpenSectionFilteredShiftedHom X
    (D.ambient ⟨q, Nat.lt_succ_self q⟩) c hc
  let γ : ShiftedHom
      ((DerivedCategory.singleFunctor (AnalyticAdditiveSheaf X) 0).obj A)
      (DerivedCategory.Q.obj
        (globalHypercohomologyInjectiveComplex X
          (hodgeFilteredDeRhamComplex X (p : ℤ))))
      ((q : ℤ) + (p : ℤ)) :=
    α.hom.comp β (by omega)
  let e := (DerivedCategory.singleFunctorIsoCompQ
    (AnalyticAdditiveSheaf X) 0).app A
  let γ' : ShiftedHom
      (DerivedCategory.Q.obj (analyticOpenFreeSingleComplex X (D.ambient 0)))
      (DerivedCategory.Q.obj
        (globalHypercohomologyInjectiveComplex X
          (hodgeFilteredDeRhamComplex X (p : ℤ))))
      ((q : ℤ) + (p : ℤ)) :=
    (ShiftedHom.mk₀ (0 : ℤ) rfl e.inv).comp γ (by omega)
  exact derivedHomAddEquivOpenSectionsKInjective X (D.ambient 0)
    (globalHypercohomologyInjectiveComplex X
      (hodgeFilteredDeRhamComplex X (p : ℤ)))
    ((q : ℤ) + (p : ℤ)) γ'

/-- Applying the actual localization boundary gives an actual supported
`F^p` class in degree `q+p+1`. -/
def analyticRelativeIteratedClosedSectionSupportedFilteredClass
    {q p : ℕ} (D : AnalyticRelativeIteratedCover X q)
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)) c = 0) :
    SupportedFilteredDeRhamHypercohomology X
      (D.ambient 0).compl (p : ℤ) ((q : ℤ) + (p : ℤ) + 1) :=
  filteredDeRhamLocalizationBoundary X (D.ambient 0).compl p
    ((q : ℤ) + (p : ℤ) + 1) (by
      simpa only [top_inf_eq, Opens.compl_compl, add_sub_cancel_right] using
        analyticRelativeIteratedClosedSectionOpenClass X D c hc)

/-- The sheafified logarithmic `p`-form on the deepest relative overlap. -/
def analyticRelativeIteratedLogarithmicFormSection
    {q p : ℕ} (D : AnalyticRelativeIteratedCover X q)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)))ˣ) :
    (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)) :=
  (toSheafify (Opens.grothendieckTopology _)
    (holomorphicDeRhamPresheaf X (dim X.left) p)).app _
      (holomorphicLogarithmicForm X (dim X.left) _ p u)

/-- The relative logarithmic form is closed. -/
theorem analyticRelativeIteratedLogarithmicFormSection_differential
    {q p : ℕ} (D : AnalyticRelativeIteratedCover X q)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)))ˣ) :
    (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩))
      (analyticRelativeIteratedLogarithmicFormSection X D u) = 0 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  change ((toSheafify J (holomorphicDeRhamPresheaf X (dim X.left) p) ≫
      sheafifyMap J (holomorphicDeRhamDifferential X (dim X.left) p)).app _)
      (holomorphicLogarithmicForm X (dim X.left) _ p u) = 0
  rw [← toSheafify_naturality, NatTrans.comp_app]
  change (toSheafify J
      (holomorphicDeRhamPresheaf X (dim X.left) (p + 1))).app _
      (holomorphicFormDifferential X (dim X.left) _ p
        (holomorphicLogarithmicForm X (dim X.left) _ p u)) = 0
  rw [holomorphicFormDifferential_logarithmicForm]
  exact map_zero _

/-- The supported filtered class of an iterated logarithmic relative
transition. -/
def analyticRelativeIteratedLogarithmicSupportedFilteredClass
    {q p : ℕ} (D : AnalyticRelativeIteratedCover X q)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)))ˣ) :
    SupportedFilteredDeRhamHypercohomology X
      (D.ambient 0).compl (p : ℤ) ((q : ℤ) + (p : ℤ) + 1) :=
  analyticRelativeIteratedClosedSectionSupportedFilteredClass X D
    (analyticRelativeIteratedLogarithmicFormSection X D u)
    (analyticRelativeIteratedLogarithmicFormSection_differential X D u)

/-- When the number of relative transition steps is `p-1`, the preceding
construction has the Thom degree `2p`. -/
def analyticRelativeIteratedLogarithmicSupportedThomClass
    {q p : ℕ} (hp : q + 1 = p)
    (D : AnalyticRelativeIteratedCover X q)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)))ˣ) :
    SupportedFilteredDeRhamHypercohomology X
      (D.ambient 0).compl (p : ℤ) (2 * (p : ℤ)) := by
  let a := analyticRelativeIteratedLogarithmicSupportedFilteredClass X D u
  have hdeg : (q : ℤ) + (p : ℤ) + 1 = 2 * (p : ℤ) := by omega
  exact hdeg ▸ a

/-- The full supported de Rham image of the relative logarithmic Thom class. -/
def analyticRelativeIteratedLogarithmicSupportedThomDeRhamClass
    {q p : ℕ} (hp : q + 1 = p)
    (D : AnalyticRelativeIteratedCover X q)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨q, Nat.lt_succ_self q⟩)))ˣ) :
    SupportedDeRhamHypercohomology X (D.ambient 0).compl (2 * (p : ℤ)) :=
  supportedFilteredToDeRhamCohomology X (D.ambient 0).compl
    (p : ℤ) (2 * (p : ℤ))
    (analyticRelativeIteratedLogarithmicSupportedThomClass X hp D u)

end Filtered

end AlgebraicGeometry.ComplexPoint
