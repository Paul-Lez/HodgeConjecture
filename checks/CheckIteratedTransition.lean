import Other.AlgebraicGeometry.AnalyticNestedTransitionClass
import Other.AlgebraicGeometry.HolomorphicLogarithmicForms
import Other.AlgebraicGeometry.FilteredLogarithmicClass
import Other.AlgebraicGeometry.SheafExtHypercohomology

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over (Spec (CommRingCat.of ℂ)))

local instance : Abelian (AnalyticAdditiveSheaf X) :=
  CategoryTheory.sheafIsAbelian

local instance : HasExt.{1} (AnalyticAdditiveSheaf X) := analyticHasExt X

structure AnalyticIteratedCover (p : ℕ) where
  ambient : Fin (p + 1) → Opens (TopCat.of (ComplexPoint X))
  left : Fin p → Opens (TopCat.of (ComplexPoint X))
  right : Fin p → Opens (TopCat.of (ComplexPoint X))
  cover : ∀ i, left i ⊔ right i = ambient i.castSucc
  overlap : ∀ i, left i ⊓ right i = ambient i.succ
  ambient_zero : ambient 0 = ⊤

def AnalyticIteratedCover.stepExt {p : ℕ} (D : AnalyticIteratedCover X p)
    (i : Fin p) :
    Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (D.ambient i.castSucc))
      (analyticOpenFreeAbelianSheaf X (D.ambient i.succ)) 1 := by
  rw [← D.overlap i]
  exact (analyticRelativeCoverMayerVietorisSquare X (D.left i) (D.right i)
    (D.ambient i.castSucc)
    (by rw [← D.cover i]; exact le_sup_left)
    (by rw [← D.cover i]; exact le_sup_right)
    (D.cover i)).shortComplex_shortExact.extClass (C := AnalyticAdditiveSheaf X)

def AnalyticIteratedCover.boundaryUpTo {p : ℕ} (D : AnalyticIteratedCover X p) :
    (k : ℕ) → (hk : k ≤ p) →
      Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (D.ambient 0))
        (analyticOpenFreeAbelianSheaf X
          (D.ambient ⟨k, Nat.lt_succ_of_le hk⟩)) k
  | 0, _ => Abelian.Ext.mk₀ (𝟙 _)
  | k + 1, hk =>
      (AnalyticIteratedCover.boundaryUpTo D k
        (Nat.le_trans (Nat.le_succ k) hk)).comp
        (AnalyticIteratedCover.stepExt (X := X) D ⟨k, by omega⟩) (by omega)

def AnalyticIteratedCover.topMap {p : ℕ} (D : AnalyticIteratedCover X p) :
    constantIntegerSheaf X ⟶ analyticOpenFreeAbelianSheaf X (D.ambient 0) :=
  (analyticTopFreeAbelianSheafIso X).inv ≫
    analyticOpenFreeAbelianMap X (homOfLE (by rw [D.ambient_zero]))

def analyticIteratedTransitionExtClass {p : ℕ} (D : AnalyticIteratedCover X p)
    (F : AnalyticAdditiveSheaf X)
    (c : F.obj.obj (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩))) :
    Abelian.Ext.{1} (constantIntegerSheaf X) F p :=
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf X)
      (analyticOpenFreeAbelianSheaf X (D.ambient 0)) 0 :=
    Abelian.Ext.mk₀ D.topMap
  let δ := AnalyticIteratedCover.boundaryUpTo (X := X) D p le_rfl
  let a : Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf X (D.ambient ⟨p, Nat.lt_succ_self p⟩)) F 0 :=
    Abelian.Ext.mk₀ (analyticSectionSheafHom X F _ c)
  a₀.comp (δ.comp a (c := p) (Nat.add_zero p))
    (c := p) (Nat.zero_add p)

def AnalyticIteratedCover.boundaryExtClass {p : ℕ}
    (D : AnalyticIteratedCover X p) :
    Abelian.Ext.{1} (constantIntegerSheaf X)
      (analyticOpenFreeAbelianSheaf X
        (D.ambient ⟨p, Nat.lt_succ_self p⟩)) p :=
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf X)
      (analyticOpenFreeAbelianSheaf X (D.ambient 0)) 0 :=
    Abelian.Ext.mk₀ D.topMap
  let δ := AnalyticIteratedCover.boundaryUpTo (X := X) D p le_rfl
  a₀.comp δ (c := p) (Nat.zero_add p)

theorem analyticIteratedTransitionExtClass_eq_boundary_comp {p : ℕ}
    (D : AnalyticIteratedCover X p) (F : AnalyticAdditiveSheaf X)
    (c : F.obj.obj (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩))) :
    analyticIteratedTransitionExtClass X D F c =
      (AnalyticIteratedCover.boundaryExtClass (X := X) D).comp
        (Abelian.Ext.mk₀ (analyticSectionSheafHom X F _ c))
        (c := p) (Nat.add_zero p) := by
  unfold analyticIteratedTransitionExtClass
    AnalyticIteratedCover.boundaryExtClass
  dsimp only
  exact (Abelian.Ext.comp_assoc _ _ _
    (Nat.zero_add p) (Nat.add_zero p) (by omega)).symm

@[simp]
theorem analyticIteratedTransitionExtClass_zero {p : ℕ}
    (D : AnalyticIteratedCover X p) (F : AnalyticAdditiveSheaf X) :
    analyticIteratedTransitionExtClass X D F 0 = 0 := by
  have hzero : Abelian.Ext.mk₀
      (analyticSectionSheafHom X F
        (D.ambient ⟨p, Nat.lt_succ_self p⟩) 0) = 0 := by
    rw [analyticSectionSheafHom_zero]
    exact Abelian.Ext.mk₀_zero _ _
  simp only [analyticIteratedTransitionExtClass]
  rw [hzero, Abelian.Ext.comp_zero, Abelian.Ext.comp_zero]

def analyticIteratedLogarithmicFormSection {p d : ℕ}
    [SmoothOfRelativeDimension d X.hom] (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X d
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    (holomorphicDeRhamSheaf X d p).obj.obj
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)) :=
  (toSheafify (Opens.grothendieckTopology _)
    (holomorphicDeRhamPresheaf X d p)).app _
      (holomorphicLogarithmicForm X d _ p u)

def analyticIteratedLogarithmicTransitionExtClass {p d : ℕ}
    [SmoothOfRelativeDimension d X.hom] (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X d
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicDeRhamSheaf X d p) p :=
  analyticIteratedTransitionExtClass X D (holomorphicDeRhamSheaf X d p)
    (analyticIteratedLogarithmicFormSection X D u)

theorem analyticIteratedLogarithmicFormSection_differential {p d : ℕ}
    [SmoothOfRelativeDimension d X.hom] (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X d
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    (holomorphicDeRhamSheafDifferential X d p).hom.app
        (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩))
        (analyticIteratedLogarithmicFormSection X D u) = 0 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  change ((toSheafify J (holomorphicDeRhamPresheaf X d p) ≫
      sheafifyMap J (holomorphicDeRhamDifferential X d p)).app _)
      (holomorphicLogarithmicForm X d _ p u) = 0
  rw [← toSheafify_naturality, NatTrans.comp_app]
  change (toSheafify J (holomorphicDeRhamPresheaf X d (p + 1))).app _
      (holomorphicFormDifferential X d _ p
        (holomorphicLogarithmicForm X d _ p u)) = 0
  rw [holomorphicFormDifferential_logarithmicForm]
  exact map_zero _

section Filtered

variable [IsIntegral X.left] [Smooth X.hom]

def analyticClosedSectionToDeRhamComplexInt {p : ℕ}
    (D : AnalyticIteratedCover X p)
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)) c = 0) :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) (p : ℤ)).obj
        (analyticOpenFreeAbelianSheaf X
          (D.ambient ⟨p, Nat.lt_succ_self p⟩)) ⟶
      holomorphicDeRhamComplexInt X :=
  HomologicalComplex.mkHomFromSingle
    (analyticSectionSheafHom X (holomorphicDeRhamSheaf X (dim X.left) p) _ c ≫
      ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
        ComplexShape.embeddingUpNat (i := p) rfl).inv) (by
      have hclosed :
          analyticSectionSheafHom X
              (holomorphicDeRhamSheaf X (dim X.left) p) _ c ≫
            holomorphicDeRhamSheafDifferential X (dim X.left) p = 0 := by
        rw [analyticSectionSheafHom_postcomp, hc,
          analyticSectionSheafHom_zero]
      intro k hk
      have hk' : k = (p : ℤ) + 1 := by
        simpa [ComplexShape.up_Rel] using hk.symm
      subst k
      unfold holomorphicDeRhamComplexInt
      rw [HomologicalComplex.extend_d_eq
        (holomorphicDeRhamComplex X (dim X.left))
        ComplexShape.embeddingUpNat
        (i' := (p : ℤ)) (j' := (p : ℤ) + 1)
        (i := p) (j := p + 1) rfl (by simp)]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_assoc]
      rw [holomorphicDeRhamComplex_d]
      rw [← Category.assoc, hclosed, zero_comp])

def analyticClosedSectionToFilteredDeRhamComplexInt {p : ℕ}
    (D : AnalyticIteratedCover X p)
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)) c = 0) :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) (p : ℤ)).obj
        (analyticOpenFreeAbelianSheaf X
          (D.ambient ⟨p, Nat.lt_succ_self p⟩)) ⟶
      hodgeFilteredDeRhamComplex X (p : ℤ) :=
  HomologicalComplex.liftStupidTrunc
    (ComplexShape.embeddingUpIntGE (p : ℤ))
    (analyticClosedSectionToDeRhamComplexInt X D c hc)

@[reassoc (attr := simp)]
theorem analyticClosedSectionToFilteredDeRhamComplexInt_comp_inclusion
    {p : ℕ} (D : AnalyticIteratedCover X p)
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)) c = 0) :
    analyticClosedSectionToFilteredDeRhamComplexInt X D c hc ≫
        hodgeFilteredDeRhamInclusion X (p : ℤ) =
      analyticClosedSectionToDeRhamComplexInt X D c hc :=
  HomologicalComplex.liftStupidTrunc_inclusion _ _

def analyticIteratedClosedSectionFilteredClass {p : ℕ}
    (D : AnalyticIteratedCover X p)
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)) c = 0) :
    FilteredDeRhamHypercohomology X (p : ℤ) (2 * (p : ℤ)) :=
  let α := sheafExtHypercohomologyEquiv X
    (analyticOpenFreeAbelianSheaf X
      (D.ambient ⟨p, Nat.lt_succ_self p⟩)) (p : ℤ) p
      (D.boundaryExtClass X)
  let hdeg : (p : ℤ) + (p : ℤ) = 2 * (p : ℤ) := by omega
  hypercohomologyMap X
    (analyticClosedSectionToFilteredDeRhamComplexInt X D c hc)
    (2 * (p : ℤ)) (hdeg ▸ α)

def analyticIteratedClosedSectionDeRhamClass {p : ℕ}
    (D : AnalyticIteratedCover X p)
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)) c = 0) :
    DeRhamHypercohomology X (2 * (p : ℤ)) :=
  let α := sheafExtHypercohomologyEquiv X
    (analyticOpenFreeAbelianSheaf X
      (D.ambient ⟨p, Nat.lt_succ_self p⟩)) (p : ℤ) p
      (D.boundaryExtClass X)
  let hdeg : (p : ℤ) + (p : ℤ) = 2 * (p : ℤ) := by omega
  hypercohomologyMap X
    (analyticClosedSectionToDeRhamComplexInt X D c hc)
    (2 * (p : ℤ)) (hdeg ▸ α)

@[simp]
theorem filteredToDeRhamCohomology_analyticIteratedClosedSectionFilteredClass
    {p : ℕ} (D : AnalyticIteratedCover X p)
    (c : (holomorphicDeRhamSheaf X (dim X.left) p).obj.obj
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))
    (hc : (holomorphicDeRhamSheafDifferential X (dim X.left) p).hom.app
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)) c = 0) :
    filteredToDeRhamCohomology X (p : ℤ) (2 * (p : ℤ))
        (analyticIteratedClosedSectionFilteredClass X D c hc) =
      analyticIteratedClosedSectionDeRhamClass X D c hc := by
  unfold filteredToDeRhamCohomology
    analyticIteratedClosedSectionFilteredClass
    analyticIteratedClosedSectionDeRhamClass
  rw [← hypercohomologyMap_comp_apply,
    analyticClosedSectionToFilteredDeRhamComplexInt_comp_inclusion]

def analyticIteratedLogarithmicFilteredClass {p : ℕ}
    (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    FilteredDeRhamHypercohomology X (p : ℤ) (2 * (p : ℤ)) :=
  analyticIteratedClosedSectionFilteredClass X D
    (analyticIteratedLogarithmicFormSection X D u)
    (analyticIteratedLogarithmicFormSection_differential X D u)

def analyticIteratedLogarithmicDeRhamClass {p : ℕ}
    (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    DeRhamHypercohomology X (2 * (p : ℤ)) :=
  analyticIteratedClosedSectionDeRhamClass X D
    (analyticIteratedLogarithmicFormSection X D u)
    (analyticIteratedLogarithmicFormSection_differential X D u)

@[simp]
theorem filteredToDeRhamCohomology_analyticIteratedLogarithmicFilteredClass
    {p : ℕ} (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    filteredToDeRhamCohomology X (p : ℤ) (2 * (p : ℤ))
        (analyticIteratedLogarithmicFilteredClass X D u) =
      analyticIteratedLogarithmicDeRhamClass X D u :=
  filteredToDeRhamCohomology_analyticIteratedClosedSectionFilteredClass X D _ _

theorem analyticIteratedLogarithmicDeRhamClass_mem_hodgeFiltration
    {p : ℕ} (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    analyticIteratedLogarithmicDeRhamClass X D u ∈
      hodgeFiltration X (p : ℤ) (2 * (p : ℤ)) :=
  ⟨analyticIteratedLogarithmicFilteredClass X D u,
    filteredToDeRhamCohomology_analyticIteratedLogarithmicFilteredClass X D u⟩

end Filtered

end
end AlgebraicGeometry.ComplexPoint
