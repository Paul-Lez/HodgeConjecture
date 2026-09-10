/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticNestedTransitionClass
public import Other.AlgebraicGeometry.HolomorphicLogarithmicForms
public import Other.AlgebraicGeometry.FilteredLogarithmicClass
public import Other.AlgebraicGeometry.SheafExtHypercohomology

/-!
# Iterated analytic transition classes

A chain of relative two-open covers gives a canonical Yoneda product of
Mayer--Vietoris extensions.  A section on the deepest overlap therefore
produces an actual degree-`p` sheaf Ext class.  If the section is a closed
holomorphic `p`-form, the same construction maps canonically to the `p`-th
Hodge-filtered de Rham complex and gives a class in total degree `2p`.

In particular, a tuple of holomorphic units on the deepest overlap gives the
closed form `dlog u₁ ∧ ⋯ ∧ dlog uₚ` and hence an explicit filtered
class.  This is the local analytic input needed by a normal-coordinate purity
comparison; no acyclicity or purity statement is assumed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec (CommRingCat.of ℂ)))

local instance iteratedTransitionSheafAbelian : Abelian (AnalyticAdditiveSheaf X) :=
  CategoryTheory.sheafIsAbelian

local instance iteratedTransitionHasExt : HasExt.{1} (AnalyticAdditiveSheaf X) :=
  analyticHasExt X

/-- A length-`p` chain of relative two-open covers.  At step `i`, `left i` and
`right i` cover `ambient i`, and their intersection is `ambient (i+1)`.
The first ambient open is the whole analytification. -/
structure AnalyticIteratedCover (p : ℕ) where
  ambient : Fin (p + 1) → Opens (TopCat.of (ComplexPoint X))
  left : Fin p → Opens (TopCat.of (ComplexPoint X))
  right : Fin p → Opens (TopCat.of (ComplexPoint X))
  cover : ∀ i, left i ⊔ right i = ambient i.castSucc
  overlap : ∀ i, left i ⊓ right i = ambient i.succ
  ambient_zero : ambient 0 = ⊤

/-- The Mayer--Vietoris extension at one step of an iterated cover. -/
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

/-- Yoneda composition of the first `k` Mayer--Vietoris boundaries. -/
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

/-- The constant integer sheaf maps to the free sheaf on the first ambient
open, using that this open is the whole space. -/
def AnalyticIteratedCover.topMap {p : ℕ} (D : AnalyticIteratedCover X p) :
    constantIntegerSheaf X ⟶ analyticOpenFreeAbelianSheaf X (D.ambient 0) :=
  (analyticTopFreeAbelianSheafIso X).inv ≫
    analyticOpenFreeAbelianMap X (homOfLE (by rw [D.ambient_zero]))

/-- The degree-`p` transition class obtained by evaluating a target-sheaf
section on the deepest overlap. -/
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

/-- The iterated boundary before applying a section on the deepest overlap. -/
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

/-- Evaluating the universal iterated boundary on a section recovers the
transition class. -/
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

/-- The sheafified logarithmic `p`-form on the deepest overlap. -/
def analyticIteratedLogarithmicFormSection {p d : ℕ}
    [SmoothOfRelativeDimension d X.hom] (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X d
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    (holomorphicDeRhamSheaf X d p).obj.obj
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)) :=
  (toSheafify (Opens.grothendieckTopology _)
    (holomorphicDeRhamPresheaf X d p)).app _
      (holomorphicLogarithmicForm X d _ p u)

/-- The degree-`p` Ext transition class of a logarithmic `p`-form. -/
def analyticIteratedLogarithmicTransitionExtClass {p d : ℕ}
    [SmoothOfRelativeDimension d X.hom] (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X d
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicDeRhamSheaf X d p) p :=
  analyticIteratedTransitionExtClass X D (holomorphicDeRhamSheaf X d p)
    (analyticIteratedLogarithmicFormSection X D u)

/-- The sheafified logarithmic `p`-form on the deepest overlap is closed. -/
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

/-- A closed `p`-form section on the deepest overlap defines a cochain map
from its open-free sheaf, placed in degree `p`, to the full de Rham complex. -/
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

/-- The closed-section cochain map factored through the `p`-th Hodge
filtration. -/
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

/-- Forgetting the filtration recovers the original closed-section cochain
map exactly. -/
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

/-- The actual filtered class defined by an iterated boundary and a closed
`p`-form on the deepest overlap. -/
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

/-- The same iterated closed-section class in full de Rham cohomology. -/
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

/-- The constructed filtered closed-section class maps to its full de Rham
class. -/
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

/-- The filtered class associated with a logarithmic normal-coordinate
`p`-form. -/
def analyticIteratedLogarithmicFilteredClass {p : ℕ}
    (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    FilteredDeRhamHypercohomology X (p : ℤ) (2 * (p : ℤ)) :=
  analyticIteratedClosedSectionFilteredClass X D
    (analyticIteratedLogarithmicFormSection X D u)
    (analyticIteratedLogarithmicFormSection_differential X D u)

/-- The full de Rham class associated with a logarithmic normal-coordinate
`p`-form. -/
def analyticIteratedLogarithmicDeRhamClass {p : ℕ}
    (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    DeRhamHypercohomology X (2 * (p : ℤ)) :=
  analyticIteratedClosedSectionDeRhamClass X D
    (analyticIteratedLogarithmicFormSection X D u)
    (analyticIteratedLogarithmicFormSection_differential X D u)

/-- Forgetting the filtration sends the explicit logarithmic lift to its
full de Rham class. -/
@[simp]
theorem filteredToDeRhamCohomology_analyticIteratedLogarithmicFilteredClass
    {p : ℕ} (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    filteredToDeRhamCohomology X (p : ℤ) (2 * (p : ℤ))
        (analyticIteratedLogarithmicFilteredClass X D u) =
      analyticIteratedLogarithmicDeRhamClass X D u :=
  filteredToDeRhamCohomology_analyticIteratedClosedSectionFilteredClass X D _ _

/-- Every iterated logarithmic transition class constructed here lies in the
expected Hodge filtration. -/
theorem analyticIteratedLogarithmicDeRhamClass_mem_hodgeFiltration
    {p : ℕ} (D : AnalyticIteratedCover X p)
    (u : Fin p → (OpenHolomorphicFunctions X (dim X.left)
      (.op (D.ambient ⟨p, Nat.lt_succ_self p⟩)))ˣ) :
    analyticIteratedLogarithmicDeRhamClass X D u ∈
      hodgeFiltration X (p : ℤ) (2 * (p : ℤ)) :=
  ⟨analyticIteratedLogarithmicFilteredClass X D u,
    filteredToDeRhamCohomology_analyticIteratedLogarithmicFilteredClass X D u⟩

end Filtered

end AlgebraicGeometry.ComplexPoint
