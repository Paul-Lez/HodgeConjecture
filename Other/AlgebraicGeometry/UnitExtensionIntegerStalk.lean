/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SheafHomOfLocalStalkMaps
public import Other.AlgebraicGeometry.UnitExtensionClassObligations

/-!
# Sections and germs of the constant integer sheaf

Two elementary facts about the constant integer sheaf on the analytic space, both consequences
of the stalk description `TopCat.Sheaf.constantSheafStalkIso`:

* `integerOneSection_zsmul_germ_injective` — the germs of `n • 1` at a point are pairwise
  distinct;
* `exists_zsmul_integerOneSection` — every section of the constant integer sheaf is, near each
  point of its domain, an integer multiple of the section `1`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open HolomorphicUnitExtension

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance unitExtensionIntegerStalkTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- The section `1` of the constant integer sheaf, restricted to an open set. -/
def integerOneRestrict (U : Opens (TopCat.of (ComplexPoint X))) :
    (constantIntegerSheaf X).obj.obj (op U) :=
  (constantIntegerSheaf X).obj.map (homOfLE (le_top : U ≤ ⊤)).op (integerOneSection (X := X))

theorem integerOneRestrict_map {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U) :
    (constantIntegerSheaf X).obj.map (homOfLE h).op (integerOneRestrict X U) =
      integerOneRestrict X V := by
  unfold integerOneRestrict
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The stalks of the constant integer sheaf are canonically the integers. -/
def integerStalkIso (x : ComplexPoint X) :
    AddCommGrpCat.of ℤ ≅ (constantIntegerSheaf X).presheaf.stalk x :=
  @TopCat.Sheaf.constantSheafStalkIso (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℤ) x

set_option backward.isDefEq.respectTransparency false in
/-- The stalk identification sends `1` to the germ of the section `1`. -/
theorem integerStalkIso_hom_one (x : ComplexPoint X) :
    (integerStalkIso X x).hom (1 : ℤ) =
      (constantIntegerSheaf X).presheaf.germ ⊤ x True.intro (integerOneSection (X := X)) := by
  unfold integerStalkIso TopCat.Sheaf.constantSheafStalkIso
  simp only [Iso.trans_hom, asIso_hom, ConcreteCategory.comp_apply]
  dsimp only [TopCat.Presheaf.Γgerm]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- The stalk identification sends an integer to the germ of `n • 1`. -/
theorem integerStalkIso_hom_apply (x : ComplexPoint X) (n : ℤ) :
    (integerStalkIso X x).hom n =
      (constantIntegerSheaf X).presheaf.germ ⊤ x True.intro
        (n • integerOneSection (X := X)) := by
  have h1 : (integerStalkIso X x).hom n = n • (integerStalkIso X x).hom (1 : ℤ) := by
    have h := map_zsmul (ConcreteCategory.hom (integerStalkIso X x).hom) n (1 : ℤ)
    rw [zsmul_eq_mul, mul_one, Int.cast_id] at h
    exact h
  rw [h1, integerStalkIso_hom_one, map_zsmul]

theorem integerOneSection_zsmul_germ_injective (x : ComplexPoint X) :
    Function.Injective (fun n : ℤ => (constantIntegerSheaf X).presheaf.germ ⊤ x True.intro
      (n • integerOneSection (X := X))) := by
  intro a b hab
  simp only at hab
  rw [← integerStalkIso_hom_apply, ← integerStalkIso_hom_apply] at hab
  exact (ConcreteCategory.bijective_of_isIso (integerStalkIso X x).hom).injective hab

/-- Every section of the constant integer sheaf is locally an integer multiple of `1`. -/
theorem exists_zsmul_integerOneSection (V : Opens (TopCat.of (ComplexPoint X)))
    (t : (constantIntegerSheaf X).obj.obj (op V)) (x : ComplexPoint X) (hx : x ∈ V) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U) (hUV : U ≤ V) (n : ℤ),
      (constantIntegerSheaf X).obj.map (homOfLE hUV).op t = n • integerOneRestrict X U := by
  classical
  set n : ℤ := (integerStalkIso X x).inv
    ((constantIntegerSheaf X).presheaf.germ V x hx t) with hn
  have hgerm : (constantIntegerSheaf X).presheaf.germ V x hx t =
      (constantIntegerSheaf X).presheaf.germ ⊤ x True.intro
        (n • integerOneSection (X := X)) := by
    rw [← integerStalkIso_hom_apply, hn]
    exact (CategoryTheory.Iso.inv_hom_id_apply (integerStalkIso X x) _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ :=
    (constantIntegerSheaf X).presheaf.germ_eq (U := V) (V := ⊤) x hx True.intro t
      (n • integerOneSection (X := X)) hgerm
  refine ⟨W, hxW, iU.le, n, ?_⟩
  have hiU : (homOfLE iU.le : W ⟶ V) = iU := rfl
  have hgoal : (constantIntegerSheaf X).obj.map iU.op t =
      (constantIntegerSheaf X).obj.map iV.op (n • integerOneSection (X := X)) := hW
  rw [hiU, hgoal, map_zsmul]
  congr 1

end AlgebraicGeometry.ComplexPoint
