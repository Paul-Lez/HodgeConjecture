/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplementFrameGeneric
public import Other.AlgebraicGeometry.HolomorphicFrameLift

/-!
# Cartier complement lifts and their local formulas

The complement lift constructed from Cartier data is the extension lift associated with
the analytified rational section. On a unit datum, it differs from the lift associated
with the regular algebraic frame by the image of the actual Cartier unit.

The strengthened gluing theorem retains restriction identities for every unit datum,
rather than only the projection-to-one property of the glued lift. These identities are
needed to compare the chosen complement lift with frames on winding charts.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open scoped Manifold ContDiff
namespace AlgebraicGeometry.ComplexPoint
variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance cartierFrameLiftTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective
variable {L : X.left.Modules} {c : Scheme.CartierData X.left}
  (g : ∀ i : c.ι, Γ(L, c.opens i))
  (E : HolomorphicUnitExtension X (dim X.left))
  (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)
  (hg : ∀ i, Scheme.Modules.Generates (g i))

lemma localLift_eq_frameLift (z : ComplexPoint X) (D : c.UnitDatum (Point.underlying z)) :
    localLift g E e z D hg =
      E.frameLift z (liftOpen E z D) (liftOpen_le_localLifts E z D)
        (liftFrame g E e z D) (holomorphicGenerates_liftFrame g E e z D hg) := rfl

namespace UnitDatum
variable {p : X.left} (D : c.UnitDatum p)

/-- The analytified algebraic local generator, transported to the line bundle of the extension. -/
def regularFrame : E.sectionSheafOfModules.val.obj (op (analyticOpen X D.opens)) :=
  e.hom.val.app (op (analyticOpen X D.opens))
    (analyticSection X (dim X.left) L D.opens (Scheme.Modules.resSection L D.le (g D.i)))

include hg in
lemma holomorphicGenerates_regularFrame : HolomorphicGenerates (regularFrame g E e D) :=
  (analytificationGenerates X (dim X.left) L D.opens _ ((hg D.i).restrict D.le)).map_iso e

lemma analyticFrame_eq_smul_regularFrame :
    analyticFrame g E e D = analyticFunction X (dim X.left) D.opens D.unit •
      regularFrame g E e D := by
  unfold analyticFrame Scheme.CartierData.UnitDatum.localSection regularFrame
  rw [analyticSection_smul]
  exact (e.hom.val.app _).hom.map_smul _ _

/-- The Cartier function as a holomorphic unit on the unit datum's open. -/
def analyticUnit : (C^ω⟮𝓘(ℂ, Fin (dim X.left) → ℂ), analyticOpen X D.opens; ℂ⟯)ˣ :=
  (isUnit_analyticFunction (d := dim X.left) D.isUnit).unit

lemma unitSection_analyticUnit :
    unitSection (analyticUnit D) = analyticFunction X (dim X.left) D.opens D.unit :=
  (isUnit_analyticFunction (d := dim X.left) D.isUnit).unit_spec

end UnitDatum

/-- On each local unit datum, the lift of the rational Cartier frame differs from the
lift of the regular algebraic frame by the analytified Cartier function. -/
lemma localLift_eq_regularFrameLift_add_unit
    (z : ComplexPoint X) (D : c.UnitDatum (Point.underlying z)) :
    localLift g E e z D hg =
      E.frameLift z (liftOpen E z D) (liftOpen_le_localLifts E z D)
        (holRes E.sectionSheafOfModules (liftOpen_le_analyticOpen E z D)
          (UnitDatum.regularFrame g E e D))
        ((UnitDatum.holomorphicGenerates_regularFrame g E e hg D).restrict _) +
      E.inclusion.hom.app (op (liftOpen E z D))
        (sres (holomorphicUnitSheaf X (dim X.left)) (liftOpen_le_analyticOpen E z D)
          (Additive.ofMul (UnitDatum.analyticUnit D))) := by
  rw [localLift_eq_frameLift]
  have hframe : liftFrame g E e z D =
      unitSection (unitOf (sres (holomorphicUnitSheaf X (dim X.left))
        (liftOpen_le_analyticOpen E z D) (Additive.ofMul (UnitDatum.analyticUnit D)))) •
      holRes E.sectionSheafOfModules (liftOpen_le_analyticOpen E z D)
        (UnitDatum.regularFrame g E e D) := by
    unfold liftFrame
    rw [UnitDatum.analyticFrame_eq_smul_regularFrame, holRes_smul]
    congr 1
  refine Eq.trans ?_ (E.frameLift_smul_unit z _ _ _
    ((UnitDatum.holomorphicGenerates_regularFrame g E e hg D).restrict _)
    (unitOf (sres (holomorphicUnitSheaf X (dim X.left))
      (liftOpen_le_analyticOpen E z D) (Additive.ofMul (UnitDatum.analyticUnit D)))))
  congr 1

/-- A complement lift retains the local lifts of the rational Cartier section. -/
def IsCartierComplementLift (Ω : Opens (TopCat.of (ComplexPoint X)))
    (ℓ : E.middle.obj.obj (op Ω)) : Prop :=
  ∀ (z : ComplexPoint X) (D : c.UnitDatum (Point.underlying z))
    (V : Opens (TopCat.of (ComplexPoint X))) (hVΩ : V ≤ Ω) (hVl : V ≤ liftOpen E z D),
    sres E.middle hVΩ ℓ = sres E.middle hVl (localLift g E e z D hg)

/-- Gluing the Cartier lift while retaining its restriction formula for every unit datum. -/
theorem exists_lift_of_goodLocus_with_localFormula
    (hrep : c.RepresentsWith L g) (Ω : Opens (TopCat.of (ComplexPoint X)))
    (hΩ : ∀ z ∈ Ω, Point.underlying z ∈ goodLocus c) (hΩc : Ω ≤ divisorComplementOpen c) :
    ∃ ℓ : E.middle.obj.obj (op Ω),
      E.projection.hom.app (op Ω) ℓ = integerOneRestrict X Ω ∧
      IsCartierComplementLift g E e hg Ω ℓ := by
  let D : ∀ z : Ω, c.UnitDatum (Point.underlying (z : ComplexPoint X)) :=
    fun z => Classical.choice (hΩ z z.property)
  let W : Ω → Opens (TopCat.of (ComplexPoint X)) := fun z => Ω ⊓ liftOpen E z (D z)
  have hWΩ : ∀ z, W z ≤ Ω := fun _ => inf_le_left
  have hWl : ∀ z, W z ≤ liftOpen E z (D z) := fun _ => inf_le_right
  have hcover : Ω ≤ iSup W := fun z hz =>
    Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hz, mem_liftOpen E z (D ⟨z, hz⟩) (hΩc hz)⟩
  have hcompat : ∀ z w : Ω,
      sres E.middle (inf_le_left : W z ⊓ W w ≤ W z)
          (sres E.middle (hWl z) (localLift g E e z (D z) hg)) =
        sres E.middle (inf_le_right : W z ⊓ W w ≤ W w)
          (sres E.middle (hWl w) (localLift g E e w (D w) hg)) := by
    intro z w
    rw [sres_sres, sres_sres]
    have h := congrArg (sres E.middle (inf_le_inf (hWl z) (hWl w)))
      (localLift_compatible g E e z (D z) hg w (D w) hrep)
    rw [sres_sres, sres_sres] at h
    exact h
  obtain ⟨ℓ, hℓ, -⟩ := E.middle.existsUnique_gluing' W Ω (fun z => homOfLE (hWΩ z)) hcover
    (fun z => sres E.middle (hWl z) (localLift g E e z (D z) hg)) hcompat
  refine ⟨ℓ, ?_, ?_⟩
  · apply (constantIntegerSheaf X).eq_of_locally_eq' W Ω (fun z => homOfLE (hWΩ z)) hcover
    intro z
    change sres (constantIntegerSheaf X) _ (E.projection.hom.app _ ℓ) =
      sres (constantIntegerSheaf X) _ (integerOneRestrict X Ω)
    rw [sres_hom, sres_integerOneRestrict]
    have h1 : sres E.middle (hWΩ z) ℓ = sres E.middle (hWl z) (localLift g E e z (D z) hg) := hℓ z
    rw [h1, ← sres_hom, projection_localLift, sres_integerOneRestrict]
  · intro z Dz V hVΩ hVl
    let W' : Ω → Opens (TopCat.of (ComplexPoint X)) := fun w => V ⊓ W w
    have hcover' : V ≤ iSup W' := by
      intro y hy
      obtain ⟨w, hw⟩ := Opens.mem_iSup.mp (hcover (hVΩ hy))
      exact Opens.mem_iSup.mpr ⟨w, hy, hw⟩
    apply E.middle.eq_of_locally_eq' W' V (fun _ => homOfLE inf_le_left) hcover'
    intro w
    change sres E.middle (inf_le_left : W' w ≤ V) (sres E.middle hVΩ ℓ) =
      sres E.middle (inf_le_left : W' w ≤ V)
        (sres E.middle hVl (localLift g E e z Dz hg))
    rw [sres_sres, sres_sres,
      ← sres_sres (hWΩ w) (inf_le_right : W' w ≤ W w)]
    have h1 : sres E.middle (hWΩ w) ℓ = sres E.middle (hWl w) (localLift g E e w (D w) hg) := hℓ w
    rw [h1, sres_sres]
    have h := congrArg (sres E.middle
      (le_inf (inf_le_right.trans (hWl w)) (inf_le_left.trans hVl) :
        W' w ≤ liftOpen E w (D w) ⊓ liftOpen E z Dz))
      (localLift_compatible g E e w (D w) hg z Dz hrep)
    simpa only [sres_sres] using h

end AlgebraicGeometry.ComplexPoint
