/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitProjectiveRatioSections
public import Other.AlgebraicGeometry.ExplicitSegreCharts

/-!
# Gluing the Segre coordinate formulas

Two morphisms to projective spaces give a morphism to projective space on pairs of coordinates.
This construction uses the actual regular coordinate ratios and glues their products.
-/

@[expose] public noncomputable section

open MvPolynomial CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SegreMorphism

universe u
variable (R : Type u) [CommRing R] {σ τ : Type u}

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Standard coordinate charts cover projective space. -/
theorem iSup_coordinateBasicOpen :
    ⨆ a : σ, Proj.basicOpen (homogeneousSubmodule σ R) (X a) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro r hr
  simp only [Set.mem_iUnion] at hr
  obtain ⟨d, hd0, hr⟩ := hr
  have hp : r ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ R)) ^ d := by
    rw [Ideal.span_pow_eq_map_homogeneousSubmodule]
    exact ⟨MvPolynomial.map MvPolynomial.C r, hr.map _, by simp⟩
  exact Ideal.pow_le_self hd0.ne' hp

variable {Y : Scheme.{u}} (c : R →+* Γ(Y, ⊤))
  (f : Y ⟶ Proj (homogeneousSubmodule σ R))
  (g : Y ⟶ Proj (homogeneousSubmodule τ R))

/-- The simultaneous nonvanishing locus of two selected projective coordinates. -/
def chart (p : σ × τ) : Y.Opens :=
  f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X p.1) ⊓
    g ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule τ R) (X p.2)

/-- The simultaneous coordinate charts cover the source scheme. -/
theorem iSup_chart : ⨆ p, chart R f g p = ⊤ := by
  change (⨆ p : σ × τ, _ ⊓ _) = _
  rw [iSup_prod]
  simp only [← inf_iSup_eq,
    f.iSup_preimage_eq_top (iSup_coordinateBasicOpen R),
    g.iSup_preimage_eq_top (iSup_coordinateBasicOpen R), inf_top_eq]

/-- Coefficients as regular sections on a simultaneous coordinate chart. -/
def scalar (p : σ × τ) : R →+* Γ(Y, chart R f g p) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp c

/-- The Segre coordinate formula, as an actual regular section. -/
def coordinate (p a : σ × τ) : Γ(Y, chart R f g p) :=
  ProjectiveRatioSections.pullRatio R f (chart R f g p) p.1 inf_le_left a.1 *
    ProjectiveRatioSections.pullRatio R g (chart R f g p) p.2 inf_le_right a.2

@[simp] theorem coordinate_self (p : σ × τ) : coordinate R f g p p = 1 := by
  simp [coordinate]

variable [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Fintype τ]

/-- The local morphism given by products of normalized homogeneous coordinates. -/
def localMap (p : σ × τ) : (chart R f g p).toScheme ⟶
    Proj (homogeneousSubmodule (σ × τ) R) :=
  ProjectiveCoordinates.fromSections (chart R f g p) (scalar R c f g p)
    (coordinate R f g p) p (by simp)

omit [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Fintype τ] in
/-- Coefficients have the same restriction on the intersection of any two charts. -/
theorem scalar_overlap (p q : σ × τ) :
    (Y.presheaf.map (homOfLE (inf_le_left : chart R f g p ⊓ chart R f g q ≤ _)).op).hom.comp
      (scalar R c f g p) =
    (Y.presheaf.map (homOfLE (inf_le_right : chart R f g p ⊓ chart R f g q ≤ _)).op).hom.comp
      (scalar R c f g q) := by
  change ((Y.presheaf.map (homOfLE le_top).op ≫ Y.presheaf.map (homOfLE inf_le_left).op).hom).comp c =
    ((Y.presheaf.map (homOfLE le_top).op ≫ Y.presheaf.map (homOfLE inf_le_right).op).hom).comp c
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

omit [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Fintype τ] in
/-- On an overlap the two families of Segre coordinates are proportional by a unit. -/
theorem coordinate_overlap (p q a : σ × τ) :
    (Y.presheaf.map (homOfLE (inf_le_left : chart R f g p ⊓ chart R f g q ≤ _)).op)
      (coordinate R f g p a) =
    (Y.presheaf.map (homOfLE (inf_le_left : chart R f g p ⊓ chart R f g q ≤ _)).op)
      (coordinate R f g p q) *
    (Y.presheaf.map (homOfLE (inf_le_right : chart R f g p ⊓ chart R f g q ≤ _)).op)
      (coordinate R f g q a) := by
  simp only [coordinate, map_mul, ProjectiveRatioSections.restrict_pullRatio]
  rw [ProjectiveRatioSections.pullRatio_transition R f (chart R f g p ⊓ chart R f g q) p.1 q.1 a.1
    (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left),
    ProjectiveRatioSections.pullRatio_transition R g (chart R f g p ⊓ chart R f g q) p.2 q.2 a.2
      (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)]
  ring

/-- The local Segre maps agree as scheme morphisms on every overlap. -/
theorem localMap_overlap (p q : σ × τ) :
    Y.homOfLE (inf_le_left : chart R f g p ⊓ chart R f g q ≤ _) ≫ localMap R c f g p =
      Y.homOfLE (inf_le_right : chart R f g p ⊓ chart R f g q ≤ _) ≫ localMap R c f g q := by
  simp only [localMap, ProjectiveCoordinates.homOfLE_fromSections]
  rw [scalar_overlap R c f g p q]
  unfold ProjectiveCoordinates.fromSections
  congr 1
  apply ProjectiveCoordinates.toProjective_eq_of_proportional
  · simp only [Function.comp_apply, coordinate_self, map_one]
  · simp only [Function.comp_apply, coordinate_self, map_one]
  · intro a
    exact coordinate_overlap R f g p q a

/-- The open cover used in the Segre construction. -/
def cover : Y.OpenCover := Y.openCoverOfIsOpenCover (chart R f g) (iSup_chart R f g)

/-- The scheme morphism obtained by gluing the Segre formulas. -/
def fromMaps : Y ⟶ Proj (homogeneousSubmodule (σ × τ) R) :=
  (cover R f g).glueMorphisms (localMap R c f g) (by
    intro p q
    change pullback.fst (chart R f g p).ι (chart R f g q).ι ≫ localMap R c f g p =
      pullback.snd (chart R f g p).ι (chart R f g q).ι ≫ localMap R c f g q
    rw [← cancel_epi (isPullback_opens_inf (chart R f g p) (chart R f g q)).isoPullback.hom]
    simpa only [IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc] using localMap_overlap R c f g p q)

/-- The global Segre formula restricts to the explicitly defined morphism on each chart. -/
@[reassoc] theorem chart_ι_fromMaps (p : σ × τ) :
    (chart R f g p).ι ≫ fromMaps R c f g = localMap R c f g p :=
  (cover R f g).ι_glueMorphisms _ _ p

omit [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Fintype τ] in
/-- The nonvanishing locus of a Segre coordinate is the intersection with the corresponding
simultaneous coordinate chart. -/
theorem basicOpen_coordinate (p q : σ × τ) :
    Y.basicOpen (coordinate R f g p q) = chart R f g p ⊓ chart R f g q := by
  simp only [coordinate, Scheme.basicOpen_mul, ProjectiveRatioSections.basicOpen_pullRatio]
  exact (inf_inf_distrib_left (chart R f g p) _ _).symm

/-- The local morphism has the expected preimage of each target coordinate chart. -/
theorem localMap_preimage_coordinate (p q : σ × τ) :
    localMap R c f g p ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X q) =
      (chart R f g p).ι ⁻¹ᵁ chart R f g q := by
  rw [localMap, ProjectiveCoordinates.fromSections_preimage_coordinate _ _ _ _ _
    (coordinate_self R f g p), basicOpen_coordinate, Scheme.Hom.preimage_inf]
  simp

/-- The global Segre morphism has exactly the prescribed source coordinate charts. -/
theorem fromMaps_preimage_coordinate (q : σ × τ) :
    fromMaps R c f g ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X q) =
      chart R f g q := by
  ext y
  obtain ⟨p, y, rfl⟩ := (cover R f g).exists_eq y
  change ((chart R f g p).ι ≫ fromMaps R c f g) y ∈
    Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X q) ↔ _
  rw [chart_ι_fromMaps]
  exact congrArg (fun V : (chart R f g p).toScheme.Opens ↦ y ∈ V)
    (localMap_preimage_coordinate R c f g p q) |>.to_iff

/-- The local Segre map with codomain restricted to its selected affine target chart. -/
def localToChart (p : σ × τ) : (chart R f g p).toScheme ⟶
    (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)).toScheme :=
  (chart R f g p).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (ProjectiveCoordinates.evaluate (scalar R c f g p)
      (coordinate R f g p) (X p) (by simp))) ≫
    (Proj.basicOpenIsoSpec (homogeneousSubmodule (σ × τ) R) (X p)
      (isHomogeneous_X R p) zero_lt_one).inv

omit [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Fintype τ] in
@[reassoc] theorem localToChart_ι (p : σ × τ) :
    localToChart R c f g p ≫
      (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)).ι = localMap R c f g p := by
  rfl

/-- The restriction of the global morphism is the explicit local chart morphism. -/
theorem fromMaps_resLE (p : σ × τ) :
    (fromMaps R c f g).resLE
      (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)) (chart R f g p)
      (fromMaps_preimage_coordinate R c f g p).ge = localToChart R c f g p := by
  rw [← cancel_mono (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)).ι,
    Scheme.Hom.resLE_comp_ι, localToChart_ι, chart_ι_fromMaps]

end AlgebraicGeometry.SegreMorphism
