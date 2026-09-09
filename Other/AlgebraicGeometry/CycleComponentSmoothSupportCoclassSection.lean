/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedSupportCoclassSection
public import Other.AlgebraicGeometry.CycleComponentSmoothSupportPurity
public import Other.AlgebraicTopology.SupportRelativeCohomologyOpenTransport

/-!
# The normalized component coclass on the original ambient smooth-support open

The component's actual smooth locus is closed in the complement of its singular
boundary. We construct its exactly normalized smooth-support section there and
transport it through the actual analytic open embedding. The result is a section
of the ORIGINAL ambient relative-cohomology sheaf on the singular-boundary
complement. No section, purity comparison, or orientation coherence is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

section GeneralOpenTransport

variable {X Y : Scheme}
  (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
  (i : Y ⟶ X) (hi : i ≫ sX = sY) (m d : ℕ)
  [SmoothOfRelativeDimension m sY] [SmoothOfRelativeDimension d sX]
  [IsClosedImmersion i]
  {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X sX) ⟶ M)
  (hf : IsOpenEmbedding f) (S : Set M)
  (hS : f ⁻¹' S = Set.range (Point.map i hi))

/-- The constructed normalized smooth-support section transported to an actual
larger ambient space through an open embedding. -/
def smoothClosedSupportOpenImageCoclassSection :
    (supportRelativeCohomologySheaf M S (2 * (d - m))).obj.obj (op (hf.functor.obj ⊤)) :=
  supportRelativeCohomologySectionOpenImage f hf S (Set.range (Point.map i hi)) hS
    (2 * (d - m)) (smoothClosedSupportCoclassSection sX sY i hi m d)

/-- On every transported chart, the section is precisely the unit image of the
actual transported normal-projection coclass. This displays exact normalization. -/
theorem smoothClosedSupportOpenImageCoclassSection_restrict_chart
    (z : ComplexPoint Y sY) :
    (supportRelativeCohomologySheaf M S (2 * (d - m))).obj.map
      (hf.functor.map (homOfLE (show
        smoothClosedSupportChartOpen sX sY i hi m d z ≤ ⊤ from le_top))).op
      (smoothClosedSupportOpenImageCoclassSection sX sY i hi m d f hf S hS) =
    (supportRelativeCohomologyToSheaf M S (2 * (d - m))).app
      (op (hf.functor.obj (smoothClosedSupportChartOpen sX sY i hi m d z)))
      ((supportRelativeCohomologyPresheafOpenIso f hf S (Set.range (Point.map i hi)) hS
          (2 * (d - m))).inv.app (op (smoothClosedSupportChartOpen sX sY i hi m d z))
        (smoothClosedSupportChartCoclass sX sY i hi m d z
          (smoothClosedSupportChartOpen sX sY i hi m d z) (le_refl _))) := by
  rw [smoothClosedSupportOpenImageCoclassSection,
    supportRelativeCohomologySectionOpenImage_restrict,
    smoothClosedSupportCoclassSection_restrict_chart]
  exact supportRelativeCohomologySheafOpenIso_unit_apply f hf S (Set.range (Point.map i hi))
    hS (2 * (d - m)) (smoothClosedSupportChartOpen sX sY i hi m d z) _

end GeneralOpenTransport

section Component

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X)
  {d p : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = p)

/-- The actual structure morphism of the closed-lift source. -/
abbrev cycleComponentSmoothClosedLiftStructureMap :=
  cycleComponentSmoothLocusClosedLift s x ≫ (cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s

include hx in
/-- The proved dimension of the actual closed-lift source. -/
theorem cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (d - p) (cycleComponentSmoothClosedLiftStructureMap s x) := by
  dsimp [cycleComponentSmoothClosedLiftStructureMap]
  rw [← Category.assoc, cycleComponentSmoothLocusClosedLift_ι, Category.assoc]
  exact cycleComponentSmoothLocus_smoothOfRelativeDimension s x (d := d) hx

include s hx in
omit [IsIntegral X] [Smooth s] [IsProjective s] in
/-- The codimension arithmetic is proved from the actual coheight bound. -/
theorem cycleComponentSmoothClosedLift_codimension :
    d - (d - p) = p := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := s) (d := d) x
  rw [hx] at h
  have hpd : p ≤ d := by exact_mod_cast h
  omega

/-- The normalized section in the auxiliary algebraic ambient open, in the proved
degree 2p. The class is the general normal-chart gluing, not supplied data. -/
def cycleComponentSmoothClosedLiftCoclassSection :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpen s x)
        ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s)))
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
        (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl)) (2 * p)).obj.obj (op ⊤) := by
  let := cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension s x (d := d) hx
  have hdeg := cycleComponentSmoothClosedLift_codimension s x (d := d) hx
  exact hdeg ▸ smoothClosedSupportCoclassSection
    ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s)
    (cycleComponentSmoothClosedLiftStructureMap s x)
    (cycleComponentSmoothLocusClosedLift s x) rfl (d - p) d

/-- The actual analytic open-embedding map back to the original ambient space. -/
def cycleComponentSmoothClosedLiftAmbientMap :
    TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpen s x)
      ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s)) ⟶
    TopCat.of (ComplexPoint X s) :=
  TopCat.ofHom (Point.continuousMap (cycleComponentSmoothLocusAmbientOpen s x).ι
    (structureMap := (cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s) rfl)

omit [IsIntegral X] [Smooth s] in
theorem cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding :
    IsOpenEmbedding (cycleComponentSmoothClosedLiftAmbientMap s x) :=
  isOpenEmbedding_map_open (cycleComponentSmoothLocusAmbientOpen s x) s

/-- Support membership is transported by the actual lift-image theorem. -/
theorem cycleComponentSmoothClosedLiftAmbientMap_support :
    cycleComponentSmoothClosedLiftAmbientMap s x ⁻¹' cycleComponentSupport s x =
      Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
        (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl) :=
  (cycleComponentSmoothLocusClosedLift_complexPoints_range s x).symm

omit [IsIntegral X] [Smooth s] in
/-- The image open is exactly the complement of the canonical first singular boundary. -/
theorem cycleComponentSmoothClosedLiftAmbientMap_imageOpen :
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding s x).functor.obj ⊤ =
      cycleComponentSmoothSupportAmbientOpen s x := by
  apply Opens.ext
  change (cycleComponentSmoothClosedLiftAmbientMap s x) '' Set.univ = _
  rw [Set.image_univ]
  exact cycleComponentSmoothLocusAmbientOpen_analytic_image s x

/-- The actual normalized component coclass section, living on the singular-boundary
complement in the ORIGINAL ambient relative-cohomology sheaf. -/
def cycleComponentSmoothSupportCoclassSection :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s))
      (cycleComponentSupport s x) (2 * p)).obj.obj
      (op (cycleComponentSmoothSupportAmbientOpen s x)) :=
  supportRelativeCohomologySectionOnOpen (cycleComponentSmoothClosedLiftAmbientMap s x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding s x)
    (cycleComponentSupport s x)
    (Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
      (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl))
    (cycleComponentSmoothClosedLiftAmbientMap_support s x)
    (2 * p) (cycleComponentSmoothSupportAmbientOpen s x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen s x)
    (cycleComponentSmoothClosedLiftCoclassSection s x (d := d) hx)

/-- Restriction to each actual image neighborhood agrees with transport of the
constructed auxiliary normalized section. No ambient section comparison is supplied. -/
theorem cycleComponentSmoothSupportCoclassSection_restrict
    (V : Opens (ComplexPoint (cycleComponentSmoothLocusAmbientOpen s x)
      ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s)))
    (hV : (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding s x).functor.obj V ≤
      cycleComponentSmoothSupportAmbientOpen s x) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s))
      (cycleComponentSupport s x) (2 * p)).obj.map (homOfLE hV).op
        (cycleComponentSmoothSupportCoclassSection s x (d := d) hx) =
    (supportRelativeCohomologySheafOpenIso (cycleComponentSmoothClosedLiftAmbientMap s x)
      (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding s x)
      (cycleComponentSupport s x)
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
        (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl))
      (cycleComponentSmoothClosedLiftAmbientMap_support s x) (2 * p)).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpen s x)
          ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s)))
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
          (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl))
        (2 * p)).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (cycleComponentSmoothClosedLiftCoclassSection s x (d := d) hx)) := by
  exact supportRelativeCohomologySectionOnOpen_restrict
    (cycleComponentSmoothClosedLiftAmbientMap s x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding s x)
    (cycleComponentSupport s x)
    (Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
      (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl))
    (cycleComponentSmoothClosedLiftAmbientMap_support s x)
    (2 * p) (cycleComponentSmoothSupportAmbientOpen s x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen s x)
    (cycleComponentSmoothClosedLiftCoclassSection s x (d := d) hx) V hV

end Component

end AlgebraicGeometry.ComplexPoint
