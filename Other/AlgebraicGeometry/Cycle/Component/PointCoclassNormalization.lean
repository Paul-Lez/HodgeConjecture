/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cycle.Component.PointBoundary
public import Other.AlgebraicGeometry.ComplexPoint.CoclassSheafIso
public import Other.AlgebraicGeometry.Cycle.Support

/-! # Exact point normalization of the general component section

This compares the general smooth-locus/open-transport construction with the
old point coclass. In maximal codimension the singular boundary is proved
empty. Actual scheme-isomorphism and pair-map naturality preserve coefficient
one through the auxiliary ambient open; no point-specific definition is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  (hi : Order.coheight (closedEmbeddingGenericPoint i) = dim X.left)

/-- The ambient image of a complex point of the smooth closed lift of the source. -/
def closedEmbeddingSmoothClosedLiftPointImage
    (a : ComplexPoint (closedEmbeddingSmoothLocusOver i)) : ComplexPoint X :=
  closedEmbeddingSmoothClosedLiftAmbientMap i
    (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i) a)

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
theorem closedEmbeddingSmoothClosedLiftPointImage_mem_support
    (a : ComplexPoint (closedEmbeddingSmoothLocusOver i)) :
    closedEmbeddingSmoothClosedLiftPointImage i a ∈ closedEmbeddingSupport i :=
  (closedEmbeddingSmoothClosedLiftAmbientMap_support i).ge ⟨a, rfl⟩

include hi in
/-- The entire support is the singleton at any closed-lift point. -/
theorem closedEmbeddingSupport_eq_singleton_smoothClosedLiftPointImage
    (a : ComplexPoint (closedEmbeddingSmoothLocusOver i)) :
    closedEmbeddingSupport i = {closedEmbeddingSmoothClosedLiftPointImage i a} := by
  obtain ⟨z, hz⟩ := (range_closedEmbeddingMap i).ge
    (closedEmbeddingSmoothClosedLiftPointImage_mem_support i a)
  rw [← hz]
  exact closedEmbeddingSupport_eq_singleton_of_coheight_eq_dimension X (dim X.left) i hi z

include hi in
/-- Injectivity of the actual ambient open embedding proves the auxiliary singleton support. -/
theorem closedEmbeddingSmoothClosedLift_range_eq_singleton
    (a : ComplexPoint (closedEmbeddingSmoothLocusOver i)) :
    Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)) =
      {Point.map (closedEmbeddingSmoothLocusClosedLiftOver i) a} := by
  rw [← closedEmbeddingSmoothClosedLiftAmbientMap_support,
    closedEmbeddingSupport_eq_singleton_smoothClosedLiftPointImage i hi a]
  ext w
  change closedEmbeddingSmoothClosedLiftAmbientMap i w = _ ↔ w = _
  exact (closedEmbeddingSmoothClosedLiftAmbientMap_isOpenEmbedding i).injective.eq_iff

include hi in
/-- The actual closed-lift source is smooth of dimension zero in maximal codimension. -/
theorem closedEmbeddingPointClosedLift_smoothOfRelativeDimension_zero :
    SmoothOfRelativeDimension 0 (closedEmbeddingSmoothLocusOver i).hom := by
  simpa only [Nat.sub_self] using
    closedEmbeddingSmoothLocusOver_hom_smoothOfRelativeDimension i hi

/-- Comparison of the auxiliary section with its old normalized point coclass.
This is a specialization theorem about the general gluing, not its definition. -/
theorem closedEmbeddingSmoothClosedLiftCoclassSection_eq_oldPoint
    (a : ComplexPoint (closedEmbeddingSmoothLocusOver i)) :
    closedEmbeddingSmoothClosedLiftCoclassSection i hi =
      (letI : IsProjective (closedEmbeddingSmoothLocusAmbientOpenOver i).hom := by
         change IsProjective ((closedEmbeddingSmoothLocusAmbientOpen i).ι ≫ X.hom)
         exact closedEmbeddingSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension i hi
       analyticPointCoclassSupportSection
        (closedEmbeddingSmoothLocusAmbientOpenOver i) (dim X.left)
        (Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)))
        (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i) a)
        ⟨a, rfl⟩ ⊤) := by
  let := closedEmbeddingPointClosedLift_smoothOfRelativeDimension_zero i hi
  let : IsProjective (closedEmbeddingSmoothLocusAmbientOpenOver i).hom := by
    change IsProjective ((closedEmbeddingSmoothLocusAmbientOpen i).ι ≫ X.hom)
    exact closedEmbeddingSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension i hi
  have hsec : closedEmbeddingSmoothClosedLiftCoclassSection i hi =
      smoothClosedSupportCoclassSection
        (closedEmbeddingSmoothLocusAmbientOpenOver i)
        (closedEmbeddingSmoothLocusOver i)
        (closedEmbeddingSmoothLocusClosedLiftOver i) 0 (dim X.left) := by
    have hcast (m : ℕ) (hm : m = 0)
        (hinst : SmoothOfRelativeDimension m (closedEmbeddingSmoothLocusOver i).hom) :
        ((show (dim X.left) - m = (dim X.left) by omega) ▸ @smoothClosedSupportCoclassSection
          (closedEmbeddingSmoothLocusAmbientOpenOver i)
          (closedEmbeddingSmoothLocusOver i)
          (closedEmbeddingSmoothLocusClosedLiftOver i) m (dim X.left) hinst inferInstance inferInstance) =
        smoothClosedSupportCoclassSection
          (closedEmbeddingSmoothLocusAmbientOpenOver i)
          (closedEmbeddingSmoothLocusOver i)
          (closedEmbeddingSmoothLocusClosedLiftOver i) 0 (dim X.left) := by
      subst m
      rfl
    exact hcast ((dim X.left) - (dim X.left)) (Nat.sub_self (dim X.left))
      (closedEmbeddingSmoothLocusOver_hom_smoothOfRelativeDimension i hi)
  rw [hsec, smoothClosedSupportCoclassSection_eq_oldPoint_of_singleton
    (closedEmbeddingSmoothLocusAmbientOpenOver i)
    (closedEmbeddingSmoothLocusOver i)
    (closedEmbeddingSmoothLocusClosedLiftOver i) (dim X.left) a
    (closedEmbeddingSmoothClosedLift_range_eq_singleton i hi a)]
  rfl

/-- The generally transported original-ambient component section agrees exactly with
the old point coclass on its actual boundary-complement open. -/
theorem closedEmbeddingSmoothSupportCoclassSection_eq_point_at_lift
    (a : ComplexPoint (closedEmbeddingSmoothLocusOver i)) :
    closedEmbeddingSmoothSupportCoclassSection i hi =
      analyticPointCoclassSupportSection X (dim X.left) (closedEmbeddingSupport i)
        (closedEmbeddingSmoothClosedLiftPointImage i a)
        (closedEmbeddingSmoothClosedLiftPointImage_mem_support i a)
        (closedEmbeddingSmoothSupportAmbientOpen i) := by
  let := closedEmbeddingSmoothLocusAmbientOpen_ι_isIso_of_coheight_eq_dimension i hi
  let : IsProjective (closedEmbeddingSmoothLocusAmbientOpenOver i).hom := by
    change IsProjective ((closedEmbeddingSmoothLocusAmbientOpen i).ι ≫ X.hom)
    exact closedEmbeddingSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension i hi
  let O := closedEmbeddingSmoothLocusAmbientOpen i
  let Y := closedEmbeddingSmoothLocusAmbientOpenOver i
  let B := Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i))
  let y := Point.map (closedEmbeddingSmoothLocusClosedLiftOver i) a
  let e : Y ≅ X := Over.isoMk (asIso O.ι)
  have hB : Point.map e.hom ⁻¹' closedEmbeddingSupport i = B :=
    closedEmbeddingSmoothClosedLiftAmbientMap_support i
  have ht := analyticPointCoclassSupportSection_schemeIso_transport
    X (dim X.left) Y e (closedEmbeddingSupport i) B hB y ⟨a, rfl⟩ ⊤
  dsimp only [closedEmbeddingSmoothSupportCoclassSection,
    supportRelativeCohomologySectionOnOpen, supportRelativeCohomologySectionOpenImage]
  rw [closedEmbeddingSmoothClosedLiftCoclassSection_eq_oldPoint i hi a]
  have ht' := congrArg
    ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (closedEmbeddingSupport i) (2 * (dim X.left))).obj.map
        (eqToHom (closedEmbeddingSmoothClosedLiftAmbientMap_imageOpen i).symm).op) ht
  refine ht'.trans ?_
  exact analyticPointCoclassSupportSection_restrict X (dim X.left) (closedEmbeddingSupport i)
    (closedEmbeddingSmoothClosedLiftPointImage i a)
    (closedEmbeddingSmoothClosedLiftPointImage_mem_support i a)
    (closedEmbeddingSmoothClosedLiftAmbientMap_imageOpen i).symm.le


/-- The exact point target may be any complex point of the actual component.
The actual open-image and support-image theorems supply a smooth-lift preimage. -/
theorem closedEmbeddingSmoothSupportCoclassSection_eq_analyticPointCoclass
    (z : ComplexPoint (Y)) :
    closedEmbeddingSmoothSupportCoclassSection i hi =
      analyticPointCoclassSupportSection X (dim X.left) (closedEmbeddingSupport i)
        (Point.map i z) (range_closedEmbeddingMap_subset i ⟨z, rfl⟩)
        (closedEmbeddingSmoothSupportAmbientOpen i) := by
  have hzS := range_closedEmbeddingMap_subset i ⟨z, rfl⟩
  have hzU : Point.map i z ∈ closedEmbeddingSmoothSupportAmbientOpen i := by
    rw [closedEmbeddingSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension i hi]
    trivial
  obtain ⟨w, hw⟩ := (closedEmbeddingSmoothLocusAmbientOpen_analytic_image i).ge hzU
  have hwS : w ∈ Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)) := by
    apply (closedEmbeddingSmoothClosedLiftAmbientMap_support i).le
    change Point.map (openInclusion X (closedEmbeddingSmoothLocusAmbientOpen i)) w ∈
      closedEmbeddingSupport i
    rw [hw]
    exact hzS
  obtain ⟨a, ha⟩ := hwS
  have heq : closedEmbeddingSmoothClosedLiftPointImage i a = Point.map i z :=
    (congrArg (closedEmbeddingSmoothClosedLiftAmbientMap i) ha).trans hw
  have hpoints :
      (⟨closedEmbeddingSmoothClosedLiftPointImage i a,
          closedEmbeddingSmoothClosedLiftPointImage_mem_support i a⟩ : closedEmbeddingSupport i) =
        ⟨Point.map i z, hzS⟩ := Subtype.ext heq
  have he := congrArg
    (fun q : closedEmbeddingSupport i =>
      analyticPointCoclassSupportSection X (dim X.left) (closedEmbeddingSupport i) q.1 q.2
        (closedEmbeddingSmoothSupportAmbientOpen i)) hpoints
  exact (closedEmbeddingSmoothSupportCoclassSection_eq_point_at_lift i hi a).trans he

/-- After the PROVED equality U=top, the general component section is exactly the
literal sheafification image of the old GLOBAL point coclass. The displayed map
is only equality transport of opens, not an extra comparison equivalence. -/
theorem closedEmbeddingSmoothSupportCoclassSection_global_point_normalization
    (z : ComplexPoint (Y)) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (closedEmbeddingSupport i) (2 * (dim X.left))).obj.map
        (eqToHom (closedEmbeddingSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension i hi)).op
        (analyticPointCoclassSupportSection X (dim X.left) (closedEmbeddingSupport i)
          (Point.map i z) (range_closedEmbeddingMap_subset i ⟨z, rfl⟩) ⊤) =
      closedEmbeddingSmoothSupportCoclassSection i hi := by
  have h := analyticPointCoclassSupportSection_restrict X (dim X.left) (closedEmbeddingSupport i)
    (Point.map i z) (range_closedEmbeddingMap_subset i ⟨z, rfl⟩)
    (show closedEmbeddingSmoothSupportAmbientOpen i ≤ ⊤ from le_top)
  exact h.trans (closedEmbeddingSmoothSupportCoclassSection_eq_analyticPointCoclass i hi z).symm

end AlgebraicGeometry.ComplexPoint
