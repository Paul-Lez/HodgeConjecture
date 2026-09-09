/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentPointBoundary
public import Other.AlgebraicGeometry.ComplexPointCoclassSheafIso

/-! # Exact point normalization of the general component section

This compares the general smooth-locus/open-transport construction with the
old point coclass. In maximal codimension the singular boundary is proved
empty. Actual scheme-isomorphism and pair-map naturality preserve coefficient
one through the auxiliary ambient open; no point-specific definition is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {d : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = d)

/-- The actual ambient image of a complex point of the component's smooth closed lift. -/
def cycleComponentSmoothClosedLiftPointImage
    (a : ComplexPoint (cycleComponentSmoothLocusOver X x)) : ComplexPoint X :=
  cycleComponentSmoothClosedLiftAmbientMap X x
    (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) a)

theorem cycleComponentSmoothClosedLiftPointImage_mem_support
    (a : ComplexPoint (cycleComponentSmoothLocusOver X x)) :
    cycleComponentSmoothClosedLiftPointImage X x a ∈ cycleComponentSupport X x :=
  (cycleComponentSmoothClosedLiftAmbientMap_support X x).ge ⟨a, rfl⟩

include d hx in
/-- The entire component support is the singleton at any actual closed-lift point. -/
theorem cycleComponentSupport_eq_singleton_smoothClosedLiftPointImage
    (a : ComplexPoint (cycleComponentSmoothLocusOver X x)) :
    cycleComponentSupport X x = {cycleComponentSmoothClosedLiftPointImage X x a} := by
  obtain ⟨z, hz⟩ := (range_cycleComponentMap X x).ge
    (cycleComponentSmoothClosedLiftPointImage_mem_support X x a)
  rw [← hz]
  exact cycleComponentSupport_eq_singleton_of_coheight_eq_dimension X d x hx z

include d hx in
/-- Injectivity of the actual ambient open embedding proves the auxiliary singleton support. -/
theorem cycleComponentSmoothClosedLift_range_eq_singleton
    (a : ComplexPoint (cycleComponentSmoothLocusOver X x)) :
    Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) =
      {Point.map (cycleComponentSmoothLocusClosedLiftOver X x) a} := by
  rw [← cycleComponentSmoothClosedLiftAmbientMap_support,
    cycleComponentSupport_eq_singleton_smoothClosedLiftPointImage X x hx a]
  ext w
  change cycleComponentSmoothClosedLiftAmbientMap X x w = _ ↔ w = _
  exact (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).injective.eq_iff

include hx in
/-- The actual closed-lift source is smooth of dimension zero in maximal codimension. -/
theorem cycleComponentPointClosedLift_smoothOfRelativeDimension_zero :
    SmoothOfRelativeDimension 0 (cycleComponentSmoothClosedLiftStructureMap X x) := by
  simpa only [Nat.sub_self] using
    cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension X x (d := d) hx

/-- Comparison of the auxiliary section with its old normalized point coclass.
This is a specialization theorem about the general gluing, not its definition. -/
theorem cycleComponentSmoothClosedLiftCoclassSection_eq_oldPoint
    (a : ComplexPoint (cycleComponentSmoothLocusOver X x)) :
    cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx =
      (letI : IsProjective (cycleComponentSmoothLocusAmbientOpenOver X x).hom := by
         change IsProjective ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom)
         exact cycleComponentSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension X x hx
       analyticPointCoclassSupportSection
        (cycleComponentSmoothLocusAmbientOpenOver X x) d
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) a)
        ⟨a, rfl⟩ ⊤) := by
  let := cycleComponentPointClosedLift_smoothOfRelativeDimension_zero X x hx
  let : IsProjective (cycleComponentSmoothLocusAmbientOpenOver X x).hom := by
    change IsProjective ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom)
    exact cycleComponentSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension X x hx
  have hsec : cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx =
      smoothClosedSupportCoclassSection
        (cycleComponentSmoothLocusAmbientOpenOver X x)
        (cycleComponentSmoothLocusOver X x)
        (cycleComponentSmoothLocusClosedLiftOver X x) 0 d := by
    have hcast (m : ℕ) (hm : m = 0)
        (hinst : SmoothOfRelativeDimension m (cycleComponentSmoothClosedLiftStructureMap X x)) :
        ((show d - m = d by omega) ▸ @smoothClosedSupportCoclassSection
          (cycleComponentSmoothLocusAmbientOpenOver X x)
          (cycleComponentSmoothLocusOver X x)
          (cycleComponentSmoothLocusClosedLiftOver X x) m d hinst inferInstance inferInstance) =
        smoothClosedSupportCoclassSection
          (cycleComponentSmoothLocusAmbientOpenOver X x)
          (cycleComponentSmoothLocusOver X x)
          (cycleComponentSmoothLocusClosedLiftOver X x) 0 d := by
      subst m
      rfl
    exact hcast (d - d) (Nat.sub_self d)
      (cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension X x (d := d) hx)
  rw [hsec, smoothClosedSupportCoclassSection_eq_oldPoint_of_singleton
    (cycleComponentSmoothLocusAmbientOpenOver X x)
    (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) d a
    (cycleComponentSmoothClosedLift_range_eq_singleton X x hx a)]
  rfl

/-- The generally transported original-ambient component section agrees exactly with
the old point coclass on its actual boundary-complement open. -/
theorem cycleComponentSmoothSupportCoclassSection_eq_point_at_lift
    (a : ComplexPoint (cycleComponentSmoothLocusOver X x)) :
    cycleComponentSmoothSupportCoclassSection X x (d := d) hx =
      analyticPointCoclassSupportSection X d (cycleComponentSupport X x)
        (cycleComponentSmoothClosedLiftPointImage X x a)
        (cycleComponentSmoothClosedLiftPointImage_mem_support X x a)
        (cycleComponentSmoothSupportAmbientOpen X x) := by
  let := cycleComponentSmoothLocusAmbientOpen_ι_isIso_of_coheight_eq_dimension X x hx
  let : IsProjective (cycleComponentSmoothLocusAmbientOpenOver X x).hom := by
    change IsProjective ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom)
    exact cycleComponentSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension X x hx
  let O := cycleComponentSmoothLocusAmbientOpen X x
  let Y := cycleComponentSmoothLocusAmbientOpenOver X x
  let B := Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))
  let y := Point.map (cycleComponentSmoothLocusClosedLiftOver X x) a
  let e : Y ≅ X := Over.isoMk (asIso O.ι)
  have hB : Point.map e.hom ⁻¹' cycleComponentSupport X x = B :=
    cycleComponentSmoothClosedLiftAmbientMap_support X x
  have ht := analyticPointCoclassSupportSection_schemeIso_transport
    X d Y e (cycleComponentSupport X x) B hB y ⟨a, rfl⟩ ⊤
  dsimp only [cycleComponentSmoothSupportCoclassSection,
    supportRelativeCohomologySectionOnOpen, supportRelativeCohomologySectionOpenImage]
  rw [cycleComponentSmoothClosedLiftCoclassSection_eq_oldPoint X x hx a]
  have ht' := congrArg
    ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * d)).obj.map
        (eqToHom (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x).symm).op) ht
  refine ht'.trans ?_
  exact analyticPointCoclassSupportSection_restrict X d (cycleComponentSupport X x)
    (cycleComponentSmoothClosedLiftPointImage X x a)
    (cycleComponentSmoothClosedLiftPointImage_mem_support X x a)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x).symm.le


/-- The exact point target may be any complex point of the actual component.
The actual open-image and support-image theorems supply a smooth-lift preimage. -/
theorem cycleComponentSmoothSupportCoclassSection_eq_analyticPointCoclass
    (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))) :
    cycleComponentSmoothSupportCoclassSection X x (d := d) hx =
      analyticPointCoclassSupportSection X d (cycleComponentSupport X x)
        (cycleComponentMap X x z) (range_cycleComponentMap_subset X x ⟨z, rfl⟩)
        (cycleComponentSmoothSupportAmbientOpen X x) := by
  have hzS := range_cycleComponentMap_subset X x ⟨z, rfl⟩
  have hzU : cycleComponentMap X x z ∈ cycleComponentSmoothSupportAmbientOpen X x := by
    rw [cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension X x hx]
    trivial
  obtain ⟨w, hw⟩ := (cycleComponentSmoothLocusAmbientOpen_analytic_image X x).ge hzU
  have hwS : w ∈ Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) := by
    apply (cycleComponentSmoothClosedLiftAmbientMap_support X x).le
    change Point.map (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)) w ∈
      cycleComponentSupport X x
    rw [hw]
    exact hzS
  obtain ⟨a, ha⟩ := hwS
  have heq : cycleComponentSmoothClosedLiftPointImage X x a = cycleComponentMap X x z :=
    (congrArg (cycleComponentSmoothClosedLiftAmbientMap X x) ha).trans hw
  have hpoints :
      (⟨cycleComponentSmoothClosedLiftPointImage X x a,
          cycleComponentSmoothClosedLiftPointImage_mem_support X x a⟩ : cycleComponentSupport X x) =
        ⟨cycleComponentMap X x z, hzS⟩ := Subtype.ext heq
  have he := congrArg
    (fun q : cycleComponentSupport X x =>
      analyticPointCoclassSupportSection X d (cycleComponentSupport X x) q.1 q.2
        (cycleComponentSmoothSupportAmbientOpen X x)) hpoints
  exact (cycleComponentSmoothSupportCoclassSection_eq_point_at_lift X x hx a).trans he

/-- After the PROVED equality U=top, the general component section is exactly the
literal sheafification image of the old GLOBAL point coclass. The displayed map
is only equality transport of opens, not an extra comparison equivalence. -/
theorem cycleComponentSmoothSupportCoclassSection_global_point_normalization
    (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * d)).obj.map
        (eqToHom (cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension X x hx)).op
        (analyticPointCoclassSupportSection X d (cycleComponentSupport X x)
          (cycleComponentMap X x z) (range_cycleComponentMap_subset X x ⟨z, rfl⟩) ⊤) =
      cycleComponentSmoothSupportCoclassSection X x (d := d) hx := by
  have h := analyticPointCoclassSupportSection_restrict X d (cycleComponentSupport X x)
    (cycleComponentMap X x z) (range_cycleComponentMap_subset X x ⟨z, rfl⟩)
    (show cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤ from le_top)
  exact h.trans (cycleComponentSmoothSupportCoclassSection_eq_analyticPointCoclass X x hx z).symm

end AlgebraicGeometry.ComplexPoint
