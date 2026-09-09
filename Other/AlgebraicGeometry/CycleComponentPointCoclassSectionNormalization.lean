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

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X)
  {d : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = d)

/-- The actual ambient image of a complex point of the component's smooth closed lift. -/
def cycleComponentSmoothClosedLiftPointImage
    (a : ComplexPoint (cycleComponentι X x ≫ s).smoothLocus
      (cycleComponentSmoothClosedLiftStructureMap s x)) : ComplexPoint X s :=
  cycleComponentSmoothClosedLiftAmbientMap s x
    (Point.map (cycleComponentSmoothLocusClosedLift s x)
      (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl a)

theorem cycleComponentSmoothClosedLiftPointImage_mem_support
    (a : ComplexPoint (cycleComponentι X x ≫ s).smoothLocus
      (cycleComponentSmoothClosedLiftStructureMap s x)) :
    cycleComponentSmoothClosedLiftPointImage s x a ∈ cycleComponentSupport s x :=
  (cycleComponentSmoothClosedLiftAmbientMap_support s x).ge ⟨a, rfl⟩

include d hx in
/-- The entire component support is the singleton at any actual closed-lift point. -/
theorem cycleComponentSupport_eq_singleton_smoothClosedLiftPointImage
    (a : ComplexPoint (cycleComponentι X x ≫ s).smoothLocus
      (cycleComponentSmoothClosedLiftStructureMap s x)) :
    cycleComponentSupport s x = {cycleComponentSmoothClosedLiftPointImage s x a} := by
  obtain ⟨z, hz⟩ := (range_cycleComponentMap s x).ge
    (cycleComponentSmoothClosedLiftPointImage_mem_support s x a)
  rw [← hz]
  exact cycleComponentSupport_eq_singleton_of_coheight_eq_dimension s d x hx z

include d hx in
/-- Injectivity of the actual ambient open embedding proves the auxiliary singleton support. -/
theorem cycleComponentSmoothClosedLift_range_eq_singleton
    (a : ComplexPoint (cycleComponentι X x ≫ s).smoothLocus
      (cycleComponentSmoothClosedLiftStructureMap s x)) :
    Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
      (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl) =
      {Point.map (cycleComponentSmoothLocusClosedLift s x)
        (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl a} := by
  rw [← cycleComponentSmoothClosedLiftAmbientMap_support,
    cycleComponentSupport_eq_singleton_smoothClosedLiftPointImage s x hx a]
  ext w
  change cycleComponentSmoothClosedLiftAmbientMap s x w = _ ↔ w = _
  exact (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding s x).injective.eq_iff

include hx in
/-- The actual closed-lift source is smooth of dimension zero in maximal codimension. -/
theorem cycleComponentPointClosedLift_smoothOfRelativeDimension_zero :
    SmoothOfRelativeDimension 0 (cycleComponentSmoothClosedLiftStructureMap s x) := by
  simpa only [Nat.sub_self] using
    cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension s x (d := d) hx

/-- Comparison of the auxiliary section with its old normalized point coclass.
This is a specialization theorem about the general gluing, not its definition. -/
theorem cycleComponentSmoothClosedLiftCoclassSection_eq_oldPoint
    (a : ComplexPoint (cycleComponentι X x ≫ s).smoothLocus
      (cycleComponentSmoothClosedLiftStructureMap s x)) :
    cycleComponentSmoothClosedLiftCoclassSection s x (d := d) hx =
      (letI := cycleComponentSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension s x hx
       analyticPointCoclassSupportSection
        ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s) d
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
          (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl))
        (Point.map (cycleComponentSmoothLocusClosedLift s x)
          (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl a)
        ⟨a, rfl⟩ ⊤) := by
  let := cycleComponentPointClosedLift_smoothOfRelativeDimension_zero s x hx
  let := cycleComponentSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension s x hx
  have hsec : cycleComponentSmoothClosedLiftCoclassSection s x (d := d) hx =
      smoothClosedSupportCoclassSection ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s)
        (cycleComponentSmoothClosedLiftStructureMap s x)
        (cycleComponentSmoothLocusClosedLift s x) rfl 0 d := by
    have hcast (m : ℕ) (hm : m = 0)
        (hinst : SmoothOfRelativeDimension m (cycleComponentSmoothClosedLiftStructureMap s x)) :
        ((show d - m = d by omega) ▸ @smoothClosedSupportCoclassSection _ _
          ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s)
          (cycleComponentSmoothClosedLiftStructureMap s x)
          (cycleComponentSmoothLocusClosedLift s x) rfl m d hinst inferInstance inferInstance) =
        smoothClosedSupportCoclassSection ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s)
          (cycleComponentSmoothClosedLiftStructureMap s x)
          (cycleComponentSmoothLocusClosedLift s x) rfl 0 d := by
      subst m
      rfl
    exact hcast (d - d) (Nat.sub_self d)
      (cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension s x (d := d) hx)
  rw [hsec, smoothClosedSupportCoclassSection_eq_oldPoint_of_singleton
    ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s)
    (cycleComponentSmoothClosedLiftStructureMap s x)
    (cycleComponentSmoothLocusClosedLift s x) rfl d a
    (cycleComponentSmoothClosedLift_range_eq_singleton s x hx a)]
  rfl

/-- The generally transported original-ambient component section agrees exactly with
the old point coclass on its actual boundary-complement open. -/
theorem cycleComponentSmoothSupportCoclassSection_eq_point_at_lift
    (a : ComplexPoint (cycleComponentι X x ≫ s).smoothLocus
      (cycleComponentSmoothClosedLiftStructureMap s x)) :
    cycleComponentSmoothSupportCoclassSection s x (d := d) hx =
      analyticPointCoclassSupportSection s d (cycleComponentSupport s x)
        (cycleComponentSmoothClosedLiftPointImage s x a)
        (cycleComponentSmoothClosedLiftPointImage_mem_support s x a)
        (cycleComponentSmoothSupportAmbientOpen s x) := by
  let := cycleComponentSmoothLocusAmbientOpen_ι_isIso_of_coheight_eq_dimension s x hx
  let := cycleComponentSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension s x hx
  let O := cycleComponentSmoothLocusAmbientOpen s x
  let B := Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
    (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl)
  let y := Point.map (cycleComponentSmoothLocusClosedLift s x)
    (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl a
  let e := asIso O.ι
  have hB : Point.map e.hom (structureMap := O.ι ≫ s) rfl ⁻¹' cycleComponentSupport s x = B :=
    cycleComponentSmoothClosedLiftAmbientMap_support s x
  have ht := analyticPointCoclassSupportSection_schemeIso_transport
    s d (O.ι ≫ s) e rfl (cycleComponentSupport s x) B hB y ⟨a, rfl⟩ ⊤
  dsimp only [cycleComponentSmoothSupportCoclassSection,
    supportRelativeCohomologySectionOnOpen, supportRelativeCohomologySectionOpenImage]
  rw [cycleComponentSmoothClosedLiftCoclassSection_eq_oldPoint s x hx a]
  have ht' := congrArg
    ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s))
      (cycleComponentSupport s x) (2 * d)).obj.map
        (eqToHom (cycleComponentSmoothClosedLiftAmbientMap_imageOpen s x).symm).op) ht
  refine ht'.trans ?_
  exact analyticPointCoclassSupportSection_restrict s d (cycleComponentSupport s x)
    (cycleComponentSmoothClosedLiftPointImage s x a)
    (cycleComponentSmoothClosedLiftPointImage_mem_support s x a)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen s x).symm.le


/-- The exact point target may be any complex point of the actual component.
The actual open-image and support-image theorems supply a smooth-lift preimage. -/
theorem cycleComponentSmoothSupportCoclassSection_eq_analyticPointCoclass
    (z : ComplexPoint (cycleComponent X x) (cycleComponentι X x ≫ s)) :
    cycleComponentSmoothSupportCoclassSection s x (d := d) hx =
      analyticPointCoclassSupportSection s d (cycleComponentSupport s x)
        (cycleComponentMap s x z) (range_cycleComponentMap_subset s x ⟨z, rfl⟩)
        (cycleComponentSmoothSupportAmbientOpen s x) := by
  have hzS := range_cycleComponentMap_subset s x ⟨z, rfl⟩
  have hzU : cycleComponentMap s x z ∈ cycleComponentSmoothSupportAmbientOpen s x := by
    rw [cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension s x hx]
    trivial
  obtain ⟨w, hw⟩ := (cycleComponentSmoothLocusAmbientOpen_analytic_image s x).ge hzU
  have hwS : w ∈ Set.range (Point.map (cycleComponentSmoothLocusClosedLift s x)
      (structureMap := cycleComponentSmoothClosedLiftStructureMap s x) rfl) := by
    apply (cycleComponentSmoothClosedLiftAmbientMap_support s x).le
    change Point.map (cycleComponentSmoothLocusAmbientOpen s x).ι rfl w ∈ cycleComponentSupport s x
    rw [hw]
    exact hzS
  obtain ⟨a, ha⟩ := hwS
  have heq : cycleComponentSmoothClosedLiftPointImage s x a = cycleComponentMap s x z :=
    (congrArg (cycleComponentSmoothClosedLiftAmbientMap s x) ha).trans hw
  have hpoints :
      (⟨cycleComponentSmoothClosedLiftPointImage s x a,
          cycleComponentSmoothClosedLiftPointImage_mem_support s x a⟩ : cycleComponentSupport s x) =
        ⟨cycleComponentMap s x z, hzS⟩ := Subtype.ext heq
  have he := congrArg
    (fun q : cycleComponentSupport s x =>
      analyticPointCoclassSupportSection s d (cycleComponentSupport s x) q.1 q.2
        (cycleComponentSmoothSupportAmbientOpen s x)) hpoints
  exact (cycleComponentSmoothSupportCoclassSection_eq_point_at_lift s x hx a).trans he

/-- After the PROVED equality U=top, the general component section is exactly the
literal sheafification image of the old GLOBAL point coclass. The displayed map
is only equality transport of opens, not an extra comparison equivalence. -/
theorem cycleComponentSmoothSupportCoclassSection_global_point_normalization
    (z : ComplexPoint (cycleComponent X x) (cycleComponentι X x ≫ s)) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s))
      (cycleComponentSupport s x) (2 * d)).obj.map
        (eqToHom (cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension s x hx)).op
        (analyticPointCoclassSupportSection s d (cycleComponentSupport s x)
          (cycleComponentMap s x z) (range_cycleComponentMap_subset s x ⟨z, rfl⟩) ⊤) =
      cycleComponentSmoothSupportCoclassSection s x (d := d) hx := by
  have h := analyticPointCoclassSupportSection_restrict s d (cycleComponentSupport s x)
    (cycleComponentMap s x z) (range_cycleComponentMap_subset s x ⟨z, rfl⟩)
    (show cycleComponentSmoothSupportAmbientOpen s x ≤ ⊤ from le_top)
  exact h.trans (cycleComponentSmoothSupportCoclassSection_eq_analyticPointCoclass s x hx z).symm

end AlgebraicGeometry.ComplexPoint
