/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cycle.Component.PointBoundary
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus
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

open CycleComponent

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  (hx : Order.coheight x = dim X.left)

/-- The actual ambient image of a complex point of the component's smooth closed lift. -/
def cycleComponentSmoothClosedLiftPointImage
    (a : ComplexPoint (smoothLocusOver X x)) : ComplexPoint X :=
  cycleComponentSmoothClosedLiftAmbientMap X x
    (Point.map (smoothClosedLift X x) a)

omit [IsIntegral X.left] in
theorem cycleComponentSmoothClosedLiftPointImage_mem_support
    (a : ComplexPoint (smoothLocusOver X x)) :
    cycleComponentSmoothClosedLiftPointImage X x a ∈ x‾(ℂ) :=
  (cycleComponentSmoothClosedLiftAmbientMap_support X x).ge ⟨a, rfl⟩

include hx in
/-- The entire component support is the singleton at any actual closed-lift point. -/
theorem cycleComponentSupport_eq_singleton_smoothClosedLiftPointImage
    (a : ComplexPoint (smoothLocusOver X x)) :
    (x‾(ℂ) : Set (ComplexPoint X)) =
      {cycleComponentSmoothClosedLiftPointImage X x a} := by
  obtain ⟨z, hz⟩ := (range_map_ι X x).ge
    (cycleComponentSmoothClosedLiftPointImage_mem_support X x a)
  rw [← hz]
  exact cycleComponentSupport_eq_singleton_of_coheight_eq_dimension X (dim X.left) x hx z

include hx in
/-- Injectivity of the actual ambient open embedding proves the auxiliary singleton support. -/
theorem cycleComponentSmoothClosedLift_range_eq_singleton
    (a : ComplexPoint (smoothLocusOver X x)) :
    Set.range (Point.map (smoothClosedLift X x)) =
      {Point.map (smoothClosedLift X x) a} := by
  rw [← cycleComponentSmoothClosedLiftAmbientMap_support,
    cycleComponentSupport_eq_singleton_smoothClosedLiftPointImage X x hx a]
  ext w
  change cycleComponentSmoothClosedLiftAmbientMap X x w = _ ↔ w = _
  exact (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).injective.eq_iff

include hx in
/-- The actual closed-lift source is smooth of dimension zero in maximal codimension. -/
theorem cycleComponentPointClosedLift_smoothOfRelativeDimension_zero :
    SmoothOfRelativeDimension 0 (smoothLocusOver X x).hom := by
  simpa only [Nat.sub_self] using
    smoothLocusOver_smoothOfRelativeDimension X x hx

/-- Comparison of the auxiliary section with its old normalized point coclass.
This is a specialization theorem about the general gluing, not its definition. -/
theorem cycleComponentSmoothClosedLiftCoclassSection_eq_oldPoint
    (a : ComplexPoint (smoothLocusOver X x)) :
    cycleComponentSmoothClosedLiftCoclassSection X x hx =
      (letI : IsProjective (smoothAmbientOpenOver X x).hom := by
         change IsProjective ((smoothAmbientOpen X x).ι ≫ X.hom)
         exact smoothAmbientOpen_isProjective_of_coheight_eq_dimension X x hx
       analyticPointCoclassSupportSection
        (smoothAmbientOpenOver X x) (dim X.left)
        (Set.range (Point.map (smoothClosedLift X x)))
        (Point.map (smoothClosedLift X x) a)
        ⟨a, rfl⟩ ⊤) := by
  let := cycleComponentPointClosedLift_smoothOfRelativeDimension_zero X x hx
  let : IsProjective (smoothAmbientOpenOver X x).hom := by
    change IsProjective ((smoothAmbientOpen X x).ι ≫ X.hom)
    exact smoothAmbientOpen_isProjective_of_coheight_eq_dimension X x hx
  have hsec : cycleComponentSmoothClosedLiftCoclassSection X x hx =
      smoothClosedSupportCoclassSection
        (smoothAmbientOpenOver X x)
        (smoothLocusOver X x)
        (smoothClosedLift X x) 0 (dim X.left) := by
    have hcast (m : ℕ) (hm : m = 0)
        (hinst : SmoothOfRelativeDimension m (smoothLocusOver X x).hom) :
        ((show (dim X.left) - m = (dim X.left) by omega) ▸ @smoothClosedSupportCoclassSection
          (smoothAmbientOpenOver X x)
          (smoothLocusOver X x)
          (smoothClosedLift X x) m (dim X.left) hinst inferInstance inferInstance) =
        smoothClosedSupportCoclassSection
          (smoothAmbientOpenOver X x)
          (smoothLocusOver X x)
          (smoothClosedLift X x) 0 (dim X.left) := by
      subst m
      rfl
    exact hcast ((dim X.left) - (dim X.left)) (Nat.sub_self (dim X.left))
      (smoothLocusOver_smoothOfRelativeDimension X x hx)
  rw [hsec, smoothClosedSupportCoclassSection_eq_oldPoint_of_singleton
    (smoothAmbientOpenOver X x)
    (smoothLocusOver X x)
    (smoothClosedLift X x) (dim X.left) a
    (cycleComponentSmoothClosedLift_range_eq_singleton X x hx a)]
  rfl

/-- The generally transported original-ambient component section agrees exactly with
the old point coclass on its actual boundary-complement open. -/
theorem cycleComponentSmoothSupportCoclassSection_eq_point_at_lift
    (a : ComplexPoint (smoothLocusOver X x)) :
    cycleComponentSmoothSupportCoclassSection X x hx =
      analyticPointCoclassSupportSection X (dim X.left) (x‾(ℂ))
        (cycleComponentSmoothClosedLiftPointImage X x a)
        (cycleComponentSmoothClosedLiftPointImage_mem_support X x a)
        (x‾ˢⁱⁿᵍ(ℂ)ᶜ) := by
  let := smoothAmbientOpen_ι_isIso_of_coheight_eq_dimension X x hx
  let : IsProjective (smoothAmbientOpenOver X x).hom := by
    change IsProjective ((smoothAmbientOpen X x).ι ≫ X.hom)
    exact smoothAmbientOpen_isProjective_of_coheight_eq_dimension X x hx
  let O := smoothAmbientOpen X x
  let Y := smoothAmbientOpenOver X x
  let B := Set.range (Point.map (smoothClosedLift X x))
  let y := Point.map (smoothClosedLift X x) a
  let e : Y ≅ X := Over.isoMk (asIso O.ι)
  have hB : Point.map e.hom ⁻¹' x‾(ℂ) = B :=
    cycleComponentSmoothClosedLiftAmbientMap_support X x
  have ht := analyticPointCoclassSupportSection_schemeIso_transport
    X (dim X.left) Y e (x‾(ℂ)) B hB y ⟨a, rfl⟩ ⊤
  dsimp only [cycleComponentSmoothSupportCoclassSection,
    supportRelativeCohomologySectionOnOpen, supportRelativeCohomologySectionOpenImage]
  rw [cycleComponentSmoothClosedLiftCoclassSection_eq_oldPoint X x hx a]
  have ht' := congrArg
    ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (x‾(ℂ)) (2 * (dim X.left))).obj.map
        (eqToHom (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x).symm).op) ht
  refine ht'.trans ?_
  exact analyticPointCoclassSupportSection_restrict X (dim X.left) (x‾(ℂ))
    (cycleComponentSmoothClosedLiftPointImage X x a)
    (cycleComponentSmoothClosedLiftPointImage_mem_support X x a)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x).symm.le


/-- The exact point target may be any complex point of the actual component.
The actual open-image and support-image theorems supply a smooth-lift preimage. -/
theorem cycleComponentSmoothSupportCoclassSection_eq_analyticPointCoclass
    (z : ComplexPoint (over X x)) :
    cycleComponentSmoothSupportCoclassSection X x hx =
      analyticPointCoclassSupportSection X (dim X.left) (x‾(ℂ))
        (Point.map (CycleComponent.ι X x) z) ((range_map_ι X x).le ⟨z, rfl⟩)
        (x‾ˢⁱⁿᵍ(ℂ)ᶜ) := by
  have hzS := (range_map_ι X x).le ⟨z, rfl⟩
  have hzU : Point.map (CycleComponent.ι X x) z ∈ x‾ˢⁱⁿᵍ(ℂ)ᶜ := by
    rw [analyticSmoothAmbientOpen_eq_top_of_coheight_eq_dimension X x hx]
    trivial
  obtain ⟨w, hw⟩ := (range_map_openInclusion X (smoothAmbientOpen X x)).ge hzU
  have hwS : w ∈ Set.range (Point.map (smoothClosedLift X x)) := by
    apply (cycleComponentSmoothClosedLiftAmbientMap_support X x).le
    change Point.map (openInclusion X (smoothAmbientOpen X x)) w ∈
      x‾(ℂ)
    rw [hw]
    exact hzS
  obtain ⟨a, ha⟩ := hwS
  have heq : cycleComponentSmoothClosedLiftPointImage X x a = Point.map (CycleComponent.ι X x) z :=
    (congrArg (cycleComponentSmoothClosedLiftAmbientMap X x) ha).trans hw
  have hpoints :
      (⟨cycleComponentSmoothClosedLiftPointImage X x a,
          cycleComponentSmoothClosedLiftPointImage_mem_support X x a⟩ : x‾(ℂ)) =
        ⟨Point.map (CycleComponent.ι X x) z, hzS⟩ := Subtype.ext heq
  have he := congrArg
    (fun q : x‾(ℂ) =>
      analyticPointCoclassSupportSection X (dim X.left) (x‾(ℂ)) q.1 q.2
        (x‾ˢⁱⁿᵍ(ℂ)ᶜ)) hpoints
  exact (cycleComponentSmoothSupportCoclassSection_eq_point_at_lift X x hx a).trans he

/-- After the PROVED equality U=top, the general component section is exactly the
literal sheafification image of the old GLOBAL point coclass. The displayed map
is only equality transport of opens, not an extra comparison equivalence. -/
theorem cycleComponentSmoothSupportCoclassSection_global_point_normalization
    (z : ComplexPoint (over X x)) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (x‾(ℂ)) (2 * (dim X.left))).obj.map
        (eqToHom (analyticSmoothAmbientOpen_eq_top_of_coheight_eq_dimension X x hx)).op
        (analyticPointCoclassSupportSection X (dim X.left) (x‾(ℂ))
          (Point.map (CycleComponent.ι X x) z) ((range_map_ι X x).le ⟨z, rfl⟩) ⊤) =
      cycleComponentSmoothSupportCoclassSection X x hx := by
  have h := analyticPointCoclassSupportSection_restrict X (dim X.left) (x‾(ℂ))
    (Point.map (CycleComponent.ι X x) z) ((range_map_ι X x).le ⟨z, rfl⟩)
    (show x‾ˢⁱⁿᵍ(ℂ)ᶜ ≤ ⊤ from le_top)
  exact h.trans (cycleComponentSmoothSupportCoclassSection_eq_analyticPointCoclass X x hx z).symm

end AlgebraicGeometry.ComplexPoint
