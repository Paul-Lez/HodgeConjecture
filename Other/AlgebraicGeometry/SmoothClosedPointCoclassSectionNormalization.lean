/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedSupportCoclassSection
public import Other.AlgebraicGeometry.SmoothClosedPointPurityNormalization

/-!
# Exact point comparison for the global smooth-support coclass section

This is a comparison theorem, not the definition of general purity. In the
singleton case the actual global section constructed by normal-chart gluing is
the sheafification image of the old, exactly normalized point coclass. We also
construct the actual closed immersion of every complex point, so the final
point theorem takes no singleton-image or smooth-source hypothesis as input.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open TopCat.Presheaf

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]

/-- The actual inclusion from a neighborhood/support pair into the pair with one
point removed. It exists when the distinguished point belongs to the support. -/
def neighborhoodSupportToPointPairMap (V S : Set M) (x : M) (hx : x ∈ S) :
    neighborhoodSupportComplementPair V S ⟶ pointComplementPair x :=
  TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun w => ⟨w.1.1, fun h => w.2 (h ▸ hx)⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩) rfl

/-- Literal ambient inclusions factor through every nested neighborhood. -/
@[simp] theorem neighborhoodSupportInclusionPairMap_toPoint {U V : Set M}
    (hUV : U ⊆ V) (S : Set M) (x : M) (hx : x ∈ S) :
    neighborhoodSupportInclusionPairMap hUV S ≫ neighborhoodSupportToPointPairMap V S x hx =
      neighborhoodSupportToPointPairMap U S x hx := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (d : ℕ)
  [SmoothOfRelativeDimension 0 Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] [IsProjective X.hom]

/-- The old ambient point coclass, pulled back to the literal whole-open pair,
then sent through the actual sheafification unit. -/
def smoothClosedOldPointCoclassSection (z : ComplexPoint Y) :
    (smoothClosedSupportCoclassSheaf X Y i 0 d).obj.obj (op ⊤) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * d)).app (op ⊤)
      (relativeCohomologyMap ℚ (2 * d)
        (neighborhoodSupportToPointPairMap (⊤ : Opens (ComplexPoint X))
          (Set.range (Point.map i)) (Point.map i z) ⟨z, rfl⟩)
        (analyticPointLocalCoclass X d (Point.map i z)))

omit [IsProjective X.hom] in
/-- The literal local-to-point map is the map used by the existing exact
normal-slice/point comparison. -/
theorem neighborhoodSupportToPointPairMap_eq_smoothClosedPointNeighborhoodPairMap
    (z : ComplexPoint Y) (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V) :
    neighborhoodSupportToPointPairMap
      (smoothClosedSupportNeighborhood X Y i 0 d z V hzV)
      (Set.range (Point.map i)) (Point.map i z) ⟨z, rfl⟩ =
      smoothClosedPointNeighborhoodPairMap X Y i d z V hzV := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- At its distinguished point the old global coclass has exactly the germ of the
general normal coclass, with coefficient one. -/
theorem smoothClosedOldPointCoclassSection_germ_eq_normalCoclass
    (z : ComplexPoint Y) (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V) :
    (smoothClosedSupportCoclassSheaf X Y i 0 d).presheaf.Γgerm (Point.map i z)
      (smoothClosedOldPointCoclassSection X Y i d z) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * d)
      (smoothClosedSupportNeighborhood X Y i 0 d z V hzV)
      (Point.map i z) (mem_smoothClosedSupportNeighborhood X Y i 0 d z V hzV)
      (smoothClosedSupportNormalCoclass X Y i 0 d z V hzV) := by
  let W := smoothClosedSupportNeighborhood X Y i 0 d z V hzV
  let a := relativeCohomologyMap ℚ (2 * d)
    (neighborhoodSupportToPointPairMap (⊤ : Opens (ComplexPoint X))
      (Set.range (Point.map i)) (Point.map i z) ⟨z, rfl⟩)
    (analyticPointLocalCoclass X d (Point.map i z))
  change supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * d) ⊤ (Point.map i z) (by trivial) a = _
  rw [← supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * d) (show W ≤ ⊤ from le_top)
    (Point.map i z) (mem_smoothClosedSupportNeighborhood X Y i 0 d z V hzV)]
  congr 1
  dsimp only [a]
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    neighborhoodSupportInclusionPairMap_toPoint]
  rw [neighborhoodSupportToPointPairMap_eq_smoothClosedPointNeighborhoodPairMap]
  exact (smoothClosedPointNormalCoclass_eq_analyticPointLocalCoclass X Y i d z V hzV).symm

omit [SmoothOfRelativeDimension 0 Y.hom] in
/-- The old global point image vanishes off the actual closed support. -/
theorem smoothClosedOldPointCoclassSection_germ_eq_zero
    (z : ComplexPoint Y) (x : ComplexPoint X) (hx : x ∉ Set.range (Point.map i)) :
    (smoothClosedSupportCoclassSheaf X Y i 0 d).presheaf.Γgerm x
      (smoothClosedOldPointCoclassSection X Y i d z) = 0 :=
  supportRelativeCohomologyGerm_eq_zero_of_not_mem (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * d) (isClosed_range_map_of_closedImmersion i)
    ⊤ x (by trivial) hx _

/-- Explicit singleton-case comparison: the general glued normal section agrees
with the actual sheafification image of the old ambient point coclass. -/
theorem smoothClosedSupportCoclassSection_eq_oldPoint_of_singleton
    (z : ComplexPoint Y) (hS : Set.range (Point.map i) = {Point.map i z}) :
    smoothClosedSupportCoclassSection X Y i 0 d =
      smoothClosedOldPointCoclassSection X Y i d z := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf X Y i 0 d)
  intro x _
  by_cases hx : x ∈ Set.range (Point.map i)
  · have heq : x = Point.map i z := by simpa only [hS, Set.mem_singleton_iff] using hx
    subst x
    exact (smoothClosedSupportCoclassSection_germ_eq_normalCoclass
      X Y i 0 d z ⊤ (by trivial)).trans
      (smoothClosedOldPointCoclassSection_germ_eq_normalCoclass
        X Y i d z ⊤ (by trivial)).symm
  · exact (smoothClosedSupportCoclassSection_germ_eq_zero X Y i 0 d x hx).trans
      (smoothClosedOldPointCoclassSection_germ_eq_zero X Y i d z x hx).symm

section ActualPoint

variable (X : Over (Spec (.of ℂ)))

/-- The identity complex point of the base scheme over itself. -/
def complexSpecIdentityPoint : ComplexPoint (Over.mk (𝟙 (Spec (.of ℂ)))) :=
  𝟙 _

local instance complexSpecIdentitySmooth :
    SmoothOfRelativeDimension 0 (Over.mk (𝟙 (Spec (.of ℂ)))).hom := by
  change SmoothOfRelativeDimension 0 (𝟙 (Spec (.of ℂ)))
  infer_instance

/-- There is just one complex point of the base over itself. -/
theorem complexSpecPoint_eq_identity (w : ComplexPoint (Over.mk (𝟙 (Spec (.of ℂ))))) :
    w = complexSpecIdentityPoint :=
  (Over.mkIdTerminal (X := Spec (.of ℂ))).hom_ext w complexSpecIdentityPoint

/-- The actual scheme morphism represented by any complex point is a closed
immersion; no point-immersion input is supplied. -/
theorem complexPoint_isClosedImmersion (z : ComplexPoint X) :
    IsClosedImmersion z.left :=
  AlgebraicGeometry.isClosedImmersion_of_comp_eq_id X.hom z.left z.w

@[simp] theorem map_complexSpecIdentityPoint (z : ComplexPoint X) :
    Point.map z complexSpecIdentityPoint = z := by
  simp [Point.map, complexSpecIdentityPoint]

/-- The actual analytic image of the point closed immersion is its singleton. -/
theorem range_map_complexPoint (z : ComplexPoint X) :
    Set.range (Point.map z) = {z} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    rw [complexSpecPoint_eq_identity w, map_complexSpecIdentityPoint]
    exact Set.mem_singleton _
  · intro hx
    exact ⟨complexSpecIdentityPoint, (map_complexSpecIdentityPoint X z).trans
      (Set.mem_singleton_iff.mp hx).symm⟩

variable (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom]

/-- The general smooth-support section specialized to the actual point immersion.
It is still defined by the same arbitrary-dimensional normal-chart gluing. -/
def complexPointSmoothSupportCoclassSection (z : ComplexPoint X) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (Set.range (Point.map z)) (2 * d)).obj.obj (op ⊤) := by
  letI := complexPoint_isClosedImmersion X z
  exact smoothClosedSupportCoclassSection X (Over.mk (𝟙 _)) z 0 d

/-- The actual sheafification image of the pre-existing global point coclass.
The only adapter is the literal inclusion of the whole-open subtype pair. -/
def analyticPointLocalCoclassSheafSection (z : ComplexPoint X) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (Set.range (Point.map z)) (2 * d)).obj.obj (op ⊤) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
    (Set.range (Point.map z)) (2 * d)).app (op ⊤)
      (relativeCohomologyMap ℚ (2 * d)
        (neighborhoodSupportToPointPairMap (⊤ : Opens (ComplexPoint X))
          (Set.range (Point.map z)) z
          ⟨complexSpecIdentityPoint, map_complexSpecIdentityPoint X z⟩)
        (analyticPointLocalCoclass X d z))

/-- Unconditional exact point normalization of the general globally glued
smooth-support section. The support-singleton equality and smooth point immersion
are constructed, not hypotheses; no rescaling or point-case definition is used. -/
theorem complexPointSmoothSupportCoclassSection_eq_analyticPointLocalCoclassSheafSection
    (z : ComplexPoint X) :
    complexPointSmoothSupportCoclassSection X d z =
      analyticPointLocalCoclassSheafSection X d z := by
  let := complexPoint_isClosedImmersion X z
  have hS : Set.range (Point.map z) =
      {Point.map z complexSpecIdentityPoint} := by
    rw [map_complexSpecIdentityPoint, range_map_complexPoint]
  change smoothClosedSupportCoclassSection X (Over.mk (𝟙 _)) z 0 d = _
  rw [smoothClosedSupportCoclassSection_eq_oldPoint_of_singleton
    X (Over.mk (𝟙 _)) z d complexSpecIdentityPoint hS]
  dsimp only [smoothClosedOldPointCoclassSection, analyticPointLocalCoclassSheafSection]
  apply congrArg ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
    (Set.range (Point.map z)) (2 * d)).app (op ⊤))
  let f : Set.range (Point.map z) → RelativeCohomology ℚ
      (neighborhoodSupportComplementPair ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
        (Set.range (Point.map z))) (2 * d) := fun x =>
    relativeCohomologyMap ℚ (2 * d)
      (neighborhoodSupportToPointPairMap ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
        (Set.range (Point.map z)) x.1 x.2)
      (analyticPointLocalCoclass X d x.1)
  have heq :
    (⟨Point.map z complexSpecIdentityPoint, ⟨complexSpecIdentityPoint, rfl⟩⟩ :
      Set.range (Point.map z)) =
    ⟨z, complexSpecIdentityPoint, map_complexSpecIdentityPoint X z⟩ :=
      Subtype.ext (map_complexSpecIdentityPoint X z)
  have hh := congrArg f heq
  exact hh

end ActualPoint

end AlgebraicGeometry.ComplexPoint
