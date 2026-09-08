/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportCoclassSection
public import HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedPointPurityNormalization

/-!
# Exact point comparison for the global smooth-support coclass section

This is a comparison theorem, not the definition of general purity. In the
singleton case the actual global section constructed by normal-chart gluing is
the sheafification image of the old, exactly normalized point coclass. We also
construct the actual closed immersion of every complex point, so the final
point theorem takes no singleton-image or smooth-source hypothesis as input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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

variable {X Y : Scheme}
  (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
  (i : Y ⟶ X) (hi : i ≫ sX = sY) (d : ℕ)
  [SmoothOfRelativeDimension 0 sY] [SmoothOfRelativeDimension d sX]
  [IsClosedImmersion i] [IsProjective sX]

/-- The old ambient point coclass, pulled back to the literal whole-open pair,
then sent through the actual sheafification unit. -/
def smoothClosedOldPointCoclassSection (z : ComplexPoint Y sY) :
    (smoothClosedSupportCoclassSheaf sX sY i hi 0 d).obj.obj (op ⊤) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X sX))
    (Set.range (Point.map i hi)) (2 * d)).app (op ⊤)
      (relativeCohomologyMap ℚ (2 * d)
        (neighborhoodSupportToPointPairMap (⊤ : Opens (ComplexPoint X sX))
          (Set.range (Point.map i hi)) (Point.map i hi z) ⟨z, rfl⟩)
        (analyticPointLocalCoclass sX d (Point.map i hi z)))

omit [IsProjective sX] in
/-- The literal local-to-point map is the map used by the existing exact
normal-slice/point comparison. -/
theorem neighborhoodSupportToPointPairMap_eq_smoothClosedPointNeighborhoodPairMap
    (z : ComplexPoint Y sY) (V : Opens (ComplexPoint X sX)) (hzV : Point.map i hi z ∈ V) :
    neighborhoodSupportToPointPairMap
      (smoothClosedSupportNeighborhood sX sY i hi 0 d z V hzV)
      (Set.range (Point.map i hi)) (Point.map i hi z) ⟨z, rfl⟩ =
      smoothClosedPointNeighborhoodPairMap sX sY i hi d z V hzV := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- At its distinguished point the old global coclass has exactly the germ of the
general normal coclass, with coefficient one. -/
theorem smoothClosedOldPointCoclassSection_germ_eq_normalCoclass
    (z : ComplexPoint Y sY) (V : Opens (ComplexPoint X sX)) (hzV : Point.map i hi z ∈ V) :
    (smoothClosedSupportCoclassSheaf sX sY i hi 0 d).presheaf.Γgerm (Point.map i hi z)
      (smoothClosedOldPointCoclassSection sX sY i hi d z) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X sX))
      (Set.range (Point.map i hi)) (2 * d)
      (smoothClosedSupportNeighborhood sX sY i hi 0 d z V hzV)
      (Point.map i hi z) (mem_smoothClosedSupportNeighborhood sX sY i hi 0 d z V hzV)
      (smoothClosedSupportNormalCoclass sX sY i hi 0 d z V hzV) := by
  let W := smoothClosedSupportNeighborhood sX sY i hi 0 d z V hzV
  let a := relativeCohomologyMap ℚ (2 * d)
    (neighborhoodSupportToPointPairMap (⊤ : Opens (ComplexPoint X sX))
      (Set.range (Point.map i hi)) (Point.map i hi z) ⟨z, rfl⟩)
    (analyticPointLocalCoclass sX d (Point.map i hi z))
  change supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X sX))
    (Set.range (Point.map i hi)) (2 * d) ⊤ (Point.map i hi z) (by trivial) a = _
  rw [← supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X sX))
    (Set.range (Point.map i hi)) (2 * d) (show W ≤ ⊤ from le_top)
    (Point.map i hi z) (mem_smoothClosedSupportNeighborhood sX sY i hi 0 d z V hzV)]
  congr 1
  dsimp only [a]
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    neighborhoodSupportInclusionPairMap_toPoint]
  rw [neighborhoodSupportToPointPairMap_eq_smoothClosedPointNeighborhoodPairMap]
  exact (smoothClosedPointNormalCoclass_eq_analyticPointLocalCoclass sX sY i hi d z V hzV).symm

omit [SmoothOfRelativeDimension 0 sY] in
/-- The old global point image vanishes off the actual closed support. -/
theorem smoothClosedOldPointCoclassSection_germ_eq_zero
    (z : ComplexPoint Y sY) (x : ComplexPoint X sX) (hx : x ∉ Set.range (Point.map i hi)) :
    (smoothClosedSupportCoclassSheaf sX sY i hi 0 d).presheaf.Γgerm x
      (smoothClosedOldPointCoclassSection sX sY i hi d z) = 0 :=
  supportRelativeCohomologyGerm_eq_zero_of_not_mem (TopCat.of (ComplexPoint X sX))
    (Set.range (Point.map i hi)) (2 * d) (isClosed_range_map_of_closedImmersion hi)
    ⊤ x (by trivial) hx _

/-- Explicit singleton-case comparison: the general glued normal section agrees
with the actual sheafification image of the old ambient point coclass. -/
theorem smoothClosedSupportCoclassSection_eq_oldPoint_of_singleton
    (z : ComplexPoint Y sY) (hS : Set.range (Point.map i hi) = {Point.map i hi z}) :
    smoothClosedSupportCoclassSection sX sY i hi 0 d =
      smoothClosedOldPointCoclassSection sX sY i hi d z := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf sX sY i hi 0 d)
  intro x _
  by_cases hx : x ∈ Set.range (Point.map i hi)
  · have heq : x = Point.map i hi z := by simpa only [hS, Set.mem_singleton_iff] using hx
    subst x
    exact (smoothClosedSupportCoclassSection_germ_eq_normalCoclass
      sX sY i hi 0 d z ⊤ (by trivial)).trans
      (smoothClosedOldPointCoclassSection_germ_eq_normalCoclass
        sX sY i hi d z ⊤ (by trivial)).symm
  · exact (smoothClosedSupportCoclassSection_germ_eq_zero sX sY i hi 0 d x hx).trans
      (smoothClosedOldPointCoclassSection_germ_eq_zero sX sY i hi d z x hx).symm

section ActualPoint

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))

/-- The identity complex point of the base scheme over itself. -/
def complexSpecIdentityPoint : ComplexPoint (Spec (.of ℂ)) (𝟙 (Spec (.of ℂ))) :=
  ⟨𝟙 _, Category.id_comp _⟩

/-- There is just one complex point of the base over itself. -/
theorem complexSpecPoint_eq_identity (w : ComplexPoint (Spec (.of ℂ)) (𝟙 (Spec (.of ℂ)))) :
    w = complexSpecIdentityPoint := by
  apply Subtype.ext
  simpa only [Category.comp_id, complexSpecIdentityPoint] using w.2

/-- The actual scheme morphism represented by any complex point is a closed
immersion; no point-immersion input is supplied. -/
theorem complexPoint_isClosedImmersion (z : ComplexPoint X s) :
    IsClosedImmersion z.1 :=
  AlgebraicGeometry.isClosedImmersion_of_comp_eq_id s z.1 z.2

@[simp] theorem map_complexSpecIdentityPoint (z : ComplexPoint X s) :
    Point.map z.1 z.2 complexSpecIdentityPoint = z := by
  apply Subtype.ext
  exact Category.id_comp _

/-- The actual analytic image of the point closed immersion is its singleton. -/
theorem range_map_complexPoint (z : ComplexPoint X s) :
    Set.range (Point.map z.1 z.2) = {z} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    rw [complexSpecPoint_eq_identity w, map_complexSpecIdentityPoint]
    exact Set.mem_singleton _
  · intro hx
    exact ⟨complexSpecIdentityPoint, (map_complexSpecIdentityPoint s z).trans
      (Set.mem_singleton_iff.mp hx).symm⟩

variable (d : ℕ) [SmoothOfRelativeDimension d s] [IsProjective s]

/-- The general smooth-support section specialized to the actual point immersion.
It is still defined by the same arbitrary-dimensional normal-chart gluing. -/
def complexPointSmoothSupportCoclassSection (z : ComplexPoint X s) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s))
      (Set.range (Point.map z.1 z.2)) (2 * d)).obj.obj (op ⊤) := by
  letI := complexPoint_isClosedImmersion s z
  exact smoothClosedSupportCoclassSection s (𝟙 _) z.1 z.2 0 d

/-- The actual sheafification image of the pre-existing global point coclass.
The only adapter is the literal inclusion of the whole-open subtype pair. -/
def analyticPointLocalCoclassSheafSection (z : ComplexPoint X s) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s))
      (Set.range (Point.map z.1 z.2)) (2 * d)).obj.obj (op ⊤) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s))
    (Set.range (Point.map z.1 z.2)) (2 * d)).app (op ⊤)
      (relativeCohomologyMap ℚ (2 * d)
        (neighborhoodSupportToPointPairMap (⊤ : Opens (ComplexPoint X s))
          (Set.range (Point.map z.1 z.2)) z
          ⟨complexSpecIdentityPoint, map_complexSpecIdentityPoint s z⟩)
        (analyticPointLocalCoclass s d z))

/-- Unconditional exact point normalization of the general globally glued
smooth-support section. The support-singleton equality and smooth point immersion
are constructed, not hypotheses; no rescaling or point-case definition is used. -/
theorem complexPointSmoothSupportCoclassSection_eq_analyticPointLocalCoclassSheafSection
    (z : ComplexPoint X s) :
    complexPointSmoothSupportCoclassSection s d z =
      analyticPointLocalCoclassSheafSection s d z := by
  let := complexPoint_isClosedImmersion s z
  have hS : Set.range (Point.map z.1 z.2) =
      {Point.map z.1 z.2 complexSpecIdentityPoint} := by
    rw [map_complexSpecIdentityPoint, range_map_complexPoint]
  change smoothClosedSupportCoclassSection s (𝟙 _) z.1 z.2 0 d = _
  rw [smoothClosedSupportCoclassSection_eq_oldPoint_of_singleton
    s (𝟙 _) z.1 z.2 d complexSpecIdentityPoint hS]
  dsimp only [smoothClosedOldPointCoclassSection, analyticPointLocalCoclassSheafSection]
  apply congrArg ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s))
    (Set.range (Point.map z.1 z.2)) (2 * d)).app (op ⊤))
  let f : Set.range (Point.map z.1 z.2) → RelativeCohomology ℚ
      (neighborhoodSupportComplementPair ((⊤ : Opens (ComplexPoint X s)) : Set (ComplexPoint X s))
        (Set.range (Point.map z.1 z.2))) (2 * d) := fun x =>
    relativeCohomologyMap ℚ (2 * d)
      (neighborhoodSupportToPointPairMap ((⊤ : Opens (ComplexPoint X s)) : Set (ComplexPoint X s))
        (Set.range (Point.map z.1 z.2)) x.1 x.2)
      (analyticPointLocalCoclass s d x.1)
  have heq :
    (⟨Point.map z.1 z.2 complexSpecIdentityPoint, ⟨complexSpecIdentityPoint, rfl⟩⟩ :
      Set.range (Point.map z.1 z.2)) =
    ⟨z, complexSpecIdentityPoint, map_complexSpecIdentityPoint s z⟩ :=
      Subtype.ext (map_complexSpecIdentityPoint s z)
  have hh := congrArg f heq
  exact hh

end ActualPoint

end AlgebraicGeometry.ComplexPoint
