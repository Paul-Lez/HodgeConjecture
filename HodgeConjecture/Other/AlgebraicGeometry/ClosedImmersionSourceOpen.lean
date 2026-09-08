/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import HodgeConjecture.Other.AlgebraicGeometry.SmoothStratificationAnalytification

/-!
# Restricting the source of a closed immersion without losing closedness

For a closed immersion `i : Y ⟶ X` and an open `A ⊆ Y`, delete `i(Y \ A)`
from the target. The actual map from `A` into this target open is closed, and its
image is exactly the restriction of the original image. This allows a smooth
source of varying local dimensions to be treated on fixed-dimensional opens.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme} (i : Y ⟶ X) [IsClosedImmersion i] (A : Y.Opens)

/-- Delete the actual closed image of the discarded source complement. -/
def closedImmersionSourceOpenTarget : X.Opens :=
  ⟨(i '' (A : Set Y)ᶜ)ᶜ, (i.isClosedEmbedding.isClosedMap _ A.isOpen.isClosed_compl).isOpen_compl⟩

theorem closedImmersionSourceOpenTarget_preimage :
    i ⁻¹' (closedImmersionSourceOpenTarget i A : Set X) = (A : Set Y) := by
  change i ⁻¹' (i '' (A : Set Y)ᶜ)ᶜ = (A : Set Y)
  rw [Set.preimage_compl, Set.preimage_image_eq _ i.isClosedEmbedding.injective,
    compl_compl]

/-- The actual factor of the source open into the corresponding target open. -/
def closedImmersionSourceOpenLift : (A : Scheme) ⟶ (closedImmersionSourceOpenTarget i A : Scheme) :=
  IsOpenImmersion.lift (closedImmersionSourceOpenTarget i A).ι (A.ι ≫ i) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    change i a.1 ∈ (closedImmersionSourceOpenTarget i A : Set X)
    change a.1 ∈ i ⁻¹' (closedImmersionSourceOpenTarget i A : Set X)
    rw [closedImmersionSourceOpenTarget_preimage]
    exact a.2)

@[reassoc (attr := simp)]
theorem closedImmersionSourceOpenLift_ι :
    closedImmersionSourceOpenLift i A ≫ (closedImmersionSourceOpenTarget i A).ι = A.ι ≫ i :=
  IsOpenImmersion.lift_fac _ _ _

/-- In the target open, the new image is exactly the old closed support. -/
theorem range_closedImmersionSourceOpenLift :
    Set.range (closedImmersionSourceOpenLift i A) =
      (closedImmersionSourceOpenTarget i A).ι ⁻¹' Set.range i := by
  have hf (a : A) :
      (closedImmersionSourceOpenTarget i A).ι (closedImmersionSourceOpenLift i A a) = i a.1 :=
    congrArg (fun f => f a) (closedImmersionSourceOpenLift_ι i A)
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, (hf a).symm⟩
  · rintro ⟨a, ha⟩
    have haA : a ∈ A := by
      change a ∈ (A : Set Y)
      rw [← closedImmersionSourceOpenTarget_preimage i A]
      change i a ∈ (closedImmersionSourceOpenTarget i A : Set X)
      exact ha ▸ y.2
    refine ⟨⟨a, haA⟩, (closedImmersionSourceOpenTarget i A).ι.isOpenEmbedding.injective ?_⟩
    exact (hf ⟨a, haA⟩).trans ha

/-- Restricting the source in this way produces a genuine closed immersion. -/
instance closedImmersionSourceOpenLift_isClosedImmersion :
    IsClosedImmersion (closedImmersionSourceOpenLift i A) := by
  have : IsPreimmersion (closedImmersionSourceOpenLift i A ≫
      (closedImmersionSourceOpenTarget i A).ι) := by
    rw [closedImmersionSourceOpenLift_ι]
    infer_instance
  let : IsPreimmersion (closedImmersionSourceOpenLift i A) :=
    .of_comp (closedImmersionSourceOpenLift i A) (closedImmersionSourceOpenTarget i A).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_closedImmersionSourceOpenLift]
  exact i.isClosedEmbedding.isClosed_range.preimage
    (closedImmersionSourceOpenTarget i A).ι.continuous

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

/-- The actual immersion image formula with an explicitly identified source structure map. -/
theorem range_map_of_isImmersion_of_comm {X Y : Scheme}
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (i : Y ⟶ X) (hi : i ≫ sX = sY) [IsImmersion i] [LocallyOfFiniteType sX] :
    Set.range (Point.map i hi) =
      (Point.underlying : ComplexPoint X sX → X) ⁻¹' Set.range i := by
  subst sY
  exact range_map_of_isImmersion sX i

end AlgebraicGeometry.ComplexPoint
