/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothEquidimensional
public import Other.AlgebraicGeometry.EtaleNonvanishingDensity
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Local analytic density of nonvanishing loci

On an affine étale coordinate neighborhood in a smooth integral complex scheme, the nonvanishing
locus of a nonzero regular function is analytically dense.
-/

@[expose] public section

open scoped Topology

open CategoryTheory Set

namespace AlgebraicGeometry

open ComplexAlgHom

noncomputable section

variable {X : Over (Spec (CommRingCat.of ℂ))} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
  {x : X.left} (D : LocalEtaleCoordinates X d x)

noncomputable local instance coordinateRingAlgebra :
    Algebra (complexPolynomialRing d) Γ(D.neighborhood.toScheme, ⊤) :=
  D.coordinateRingHomOnOpen.toAlgebra

noncomputable local instance coordinateRingComplexAlgebra :
    Algebra ℂ Γ(D.neighborhood.toScheme, ⊤) :=
  (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra

noncomputable local instance coordinateRingScalarTower :
    IsScalarTower ℂ (complexPolynomialRing d) Γ(D.neighborhood.toScheme, ⊤) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

noncomputable local instance coordinateRingEtale :
    Algebra.Etale (complexPolynomialRing d) Γ(D.neighborhood.toScheme, ⊤) :=
  RingHom.etale_algebraMap.mp D.coordinateRingHomOnOpen_etale

/-- A nonzero function on an affine étale coordinate neighborhood has analytically dense
nonvanishing locus. -/
theorem LocalEtaleCoordinates.dense_evaluate_ne_zero [IsIntegral X.left]
    (r : Γ(D.neighborhood.toScheme, ⊤)) (hr : r ≠ 0) :
    Dense {z : ComplexPoint (ComplexPoint.openScheme X D.neighborhood) |
      Point.evaluate ⊤ r z ≠ 0} := by
  let : Nonempty D.neighborhood := ⟨⟨x, D.mem⟩⟩
  rw [show {z : ComplexPoint (ComplexPoint.openScheme X D.neighborhood) |
      Point.evaluate ⊤ r z ≠ 0} =
      D.pointAlgHomHomeomorph ⁻¹' {v : Γ(D.neighborhood.toScheme, ⊤) →ₐ[ℂ] ℂ |
        v r ≠ 0} by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [D.pointAlgHomHomeomorph_apply]]
  exact D.pointAlgHomHomeomorph.isOpenQuotientMap.dense_preimage_iff.2
    (ComplexAlgHom.dense_eval_ne_zero Γ(D.neighborhood.toScheme, ⊤) d r hr)

end

end AlgebraicGeometry

namespace AlgebraicGeometry

open CategoryTheory

noncomputable section

variable {X : Over (Spec (CommRingCat.of ℂ))} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
  {x : X.left} (D : LocalEtaleCoordinates X d x)

lemma LocalEtaleCoordinates.injective_appTop [IsIntegral X.left]
    [QuasiSeparatedSpace X.left] :
    Function.Injective D.neighborhood.ι.appTop := by
  let : Nonempty D.neighborhood := ⟨⟨x, D.mem⟩⟩
  let : IsDominant D.neighborhood.ι :=
    Opens.isDominant_ι (D.neighborhood.2.dense ⟨x, D.mem⟩)
  let : CompactSpace D.neighborhood :=
    isCompact_iff_compactSpace.mp D.isAffine.isCompact
  let : IsSchemeTheoreticallyDominant D.neighborhood.ι :=
    IsSchemeTheoreticallyDominant.of_isDominant D.neighborhood.ι
  exact Scheme.Hom.app_injective D.neighborhood.ι ⊤

/-- A nonzero global section restricts to a function with dense nonvanishing locus on every
local étale coordinate neighborhood. -/
theorem LocalEtaleCoordinates.dense_restrict_evaluate_ne_zero [IsIntegral X.left]
    [QuasiSeparatedSpace X.left] (t : Γ(X.left, ⊤)) (ht : t ≠ 0) :
    Dense {z : ComplexPoint (ComplexPoint.openScheme X D.neighborhood) |
      Point.evaluate ⊤ (D.neighborhood.ι.appTop t) z ≠ 0} := by
  apply D.dense_evaluate_ne_zero
  intro h
  apply ht
  apply D.injective_appTop
  simpa using h

end

end AlgebraicGeometry

namespace AlgebraicGeometry

open CategoryTheory Set Topology

noncomputable section

variable (X : Over (Spec (CommRingCat.of ℂ)))

/-- On a smooth integral quasi-separated complex scheme, the nonvanishing locus of a nonzero
global regular function is analytically dense. -/
theorem ComplexPoint.dense_evaluate_ne_zero [IsIntegral X.left] [Smooth X.hom]
    [QuasiSeparatedSpace X.left] (t : Γ(X.left, ⊤)) (ht : t ≠ 0) :
    Dense {z : ComplexPoint X | Point.evaluate ⊤ t z ≠ 0} := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨z, hzO⟩ := hOne
  let D := ComplexPoint.localEtaleCoordinates X (TopologicalSpace.dim X.left) z
  have hzD : z ∈ Point.overOpen D.neighborhood :=
    ComplexPoint.mem_localEtaleCoordinates X (TopologicalSpace.dim X.left) z
  let zD := ComplexPoint.asOpenPoint X D.neighborhood z hzD
  have hmapzD : Point.map (ComplexPoint.openInclusion X D.neighborhood) zD = z := by
    exact congrArg Subtype.val
      ((ComplexPoint.openHomeomorph X D.neighborhood).apply_symm_apply ⟨z, hzD⟩)
  let W : Set (ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) :=
    Point.map (ComplexPoint.openInclusion X D.neighborhood) ⁻¹' O
  have hWopen : IsOpen W :=
    hO.preimage (ComplexPoint.isOpenEmbedding_map_open X D.neighborhood).continuous
  have hzDW : zD ∈ W := by
    change Point.map (ComplexPoint.openInclusion X D.neighborhood) zD ∈ O
    rwa [hmapzD]
  obtain ⟨y, hyW, hynz⟩ :=
    (D.dense_restrict_evaluate_ne_zero t ht).inter_open_nonempty
      W hWopen ⟨zD, hzDW⟩
  refine ⟨Point.map (ComplexPoint.openInclusion X D.neighborhood) y, hyW, ?_⟩
  change Point.evaluate ⊤ t
    (Point.map (ComplexPoint.openInclusion X D.neighborhood) y) ≠ 0
  rw [Point.evaluate_map]
  exact hynz

end

end AlgebraicGeometry

namespace AlgebraicGeometry

open CategoryTheory Set Topology

noncomputable section

variable (X : Over (Spec (CommRingCat.of ℂ)))

/-- Every nonempty Zariski open subset of a smooth integral quasi-separated complex scheme has
dense complex points in the analytic topology. -/
theorem ComplexPoint.dense_overOpen [IsIntegral X.left] [Smooth X.hom]
    [QuasiSeparatedSpace X.left] (U : X.left.Opens) [Nonempty U] :
    Dense (Point.overOpen U : Set (ComplexPoint X)) := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨z, hzO⟩ := hOne
  let D := ComplexPoint.localEtaleCoordinates X (TopologicalSpace.dim X.left) z
  have hzD : z ∈ Point.overOpen D.neighborhood :=
    ComplexPoint.mem_localEtaleCoordinates X (TopologicalSpace.dim X.left) z
  let zD := ComplexPoint.asOpenPoint X D.neighborhood z hzD
  have hmapzD : Point.map (ComplexPoint.openInclusion X D.neighborhood) zD = z := by
    exact congrArg Subtype.val
      ((ComplexPoint.openHomeomorph X D.neighborhood).apply_symm_apply ⟨z, hzD⟩)
  let W : Set (ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) :=
    Point.map (ComplexPoint.openInclusion X D.neighborhood) ⁻¹' O
  have hWopen : IsOpen W :=
    hO.preimage (ComplexPoint.isOpenEmbedding_map_open X D.neighborhood).continuous
  have hzDW : zD ∈ W := by
    change Point.map (ComplexPoint.openInclusion X D.neighborhood) zD ∈ O
    rwa [hmapzD]
  obtain ⟨uU⟩ : Nonempty U := inferInstance
  obtain ⟨u, huD, huU⟩ : ((D.neighborhood : Set X.left) ∩ U).Nonempty :=
    nonempty_preirreducible_inter D.neighborhood.2 U.2
      ⟨z.underlying, D.mem⟩ ⟨uU.1, uU.2⟩
  let uD : D.neighborhood := ⟨u, huD⟩
  have huPre : uD ∈ D.neighborhood.ι ⁻¹ᵁ U := huU
  let : IsAffine D.neighborhood.toScheme := D.isAffine
  obtain ⟨r, hrle, hur⟩ :=
    (isAffineOpen_top D.neighborhood.toScheme).exists_basicOpen_le
      (V := D.neighborhood.ι ⁻¹ᵁ U) ⟨uD, huPre⟩ trivial
  have hopen : D.neighborhood.toScheme.basicOpen r ≠ ⊥ := by
    intro hbot
    rw [hbot] at hur
    exact hur
  have hr : r ≠ 0 := by
    intro h
    apply hopen
    subst r
    exact Scheme.basicOpen_zero _ _
  obtain ⟨y, hyW, hynz⟩ :=
    (D.dense_evaluate_ne_zero r hr).inter_open_nonempty W hWopen ⟨zD, hzDW⟩
  have hyBasic : y ∈ Point.overOpen (D.neighborhood.toScheme.basicOpen r) :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := ComplexPoint.openScheme X D.neighborhood) (U := ⊤) r y trivial).2 hynz
  refine ⟨Point.map (ComplexPoint.openInclusion X D.neighborhood) y, hyW, ?_⟩
  change (Point.map (ComplexPoint.openInclusion X D.neighborhood) y).underlying ∈ U
  rw [Point.underlying_map]
  exact hrle hyBasic

end

end AlgebraicGeometry

namespace AlgebraicGeometry

open CategoryTheory Set Topology

noncomputable section

variable (X : Over (Spec (CommRingCat.of ℂ)))

/-- A connected nonempty Zariski open with dense complex points forces the entire analytic complex
point space to be connected. -/
theorem ComplexPoint.connectedSpace_of_open [IsIntegral X.left] [Smooth X.hom]
    [QuasiSeparatedSpace X.left] (U : X.left.Opens) [Nonempty U]
    [ConnectedSpace (ComplexPoint (ComplexPoint.openScheme X U))] :
    ConnectedSpace (ComplexPoint X) := by
  let e := ComplexPoint.openHomeomorph X U
  let w : {z : ComplexPoint X // z ∈ Point.overOpen U} :=
    e (Classical.choice (inferInstance : Nonempty
      (ComplexPoint (ComplexPoint.openScheme X U))))
  let : PreconnectedSpace {z : ComplexPoint X // z ∈ Point.overOpen U} := ⟨by
    rw [← Set.image_univ_of_surjective e.surjective]
    exact isPreconnected_univ.image e e.continuous.continuousOn⟩
  let : Nonempty {z : ComplexPoint X // z ∈ Point.overOpen U} := ⟨w⟩
  let : PreconnectedSpace (ComplexPoint X) :=
    (ComplexPoint.dense_overOpen X U).denseRange_val.preconnectedSpace continuous_subtype_val
  exact connectedSpace_iff (ComplexPoint X) |>.2 ⟨inferInstance, ⟨w.1⟩⟩

end

end AlgebraicGeometry
