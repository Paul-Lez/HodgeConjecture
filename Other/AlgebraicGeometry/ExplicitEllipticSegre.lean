/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurface
public import Other.AlgebraicGeometry.ExplicitSegreMorphism
public import Other.AlgebraicGeometry.ExplicitProjectiveRelabeling
public import Other.AlgebraicGeometry.ExplicitSegreCancellation
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The Segre morphism of the constructed elliptic self-product

The integral smooth self-product embeds as a closed subscheme of projective 8-space over
the complex numbers. The embedding is defined from the two actual curve projections and the
regular coordinate-ratio construction. Its monomorphism property follows by recovering both
factors from the Segre coordinates, and properness then gives the closed immersion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The first projective-plane coordinate map of the actual elliptic self-product. -/
def surfaceFirstPlane : surface ⟶ integerPlane :=
  pullback.fst curveToBase curveToBase ≫ curveToIntegerPlane

/-- The second projective-plane coordinate map of the actual elliptic self-product. -/
def surfaceSecondPlane : surface ⟶ integerPlane :=
  pullback.snd curveToBase curveToBase ≫ curveToIntegerPlane

/-- The canonical integral coefficients in the surface's regular functions. -/
def surfaceIntegerScalar : ULift.{0} ℤ →+* Γ(surface, ⊤) :=
  (Int.castRingHom Γ(surface, ⊤)).comp ULift.ringEquiv.toRingHom

/-- The Segre morphism on the integral projective-spectrum models. -/
def surfaceToIntegerMatrixSpace : surface ⟶
    Proj (homogeneousSubmodule (Fin 3 × Fin 3) (ULift.{0} ℤ)) :=
  SegreMorphism.fromMaps (ULift.{0} ℤ) surfaceIntegerScalar surfaceFirstPlane surfaceSecondPlane

/-- Reindex the nine matrix coordinates by `Fin 9`. -/
def surfaceToIntegerP8 : surface ⟶ Proj (homogeneousSubmodule (Fin 9) (ULift.{0} ℤ)) :=
  surfaceToIntegerMatrixSpace ≫ (ProjectiveRelabeling.iso (ULift.{0} ℤ) finProdFinEquiv).hom

/-- The actual Segre morphism of the surface into complex projective eight-space. -/
def surfaceSegre : surface ⟶ ProjectiveSpace (Fin 9) base :=
  pullback.lift surfaceToBase surfaceToIntegerP8 (Subsingleton.elim _ _)

/-- The constructed Segre morphism is over the complex base. -/
@[reassoc] theorem surfaceSegre_toBase :
    surfaceSegre ≫ ProjectiveSpace.toBase (Fin 9) base = surfaceToBase :=
  pullback.lift_fst _ _ _

/-- On every simultaneous coordinate chart, the morphism is given by the products of the
actual regular coordinate ratios of the two elliptic factors. -/
@[reassoc] theorem surfaceToIntegerMatrixSpace_chart (p : Fin 3 × Fin 3) :
    (SegreMorphism.chart (ULift.{0} ℤ) surfaceFirstPlane surfaceSecondPlane p).ι ≫
      surfaceToIntegerMatrixSpace =
    SegreMorphism.localMap (ULift.{0} ℤ) surfaceIntegerScalar surfaceFirstPlane surfaceSecondPlane p :=
  SegreMorphism.chart_ι_fromMaps (ULift.{0} ℤ) surfaceIntegerScalar surfaceFirstPlane surfaceSecondPlane p

/-- The curve's complex base map and integral projective coordinates jointly determine a map
into the curve. -/
theorem curve_hom_ext {T : Scheme} (h k : T ⟶ curve)
    (hb : h ≫ curveToBase = k ≫ curveToBase)
    (hp : h ≫ curveToIntegerPlane = k ≫ curveToIntegerPlane) : h = k := by
  apply (cancel_mono curveToPlane).mp
  apply pullback.hom_ext
  · simpa only [curveToBase, ProjectiveSpace.toBase, Category.assoc] using hb
  · simpa only [curveToIntegerPlane, planeToIntegerPlane, integerPlane, Category.assoc] using hp

/-- The Segre morphism of the actual self-product is a monomorphism. -/
instance surfaceSegre_mono : Mono surfaceSegre where
  right_cancellation := by
    intro T h k hhk
    have hb : h ≫ surfaceToBase = k ≫ surfaceToBase := by
      simpa only [Category.assoc, surfaceSegre_toBase] using
        congrArg (fun m ↦ m ≫ ProjectiveSpace.toBase (Fin 9) base) hhk
    have h9 : h ≫ surfaceToIntegerP8 = k ≫ surfaceToIntegerP8 := by
      simpa only [surfaceSegre, Category.assoc, pullback.lift_snd] using
        congrArg (fun m ↦ m ≫ pullback.snd (terminal.from base)
          (terminal.from (Proj (homogeneousSubmodule (Fin 9) (ULift.{0} ℤ))))) hhk
    have hm : h ≫ surfaceToIntegerMatrixSpace = k ≫ surfaceToIntegerMatrixSpace := by
      apply (cancel_mono (ProjectiveRelabeling.iso (ULift.{0} ℤ)
        (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9)).hom).mp
      exact h9
    have hf : h ≫ surfaceFirstPlane = k ≫ surfaceFirstPlane :=
      SegreMorphism.comp_first_eq (ULift.{0} ℤ) surfaceIntegerScalar surfaceFirstPlane
        surfaceSecondPlane h k hm (fun _ ↦ SegreMorphism.uliftInt_ringHom_ext _ _)
    have hg : h ≫ surfaceSecondPlane = k ≫ surfaceSecondPlane :=
      SegreMorphism.comp_second_eq (ULift.{0} ℤ) surfaceIntegerScalar surfaceFirstPlane
        surfaceSecondPlane h k hm (fun _ ↦ SegreMorphism.uliftInt_ringHom_ext _ _)
    apply pullback.hom_ext
    · apply curve_hom_ext
      · exact hb
      · exact hf
    · apply curve_hom_ext
      · simpa only [surfaceToBase, Category.assoc, ← pullback.condition] using hb
      · exact hg

/-- The map to projective eight-space is proper because the surface is proper over the complex
base and the projective target is separated over that base. -/
instance surfaceSegre_isProper : IsProper surfaceSegre := by
  have : IsProper (surfaceSegre ≫ ProjectiveSpace.toBase (Fin 9) base) := by
    rw [surfaceSegre_toBase]
    infer_instance
  exact IsProper.of_comp (f := surfaceSegre) (g := ProjectiveSpace.toBase (Fin 9) base)

/-- The Segre map is a closed immersion of the constructed integral smooth surface. -/
instance surfaceSegre_isClosedImmersion : IsClosedImmersion surfaceSegre :=
  (IsClosedImmersion.iff_isProper_and_mono surfaceSegre).mpr ⟨inferInstance, inferInstance⟩

/-- The actual elliptic self-product has an explicit projective presentation in projective
8-space over the complex numbers. -/
instance surface_isProjective : IsProjective surfaceToBase :=
  ⟨⟨{ ambientDimension := 8, immersion := surfaceSegre,
        immersion_toBase := surfaceSegre_toBase }⟩⟩

/-- The explicit smooth projective elliptic curve as a packaged integral complex variety. -/
def curveVariety : IntegralProjectiveComplexVariety where
  scheme := curve
  structureMap := curveToBase

/-- The explicit smooth projective surface as a packaged integral complex variety. -/
def surfaceVariety : IntegralProjectiveComplexVariety where
  scheme := surface
  structureMap := surfaceToBase

instance curveVariety_smooth : SmoothOfRelativeDimension 1 curveVariety.structureMap :=
  curve_smoothOfRelativeDimension

instance surfaceVariety_smooth : SmoothOfRelativeDimension 2 surfaceVariety.structureMap :=
  surface_smoothOfRelativeDimension

end AlgebraicGeometry.ExplicitEllipticCandidate
