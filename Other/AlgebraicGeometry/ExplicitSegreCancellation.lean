/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitSegreProjections

/-!
# Cancellation of the two factors of the Segre morphism
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- If a scheme morphism can be recovered from another morphism on an open cover of its target,
then equality after the latter implies equality after the former. -/
theorem comp_eq_of_local_recovery {X Y Z W : Scheme.{u}}
    (F : Y ⟶ Z) (f : Y ⟶ W) {ι : Type*} (V : ι → Z.Opens) (hV : ⨆ i, V i = ⊤)
    (r : ∀ i, (V i).toScheme ⟶ W)
    (hr : ∀ i, F ∣_ V i ≫ r i = (F ⁻¹ᵁ V i).ι ≫ f)
    (h k : X ⟶ Y) (heq : h ≫ F = k ≫ F) : h ≫ f = k ≫ f := by
  let C := X.openCoverOfIsOpenCover (fun i ↦ (h ≫ F) ⁻¹ᵁ V i)
    ((h ≫ F).iSup_preimage_eq_top hV)
  apply C.hom_ext
  intro i
  let U := (h ≫ F) ⁻¹ᵁ V i
  have hh : U ≤ h ⁻¹ᵁ (F ⁻¹ᵁ V i) := le_rfl
  have hk : U ≤ k ⁻¹ᵁ (F ⁻¹ᵁ V i) := by
    change (h ≫ F) ⁻¹ᵁ V i ≤ (k ≫ F) ⁻¹ᵁ V i
    rw [heq]
  have hres : h.resLE (F ⁻¹ᵁ V i) U hh ≫ F ∣_ V i =
      k.resLE (F ⁻¹ᵁ V i) U hk ≫ F ∣_ V i := by
    rw [← cancel_mono (V i).ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
    rw [heq]
  change U.ι ≫ (h ≫ f) = U.ι ≫ (k ≫ f)
  calc U.ι ≫ (h ≫ f) = h.resLE (F ⁻¹ᵁ V i) U hh ≫ ((F ⁻¹ᵁ V i).ι ≫ f) := by simp
       _ = h.resLE (F ⁻¹ᵁ V i) U hh ≫ (F ∣_ V i ≫ r i) := by rw [hr]
       _ = k.resLE (F ⁻¹ᵁ V i) U hk ≫ (F ∣_ V i ≫ r i) := by rw [← Category.assoc, hres, Category.assoc]
       _ = k.resLE (F ⁻¹ᵁ V i) U hk ≫ ((F ⁻¹ᵁ V i).ι ≫ f) := by rw [hr]
       _ = U.ι ≫ (k ≫ f) := by simp

namespace SegreMorphism

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] {σ τ : Type u}
  [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Fintype τ]
  {Y : Scheme.{u}} (c : R →+* Γ(Y, ⊤))
  (f : Y ⟶ Proj (homogeneousSubmodule σ R))
  (g : Y ⟶ Proj (homogeneousSubmodule τ R))

/-- Recovery of the first factor holds on the actual target-chart restriction of the global map. -/
theorem morphismRestrict_firstProjection (p : σ × τ)
    (hc : scalar R c f g p = ProjectiveRatioSections.pullCoefficient R f
      (chart R f g p) p.1 inf_le_left) :
    (fromMaps R c f g) ∣_ Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p) ≫
      firstProjection R p =
    (fromMaps R c f g ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)).ι ≫ f := by
  let e := Y.isoOfEq (fromMaps_preimage_coordinate R c f g p)
  rw [← cancel_epi e.inv]
  change ((fromMaps R c f g).resLE
    (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)) (chart R f g p)
    (fromMaps_preimage_coordinate R c f g p).ge) ≫ firstProjection R p = _
  rw [fromMaps_resLE,
    localToChart_firstProjection R c f g p hc]
  simp [e]

/-- Recovery of the second factor holds on the actual target-chart restriction of the global map. -/
theorem morphismRestrict_secondProjection (p : σ × τ)
    (hc : scalar R c f g p = ProjectiveRatioSections.pullCoefficient R g
      (chart R f g p) p.2 inf_le_right) :
    (fromMaps R c f g) ∣_ Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p) ≫
      secondProjection R p =
    (fromMaps R c f g ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)).ι ≫ g := by
  let e := Y.isoOfEq (fromMaps_preimage_coordinate R c f g p)
  rw [← cancel_epi e.inv]
  change ((fromMaps R c f g).resLE
    (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)) (chart R f g p)
    (fromMaps_preimage_coordinate R c f g p).ge) ≫ secondProjection R p = _
  rw [fromMaps_resLE,
    localToChart_secondProjection R c f g p hc]
  simp [e]

/-- Equality after the Segre map implies equality of the first projective factors. -/
theorem comp_first_eq {T : Scheme.{u}} (h k : T ⟶ Y)
    (heq : h ≫ fromMaps R c f g = k ≫ fromMaps R c f g)
    (hc : ∀ p, scalar R c f g p = ProjectiveRatioSections.pullCoefficient R f
      (chart R f g p) p.1 inf_le_left) : h ≫ f = k ≫ f :=
  comp_eq_of_local_recovery (fromMaps R c f g) f _ (iSup_coordinateBasicOpen R)
    (firstProjection R) (fun p ↦ morphismRestrict_firstProjection R c f g p (hc p)) h k heq

/-- Equality after the Segre map implies equality of the second projective factors. -/
theorem comp_second_eq {T : Scheme.{u}} (h k : T ⟶ Y)
    (heq : h ≫ fromMaps R c f g = k ≫ fromMaps R c f g)
    (hc : ∀ p, scalar R c f g p = ProjectiveRatioSections.pullCoefficient R g
      (chart R f g p) p.2 inf_le_right) : h ≫ g = k ≫ g :=
  comp_eq_of_local_recovery (fromMaps R c f g) g _ (iSup_coordinateBasicOpen R)
    (secondProjection R) (fun p ↦ morphismRestrict_secondProjection R c f g p (hc p)) h k heq

/-- Integral coefficient maps to the same ring are unique. -/
theorem uliftInt_ringHom_ext {S : Type u} [CommRing S] (φ ψ : ULift.{u} ℤ →+* S) : φ = ψ := by
  apply RingHom.ext
  rintro ⟨n⟩
  exact (map_intCast φ n).trans (map_intCast ψ n).symm

end SegreMorphism
end AlgebraicGeometry
