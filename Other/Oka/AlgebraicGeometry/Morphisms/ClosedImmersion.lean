/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Other.Oka.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Morphisms of locally ringed spaces into a closed subscheme of an affine scheme

Let `i : Z ⟶ X` be a closed immersion of schemes with `X` affine. For an arbitrary locally
ringed space `T` (not necessarily a scheme), a morphism of locally ringed spaces `φ : T ⟶ X`
factors through `Z` if and only if `φ^♯ : Γ(X, 𝒪_X) → Γ(T, 𝒪_T)` kills the kernel of
`i^♯ : Γ(X, 𝒪_X) → Γ(Z, 𝒪_Z)`, and the factorisation is unique. Both halves are formal
consequences of the `Γ`-`Spec` adjunction for locally ringed spaces: morphisms `T ⟶ X` into an
affine scheme are determined by the map on global sections, and `Γ(X) → Γ(Z)` is surjective.

We also describe the image of `i` as the common vanishing locus of generators of that kernel.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_isAffine`: a morphism of locally ringed spaces
  into an affine scheme is determined by its map on global sections.
- `AlgebraicGeometry.LocallyRingedSpace.closedImmersion_hom_ext`: a closed immersion into an affine
  scheme is a monomorphism of locally ringed spaces.
- `AlgebraicGeometry.LocallyRingedSpace.closedImmersionLift`, `closedImmersionLift_comp`: the
  factorisation of a morphism killing the kernel of `Γ(X) → Γ(Z)`.
- `AlgebraicGeometry.IsClosedImmersion.range_eq_of_isAffine`: the image of `i` is the set of
  points at which the germs of given generators of the kernel are non-units.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

variable {T : LocallyRingedSpace.{u}}

instance isIso_toΓSpec_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    IsIso X.toLocallyRingedSpace.toΓSpec :=
  inferInstanceAs (IsIso (Scheme.forgetToLocallyRingedSpace.map X.toSpecΓ))

/-- **A morphism of locally ringed spaces into an affine scheme is determined by its map on global
sections.** -/
theorem hom_ext_of_isAffine {X : Scheme.{u}} [IsAffine X] {φ ψ : T ⟶ X.toLocallyRingedSpace}
    (h : Γ.map φ.op = Γ.map ψ.op) : φ = ψ := by
  rw [← cancel_mono X.toLocallyRingedSpace.toΓSpec, toΓSpec_naturality, toΓSpec_naturality, h]

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X]

include i in
lemma isAffine_of_isClosedImmersion : IsAffine Z :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).1

/-- **A closed immersion into an affine scheme is a monomorphism of locally ringed spaces.** -/
theorem closedImmersion_hom_ext {ψ₁ ψ₂ : T ⟶ Z.toLocallyRingedSpace}
    (h : ψ₁ ≫ i.toLRSHom = ψ₂ ≫ i.toLRSHom) : ψ₁ = ψ₂ := by
  haveI := isAffine_of_isClosedImmersion i
  refine hom_ext_of_isAffine ?_
  have hs : Function.Surjective i.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have h' := congrArg (fun φ ↦ Γ.map (Quiver.Hom.op φ)) h
  simp only [op_comp, Functor.map_comp] at h'
  ext a
  obtain ⟨b, rfl⟩ := hs a
  exact congrArg (fun m ↦ m.hom b) h'

/-- The ring map `Γ(Z) → Γ(T)` induced by a morphism `φ : T ⟶ X` killing the kernel of the
surjection `Γ(X) → Γ(Z)`. -/
noncomputable def closedImmersionLiftΓ (φ : T ⟶ X.toLocallyRingedSpace)
    (hφ : ∀ a, i.appTop a = 0 → (Γ.map φ.op) a = 0) :
    Γ.obj (op Z.toLocallyRingedSpace) ⟶ Γ.obj (op T) :=
  CommRingCat.ofHom <| RingHom.liftOfSurjective (Γ.map i.toLRSHom.op).hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
    ⟨(Γ.map φ.op).hom, fun a ha ↦ hφ a ha⟩

lemma closedImmersionLiftΓ_appTop (φ : T ⟶ X.toLocallyRingedSpace)
    (hφ : ∀ a, i.appTop a = 0 → (Γ.map φ.op) a = 0) (a : Γ.obj (op X.toLocallyRingedSpace)) :
    closedImmersionLiftΓ i φ hφ (Γ.map i.toLRSHom.op a) = Γ.map φ.op a :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ a

/-- **The factorisation through a closed subscheme of an affine scheme**: a morphism of locally
ringed spaces `φ : T ⟶ X` whose map on global sections kills the kernel of `Γ(X) → Γ(Z)`
factors through `i : Z ⟶ X`. -/
noncomputable def closedImmersionLift (φ : T ⟶ X.toLocallyRingedSpace)
    (hφ : ∀ a, i.appTop a = 0 → (Γ.map φ.op) a = 0) : T ⟶ Z.toLocallyRingedSpace :=
  T.toΓSpec ≫ Spec.locallyRingedSpaceMap (closedImmersionLiftΓ i φ hφ) ≫
    @inv _ _ _ _ Z.toLocallyRingedSpace.toΓSpec
      (@isIso_toΓSpec_of_isAffine Z (isAffine_of_isClosedImmersion i))

@[reassoc (attr := simp)]
theorem closedImmersionLift_comp (φ : T ⟶ X.toLocallyRingedSpace)
    (hφ : ∀ a, i.appTop a = 0 → (Γ.map φ.op) a = 0) :
    closedImmersionLift i φ hφ ≫ i.toLRSHom = φ := by
  haveI : IsAffine Z := isAffine_of_isClosedImmersion i
  have hi := toΓSpec_naturality i.toLRSHom
  have hρ : Γ.map i.toLRSHom.op ≫ closedImmersionLiftΓ i φ hφ = Γ.map φ.op :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ closedImmersionLiftΓ_appTop i φ hφ a)
  rw [← cancel_mono X.toLocallyRingedSpace.toΓSpec, toΓSpec_naturality φ, closedImmersionLift,
    Category.assoc, Category.assoc, hi]
  simp only [Category.assoc]
  rw [IsIso.inv_hom_id_assoc, ← Spec.locallyRingedSpaceMap_comp, hρ]

/-- **The mapping property of a closed subscheme of an affine scheme**, for morphisms of locally
ringed spaces: `φ : T ⟶ X` factors, uniquely, through `i` as soon as `φ^♯` kills the kernel of
`Γ(X) → Γ(Z)`. -/
theorem existsUnique_closedImmersionLift (φ : T ⟶ X.toLocallyRingedSpace)
    (hφ : ∀ a, i.appTop a = 0 → (Γ.map φ.op) a = 0) :
    ∃! ψ : T ⟶ Z.toLocallyRingedSpace, ψ ≫ i.toLRSHom = φ :=
  ⟨closedImmersionLift i φ hφ, closedImmersionLift_comp i φ hφ, fun _ hψ ↦
    closedImmersion_hom_ext i (hψ.trans (closedImmersionLift_comp i φ hφ).symm)⟩

end LocallyRingedSpace

namespace IsClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X]

/-- **The image of a closed immersion into an affine scheme** is the set of points at which the
germs of a generating family of the kernel of `Γ(X) → Γ(Z)` all fail to be units. -/
theorem range_eq_of_isAffine {ι : Type*} (h : ι → Γ(X, ⊤))
    (hh : Ideal.span (Set.range h) = RingHom.ker i.appTop.hom) :
    Set.range i = {x | ∀ j, ¬ IsUnit (X.presheaf.Γgerm x (h j))} := by
  have hcl : closure (Set.range i) = Set.range i := i.isClosedEmbedding.isClosed_range.closure_eq
  ext x
  rw [← hcl, ← Scheme.Hom.support_ker, SetLike.mem_coe,
    Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top X⟩) trivial,
    Scheme.Hom.ker_apply]
  change x ∈ X.zeroLocus (U := ⊤) (RingHom.ker i.appTop.hom : Set Γ(X, ⊤)) ↔ _
  rw [← hh, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq]
  refine forall_congr' fun j ↦ not_congr ?_
  exact X.mem_basicOpen_top (h j) x

end IsClosedImmersion

end AlgebraicGeometry

end
