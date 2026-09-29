/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.StructureSheaf
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# `ℂ^ι` as a locally ringed space

The structure sheaf `okaSheaf ι` of `Other.Oka.StructureSheaf` is a sheaf of rings; here we upgrade it
to a sheaf of *commutative* rings and show that its stalks are local rings, so that `ℂ^ι` becomes
a `LocallyRingedSpace`. This is the object that complex analytic spaces are locally modelled on.

The key point is that a holomorphic function which does not vanish at `x` is invertible on a
neighbourhood of `x`, so that the non-units in the stalk at `x` are exactly the germs vanishing
at `x`.

## Main definitions

- `okaCommPresheaf`, `okaCommSheaf`: the structure sheaf of `ℂ^ι`, valued in `CommRingCat`.
- `complexSpace ι`: `ℂ^ι` as a locally ringed space.
- `complexAffineSpace n`: `ℂ^n` as a locally ringed space in an arbitrary universe.

## Main results

- `isUnit_okaGerm`: a holomorphic function not vanishing at `x` has invertible germ at `x`.
- the stalks of `𝒪_{ℂ^ι}` are local rings. The instance is anonymous, so it has no name to cite;
  it is `IsLocalRing ((okaCommPresheaf ι).stalk x)`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Limits

universe u

variable {ι : Type u} [Fintype ι]

/-- The presheaf of commutative rings of holomorphic functions on `ℂ^ι`. -/
noncomputable def okaCommPresheaf (ι : Type u) [Fintype ι] :
    TopCat.Presheaf CommRingCat.{u} (TopCat.of (ι → ℂ)) where
  obj U := CommRingCat.of (OkaRing U.unop)
  map f := CommRingCat.ofHom (OkaRing.restrict (leOfHom f.unop)).toRingHom
  map_id U := by ext f; rfl
  map_comp f g := by ext h; rfl

lemma okaCommPresheaf_comp_forget₂ (ι : Type u) [Fintype ι] :
    okaCommPresheaf ι ⋙ forget₂ CommRingCat.{u} RingCat.{u} = okaPresheaf ι := rfl

theorem okaCommPresheaf_isSheaf (ι : Type u) [Fintype ι] :
    Presheaf.IsSheaf (Opens.grothendieckTopology (ι → ℂ)) (okaCommPresheaf ι) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget CommRingCat.{u})]
  have h := okaPresheaf_isSheaf ι
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat.{u})] at h
  exact h

variable {U : Opens (ι → ℂ)}

instance (x : ι → ℂ) : Nontrivial ((okaCommPresheaf ι).stalk x) := by
  refine ⟨1, 0, fun hcon ↦ ?_⟩
  have h1 : (okaCommPresheaf ι).germ ⊤ x trivial (1 : (okaCommPresheaf ι).obj (op ⊤)) =
      (okaCommPresheaf ι).germ ⊤ x trivial (0 : (okaCommPresheaf ι).obj (op ⊤)) := by
    simpa using hcon
  obtain ⟨W, hxW, iU, iV, hW⟩ :=
    (okaCommPresheaf ι).germ_eq (U := ⊤) (V := ⊤) x trivial trivial _ _ h1
  have h2 := congrArg (fun g : OkaRing W ↦ OkaRing.evalHom hxW g) hW
  simp only [OkaRing.evalHom_apply] at h2
  exact one_ne_zero h2

/-- A holomorphic function which does not vanish at `x` has invertible germ at `x`. -/
lemma isUnit_okaGerm {x : ι → ℂ} (hx : x ∈ U) (f : OkaRing U)
    (hf : OkaRing.evalHom hx f ≠ 0) :
    IsUnit ((okaCommPresheaf ι).germ U x hx f) := by
  have hana : ∀ y ∈ U, AnalyticAt ℂ (f.toGlobalFun _) y := (okaAnalytic_iff _).1 f.2
  have hcont : ContinuousOn (f.toGlobalFun _) U := fun y hy ↦
    (hana y hy).continuousAt.continuousWithinAt
  set V : Opens (ι → ℂ) :=
    ⟨(U : Set (ι → ℂ)) ∩ (f.toGlobalFun _) ⁻¹' {0}ᶜ,
      hcont.isOpen_inter_preimage U.isOpen isOpen_compl_singleton⟩ with hVdef
  have hVU : V ≤ U := fun y hy ↦ hy.1
  have hxV : x ∈ V := ⟨hx, by simpa [OkaRing.toGlobalFun_apply f hx] using hf⟩
  have hne : ∀ y ∈ V, f.toGlobalFun _ y ≠ 0 := fun _ hy ↦ hy.2
  -- the reciprocal of `f` is holomorphic on `V`
  have hginv : OkaAnalytic (fun y : V ↦ (f.toGlobalFun _ y.1)⁻¹) :=
    okaAnalytic_restrict fun y hy ↦ (hana y (hVU hy)).inv (hne y hy)
  have hmul : OkaRing.restrict hVU f * OkaRing.mk _ hginv = 1 := by
    refine OkaRing.ext (funext fun y ↦ ?_)
    change f.toFun _ (Opens.inclusion hVU y) * (f.toGlobalFun _ y.1)⁻¹ = 1
    rw [← OkaRing.toGlobalFun_apply f (hVU y.2)]
    exact mul_inv_cancel₀ (hne y y.2)
  have hunit : IsUnit (OkaRing.restrict hVU f) :=
    ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  rw [← TopCat.Presheaf.germ_res_apply (okaCommPresheaf ι) (homOfLE hVU) x hxV f]
  exact hunit.map ((okaCommPresheaf ι).germ V x hxV).hom

instance (x : ι → ℂ) : IsLocalRing ((okaCommPresheaf ι).stalk x) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  obtain ⟨U, hx, f, rfl⟩ := (okaCommPresheaf ι).exists_germ_eq a
  by_cases h : OkaRing.evalHom hx f = 0
  · right
    have hne : OkaRing.evalHom hx (1 - f : (okaCommPresheaf ι).obj (op U)) ≠ 0 := by
      change (1 : ℂ) - OkaRing.evalHom hx f ≠ 0
      rw [h, sub_zero]
      exact one_ne_zero
    simpa using isUnit_okaGerm hx (1 - f : (okaCommPresheaf ι).obj (op U)) hne
  · exact Or.inl (isUnit_okaGerm hx f h)

/-- The structure sheaf of `ℂ^ι`, as a sheaf of commutative rings. -/
noncomputable def okaCommSheaf (ι : Type u) [Fintype ι] :
    TopCat.Sheaf CommRingCat.{u} (TopCat.of (ι → ℂ)) :=
  ⟨okaCommPresheaf ι, okaCommPresheaf_isSheaf ι⟩

/-- The complex space `ℂ^ι` as a locally ringed space. -/
noncomputable def complexSpace (ι : Type u) [Fintype ι] : LocallyRingedSpace.{u} where
  carrier := TopCat.of (ι → ℂ)
  presheaf := okaCommPresheaf ι
  IsSheaf := okaCommPresheaf_isSheaf ι
  isLocalRing := inferInstance

@[simp]
lemma complexSpace_presheaf (ι : Type u) [Fintype ι] :
    (complexSpace ι).presheaf = okaCommPresheaf ι :=
  rfl

/-- Complex affine `n`-space `ℂ^n`, as a locally ringed space in an arbitrary universe.

We index the coordinates by `ULift (Fin n)` rather than `Fin n` so that the underlying type
`ULift (Fin n) → ℂ` lives in `Type u`; this keeps `complexAffineSpace` universe polymorphic,
matching `AlgebraicGeometry.Scheme`. -/
noncomputable abbrev complexAffineSpace (n : ℕ) : LocallyRingedSpace.{u} :=
  complexSpace (ULift.{u} (Fin n))

end
