/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.RelativeSerreFinite
public import Other.Oka.Analytification.GAGA.ProjectiveSpace

/-!
# Relative Serre vanishing for schemes over `ℂ`

Let `π : Y' ⟶ Y` and `j : Y' ⟶ ℙⁿ` be morphisms of schemes locally of finite type over `ℂ`
such that `(π, j) : Y' ⟶ Y ×_ℂ ℙⁿ` is a closed immersion (as produced by Chow's lemma). For a
sheaf of modules `G` on `Y'` let `G(m) = G ⊗ j^* O(m)` (`ComplexAnalytic.twistAlong j G m`): the
twist of `G` by the pullback along `j` of the `m`-th power of the standard cocycle `(Xⱼ / Xᵢ)` of
`ℙⁿ` (`AlgebraicGeometry.Scheme.Modules.twist` with
`AlgebraicGeometry.Scheme.Modules.Cocycle.comap`).

* **Relative Serre vanishing** (`ComplexAnalytic.exists_isPushforwardAcyclic_twistAlong`): if `Y`
  is quasi-compact, for coherent `G` there is `m₀` such that `G(m)` is `π`-acyclic for all
  `m ≥ m₀`, i.e. the higher direct images `Rᵠ π_* G(m)` vanish
  (`TopCat.Sheaf.IsPushforwardAcyclic`).
* **Direct images** (for every `m`): `π_* G(m)` is quasi-coherent for quasi-coherent `G`
  (`ComplexAnalytic.isQuasicoherent_pushforward_twistAlong`), and over an affine open `V ⊆ Y` its
  sections over `D(g)` are the localisation at `g` of `Γ(V, π_* G(m)) = Γ(π⁻¹ V, G(m))`
  (`ComplexAnalytic.exists_restrictOpen_eq_pow_smul_pushforward_twistAlong`,
  `ComplexAnalytic.exists_pow_smul_eq_zero_pushforward_twistAlong`).
* **Finiteness** (`ComplexAnalytic.exists_module_finite_pushforward_twistAlong`): for coherent `G`
  and an affine open `V ⊆ Y`, `Γ(V, π_* G(m))` is a finite `Γ(Y, V)`-module for `m ≫ 0`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic

variable {Y Y' : SchemeLFTℂ.{u}} (π : Y' ⟶ Y) {n : ℕ} (j : Y' ⟶ projectiveSpace.{u} n)

/-- The morphisms `π : Y' ⟶ Y` and `j : Y' ⟶ ℙⁿ` agree over `Spec ℂ`. -/
lemma hom_left_comp_obj_hom_eq :
    π.hom.left ≫ Y.obj.hom = j.hom.left ≫ (projectiveSpace.{u} n).obj.hom :=
  (Over.w π.hom).trans (Over.w j.hom).symm

/-- The twist `G(m) = G ⊗ j^* O(m)` of a sheaf of modules `G` on `Y'` along `j : Y' ⟶ ℙⁿ`. -/
noncomputable abbrev twistAlong
    (G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf) (m : ℤ) :
    SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf :=
  ProjectiveSpace.twistAlong j.hom.left G m

/-- **Relative Serre vanishing.** Let `π : Y' ⟶ Y` and `j : Y' ⟶ ℙⁿ` be morphisms of schemes
locally of finite type over `ℂ` such that `(π, j) : Y' ⟶ Y ×_ℂ ℙⁿ` is a closed immersion, with
`Y` quasi-compact. For every coherent `G` on `Y'` there is `m₀` such that `G(m) = G ⊗ j^* O(m)`
is `π`-acyclic for all `m ≥ m₀`. -/
theorem exists_isPushforwardAcyclic_twistAlong [CompactSpace Y.obj.left]
    [IsClosedImmersion (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j))]
    (G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf) [hG : G.IsCoherent] :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → TopCat.Sheaf.IsPushforwardAcyclic π.hom.left.toLRSHom.base
      (twistAlong j G m).toAb := by
  haveI : LocallyOfFiniteType Y.obj.hom := Y.property
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  haveI : IsLocallyNoetherian Y.obj.left := LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
  haveI : SheafOfModules.IsCoherent (R := Y'.obj.left.ringCatSheaf) G := hG
  haveI : IsClosedImmersion (pullback.lift (f := Y.obj.hom) (g := ProjectiveSpace.toSpec n _)
      π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)) := ‹_›
  exact ProjectiveSpace.exists_isPushforwardAcyclic_twistAlong Y.obj.hom π.hom.left j.hom.left
    (hom_left_comp_obj_hom_eq π j) G

section Sections

variable [IsClosedImmersion (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j))]

/-- The pushforward `π_* G(m)` of the twist of a quasi-coherent sheaf is quasi-coherent. -/
theorem isQuasicoherent_pushforward_twistAlong
    (G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf) [hG : G.IsQuasicoherent]
    (m : ℤ) : ((SheafOfModules.pushforward.{u} π.hom.left.toLRSHom.toRingSheafHom).obj
      (twistAlong j G m)).IsQuasicoherent := by
  haveI : SheafOfModules.IsQuasicoherent (R := Y'.obj.left.ringCatSheaf) G := hG
  haveI : IsClosedImmersion (pullback.lift (f := Y.obj.hom) (g := ProjectiveSpace.toSpec n _)
      π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)) := ‹_›
  exact ProjectiveSpace.isQuasicoherent_pushforward_twistAlong Y.obj.hom π.hom.left j.hom.left
    (hom_left_comp_obj_hom_eq π j) G m

variable {V : Y.obj.left.Opens} (hV : IsAffineOpen V)
  (G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf)

include hV in
/-- Sections of `π_* G(m)` over a basic open `D(g)` of an affine open `V` extend to `V` after
multiplication by a power of `g`: `Γ(D(g), π_* G(m))` is the localisation of
`Γ(V, π_* G(m)) = Γ(π⁻¹ V, G(m))` at `g`. -/
theorem exists_restrictOpen_eq_pow_smul_pushforward_twistAlong [hG : G.IsQuasicoherent]
    (m : ℤ) (g : Γ(Y.obj.left, V))
    (s : Γ((Scheme.Modules.pushforward π.hom.left).obj (twistAlong j G m),
      Y.obj.left.basicOpen g)) :
    ∃ (k : ℕ) (t : Γ((Scheme.Modules.pushforward π.hom.left).obj (twistAlong j G m), V)),
      TopCat.Presheaf.restrictOpen t (Y.obj.left.basicOpen g) (Y.obj.left.basicOpen_le g) =
        TopCat.Presheaf.restrictOpen g (Y.obj.left.basicOpen g)
          (Y.obj.left.basicOpen_le g) ^ k • s := by
  haveI : SheafOfModules.IsQuasicoherent (R := Y'.obj.left.ringCatSheaf) G := hG
  haveI : IsClosedImmersion (pullback.lift (f := Y.obj.hom) (g := ProjectiveSpace.toSpec n _)
      π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)) := ‹_›
  exact ProjectiveSpace.exists_restrictOpen_eq_pow_smul_pushforward_twistAlong Y.obj.hom
    π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j) hV G m g s

include hV in
/-- A section of `π_* G(m)` over an affine open `V` vanishing on `D(g)` is killed by a power
of `g`. -/
theorem exists_pow_smul_eq_zero_pushforward_twistAlong [hG : G.IsQuasicoherent] (m : ℤ)
    (g : Γ(Y.obj.left, V))
    (t : Γ((Scheme.Modules.pushforward π.hom.left).obj (twistAlong j G m), V))
    (ht : TopCat.Presheaf.restrictOpen t (Y.obj.left.basicOpen g)
      (Y.obj.left.basicOpen_le g) = 0) :
    ∃ k : ℕ, g ^ k • t = 0 := by
  haveI : SheafOfModules.IsQuasicoherent (R := Y'.obj.left.ringCatSheaf) G := hG
  haveI : IsClosedImmersion (pullback.lift (f := Y.obj.hom) (g := ProjectiveSpace.toSpec n _)
      π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)) := ‹_›
  exact ProjectiveSpace.exists_pow_smul_eq_zero_pushforward_twistAlong Y.obj.hom
    π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j) hV G m g t ht

include hV in
/-- **Finiteness of direct images.** For coherent `G` and an affine open `V ⊆ Y`,
`Γ(V, π_* G(m)) = Γ(π⁻¹ V, G(m))` is a finite `Γ(Y, V)`-module for `m ≫ 0`. -/
theorem exists_module_finite_pushforward_twistAlong [hG : G.IsCoherent] :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → Module.Finite Γ(Y.obj.left, V)
      Γ((Scheme.Modules.pushforward π.hom.left).obj (twistAlong j G m), V) := by
  haveI : LocallyOfFiniteType Y.obj.hom := Y.property
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  haveI : IsLocallyNoetherian Y.obj.left := LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
  haveI : SheafOfModules.IsCoherent (R := Y'.obj.left.ringCatSheaf) G := hG
  haveI : IsClosedImmersion (pullback.lift (f := Y.obj.hom) (g := ProjectiveSpace.toSpec n _)
      π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)) := ‹_›
  exact ProjectiveSpace.exists_module_finite_pushforward_twistAlong Y.obj.hom hV π.hom.left
    j.hom.left (hom_left_comp_obj_hom_eq π j) G

end Sections

end ComplexAnalytic

end
