/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Other.Oka.AlgebraicGeometry.Modules.AffineVanishing
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Presentation
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Cohomology
public import Other.Oka.Topology.Sheaves.Cohomology.Dimension

/-!
# Quasi-coherence is local, and cohomology of quasi-coherent sheaves on affine covers

Let `X` be a scheme.

* If `M` is an `𝒪_X`-module and `X = ⋃ᵢ Uᵢ` is an open cover such that each `M|_{Uᵢ}` is
  isomorphic to `Nᵢ|_{Uᵢ}` for a quasi-coherent `Nᵢ`, then `M` is quasi-coherent
  (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_restrictIso`).
* If `X = U₁ ∪ ⋯ ∪ U_m` is a finite open cover all of whose nonempty finite intersections are
  affine, then `Hᵠ(X, F) = 0` for every quasi-coherent `F` and `q ≥ m`
  (`AlgebraicGeometry.Scheme.Modules.H_eq_zero_of_isAffineOpen_cover`): Serre's affine vanishing
  and the Mayer–Vietoris dimension bound `TopCat.Sheaf.subsingleton_H_of_iSup_eq_top`.

## The two spellings of `𝒪_X`-modules

`X.Modules` is `SheafOfModules X.ringCatSheaf`, while the cohomology
`AlgebraicGeometry.LocallyRingedSpace.H` (and the GAGA comparison map) is stated for
`SheafOfModules X.toLocallyRingedSpace.ringSheaf`. The two sheaves of rings agree by `rfl`
(only the spelling of the site differs), so the two categories of modules are *the same category*,
and for `F : X.Modules` the abelian sheaves `F.toAb` and `(SheafOfModules.toSheaf _).obj F` agree
by `rfl` as well (`AlgebraicGeometry.Scheme.Modules.toAb_eq`); hence so do the cohomology groups
(`AlgebraicGeometry.Scheme.Modules.locallyRingedSpaceH_eq`). Only instance search does not cross
the two spellings, so quasi-coherence is transported by `Iff.rfl`
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_ringSheaf`), and the results are also
stated in the `LocallyRingedSpace.H` spelling
(`AlgebraicGeometry.Scheme.Modules.locallyRingedSpaceH_restrictOpen_eq_zero_of_isAffineOpen`,
`AlgebraicGeometry.Scheme.Modules.locallyRingedSpaceH_eq_zero_of_isAffineOpen_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The structure sheaf is quasi-coherent (it is `free PUnit`). -/
instance isQuasicoherent_unit : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  (SheafOfModules.QuasicoherentData.ofIsIso
    (coproductUniqueIso (fun (_ : PUnit.{u + 1}) ↦ SheafOfModules.unit X.ringCatSheaf)).hom
    (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
      (M := SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1})).some).isQuasicoherent

/-- **Quasi-coherence is local.** If `X = ⋃ᵢ Uᵢ` and `M|_{Uᵢ} ≅ Nᵢ|_{Uᵢ}` with `Nᵢ`
quasi-coherent, then `M` is quasi-coherent. -/
theorem isQuasicoherent_of_restrictIso {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (M : X.Modules) (N : ι → X.Modules) [∀ i, (N i).IsQuasicoherent]
    (e : ∀ i, M.restrict (U i).ι ≅ (N i).restrict (U i).ι) : M.IsQuasicoherent := by
  haveI (V : X.Opens) (Y : Over V) :
      HasSheafify (((Opens.grothendieckTopology X).over V).over Y) AddCommGrpCat.{u} :=
    inferInstance
  haveI (V : X.Opens) (Y : Over V) :
      (((Opens.grothendieckTopology X).over V).over Y).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
    inferInstance
  have (i : ι) : (M.over (U i)).IsQuasicoherent := by
    have : ((N i).over (U i)).IsQuasicoherent := SheafOfModules.isQuasicoherent_over.{u} _ _
    exact (SheafOfModules.QuasicoherentData.ofIsIso
      ((overEquiv (U i)).fullyFaithfulFunctor.preimageIso
        ((overFunctorEquiv (U i)).app M ≪≫ e i ≪≫
          ((overFunctorEquiv (U i)).app (N i)).symm)).inv
      this.nonempty_quasicoherentData.some).isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U (by rw [Opens.coversTop_iff]; exact hU)

section Cover

variable {ι : Type*} [Fintype ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hA : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (⨅ i ∈ I, U i))
  (F : X.Modules) [F.IsQuasicoherent]

include hU hA

/-- **Cohomological dimension of a scheme with a finite affine cover.** If `X` is covered by
`m` opens all of whose nonempty finite intersections are affine, then `Hᵠ(X, F) = 0` for every
quasi-coherent `F` and `q ≥ m`. -/
lemma subsingleton_H_of_isAffineOpen_cover (q : ℕ) (hq : Fintype.card ι ≤ q) :
    Subsingleton (TopCat.Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q) :=
  TopCat.Sheaf.subsingleton_H_of_iSup_eq_top _ U hU (fun I hI q hq ↦ by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne'
    exact subsingleton_H_restrictOpen_of_isAffineOpen F (hA I hI) q) q hq

/-- **Cohomological dimension of a scheme with a finite affine cover**, element form. -/
theorem H_eq_zero_of_isAffineOpen_cover (q : ℕ) (hq : Fintype.card ι ≤ q)
    (x : TopCat.Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q) : x = 0 :=
  (subsingleton_H_of_isAffineOpen_cover U hU hA F q hq).elim x 0

end Cover

section LocallyRingedSpace

/-! ### The `LocallyRingedSpace.H` spelling -/

/-- The underlying abelian sheaf `F.toAb` of `F` regarded as a sheaf of modules over
`X.toLocallyRingedSpace.ringSheaf` is the abelian sheaf `(SheafOfModules.toSheaf _).obj F`. -/
lemma toAb_eq (F : X.Modules) :
    SheafOfModules.toAb (Y := X.toLocallyRingedSpace) F =
      (SheafOfModules.toSheaf X.ringCatSheaf).obj F :=
  rfl

/-- The cohomology `LocallyRingedSpace.H F q` of `F : X.Modules` is the cohomology of the
abelian sheaf `(SheafOfModules.toSheaf _).obj F`. -/
lemma locallyRingedSpaceH_eq (F : X.Modules) (q : ℕ) :
    LocallyRingedSpace.H (Y := X.toLocallyRingedSpace) F q =
      TopCat.Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q :=
  rfl

/-- Quasi-coherence over `X.toLocallyRingedSpace.ringSheaf` is quasi-coherence over
`X.ringCatSheaf` (instance search does not cross the two spellings). -/
lemma isQuasicoherent_iff_ringSheaf (F : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) :
    F.IsQuasicoherent ↔ SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F :=
  Iff.rfl

/-- A coherent sheaf on a scheme is quasi-coherent, in the `X.Modules` spelling. -/
lemma isQuasicoherent_of_isCoherent (F : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F :=
  SheafOfModules.IsCoherent.isQuasicoherent F

/-- **Serre's vanishing theorem for affine opens**, for sheaves of modules over
`X.toLocallyRingedSpace.ringSheaf`. -/
theorem locallyRingedSpaceH_restrictOpen_eq_zero_of_isAffineOpen
    (F : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [hF : F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (q : ℕ)
    (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen U).obj F.toAb) (q + 1)) : x = 0 :=
  @H_restrictOpen_eq_zero_of_isAffineOpen X F hF U hU q x

/-- **Cohomological dimension of a scheme with a finite affine cover**, for sheaves of modules
over `X.toLocallyRingedSpace.ringSheaf`: `Hᵠ(X, F) = 0` for `q ≥ m` if `X` is covered by `m`
opens all of whose nonempty finite intersections are affine. -/
theorem locallyRingedSpaceH_eq_zero_of_isAffineOpen_cover {ι : Type*} [Fintype ι]
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hA : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (⨅ i ∈ I, U i))
    (F : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [hF : F.IsQuasicoherent]
    (q : ℕ) (hq : Fintype.card ι ≤ q) (x : LocallyRingedSpace.H F q) : x = 0 :=
  @H_eq_zero_of_isAffineOpen_cover X ι _ U hU hA F hF q hq x

end LocallyRingedSpace

end AlgebraicGeometry.Scheme.Modules

end
