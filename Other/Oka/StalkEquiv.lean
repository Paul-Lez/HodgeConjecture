/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.ComplexSpace
public import Other.Oka.Weierstrass

/-!
# The stalks of the structure sheaf of `ℂ^ι`

We identify the stalk of `𝒪_{ℂ^ι}` at a point `y` with the ring `LocalOkaRing ι` of power
series converging on a neighbourhood of the origin.

This is the bridge between the two descriptions of germs used in the project: the sheaf
theoretic one, `(okaCommPresheaf ι).stalk y`, on which `Oka.ComplexSpace` builds the locally
ringed space `ℂ^ι`, and the concrete one, `OkaRing.germ` of `Oka.Weierstrass`, in terms of
which Weierstrass theory is developed. Both send a holomorphic function near `y` to its
Taylor expansion at `y`, and `okaStalkEquiv` says that this determines the same ring.

## Main definitions

- `okaStalkHom`: the map from the stalk at `y` to `LocalOkaRing ι` induced by `OkaRing.germ`.
- `okaStalkEquiv`: the same map, as a ring isomorphism.

## Main results

- `okaStalkEquiv_germ`: the isomorphism sends the germ of `f` to its Taylor series at `y`.
- `constantCoeff_okaStalkEquiv_germ`: its composition with the constant term of a power series
  is evaluation at `y`.
- `mem_maximalIdeal_stalk_iff` and `germ_mem_maximalIdeal_iff`: the maximal ideal of the stalk
  at `y` consists exactly of the germs of functions vanishing at `y`; correspondingly
  `map_okaStalkEquiv_maximalIdeal` and `isLocalRing_okaStalk`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type u} [Fintype ι]

/-- Taking Taylor series at `y` is a cocone on the diagram computing the stalk at `y`. -/
noncomputable def okaStalkCocone (y : ι → ℂ) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of (ι → ℂ)) y).op ⋙ okaCommPresheaf ι) where
  pt := CommRingCat.of (LocalOkaRing ι)
  ι :=
    { app := fun U ↦ CommRingCat.ofHom (OkaRing.germ U.unop.2).toRingHom
      naturality := fun U V f ↦ by
        refine CommRingCat.hom_ext (RingHom.ext fun g ↦ ?_)
        exact OkaRing.germ_restrict (leOfHom f.unop) V.unop.2 g }

/-- The map from the stalk of `𝒪_{ℂ^ι}` at `y` to the ring of convergent power series sending
the germ of a holomorphic function to its Taylor series at `y`. -/
noncomputable def okaStalkHom (y : ι → ℂ) :
    (okaCommPresheaf ι).stalk y ⟶ CommRingCat.of (LocalOkaRing ι) :=
  colimit.desc _ (okaStalkCocone y)

@[simp]
lemma okaStalkHom_germ {y : ι → ℂ} {U : Opens (ι → ℂ)} (hy : y ∈ U) (f : OkaRing U) :
    okaStalkHom y ((okaCommPresheaf ι).germ U y hy f) = OkaRing.germ hy f := by
  rw [← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom (colimit.ι_desc (okaStalkCocone y)
    (op (⟨U, hy⟩ : OpenNhds (X := TopCat.of (ι → ℂ)) y))) f

/-- Every germ at `y` of the structure sheaf is the germ of a holomorphic function on some
neighbourhood of `y`, so the Taylor expansion map is surjective. -/
lemma okaStalkHom_surjective (y : ι → ℂ) :
    Function.Surjective (okaStalkHom y).hom := by
  intro P
  obtain ⟨W, hy, f, hf⟩ := LocalOkaRing.exists_okaRing_germ P y
  exact ⟨(okaCommPresheaf ι).germ W y hy f, by rw [okaStalkHom_germ hy f, hf]⟩

/-- A holomorphic function whose Taylor series at `y` vanishes vanishes on a neighbourhood of
`y`, so the Taylor expansion map is injective: this is the identity theorem. -/
lemma okaStalkHom_injective (y : ι → ℂ) :
    Function.Injective (okaStalkHom y).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨U, hy, f, rfl⟩ := (okaCommPresheaf ι).exists_germ_eq a
  rw [okaStalkHom_germ hy f] at ha
  obtain ⟨W, hWU, hyW, hres⟩ := OkaRing.exists_restrict_eq_zero hy ha
  rw [← TopCat.Presheaf.germ_res_apply (okaCommPresheaf ι) (homOfLE hWU) y hyW f]
  change (okaCommPresheaf ι).germ W y hyW (OkaRing.restrict hWU f) = 0
  rw [hres]
  exact map_zero _

/-- The stalk of the structure sheaf of `ℂ^ι` at a point `y` is the ring of power series
converging near the origin, via the Taylor expansion at `y`. -/
noncomputable def okaStalkEquiv (y : ι → ℂ) :
    (okaCommPresheaf ι).stalk y ≃+* LocalOkaRing ι :=
  RingEquiv.ofBijective (okaStalkHom y).hom ⟨okaStalkHom_injective y, okaStalkHom_surjective y⟩

@[simp]
lemma okaStalkEquiv_germ {y : ι → ℂ} {U : Opens (ι → ℂ)} (hy : y ∈ U) (f : OkaRing U) :
    okaStalkEquiv y ((okaCommPresheaf ι).germ U y hy f) = OkaRing.germ hy f :=
  okaStalkHom_germ hy f

-- Deliberately not `@[simp]`: this lemma's left-hand side is a strict instance of
-- `okaStalkEquiv_germ`'s, so it would be shadowed by it. Note that *neither* fires at present,
-- for an unrelated and far more general reason, which has nothing to do with germs, presheaves
-- or `TopCat`: a lemma stated over a *variable* object of a bundled category indexes that
-- object's carrier in its discrimination-tree keys as a projection, whereas a goal over a
-- *concrete* object has the carrier reduced away before its lookup keys are taken, so the
-- lemma is never retrieved. `rw` is unaffected, and pinning the object restores `simp` ;
-- `simp [okaStalkEquiv_germ (ι := ι)]` does fire. See issue #583.
/-- The stalk isomorphism is `ℂ`-linear: it sends the germ of a constant function to the
corresponding constant power series. -/
lemma okaStalkEquiv_germ_algebraMap {y : ι → ℂ} {U : Opens (ι → ℂ)} (hy : y ∈ U) (c : ℂ) :
    okaStalkEquiv y ((okaCommPresheaf ι).germ U y hy (algebraMap ℂ (OkaRing U) c)) =
      algebraMap ℂ (LocalOkaRing ι) c := by
  rw [okaStalkEquiv_germ hy, AlgHom.commutes]

-- Not `@[simp]`, for a second reason on top of the matching failure described above:
-- `LocalOkaRing.constantCoeff_apply` is `@[simp]` and rewrites the left-hand side to
-- `MvPowerSeries.constantCoeff ↑(…)`, so this statement is not in `simp` normal form either.
/-- Reading off the constant term of the Taylor series at `y` is evaluation at `y`. -/
lemma constantCoeff_okaStalkEquiv_germ {y : ι → ℂ} {U : Opens (ι → ℂ)} (hy : y ∈ U)
    (f : OkaRing U) :
    LocalOkaRing.constantCoeff (okaStalkEquiv y ((okaCommPresheaf ι).germ U y hy f)) =
      OkaRing.evalHom hy f := by
  rw [okaStalkEquiv_germ hy, OkaRing.constantCoeff_germ]

/-- Being a unit is detected by the stalk isomorphism, it being an isomorphism. -/
lemma isUnit_okaStalkEquiv_iff {y : ι → ℂ} (a : (okaCommPresheaf ι).stalk y) :
    IsUnit (okaStalkEquiv y a) ↔ IsUnit a :=
  ⟨fun h ↦ by simpa using h.map (okaStalkEquiv y).symm, fun h ↦ h.map (okaStalkEquiv y)⟩

/-- The maximal ideal of the stalk at `y` consists of the germs whose Taylor series at `y` has
vanishing constant term, i.e. of the germs of functions vanishing at `y`. -/
lemma mem_maximalIdeal_stalk_iff {y : ι → ℂ} (a : (okaCommPresheaf ι).stalk y) :
    a ∈ IsLocalRing.maximalIdeal ((okaCommPresheaf ι).stalk y) ↔
      LocalOkaRing.constantCoeff (okaStalkEquiv y a) = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_okaStalkEquiv_iff,
    LocalOkaRing.isUnit_iff, not_not]

/-- The maximal ideal of the stalk at `y` corresponds to the maximal ideal of `LocalOkaRing ι`,
which is the ideal of series with vanishing constant term. -/
-- Not `@[simp]`: this is `IsLocalRing.map_ringEquiv_maximalIdeal`, which is already `@[simp]`.
lemma map_okaStalkEquiv_maximalIdeal (y : ι → ℂ) :
    (IsLocalRing.maximalIdeal ((okaCommPresheaf ι).stalk y)).map (okaStalkEquiv y) =
      IsLocalRing.maximalIdeal (LocalOkaRing ι) :=
  IsLocalRing.map_ringEquiv_maximalIdeal _

/-- The germ of `f` at `y` lies in the maximal ideal of the stalk exactly when `f` vanishes
at `y`. -/
lemma germ_mem_maximalIdeal_iff {y : ι → ℂ} {U : Opens (ι → ℂ)} (hy : y ∈ U) (f : OkaRing U) :
    (okaCommPresheaf ι).germ U y hy f ∈
        IsLocalRing.maximalIdeal ((okaCommPresheaf ι).stalk y) ↔
      OkaRing.evalHom hy f = 0 := by
  rw [mem_maximalIdeal_stalk_iff, constantCoeff_okaStalkEquiv_germ]

/-- The stalks of `𝒪_{ℂ^ι}` are local rings; this recovers the instance of `Oka.ComplexSpace`
from `LocalOkaRing.instIsLocalRing`. -/
theorem isLocalRing_okaStalk (y : ι → ℂ) : IsLocalRing ((okaCommPresheaf ι).stalk y) :=
  (okaStalkEquiv y).symm.isLocalRing

end
