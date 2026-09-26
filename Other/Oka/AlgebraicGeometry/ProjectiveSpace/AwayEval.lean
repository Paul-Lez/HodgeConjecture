/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.GammaSpecAdjunction
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.Points

/-!
# Values of sections of `𝒪_{ℙⁿ}` over a standard open at rational points

For `f` homogeneous of positive degree, sections of `𝒪_{ℙⁿ}` over `D₊(f)` are `awayToSection a`,
`a ∈ (A_f)₀`. At the point `p = Proj.awayι (awayPoint v f)` given by a vector `v` with
`f(v) ≠ 0`, the section `awayToSection a` is a unit in the stalk iff `a(v) ≠ 0`
(`ProjectiveSpace.awayι_awayPoint_mem_basicOpen_iff`). The restriction to `D₊(f)` of the global
constant `r` (pulled back along `ℙⁿ ⟶ Spec R`) is `awayToSection` of the constant `r` of `(A_f)₀`
(`ProjectiveSpace.restrict_toSpec_appTop`). Together these compute values of sections of `𝒪` at
rational points; for the analytification this is done in
`Other/Oka/Analytification/GAGA/TwistTransition.lean`.

## Main results

- `LocallyRingedSpace.toSpecOfAlgMap_comapAlgMap`: a morphism to `Spec R` is the morphism of the
  algebra structure it pulls back.
- `ProjectiveSpace.restrict_toSpec_appTop`, `ProjectiveSpace.awayι_awayPoint_mem_basicOpen_iff`,
  `ProjectiveSpace.awayEval_awayXDiv`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- A morphism to an affine scheme is the morphism of the algebra structure it pulls back. -/
lemma LocallyRingedSpace.toSpecOfAlgMap_comapAlgMap {X : LocallyRingedSpace.{u}}
    {R : CommRingCat.{u}} (g : X ⟶ Spec.locallyRingedSpaceObj R) :
    X.toSpecOfAlgMap (LocallyRingedSpace.comapAlgMap g (toSpecΓ R).hom) = g := by
  rw [← LocallyRingedSpace.comp_toSpecOfAlgMap]
  have := ΓSpec.right_triangle R
  exact (congrArg (g ≫ ·) this).trans (Category.comp_id g)

/-- The restriction of a global section to `U`, read on the open subscheme `U`, is its pullback
along the inclusion. -/
lemma Scheme.Opens.topIso_inv_restrictOpen {X : Scheme.{u}} (U : X.Opens) (x : Γ(X, ⊤)) :
    U.topIso.inv (TopCat.Presheaf.restrictOpen x U le_top) = U.ι.appTop x := by
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop, TopCat.Presheaf.restrictOpen,
    TopCat.Presheaf.restrict]
  rw [← CommRingCat.comp_apply]
  exact congr($((X.presheaf.map_comp _ _).symm).hom x)

end AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

open HomogeneousLocalization MvPolynomial

variable {n : ℕ} {R : Type u} [CommRing R]

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R

/-- The constants `R → Away 𝒜 f`, through `𝒜 0`. -/
noncomputable abbrev awayConst (f : MvPolynomial (Fin (n + 1)) R) : R →+* Away 𝒜 f :=
  (fromZeroRingHom 𝒜 _).comp (algebraMap R (𝒜 0))

/-- The standard open `D₊(f)` maps to `Spec R` through `Spec (A_f)₀`. -/
lemma basicOpen_ι_toSpec {f : MvPolynomial (Fin (n + 1)) R} {m : ℕ} (f_deg : f ∈ 𝒜 m)
    (hm : 0 < m) :
    (Proj.basicOpen 𝒜 f).ι ≫ toSpec n R =
      Proj.basicOpenToSpec 𝒜 f ≫ Spec.map (CommRingCat.ofHom (awayConst f)) := by
  have h : Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f f_deg hm = (Proj.basicOpen 𝒜 f).ι := by
    rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm, ← Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hm,
      Iso.hom_inv_id_assoc]
  rw [← h, Category.assoc, toSpec, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- **The constants of `ℙⁿ` on a standard open**: the restriction to `D₊(f)` of the global
constant `r` is `awayToSection` of the constant `r` of `(A_f)₀`. -/
lemma restrict_toSpec_appTop {f : MvPolynomial (Fin (n + 1)) R} {m : ℕ} (f_deg : f ∈ 𝒜 m)
    (hm : 0 < m) (r : R) :
    TopCat.Presheaf.restrictOpen ((toSpec n R).appTop ((Scheme.ΓSpecIso (.of R)).inv r))
      (Proj.basicOpen 𝒜 f) le_top = Proj.awayToSection 𝒜 f (awayConst f r) := by
  apply (Proj.basicOpen 𝒜 f).topIso.commRingCatIsoToRingEquiv.symm.injective
  have h1 := congr($(Proj.basicOpenToSpec_app_top 𝒜 f).hom
    ((Scheme.ΓSpecIso (.of (Away 𝒜 f))).inv (awayConst f r)))
  have h2 := congr($(basicOpen_ι_toSpec f_deg hm).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv r))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h1 h2
  have h3 := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (awayConst (R := R) f))).hom
    r)
  rw [Iso.inv_hom_id_apply] at h1
  refine (Scheme.Opens.topIso_inv_restrictOpen _ _).trans (h2.trans ?_)
  exact (congrArg _ h3.symm).trans h1


variable {K : Type*} [Field K] (φ : R →+* K)

/-- Evaluation at `v` is `φ` on the constants of `(A_{Xᵢ})₀`. -/
lemma awayEval_awayXBase (v : Fin (n + 1) → K) (i : Fin (n + 1)) (hi : eval₂ φ v (X i) ≠ 0)
    (r : R) : awayEval (φ := φ) v (X i) hi (awayXBase R i r) = φ r := by
  have := congr($(awayEval_comp_toAwayX (φ := φ) v i hi) (C r))
  simpa using this

/-- The value of `Xⱼ / Xᵢ` at `v` is `vⱼ / vᵢ`. -/
lemma awayEval_awayXDiv (v : Fin (n + 1) → K) (i j : Fin (n + 1)) (hi : eval₂ φ v (X i) ≠ 0) :
    awayEval (φ := φ) v (X i) hi (awayXDiv R i j) = v j / v i := by
  have hi' : v i ≠ 0 := by simpa using hi
  obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · rw [awayXDiv_self, map_one, div_self hi']
  · have := congr($(awayEval_comp_toAwayX (φ := φ) v i hi) (X m))
    simpa [dehomogenizeVec] using this

/-- **A point of a chart lies in the basic open of a section iff the section does not vanish
there**: for `p = Proj.awayι (awayPoint v)`, `p ∈ D(awayToSection a)` iff `a(v) ≠ 0`. -/
lemma awayι_awayPoint_mem_basicOpen_iff (v : Fin (n + 1) → K) (i : Fin (n + 1))
    (hi : eval₂ φ v (X i) ≠ 0) (a : Away 𝒜 (X i)) :
    (Proj.awayι 𝒜 (X i) (X_mem_homogeneousSubmodule_one i) Nat.one_pos).base
        (awayPoint (φ := φ) v (X i) hi) ∈
      ℙₒ(n; R).basicOpen (Proj.awayToSection 𝒜 (X i) a) ↔ awayEval (φ := φ) v (X i) hi a ≠ 0 := by
  have hX := X_mem_homogeneousSubmodule_one (R := R) i
  have e1 : Proj.basicOpenToSpec 𝒜 (X i) ⁻¹ᵁ PrimeSpectrum.basicOpen a =
      (U n R i).ι ⁻¹ᵁ ℙₒ(n; R).basicOpen (Proj.awayToSection 𝒜 (X i) a) := by
    rw [Proj.basicOpenToSpec, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
      Scheme.Opens.toSpecΓ_preimage_basicOpen]
    rfl
  set q := awayPoint (φ := φ) v (X i) hi
  have hq : (Proj.awayι 𝒜 (X i) hX Nat.one_pos).base q =
      (U n R i).ι.base ((Proj.basicOpenIsoSpec 𝒜 (X i) hX Nat.one_pos).inv.base q) := by
    rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 (X i) hX Nat.one_pos, Scheme.Hom.comp_apply]
    rfl
  have hq' : (Proj.basicOpenToSpec 𝒜 (X i)).base
      ((Proj.basicOpenIsoSpec 𝒜 (X i) hX Nat.one_pos).inv.base q) = q := by
    rw [← Proj.basicOpenIsoSpec_hom 𝒜 (X i) hX Nat.one_pos, ← Scheme.Hom.comp_apply,
      Iso.inv_hom_id]
    rfl
  rw [hq, ← Scheme.Hom.mem_preimage, ← e1]
  change (Proj.basicOpenToSpec 𝒜 (X i)).base
    ((Proj.basicOpenIsoSpec 𝒜 (X i) hX Nat.one_pos).inv.base q) ∈ PrimeSpectrum.basicOpen a ↔ _
  rw [hq']
  change a ∉ q.asIdeal ↔ _
  exact not_congr RingHom.mem_ker

end AlgebraicGeometry.ProjectiveSpace

end
