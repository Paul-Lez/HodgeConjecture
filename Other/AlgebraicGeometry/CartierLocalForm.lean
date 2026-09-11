/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DiscreteValuationLocalRing
public import Other.AlgebraicGeometry.DivisorOfRationalSection
public import HodgeConjecture.Definitions.AlgebraicGeometry.Points

/-!
# The algebraic local form of a Cartier local equation

This file carries out sub-obligation (2) of §4.3 step 4 of `docs/DIVISOR_HANDOFF.md`: the purely
algebraic normal form of the local equation of a Cartier datum at a codimension-one point.

`Scheme.CartierData.LocalForm c i x` bundles, for a point `x` of codimension one lying in the
`i`-th member of the trivializing cover:

* an affine open `V ∋ x` contained in `c.opens i`;
* a regular function `h : Γ(S, V)` whose order of vanishing at `x` is one — a local equation of
  the prime divisor `Z_x = closure {x}`;
* a unit `u : Γ(S, V)ˣ`;

together with the factorisation `c.fn i = u · h ^ (c.divisor x)` in the function field and the
fact that the zero locus of `h` on `V` is exactly `Z_x ∩ V`
(`Scheme.CartierData.LocalForm.zeroLocus_eq`).

The existence theorem `Scheme.CartierData.exists_localForm` is proved for a smooth integral
projective complex scheme. Its inputs are:

* `isDiscreteValuationRing_stalk_of_coheight_eq_one` — the stalk at `x` is a discrete valuation
  ring, because it is regular (smoothness) of dimension one (codimension one);
* `Scheme.exists_unit_mul_zpow_eq` — the resulting factorisation `c.fn i = u · π ^ n` of the local
  equation in the function field, `π` a uniformiser of the stalk and `n = ord_x (c.fn i)`;
* the passage from the stalk to a small enough affine neighbourhood, where `π` and `u` become a
  regular function and a unit;
* `exists_coheight_eq_one_of_not_isUnit_germ` — Krull's principal ideal theorem, in the form that
  a nonzero regular function vanishing at a point of an affine open vanishes at a codimension-one
  generization of it — together with the finiteness `Scheme.ord_support_finite` of the divisor of
  `h`, which is what allows the neighbourhood to be shrunk until the zero locus of `h` is exactly
  `Z_x`: all the other codimension-one zeros of `h` are removed, and no new component can appear
  because every point of the zero locus specializes from a codimension-one zero.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **The local form of a Cartier local equation at a codimension-one point.** An affine
neighbourhood `V` of `x` inside the `i`-th member of the cover, a local equation `h` of the prime
divisor `Z_x` on `V`, and a unit `u` on `V`, with `c.fn i = u · h ^ (c.divisor x)` in the function
field. -/
structure Scheme.CartierData.LocalForm {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S]
    (c : S.CartierData) (i : c.ι) (x : S) where
  /-- The affine neighbourhood of `x` on which the local equation takes its normal form. -/
  opens : S.Opens
  /-- The neighbourhood is affine. -/
  isAffineOpen : IsAffineOpen opens
  /-- The neighbourhood contains `x`. -/
  mem : x ∈ opens
  /-- The neighbourhood is contained in the `i`-th member of the trivializing cover. -/
  le : opens ≤ c.opens i
  /-- The local equation of the prime divisor of `x`. -/
  equation : Γ(S, opens)
  /-- The unit comparing the Cartier local equation with the power of the local equation. -/
  unit : Γ(S, opens)ˣ
  /-- The local equation vanishes to order exactly one along `Z_x`. -/
  ord_equation :
    S.ord (S.germToFunctionField (h := ⟨⟨x, mem⟩⟩) opens equation) x = 1
  /-- The Cartier local equation is the `c.divisor x`-th power of the local equation, up to a
  unit, as an element of the function field. -/
  fn_eq : c.fn i =
    S.germToFunctionField (h := ⟨⟨x, mem⟩⟩) opens (unit : Γ(S, opens)) *
      (S.germToFunctionField (h := ⟨⟨x, mem⟩⟩) opens equation) ^ (c.divisor x)
  /-- The local equation vanishes on the prime divisor `Z_x = closure {x}`. -/
  notMem_basicOpen : ∀ y ∈ closure ({x} : Set S), y ∉ S.basicOpen equation
  /-- The local equation vanishes *only* on the prime divisor `Z_x`: its zero locus on `opens`
  is exactly `Z_x ∩ opens`. -/
  mem_closure_of_notMem_basicOpen :
    ∀ y ∈ opens, y ∉ S.basicOpen equation → y ∈ closure ({x} : Set S)

/-- The image in the function field of a regular function, computed through the stalk at a point
of its domain. -/
theorem germToFunctionField_eq_algebraMap_germ {S : Scheme.{u}} [IsIntegral S] {U : S.Opens}
    {x : S} (hx : x ∈ U) (s : Γ(S, U)) :
    S.germToFunctionField (h := ⟨⟨x, hx⟩⟩) U s =
      algebraMap (S.presheaf.stalk x) S.functionField (S.presheaf.germ U x hx s) :=
  (@Scheme.algebraMap_germ_eq_germToFunctionField S _ U ⟨⟨x, hx⟩⟩ x hx s).symm

namespace Scheme.CartierData.LocalForm

variable {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S] {c : S.CartierData} {i : c.ι} {x : S}

/-- The zero locus of the local equation on its affine neighbourhood is exactly the prime divisor
`Z_x = closure {x}` cut down to that neighbourhood. -/
theorem zeroLocus_eq (f : c.LocalForm i x) :
    (f.opens : Set S) \ (S.basicOpen f.equation : Set S) =
      closure ({x} : Set S) ∩ (f.opens : Set S) := by
  ext y
  constructor
  · rintro ⟨hy, hyb⟩
    exact ⟨f.mem_closure_of_notMem_basicOpen y hy hyb, hy⟩
  · rintro ⟨hy, hyV⟩
    exact ⟨hyV, f.notMem_basicOpen y hy⟩

end Scheme.CartierData.LocalForm

/-- The image of a regular function in the function field does not depend on the point of its
domain through whose stalk it is computed. -/
theorem algebraMap_germ_eq_of_mem {S : Scheme.{u}} [IsIntegral S] {U : S.Opens} {x y : S}
    (hx : x ∈ U) (hy : y ∈ U) (s : Γ(S, U)) :
    algebraMap (S.presheaf.stalk x) S.functionField (S.presheaf.germ U x hx s) =
      algebraMap (S.presheaf.stalk y) S.functionField (S.presheaf.germ U y hy s) := by
  rw [← germToFunctionField_eq_algebraMap_germ hx s, ← germToFunctionField_eq_algebraMap_germ hy s]

/-- On an affine open, a regular function is a unit in the stalk at a point exactly when it lies
outside the prime ideal of that point: the stalk is the localization at that prime. -/
theorem IsAffineOpen.isUnit_germ_iff_notMem {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)
    (y : U) (f : Γ(S, U)) :
    IsUnit (S.presheaf.germ U y.1 y.2 f) ↔ f ∉ (hU.primeIdealOf y).asIdeal := by
  have := hU.isLocalization_stalk y
  exact IsLocalization.AtPrime.isUnit_to_map_iff
    (S.presheaf.stalk y.1) (hU.primeIdealOf y).asIdeal f

/-- **Krull's principal ideal theorem, geometrically.** If a nonzero regular function on an affine
open of a Noetherian integral scheme vanishes at a point, then it vanishes at a generization of
that point of codimension one: a minimal prime over the principal ideal it generates has height
one. -/
theorem exists_coheight_eq_one_of_not_isUnit_germ {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S]
    {U : S.Opens} (hU : IsAffineOpen U) (f : Γ(S, U)) (hf : f ≠ 0) {z : S} (hz : z ∈ U)
    (hfz : ¬ IsUnit (S.presheaf.germ U z hz f)) :
    ∃ (y : S) (hy : y ∈ U), coheight y = 1 ∧ y ⤳ z ∧
      ¬ IsUnit (S.presheaf.germ U y hy f) := by
  have : IsDomain Γ(S, U) := @IsIntegral.component_integral S _ U ⟨⟨z, hz⟩⟩
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : (Ideal.span {f}).IsPrincipal := ⟨⟨f, rfl⟩⟩
  have hfP : f ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
    by_contra hc
    exact hfz ((hU.isUnit_germ_iff_notMem ⟨z, hz⟩ f).mpr hc)
  obtain ⟨q, hq, hqle⟩ :=
    Ideal.exists_minimalPrimes_le (I := Ideal.span {f})
      (J := (hU.primeIdealOf ⟨z, hz⟩).asIdeal) ((Ideal.span_singleton_le_iff_mem _).mpr hfP)
  have hqp : q.IsPrime := hq.1.1
  have hfq : f ∈ q := hq.1.2 (Ideal.mem_span_singleton_self f)
  have hqbot : q ≠ ⊥ := by
    intro hbot
    exact hf (by simpa [hbot] using hfq)
  have hq1 : q.height = 1 :=
    le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq)
      (Order.one_le_iff_ne_zero.mpr fun h => hqbot (Ideal.height_eq_zero_iff_eq_bot.mp h))
  set Q : ↥(Spec Γ(S, U)) := ⟨q, hqp⟩ with hQ
  set yU : ↥U.toScheme := hU.isoSpec.inv Q with hyU
  have hyQ : hU.primeIdealOf (yU : ↥U) = Q := by
    have h := Scheme.Hom.comp_apply hU.isoSpec.inv hU.isoSpec.hom Q
    rw [hU.isoSpec.inv_hom_id] at h
    rw [hyU]
    exact h.symm
  have hcoh : coheight (U.ι yU) = 1 := by
    have h1 : coheight (U.ι yU) = coheight yU := coheight_eq_of_isOpenImmersion U.ι
    have h2 : coheight (hU.isoSpec.hom yU) = coheight yU :=
      coheight_eq_of_isOpenImmersion hU.isoSpec.hom
    have h3 : hU.isoSpec.hom yU = Q := hyQ
    rw [h1, ← h2, h3, ← idealHeight_eq_coheight]
    exact hq1
  have hspec : U.ι yU ⤳ z := by
    have h1 : Q ⤳ hU.primeIdealOf ⟨z, hz⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hqle
    have h2 := h1.map hU.fromSpec.continuous
    have h3 : hU.fromSpec Q = U.ι yU := by
      rw [← IsAffineOpen.isoSpec_inv_ι, hyU]
      exact Scheme.Hom.comp_apply hU.isoSpec.inv U.ι Q
    rwa [h3, hU.fromSpec_primeIdealOf ⟨z, hz⟩] at h2
  have hnot : ¬ IsUnit (S.presheaf.germ U (yU : ↥U).1 (yU : ↥U).2 f) := by
    rw [hU.isUnit_germ_iff_notMem (yU : ↥U) f, hyQ]
    simpa [hQ] using hfq
  exact ⟨(yU : ↥U).1, (yU : ↥U).2, hcoh, hspec, hnot⟩

namespace Scheme.CartierData

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

/-- **Existence of the algebraic local form.** At a codimension-one point of a smooth integral
complex scheme, the local equation of a Cartier datum is a unit times the `c.divisor x`-th power
of a regular function of order of vanishing one. -/
theorem exists_localForm (c : X.left.CartierData) (i : c.ι) (x : X.left)
    (hx : coheight x = 1) (hxi : x ∈ c.opens i) : Nonempty (c.LocalForm i x) := by
  have hdvr : IsDiscreteValuationRing (X.left.presheaf.stalk x) :=
    isDiscreteValuationRing_stalk_of_coheight_eq_one X.hom hx
  obtain ⟨p, u, hp, hordp, hfact⟩ := X.left.exists_unit_mul_zpow_eq hx (c.fn_ne_zero i)
  obtain ⟨W₁, hxW₁, s₁, hs₁⟩ := X.left.presheaf.exists_germ_eq (x := x) p
  obtain ⟨W₂, hxW₂, s₂, hs₂⟩ :=
    X.left.presheaf.exists_germ_eq (x := x) (u : X.left.presheaf.stalk x)
  have hW₁ : W₁ ⊓ W₂ ⊓ c.opens i ≤ W₁ := le_trans inf_le_left inf_le_left
  have hW₂ : W₁ ⊓ W₂ ⊓ c.opens i ≤ W₂ := le_trans inf_le_left inf_le_right
  have hxW : x ∈ W₁ ⊓ W₂ ⊓ c.opens i := ⟨⟨hxW₁, hxW₂⟩, hxi⟩
  set t₁ : Γ(X.left, W₁ ⊓ W₂ ⊓ c.opens i) := X.left.presheaf.map (homOfLE hW₁).op s₁ with ht₁
  set t₂ : Γ(X.left, W₁ ⊓ W₂ ⊓ c.opens i) := X.left.presheaf.map (homOfLE hW₂).op s₂ with ht₂
  have hg₁ : X.left.presheaf.germ _ x hxW t₁ = p := by
    rw [ht₁, X.left.presheaf.germ_res_apply (homOfLE hW₁) x hxW s₁, hs₁]
  have hg₂ : X.left.presheaf.germ _ x hxW t₂ = (u : X.left.presheaf.stalk x) := by
    rw [ht₂, X.left.presheaf.germ_res_apply (homOfLE hW₂) x hxW s₂, hs₂]
  have hxb : x ∈ X.left.basicOpen t₂ := by
    rw [Scheme.mem_basicOpen _ _ x hxW, hg₂]
    exact u.isUnit
  obtain ⟨_, ⟨V, hxV, hVb⟩⟩ :
      ∃ _ : Unit, ∃ V : X.left.affineOpens, x ∈ V.1 ∧ (V.1 : Set X.left) ⊆ X.left.basicOpen t₂ := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVb⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
      hxb (X.left.basicOpen t₂).isOpen
    exact ⟨(), ⟨V, hV⟩, hxV, hVb⟩
  have hVW : V.1 ≤ W₁ ⊓ W₂ ⊓ c.opens i :=
    le_trans hVb (X.left.basicOpen_le t₂)
  have hVi : V.1 ≤ c.opens i := le_trans hVW inf_le_right
  set hh : Γ(X.left, V.1) := X.left.presheaf.map (homOfLE hVW).op t₁ with hhh
  set aa : Γ(X.left, V.1) := X.left.presheaf.map (homOfLE hVW).op t₂ with haa
  have hgh : X.left.presheaf.germ _ x hxV hh = p := by
    rw [hhh, X.left.presheaf.germ_res_apply (homOfLE hVW) x hxV t₁, hg₁]
  have hga : X.left.presheaf.germ _ x hxV aa = (u : X.left.presheaf.stalk x) := by
    rw [haa, X.left.presheaf.germ_res_apply (homOfLE hVW) x hxV t₂, hg₂]
  have hunit : IsUnit aa := by
    refine X.left.toRingedSpace.isUnit_of_isUnit_germ V.1 aa fun y hy => ?_
    have hyb : y ∈ X.left.basicOpen t₂ := hVb hy
    rw [Scheme.mem_basicOpen _ _ y (hVW hy)] at hyb
    rwa [haa, X.left.presheaf.germ_res_apply (homOfLE hVW) y hy t₂]
  -- Shrink to an affine open meeting no other component of the divisor of `hh`.
  set H : X.left.functionField :=
    algebraMap (X.left.presheaf.stalk x) X.left.functionField p with hH
  have hHne : H ≠ 0 := (map_ne_zero_iff _
    (IsFractionRing.injective (X.left.presheaf.stalk x) X.left.functionField)).mpr hp.ne_zero
  have hFfin : (Function.support (X.left.ord H) \ {x}).Finite :=
    (X.left.ord_support_finite H hHne).sdiff
  have hZclosed :
      IsClosed (⋃ y ∈ Function.support (X.left.ord H) \ {x}, closure ({y} : Set X.left)) :=
    hFfin.isClosed_biUnion fun y _ => isClosed_closure
  have hxZ : x ∉ ⋃ y ∈ Function.support (X.left.ord H) \ {x}, closure ({y} : Set X.left) := by
    simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
    rintro y hyF hxcl
    have hy0 : X.left.ord H y ≠ 0 := Function.mem_support.mp hyF.1
    have hy1 : coheight y = 1 := by
      by_contra hc
      exact hy0 (Scheme.ord_eq_zero_of_coheight_neq_one hc H)
    have hyx : y ⤳ x := specializes_iff_mem_closure.mpr hxcl
    have hne : x ≠ y := fun h => hyF.2 (by rw [h]; rfl)
    have hlt : x < y := ⟨hyx, fun hxy => hne (hxy.antisymm hyx).eq⟩
    have hcolt := Order.coheight_strictAnti hlt (by simp [hy1])
    rw [hy1, hx] at hcolt
    exact absurd hcolt (by simp)
  obtain ⟨W, hxW, hWsub⟩ : ∃ W : X.left.affineOpens, x ∈ W.1 ∧ (W.1 : Set X.left) ⊆
      (V.1 : Set X.left) ∩
        (⋃ y ∈ Function.support (X.left.ord H) \ {x}, closure ({y} : Set X.left))ᶜ := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWsub⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_inter hxV hxZ) (V.1.isOpen.inter hZclosed.isOpen_compl)
    exact ⟨⟨W, hW⟩, hxW, hWsub⟩
  have hWV : W.1 ≤ V.1 := fun y hy => (hWsub hy).1
  have hWi : W.1 ≤ c.opens i := le_trans hWV hVi
  set hw : Γ(X.left, W.1) := X.left.presheaf.map (homOfLE hWV).op hh with hhw
  set aw : Γ(X.left, W.1) := X.left.presheaf.map (homOfLE hWV).op aa with haw
  have hgermW : ∀ {y : X.left} (hy : y ∈ W.1),
      X.left.presheaf.germ W.1 y hy hw = X.left.presheaf.germ V.1 y (hWV hy) hh :=
    fun hy => X.left.presheaf.germ_res_apply (homOfLE hWV) _ hy hh
  have hgermWa : ∀ {y : X.left} (hy : y ∈ W.1),
      X.left.presheaf.germ W.1 y hy aw = X.left.presheaf.germ V.1 y (hWV hy) aa :=
    fun hy => X.left.presheaf.germ_res_apply (homOfLE hWV) _ hy aa
  have hgw : X.left.presheaf.germ W.1 x hxW hw = p := by rw [hgermW hxW, hgh]
  have hgaw : X.left.presheaf.germ W.1 x hxW aw = (u : X.left.presheaf.stalk x) := by
    rw [hgermWa hxW, hga]
  have hunitW : IsUnit aw := by
    rw [haw]
    exact hunit.map (X.left.presheaf.map (homOfLE hWV).op).hom
  have hwne : hw ≠ 0 := by
    intro h0
    apply hp.ne_zero
    rw [← hgw, h0]
    simp
  have hgerm : ∀ (s : Γ(X.left, W.1)),
      X.left.germToFunctionField (h := ⟨⟨x, hxW⟩⟩) W.1 s =
        algebraMap (X.left.presheaf.stalk x) X.left.functionField
          (X.left.presheaf.germ _ x hxW s) := fun s =>
    germToFunctionField_eq_algebraMap_germ hxW s
  refine ⟨{
    opens := W.1
    isAffineOpen := W.2
    mem := hxW
    le := hWi
    equation := hw
    unit := hunitW.unit
    ord_equation := ?_
    fn_eq := ?_
    notMem_basicOpen := ?_
    mem_closure_of_notMem_basicOpen := ?_ }⟩
  · rw [hgerm, hgw]
    exact hordp
  · rw [hgerm, hgerm, hgw, IsUnit.unit_spec, hgaw, c.divisor_apply_of_mem i x hxi]
    exact hfact
  · intro y hy hyb
    have hxbh : x ∈ X.left.basicOpen hw := by
      obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp hy _ (X.left.basicOpen hw).isOpen hyb
      rwa [Set.mem_singleton_iff.mp hz'] at hz
    rw [Scheme.mem_basicOpen _ _ x hxW, hgw] at hxbh
    exact hp.not_isUnit hxbh
  · intro z hzW hzb
    have hnu : ¬ IsUnit (X.left.presheaf.germ W.1 z hzW hw) := by
      rw [← Scheme.mem_basicOpen _ _ z hzW]
      exact hzb
    obtain ⟨y, hyW, hy1, hyz, hynu⟩ :=
      exists_coheight_eq_one_of_not_isUnit_germ W.2 hw hwne hzW hnu
    have : IsDiscreteValuationRing (X.left.presheaf.stalk y) :=
      isDiscreteValuationRing_stalk_of_coheight_eq_one X.hom hy1
    have hHy : H = algebraMap (X.left.presheaf.stalk y) X.left.functionField
        (X.left.presheaf.germ W.1 y hyW hw) := by
      rw [hgermW hyW, hH, ← hgh]
      exact (algebraMap_germ_eq_of_mem (hWV hyW) hxV hh).symm
    have hgy0 : X.left.presheaf.germ W.1 y hyW hw ≠ 0 := by
      intro h0
      exact hwne (germ_injective_of_isIntegral X.left y hyW (h0.trans (map_zero _).symm))
    have hord : X.left.ord H y ≠ 0 := by
      rw [hHy]
      exact Scheme.ord_ne_zero_of_not_isUnit hy1 hgy0 hynu
    have hyx : y = x := by
      by_contra hne
      exact (hWsub hyW).2
        (Set.mem_biUnion ⟨Function.mem_support.mpr hord, hne⟩ (subset_closure rfl))
    rw [← hyx]
    exact specializes_iff_mem_closure.mp hyz

end Scheme.CartierData

end AlgebraicGeometry
