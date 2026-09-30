/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SimplicialCochainCoefficientChange
public import Other.LinearAlgebra.RationalDenominators
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Clearing denominators of rational simplicial cohomology classes

Let `X` be a simplicial set whose integral simplicial homology in degree `n` is finitely
generated. Every rational simplicial cohomology class of degree `n` (computed by the algebraic
dual of the rational chain complex) has a nonzero integer multiple which comes from an integral
cohomology class (computed by the algebraic dual of the integral chain complex).

The proof is elementary and uses neither the universal coefficient theorem nor any freeness of
submodules of free abelian groups: a rational cocycle which is integer-valued on integral cycles
is cohomologous to an integer-valued cocycle, by extending the induced `ℚ/ℤ`-valued map on
boundaries to all chains one degree down (Baer's criterion, since `ℚ/ℤ` is divisible); and the
denominators of a rational cocycle on cycles are bounded because the induced map on the finitely
generated homology group has a single denominator.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

namespace SSet

variable (X : SSet.{0})

section Lift

variable {M : Type} [AddCommGroup M] [Module ℤ M] (n : ℕ)

/-- The `ℤ`-linear map on integral `n`-chains with prescribed values on the `n`-simplices. -/
def intChainsLift (g : X _⦋n⦌ → M) : (X.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ] M :=
  (Cofan.IsColimit.desc (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M (g x))).hom

lemma intChainsLift_chainOfSimplex (g : X _⦋n⦌ → M) (x : X _⦋n⦌) :
    intChainsLift X n g (chainOfSimplex ℤ X n x) = g x := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M (g x))) x
  have h1 := congrArg (fun z ↦ ModuleCat.Hom.hom z (1 : ℤ)) h
  exact h1.trans (LinearMap.toSpanSingleton_apply_one ℤ M (g x))

/-- Two `ℤ`-linear maps on integral `n`-chains agreeing on the `n`-simplices are equal. -/
lemma intChains_hom_ext {f g : (X.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ] M}
    (h : ∀ x, f (chainOfSimplex ℤ X n x) = g (chainOfSimplex ℤ X n x)) : f = g := by
  have : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply chainComplex_hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact h x
  exact congrArg ModuleCat.Hom.hom this

/-- An additive map between `ℤ`-modules is `ℤ`-linear, whatever the module structures. -/
def _root_.AddMonoidHom.toIntLinearMap' {A B : Type} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (f : A →+ B) : A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' m x := by simpa using map_intCast_smul f ℤ ℤ m x

/-- Two additive maps on integral `n`-chains agreeing on the `n`-simplices are equal. -/
lemma intChains_addHom_ext {f g : (X.chainComplex (ModuleCat.of ℤ ℤ)).X n →+ M}
    (h : ∀ x, f (chainOfSimplex ℤ X n x) = g (chainOfSimplex ℤ X n x)) : f = g := by
  have := intChains_hom_ext X n (f := f.toIntLinearMap') (g := g.toIntLinearMap') h
  exact AddMonoidHom.ext fun x ↦ DFunLike.congr_fun this x

/-- Precomposing a lifted map with the boundary gives the lift of the alternating face sum. -/
lemma intChainsLift_comp_d (g : X _⦋n⦌ → M) :
    intChainsLift X n g ∘ₗ ((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom =
      intChainsLift X (n + 1) (fun x ↦ ∑ i : Fin (n + 2), (-1) ^ (i : ℕ) • g (X.δ i x)) := by
  apply intChains_hom_ext
  intro x
  rw [intChainsLift_chainOfSimplex]
  simp only [LinearMap.comp_apply, chainOfSimplex]
  have h := congrArg (fun k ↦ intChainsLift X n g (k.hom 1))
    (X.ιChainComplex_d (ModuleCat.of ℤ ℤ) x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, map_sum, ModuleCat.hom_zsmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change intChainsLift X n g ((-1) ^ (i : ℕ) • chainOfSimplex ℤ X n (X.δ i x)) = _
  rw [map_zsmul, intChainsLift_chainOfSimplex]

end Lift

section RatEval

variable (n : ℕ)

/-- Evaluation of a rational cochain on integral chains. -/
def ratEval (c : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n)) :
    (X.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ] ℚ :=
  intChainsLift X n (dualToFun ℚ X n c)

lemma ratEval_chainOfSimplex (c : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n))
    (x : X _⦋n⦌) :
    ratEval X n c (chainOfSimplex ℤ X n x) = c (chainOfSimplex ℚ X n x) :=
  intChainsLift_chainOfSimplex X n _ x

lemma ratEval_zero : ratEval X n 0 = 0 :=
  intChains_hom_ext X n fun x ↦ by simp [ratEval_chainOfSimplex]

lemma ratEval_sub (c c' : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n)) :
    ratEval X n (c - c') = ratEval X n c - ratEval X n c' :=
  intChains_hom_ext X n fun x ↦ by simp [ratEval_chainOfSimplex]

lemma ratEval_smul (r : ℚ) (c : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n)) :
    ratEval X n (r • c) = r • ratEval X n c :=
  intChains_hom_ext X n fun x ↦ by simp [ratEval_chainOfSimplex]

/-- Evaluation intertwines the rational coboundary and the integral boundary. -/
lemma ratEval_dualMap_d (c : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n)) :
    ratEval X (n + 1) (((X.chainComplex (ModuleCat.of ℚ ℚ)).d (n + 1) n).hom.dualMap c) =
      ratEval X n c ∘ₗ ((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom := by
  unfold ratEval
  rw [intChainsLift_comp_d]
  congr 1
  funext x
  exact dualToFun_dualMap_d X n c x

/-- A rational cocycle vanishes on integral boundaries. -/
lemma ratEval_d_eq_zero (c : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n))
    (hc : ((X.chainComplex (ModuleCat.of ℚ ℚ)).d (n + 1) n).hom.dualMap c = 0)
    (i : ℕ) (hi : i = n + 1) (y : (X.chainComplex (ModuleCat.of ℤ ℤ)).X i) :
    ratEval X n c (((X.chainComplex (ModuleCat.of ℤ ℤ)).d i n).hom y) = 0 := by
  subst hi
  have h := LinearMap.congr_fun (ratEval_dualMap_d X n c) y
  rw [hc, ratEval_zero] at h
  exact h.symm

/-- Evaluation of an integral cochain, after change of coefficients, is the cast of its values. -/
lemma ratEval_dualCoefficientChange (b : Module.Dual ℤ ((X.chainComplex (ModuleCat.of ℤ ℤ)).X n))
    (z : (X.chainComplex (ModuleCat.of ℤ ℤ)).X n) :
    ratEval X n (dualCoefficientChange (Int.castRingHom ℚ) X n b) z = (b z : ℚ) := by
  have : ratEval X n (dualCoefficientChange (Int.castRingHom ℚ) X n b) =
      (Algebra.linearMap ℤ ℚ) ∘ₗ b := by
    apply intChains_hom_ext
    intro x
    rw [ratEval_chainOfSimplex]
    have h := congrFun (dualToFun_dualCoefficientChange (Int.castRingHom ℚ) X n b) x
    simp only [dualToFun_apply, Function.comp_apply] at h
    rw [h]
    simp
  rw [this]
  simp

end RatEval

section IntegralCocycle

/-- The subgroup `ℤ ⊆ ℚ`. -/
abbrev intSubgroup : AddSubgroup ℚ := AddSubgroup.zmultiples (1 : ℚ)

lemma mem_intSubgroup (q : ℚ) : q ∈ intSubgroup ↔ ∃ m : ℤ, (m : ℚ) = q := by
  simp [intSubgroup, AddSubgroup.mem_zmultiples_iff]

/-- The divisible group `ℚ / ℤ`. -/
abbrev RatModInt : Type := ℚ ⧸ intSubgroup

instance : DivisibleBy RatModInt ℤ :=
  Function.Surjective.divisibleBy (A := ℚ) (α := ℤ) (QuotientAddGroup.mk' intSubgroup)
    (QuotientAddGroup.mk'_surjective intSubgroup)
    fun a n ↦ map_zsmul (QuotientAddGroup.mk' intSubgroup) n a

lemma ratModInt_baer : Module.Baer ℤ RatModInt := Module.Baer.of_divisible _

variable (n : ℕ)

/-- A rational cochain whose values on all integral chains are integers comes from an integral
cochain. -/
lemma exists_intCochain_of_integral (c : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n))
    (h : ∀ z, ∃ m : ℤ, (m : ℚ) = ratEval X n c z) :
    ∃ b : Module.Dual ℤ ((X.chainComplex (ModuleCat.of ℤ ℤ)).X n),
      dualCoefficientChange (Int.castRingHom ℚ) X n b = c := by
  refine ⟨dualOfFun ℤ X n (fun x ↦ (h (chainOfSimplex ℤ X n x)).choose), ?_⟩
  apply dualToFun_injective ℚ X n
  rw [dualToFun_dualCoefficientChange, dualToFun_dualOfFun]
  funext x
  simp only [Function.comp_apply, eq_intCast, dualToFun_apply]
  rw [(h (chainOfSimplex ℤ X n x)).choose_spec, ratEval_chainOfSimplex]

lemma dualCoefficientChange_injective :
    Function.Injective (dualCoefficientChange (Int.castRingHom ℚ) X n) := by
  intro b b' h
  apply dualToFun_injective ℤ X n
  have h' := congrArg (dualToFun ℚ X n) h
  rw [dualToFun_dualCoefficientChange, dualToFun_dualCoefficientChange] at h'
  funext x
  have := congrFun h' x
  simp only [Function.comp_apply, eq_intCast, Int.cast_inj] at this
  exact this

/-- An integral cochain whose rationalisation is a cocycle is a cocycle. -/
lemma dualMap_d_eq_zero_of_dualCoefficientChange
    (b : Module.Dual ℤ ((X.chainComplex (ModuleCat.of ℤ ℤ)).X n))
    (hb : ((X.chainComplex (ModuleCat.of ℚ ℚ)).d (n + 1) n).hom.dualMap
      (dualCoefficientChange (Int.castRingHom ℚ) X n b) = 0) :
    ((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom.dualMap b = 0 := by
  apply dualCoefficientChange_injective X (n + 1)
  rw [dualCoefficientChange_dualMap_d, hb, map_zero]

/-- The composite of two consecutive coboundaries vanishes. -/
lemma dualMap_d_dualMap_d {R : Type} [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ)
    (e : Module.Dual R (K.X n)) :
    (K.d (n + 2) (n + 1)).hom.dualMap ((K.d (n + 1) n).hom.dualMap e) = 0 := by
  ext z
  change e ((K.d (n + 1) n).hom ((K.d (n + 2) (n + 1)).hom z)) = 0
  rw [show (K.d (n + 1) n).hom ((K.d (n + 2) (n + 1)).hom z) = 0 from
    ConcreteCategory.congr_hom (K.d_comp_d (n + 2) (n + 1) n) z, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- **Integrality criterion.** A rational cocycle of positive degree which is integer-valued on
integral cycles is cohomologous to the rationalisation of an integral cocycle. -/
theorem exists_integral_cocycle_succ (k : ℕ)
    (c : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X (k + 1)))
    (hc : ((X.chainComplex (ModuleCat.of ℚ ℚ)).d (k + 2) (k + 1)).hom.dualMap c = 0)
    (hint : ∀ z, ((X.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k).hom z = 0 →
      ∃ m : ℤ, (m : ℚ) = ratEval X (k + 1) c z) :
    ∃ (b : Module.Dual ℤ ((X.chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1)))
      (e : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X k)),
      ((X.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 2) (k + 1)).hom.dualMap b = 0 ∧
      dualCoefficientChange (Int.castRingHom ℚ) X (k + 1) b =
        c - ((X.chainComplex (ModuleCat.of ℚ ℚ)).d (k + 1) k).hom.dualMap e := by
  obtain ⟨d, hd⟩ : ∃ d, d = ((X.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k).hom := ⟨_, rfl⟩
  rw [← hd] at hint
  let q : ℚ →+ RatModInt := QuotientAddGroup.mk' intSubgroup
  let φ : (X.chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1) →+ RatModInt :=
    q.comp (ratEval X (k + 1) c).toAddMonoidHom
  let dA := d.toAddMonoidHom
  have hker : dA.ker ≤ φ.ker := by
    intro z hz
    obtain ⟨m, hm⟩ := hint z hz
    simp only [AddMonoidHom.mem_ker, φ, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, q,
      QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, mem_intSubgroup]
    exact ⟨m, hm⟩
  let g₀ : dA.range →+ RatModInt := (QuotientAddGroup.lift dA.ker φ hker).comp
    (QuotientAddGroup.quotientKerEquivRange dA).symm.toAddMonoidHom
  have hmem : ∀ z, d z ∈ dA.range := fun z ↦ AddMonoidHom.mem_range.mpr ⟨z, rfl⟩
  have hg₀ : ∀ z, g₀ ⟨d z, hmem z⟩ = φ z := by
    intro z
    have h1 : (QuotientAddGroup.quotientKerEquivRange dA).symm ⟨d z, hmem z⟩ =
        QuotientAddGroup.mk z := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    simp only [g₀, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h1,
      QuotientAddGroup.lift_mk]
  obtain ⟨g, hg⟩ := ratModInt_baer.extension_property_addMonoidHom
    dA.range.subtype Subtype.val_injective g₀
  have hg' : ∀ z, g (d z) = φ z := by
    intro z
    have := congrArg (fun h ↦ h ⟨d z, hmem z⟩) hg
    simpa using this.trans (hg₀ z)
  -- lift `g` to a rational-valued map on `k`-chains
  choose lift hlift using fun x : X _⦋k⦌ ↦
    QuotientAddGroup.mk'_surjective intSubgroup (g (chainOfSimplex ℤ X k x))
  let e' : (X.chainComplex (ModuleCat.of ℤ ℤ)).X k →ₗ[ℤ] ℚ := intChainsLift X k lift
  have he' : ∀ y, q (e' y) = g y := by
    have : q.comp e'.toAddMonoidHom = g :=
      intChains_addHom_ext X k fun x ↦ by
        simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, e',
          intChainsLift_chainOfSimplex, q, hlift]
    intro y
    exact DFunLike.congr_fun this y
  let e : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X k) :=
    dualOfFun ℚ X k (fun x ↦ e' (chainOfSimplex ℤ X k x))
  have he : ratEval X k e = e' :=
    intChains_hom_ext X k fun x ↦ by
      rw [ratEval_chainOfSimplex]
      exact congrFun (dualToFun_dualOfFun ℚ X k _) x
  let c' := c - ((X.chainComplex (ModuleCat.of ℚ ℚ)).d (k + 1) k).hom.dualMap e
  have hc' : ∀ z, ∃ m : ℤ, (m : ℚ) = ratEval X (k + 1) c' z := by
    intro z
    have h1 : ratEval X (k + 1) c' z = ratEval X (k + 1) c z - e' (d z) := by
      simp only [c', ratEval_sub, ratEval_dualMap_d, he, LinearMap.sub_apply,
        LinearMap.comp_apply, hd]
    have : q (ratEval X (k + 1) c' z) = 0 := by
      rw [h1, map_sub, he', hg']
      exact sub_self _
    rwa [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, mem_intSubgroup] at this
  obtain ⟨b, hb⟩ := exists_intCochain_of_integral X (k + 1) c' hc'
  refine ⟨b, e, ?_, hb⟩
  apply dualMap_d_eq_zero_of_dualCoefficientChange
  rw [hb]
  simp only [c', map_sub, hc, dualMap_d_dualMap_d, sub_zero]

end IntegralCocycle

section Denominators

set_option backward.isDefEq.respectTransparency false in
/-- Chains killed by the boundary are cycles. -/
lemma exists_cycles_of_d_eq_zero {R : Type} [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ)
    (n j : ℕ) (hj : (ComplexShape.down ℕ).next n = j) (z : K.X n) (hz : (K.d n j).hom z = 0) :
    ∃ ζ : K.cycles n, (K.iCycles n).hom ζ = z := by
  subst hj
  refine ⟨(K.sc n).moduleCatCyclesIso.inv ⟨z, hz⟩, ?_⟩
  exact ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_iCycles ⟨z, hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- Cochains killed by the coboundary are cocycles. -/
lemma exists_cycles_of_d_eq_zero_ab (K : CochainComplex AddCommGrpCat.{0} ℕ)
    (n j : ℕ) (hj : (ComplexShape.up ℕ).next n = j) (z : K.X n) (hz : (K.d n j).hom z = 0) :
    ∃ ζ : K.cycles n, (K.iCycles n).hom ζ = z := by
  subst hj
  exact ⟨(K.sc n).abCyclesIso.inv ⟨z, hz⟩, (K.sc n).abCyclesIso_inv_apply_iCycles ⟨z, hz⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The differential of the forgotten dual cochain complex is the dual of the boundary. -/
lemma forgetDual_d_apply {R : Type} [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (φ : Module.Dual R (K.X n)) :
    ((((forget₂ (ModuleCat.{0} R) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K.linearDualCochainComplex).d n (n + 1)).hom φ =
      (K.d (n + 1) n).hom.dualMap φ := by
  simp only [Functor.mapHomologicalComplex_obj_d, HomologicalComplex.linearDualCochainComplex_d]
  rfl

/-- An element of the forgotten dual cochain complex, viewed as a linear functional. -/
def forgetDualElem {R : Type} [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (x : (((forget₂ (ModuleCat.{0} R) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K.linearDualCochainComplex).X n) : Module.Dual R (K.X n) :=
  x

set_option backward.isDefEq.respectTransparency false in
/-- **Bounded denominators.** If the integral homology in degree `n` is finitely generated, a
rational cocycle has a nonzero integer multiple which is integer-valued on integral cycles. -/
theorem exists_integer_multiple_ratEval (n : ℕ)
    [Module.Finite ℤ ((X.chainComplex (ModuleCat.of ℤ ℤ)).homology n)]
    (c : Module.Dual ℚ ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n))
    (hc : ((X.chainComplex (ModuleCat.of ℚ ℚ)).d (n + 1) n).hom.dualMap c = 0) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ ζ : (X.chainComplex (ModuleCat.of ℤ ℤ)).cycles n,
      ∃ a : ℤ, (a : ℚ) = (m : ℚ) *
        ratEval X n c (((X.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n).hom ζ) := by
  let F : (X.chainComplex (ModuleCat.of ℤ ℤ)).cycles n →ₗ[ℤ] ℚ :=
    ratEval X n c ∘ₗ ((X.chainComplex (ModuleCat.of ℤ ℤ)).iCycles n).hom
  have hF : ((X.chainComplex (ModuleCat.of ℤ ℤ)).sc n).toCycles ≫ ModuleCat.ofHom F = 0 := by
    ext y
    have h1 : ((X.chainComplex (ModuleCat.of ℤ ℤ)).sc n).iCycles.hom
        (((X.chainComplex (ModuleCat.of ℤ ℤ)).sc n).toCycles.hom y) =
        ((X.chainComplex (ModuleCat.of ℤ ℤ)).sc n).f.hom y :=
      ConcreteCategory.congr_hom ((X.chainComplex (ModuleCat.of ℤ ℤ)).sc n).toCycles_i y
    change ratEval X n c (((X.chainComplex (ModuleCat.of ℤ ℤ)).sc n).iCycles.hom
      (((X.chainComplex (ModuleCat.of ℤ ℤ)).sc n).toCycles.hom y)) = 0
    rw [h1]
    exact ratEval_d_eq_zero X n c hc _ (ChainComplex.prev ℕ n) y
  let G : (X.chainComplex (ModuleCat.of ℤ ℤ)).homology n →ₗ[ℤ] ℚ :=
    (((X.chainComplex (ModuleCat.of ℤ ℤ)).sc n).descHomology (ModuleCat.ofHom F) hF).hom
  have hG : ∀ ζ, G (((X.chainComplex (ModuleCat.of ℤ ℤ)).homologyπ n).hom ζ) = F ζ := fun ζ ↦
    ConcreteCategory.congr_hom
      (((X.chainComplex (ModuleCat.of ℤ ℤ)).sc n).π_descHomology (ModuleCat.ofHom F) hF) ζ
  obtain ⟨m, g, hm, hg⟩ := LinearMap.exists_integer_multiple G
  refine ⟨m, hm, fun ζ ↦ ⟨g (((X.chainComplex (ModuleCat.of ℤ ℤ)).homologyπ n).hom ζ), ?_⟩⟩
  have := LinearMap.congr_fun hg (((X.chainComplex (ModuleCat.of ℤ ℤ)).homologyπ n).hom ζ)
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
    algebraMap_int_eq, eq_intCast, hG] at this
  rw [this, zsmul_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Clearing denominators of rational simplicial cohomology classes.** If the integral
simplicial homology of `X` in degree `n` is finitely generated, then every degree-`n` rational
cohomology class (of the algebraic-dual cochain complex) has a nonzero integer multiple in the
image of integral cohomology under change of coefficients. -/
theorem exists_integer_multiple_of_finite_homology (n : ℕ)
    [Module.Finite ℤ ((X.chainComplex (ModuleCat.of ℤ ℤ)).homology n)]
    (α : (((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (X.chainComplex (ModuleCat.of ℚ ℚ)).linearDualCochainComplex).homology
        n) :
    ∃ (m : ℤ) (β : (((forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (X.chainComplex (ModuleCat.of ℤ ℤ)).linearDualCochainComplex).homology
        n), m ≠ 0 ∧
      HomologicalComplex.homologyMap (linearDualCoefficientChange (Int.castRingHom ℚ) X) n β =
        m • α := by
  let Kℤ := X.chainComplex (ModuleCat.of ℤ ℤ)
  let Kℚ := X.chainComplex (ModuleCat.of ℚ ℚ)
  let Dℤ := ((forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj Kℤ.linearDualCochainComplex
  let Dℚ := ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj Kℚ.linearDualCochainComplex
  let θ : Dℤ ⟶ Dℚ := linearDualCoefficientChange (Int.castRingHom ℚ) X
  obtain ⟨ζ, hζ⟩ := (AddCommGrpCat.epi_iff_surjective (Dℚ.homologyπ n)).mp inferInstance α
  let c : Module.Dual ℚ (Kℚ.X n) := forgetDualElem Kℚ n ((Dℚ.iCycles n).hom ζ)
  have hc : (Kℚ.d (n + 1) n).hom.dualMap c = 0 := by
    have := ConcreteCategory.congr_hom (Dℚ.iCycles_d n (n + 1)) ζ
    rw [← forgetDual_d_apply]
    exact this
  obtain ⟨m, hm, hint⟩ := exists_integer_multiple_ratEval X n c hc
  have key : ∃ (b : Module.Dual ℤ (Kℤ.X n)) (w : Dℚ.cycles n),
      (Kℤ.d (n + 1) n).hom.dualMap b = 0 ∧ (Dℚ.homologyπ n).hom w = 0 ∧
      dualCoefficientChange (Int.castRingHom ℚ) X n b =
        (m : ℚ) • c - forgetDualElem Kℚ n ((Dℚ.iCycles n).hom w) := by
    cases n with
    | zero =>
      have hint' : ∀ z, ∃ a : ℤ, (a : ℚ) = ratEval X 0 ((m : ℚ) • c) z := by
        intro z
        obtain ⟨ζ', hζ'⟩ := exists_cycles_of_d_eq_zero Kℤ 0 0 ChainComplex.next_nat_zero z
          (by rw [Kℤ.shape 0 0 (by simp)]; rfl)
        obtain ⟨a, ha⟩ := hint ζ'
        exact ⟨a, by rw [ratEval_smul, LinearMap.smul_apply, smul_eq_mul, ha, hζ']⟩
      obtain ⟨b, hb⟩ := exists_intCochain_of_integral X 0 ((m : ℚ) • c) hint'
      refine ⟨b, 0, ?_, map_zero _, by rw [hb, map_zero]; exact (sub_zero _).symm⟩
      apply dualMap_d_eq_zero_of_dualCoefficientChange
      rw [hb, map_smul, hc, smul_zero]
    | succ k =>
      have hint' : ∀ z, (Kℤ.d (k + 1) k).hom z = 0 →
          ∃ a : ℤ, (a : ℚ) = ratEval X (k + 1) ((m : ℚ) • c) z := by
        intro z hz
        obtain ⟨ζ', hζ'⟩ := exists_cycles_of_d_eq_zero Kℤ (k + 1) k (ChainComplex.next_nat_succ k)
          z hz
        obtain ⟨a, ha⟩ := hint ζ'
        exact ⟨a, by rw [ratEval_smul, LinearMap.smul_apply, smul_eq_mul, ha, hζ']⟩
      obtain ⟨b, e, hb, hbe⟩ := exists_integral_cocycle_succ X k ((m : ℚ) • c)
        (by rw [map_smul, hc, smul_zero]) hint'
      refine ⟨b, (Dℚ.toCycles k (k + 1)).hom e, hb, ?_, ?_⟩
      · exact ConcreteCategory.congr_hom (Dℚ.toCycles_comp_homologyπ k (k + 1)) e
      · rw [hbe]
        congr 1
        have := ConcreteCategory.congr_hom (Dℚ.toCycles_i k (k + 1)) e
        rw [forgetDual_d_apply] at this
        exact this.symm
  obtain ⟨b, w, hb, hw, hbw⟩ := key
  obtain ⟨ζb, hζb⟩ := exists_cycles_of_d_eq_zero_ab Dℤ n (n + 1) (by simp) b
    (by rw [forgetDual_d_apply]; exact hb)
  refine ⟨m, (Dℤ.homologyπ n).hom ζb, hm, ?_⟩
  have h1 : (HomologicalComplex.homologyMap θ n).hom ((Dℤ.homologyπ n).hom ζb) =
      (Dℚ.homologyπ n).hom ((HomologicalComplex.cyclesMap θ n).hom ζb) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality θ n) ζb
  have h2 : (HomologicalComplex.cyclesMap θ n).hom ζb = m • ζ - w := by
    apply (AddCommGrpCat.mono_iff_injective (Dℚ.iCycles n)).mp inferInstance
    have := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i θ n) ζb
    change (Dℚ.iCycles n).hom ((HomologicalComplex.cyclesMap θ n).hom ζb) =
      (θ.f n).hom ((Dℤ.iCycles n).hom ζb) at this
    change (Dℚ.iCycles n).hom ((HomologicalComplex.cyclesMap θ n).hom ζb) =
      (Dℚ.iCycles n).hom (m • ζ - w)
    rw [this, hζb, map_sub, map_zsmul]
    change dualCoefficientChange (Int.castRingHom ℚ) X n b =
      m • c - forgetDualElem Kℚ n ((Dℚ.iCycles n).hom w)
    rw [hbw, Int.cast_smul_eq_zsmul]
  change (HomologicalComplex.homologyMap θ n).hom ((Dℤ.homologyπ n).hom ζb) = m • α
  rw [h1, h2, map_sub, map_zsmul, hw, sub_zero, hζ]

end Denominators

end SSet
