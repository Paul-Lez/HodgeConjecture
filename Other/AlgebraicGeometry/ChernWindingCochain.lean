/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingLift
public import Other.AlgebraicTopology.SingularCohomology
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# The winding cocycle of a nonvanishing continuous function

For a continuous nowhere vanishing `g : Y → ℂ` this file builds the singular `1`-cochain

  `σ ↦ (1 / 2πi) · (logarithmic increment of g along σ)`

and proves that it is a cocycle, that it is additive in `g`, and that it is a coboundary as soon
as `g` has a global continuous logarithm.  The resulting linear functional on rational singular
homology `H₁(Y; ℚ)` is `ChernWinding.windingPeriod`; it is the winding number
`(1/2πi) ∮ d log g`, the degree-`0 → 1` connecting map of the exponential sequence, computed
without any sheaf theory.

The construction is elementary: a singular `n`-simplex of `Y` is a continuous map from the convex
compact set `stdSimplex ℝ (Fin (n + 1))`, which is contractible and locally path connected, so
`ChernWinding.logIncrement` applies to it; the cocycle identity for a `2`-simplex `τ` is the
telescoping of the increments of a single continuous logarithm of `g ∘ τ` between the three
vertices of `stdSimplex ℝ (Fin 3)`.

The functional takes values in `ℂ`, not in `ℚ`: it is *rational* — indeed integral on integral
cycles — but that is a statement about the periods of the class, isolated separately.  Everything
proved here holds for an arbitrary topological space `Y`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial

namespace ChernWinding

/-! ### The standard topological simplices -/

instance stdSimplexNonempty (n : ℕ) : Nonempty (stdSimplex ℝ (Fin (n + 1))) :=
  inferInstance

instance stdSimplexContractibleSpace (n : ℕ) :
    ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    (Set.nonempty_coe_sort.1 (stdSimplexNonempty n))

instance stdSimplexLocallyPathConnectedSpace (n : ℕ) :
    LocallyPathConnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
  Convex.locallyPathConnectedSpace (convex_stdSimplex ℝ (Fin (n + 1)))

/-! ### The increment along a singular simplex -/

variable {Y : TopCat.{0}} (g : C(Y, ℂ))

/-- A singular simplex of `Y`, as an honest continuous map from the standard simplex. -/
abbrev simplexMap {n : ℕ} (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    C(stdSimplex ℝ (Fin (n + 1)), Y) :=
  Y.toSSetObjEquiv _ σ

/-- `g`, read along a singular simplex. -/
abbrev simplexPullback {n : ℕ} (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    C(stdSimplex ℝ (Fin (n + 1)), ℂ) :=
  g.comp (simplexMap σ)

theorem simplexPullback_ne_zero (hg : ∀ y, g y ≠ 0) {n : ℕ}
    (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (t : stdSimplex ℝ (Fin (n + 1))) :
    simplexPullback g σ t ≠ 0 :=
  hg _

/-- The pullback of `g` along a face of a singular simplex is the pullback along the simplex,
composed with the affine face map of the standard simplices. -/
theorem simplexPullback_δ {n : ℕ} (τ : (TopCat.toSSet.obj Y) _⦋n + 1⦌) (i : Fin (n + 2)) :
    simplexPullback g ((TopCat.toSSet.obj Y).δ i τ) =
      (simplexPullback g τ).comp
        ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map _⟩ := by
  ext t
  exact congrArg g (TopCat.toSSetObjEquiv_δ_apply τ i t)

/-- The complex logarithmic increment of `g` along a singular `1`-simplex, from the `0`-th to the
`1`-st vertex of the standard `1`-simplex. -/
def simplexIncrement (hg : ∀ y, g y ≠ 0) (σ : (TopCat.toSSet.obj Y) _⦋1⦌) : ℂ :=
  logIncrement (simplexPullback g σ) (simplexPullback_ne_zero g hg σ)
    (stdSimplex.vertex 0) (stdSimplex.vertex 1)

/-- The increment along a face of a `2`-simplex is the increment of the pullback along the
`2`-simplex, between the two corresponding vertices of the standard `2`-simplex. -/
theorem simplexIncrement_δ (hg : ∀ y, g y ≠ 0) (τ : (TopCat.toSSet.obj Y) _⦋2⦌) (i : Fin 3) :
    simplexIncrement g hg ((TopCat.toSSet.obj Y).δ i τ) =
      logIncrement (simplexPullback g τ) (simplexPullback_ne_zero g hg τ)
        (stdSimplex.vertex (i.succAbove 0)) (stdSimplex.vertex (i.succAbove 1)) := by
  have hφ : ∀ t : stdSimplex ℝ (Fin 2),
      ((simplexPullback g τ).comp
        (⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map _⟩ :
          C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 3)))) t ≠ 0 :=
    fun t => simplexPullback_ne_zero g hg τ _
  rw [simplexIncrement,
    logIncrement_congr _ hφ (simplexPullback_δ g τ i),
    logIncrement_comp (simplexPullback g τ) (simplexPullback_ne_zero g hg τ) _ hφ,
    ← stdSimplex.map_vertex (S := ℝ) i.succAbove 0,
    ← stdSimplex.map_vertex (S := ℝ) i.succAbove 1]
  rfl

/-- **The cocycle identity.**  The alternating sum of the increments along the faces of a
singular `2`-simplex vanishes: the increments of a single continuous logarithm of `g` along the
`2`-simplex telescope. -/
theorem simplexIncrement_boundary (hg : ∀ y, g y ≠ 0) (τ : (TopCat.toSSet.obj Y) _⦋2⦌) :
    ∑ i : Fin 3, (-1 : ℂ) ^ (i : ℕ) *
      simplexIncrement g hg ((TopCat.toSSet.obj Y).δ i τ) = 0 := by
  obtain ⟨L, hL⟩ := exists_expLift (simplexPullback g τ) (simplexPullback_ne_zero g hg τ)
    (stdSimplex.vertex 0)
  have h : ∀ i : Fin 3, simplexIncrement g hg ((TopCat.toSSet.obj Y).δ i τ) =
      L (stdSimplex.vertex (i.succAbove 1)) - L (stdSimplex.vertex (i.succAbove 0)) := by
    intro i
    rw [simplexIncrement_δ g hg τ i, logIncrement_eq _ _ L hL]
  have e00 : (0 : Fin 3).succAbove 0 = 1 := by decide
  have e01 : (0 : Fin 3).succAbove 1 = 2 := by decide
  have e10 : (1 : Fin 3).succAbove 0 = 0 := by decide
  have e11 : (1 : Fin 3).succAbove 1 = 2 := by decide
  have e20 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have e21 : (2 : Fin 3).succAbove 1 = 1 := by decide
  rw [Fin.sum_univ_three, h 0, h 1, h 2, e00, e01, e10, e11, e20, e21]
  norm_num

/-! ### The winding cochain and the winding period -/

/-- `2πi`. -/
abbrev twoPiI : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem twoPiI_ne_zero : (twoPiI : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero]

variable (Y) in
/-- The rational singular chain complex of `Y`. -/
abbrev singularChains : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)

variable (Y) in
theorem homology_eq_singularChains_homology (n : ℕ) :
    AlgebraicTopology.Singular.Homology ℚ Y n = (singularChains Y).homology n := rfl

/-- The scalar `z`, as a morphism `ℚ ⟶ ℂ` of rational vector spaces. -/
abbrev scalarHom (z : ℂ) : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℂ :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℂ z)

theorem scalarHom_add (z w : ℂ) : scalarHom (z + w) = scalarHom z + scalarHom w := by
  ext; simp [LinearMap.toSpanSingleton]

/-- Dividing by `2πi` and viewing the result as a morphism `ℚ ⟶ ℂ`, as an additive map. -/
def scalarHomDiv : ℂ →+ (ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℂ) :=
  AddMonoidHom.mk' (fun z => scalarHom (z / twoPiI)) (by
    intro z w; rw [add_div, scalarHom_add])

theorem scalarHomDiv_apply (z : ℂ) : scalarHomDiv z = scalarHom (z / twoPiI) := rfl

theorem scalarHom_zsmul (n : ℤ) (z : ℂ) : scalarHom ((n : ℂ) * z) = n • scalarHom z := by
  ext
  simp [LinearMap.toSpanSingleton, mul_comm]

/-- **The winding `1`-cochain.**  Its value on a singular `1`-simplex is the winding number
`(1/2πi)` times the logarithmic increment of `g` along it. -/
def windingCochain (hg : ∀ y, g y ≠ 0) : (singularChains Y).X 1 ⟶ ModuleCat.of ℚ ℂ :=
  Limits.Cofan.IsColimit.desc
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 1)
    fun σ => scalarHom (simplexIncrement g hg σ / twoPiI)

@[reassoc] theorem ιChainComplex_comp_windingCochain (hg : ∀ y, g y ≠ 0)
    (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    (TopCat.toSSet.obj Y).ιChainComplex σ ≫ windingCochain g hg =
      scalarHom (simplexIncrement g hg σ / twoPiI) :=
  Limits.Cofan.IsColimit.fac
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 1) _ σ

/-- **The winding cochain is a cocycle.** -/
theorem d_comp_windingCochain (hg : ∀ y, g y ≠ 0) :
    (singularChains Y).d 2 1 ≫ windingCochain g hg = 0 := by
  refine SSet.chainComplex_hom_ext fun τ => ?_
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp, comp_zero]
  have hterm : ∀ i : Fin 3,
      ((-1 : ℤ) ^ (i : ℕ) • (TopCat.toSSet.obj Y).ιChainComplex
          ((TopCat.toSSet.obj Y).δ i τ)) ≫ windingCochain g hg =
        scalarHom (((-1 : ℂ) ^ (i : ℕ) *
          simplexIncrement g hg ((TopCat.toSSet.obj Y).δ i τ)) / twoPiI) := by
    intro i
    rw [Preadditive.zsmul_comp, ιChainComplex_comp_windingCochain]
    rw [show (((-1 : ℂ) ^ (i : ℕ) *
        simplexIncrement g hg ((TopCat.toSSet.obj Y).δ i τ)) / twoPiI) =
      (((-1 : ℤ) ^ (i : ℕ) : ℤ) : ℂ) *
        (simplexIncrement g hg ((TopCat.toSSet.obj Y).δ i τ) / twoPiI) by push_cast; ring]
    exact (scalarHom_zsmul _ _).symm
  simp_rw [hterm, ← scalarHomDiv_apply]
  rw [← map_sum scalarHomDiv, simplexIncrement_boundary g hg τ, map_zero]

/-- **The winding period.**  The linear functional on rational singular homology `H₁(Y; ℚ)`
represented by the winding cocycle: the winding number `(1/2πi) ∮ d log g`. -/
def windingPeriodHom (hg : ∀ y, g y ≠ 0) :
    (singularChains Y).homology 1 ⟶ ModuleCat.of ℚ ℂ :=
  (Limits.CokernelCofork.IsColimit.desc'
    ((singularChains Y).homologyIsCokernel 2 1 (by simp))
    ((singularChains Y).iCycles 1 ≫ windingCochain g hg)
    (by rw [← Category.assoc, HomologicalComplex.toCycles_i, d_comp_windingCochain])).1

theorem homologyπ_comp_windingPeriodHom (hg : ∀ y, g y ≠ 0) :
    (singularChains Y).homologyπ 1 ≫ windingPeriodHom g hg =
      (singularChains Y).iCycles 1 ≫ windingCochain g hg :=
  (Limits.CokernelCofork.IsColimit.desc'
    ((singularChains Y).homologyIsCokernel 2 1 (by simp))
    ((singularChains Y).iCycles 1 ≫ windingCochain g hg)
    (by rw [← Category.assoc, HomologicalComplex.toCycles_i, d_comp_windingCochain])).2

/-- The winding period as a rational-linear functional with complex values. -/
def windingPeriod (hg : ∀ y, g y ≠ 0) :
    AlgebraicTopology.Singular.Homology ℚ Y 1 →ₗ[ℚ] ℂ :=
  (windingPeriodHom g hg).hom

theorem windingPeriod_apply (hg : ∀ y, g y ≠ 0)
    (z : AlgebraicTopology.Singular.Homology ℚ Y 1) :
    windingPeriod g hg z = (windingPeriodHom g hg).hom z := rfl

/-! ### Additivity in the function -/

theorem simplexIncrement_mul (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    simplexIncrement k hk σ = simplexIncrement g hg σ + simplexIncrement h hh σ :=
  logIncrement_mul (simplexPullback g σ) (simplexPullback h σ) (simplexPullback k σ)
    (simplexPullback_ne_zero g hg σ) (simplexPullback_ne_zero h hh σ)
    (simplexPullback_ne_zero k hk σ) (fun _ => hmul _) _ _

theorem windingCochain_mul (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    windingCochain k hk = windingCochain g hg + windingCochain h hh := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [Preadditive.comp_add, ιChainComplex_comp_windingCochain,
    ιChainComplex_comp_windingCochain, ιChainComplex_comp_windingCochain,
    simplexIncrement_mul g h k hg hh hk hmul σ, add_div, scalarHom_add]

theorem windingPeriodHom_mul (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    windingPeriodHom k hk = windingPeriodHom g hg + windingPeriodHom h hh := by
  rw [← cancel_epi ((singularChains Y).homologyπ 1), Preadditive.comp_add,
    homologyπ_comp_windingPeriodHom, homologyπ_comp_windingPeriodHom,
    homologyπ_comp_windingPeriodHom, ← Preadditive.comp_add,
    windingCochain_mul g h k hg hh hk hmul]

theorem windingPeriod_mul (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    windingPeriod k hk = windingPeriod g hg + windingPeriod h hh :=
  congrArg ModuleCat.Hom.hom (windingPeriodHom_mul g h k hg hh hk hmul)

/-! ### Vanishing for a function with a global logarithm -/

/-- The `0`-cochain attached to a continuous complex function, normalised by `2πi`. -/
def vertexCochain (f : C(Y, ℂ)) : (singularChains Y).X 0 ⟶ ModuleCat.of ℚ ℂ :=
  Limits.Cofan.IsColimit.desc
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 0)
    fun v => scalarHom (f (simplexMap v default) / twoPiI)

@[reassoc] theorem ιChainComplex_comp_vertexCochain (f : C(Y, ℂ))
    (v : (TopCat.toSSet.obj Y) _⦋0⦌) :
    (TopCat.toSSet.obj Y).ιChainComplex v ≫ vertexCochain f =
      scalarHom (f (simplexMap v default) / twoPiI) :=
  Limits.Cofan.IsColimit.fac
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 0) _ v

theorem simplexMap_δ_default (σ : (TopCat.toSSet.obj Y) _⦋1⦌) (i : Fin 2) :
    simplexMap ((TopCat.toSSet.obj Y).δ i σ) default =
      simplexMap σ (stdSimplex.vertex (i.succAbove 0)) := by
  have h := TopCat.toSSetObjEquiv_δ_apply σ i (default : stdSimplex ℝ (Fin 1))
  rw [h, show (default : stdSimplex ℝ (Fin 1)) = stdSimplex.vertex 0 from Subsingleton.elim _ _,
    stdSimplex.map_vertex]

theorem simplexIncrement_of_exp (f : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hfg : ∀ y, Complex.exp (f y) = g y) (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    simplexIncrement g hg σ =
      f (simplexMap σ (stdSimplex.vertex 1)) - f (simplexMap σ (stdSimplex.vertex 0)) :=
  logIncrement_of_exp (f.comp (simplexMap σ)) (simplexPullback g σ)
    (simplexPullback_ne_zero g hg σ) (fun _ => hfg _) _ _

/-- If `g` has a global continuous logarithm, its winding cochain is the coboundary of the
`0`-cochain given by that logarithm. -/
theorem windingCochain_eq_d_comp_vertexCochain (f : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hfg : ∀ y, Complex.exp (f y) = g y) :
    windingCochain g hg = (singularChains Y).d 1 0 ≫ vertexCochain f := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [ιChainComplex_comp_windingCochain, ← Category.assoc, SSet.ιChainComplex_d,
    Preadditive.sum_comp]
  have hterm : ∀ i : Fin 2,
      ((-1 : ℤ) ^ (i : ℕ) • (TopCat.toSSet.obj Y).ιChainComplex
          ((TopCat.toSSet.obj Y).δ i σ)) ≫ vertexCochain f =
        scalarHom (((-1 : ℂ) ^ (i : ℕ) *
          f (simplexMap σ (stdSimplex.vertex (i.succAbove 0)))) / twoPiI) := by
    intro i
    rw [Preadditive.zsmul_comp, ιChainComplex_comp_vertexCochain, simplexMap_δ_default]
    rw [show (((-1 : ℂ) ^ (i : ℕ) *
        f (simplexMap σ (stdSimplex.vertex (i.succAbove 0)))) / twoPiI) =
      (((-1 : ℤ) ^ (i : ℕ) : ℤ) : ℂ) *
        (f (simplexMap σ (stdSimplex.vertex (i.succAbove 0))) / twoPiI) by push_cast; ring]
    exact (scalarHom_zsmul _ _).symm
  simp_rw [hterm, ← scalarHomDiv_apply]
  rw [← map_sum scalarHomDiv, scalarHomDiv_apply, simplexIncrement_of_exp g f hg hfg σ]
  have e0 : (0 : Fin 2).succAbove 0 = 1 := by decide
  have e1 : (1 : Fin 2).succAbove 0 = 0 := by decide
  rw [Fin.sum_univ_two, e0, e1]
  norm_num
  rw [← scalarHomDiv_apply, map_sub, sub_eq_add_neg]

/-- **A function with a global continuous logarithm has vanishing winding period.** -/
theorem windingPeriodHom_eq_zero_of_exp (f : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hfg : ∀ y, Complex.exp (f y) = g y) : windingPeriodHom g hg = 0 := by
  rw [← cancel_epi ((singularChains Y).homologyπ 1), comp_zero,
    homologyπ_comp_windingPeriodHom, windingCochain_eq_d_comp_vertexCochain g f hg hfg,
    ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

theorem windingPeriod_eq_zero_of_exp (f : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hfg : ∀ y, Complex.exp (f y) = g y) : windingPeriod g hg = 0 :=
  congrArg ModuleCat.Hom.hom (windingPeriodHom_eq_zero_of_exp g f hg hfg)

/-! ### Naturality in the space -/

section Naturality

variable {Y' : TopCat.{0}} (f : Y' ⟶ Y)

/-- A continuous map of spaces, as a bundled continuous map. -/
abbrev topMap : C(Y', Y) := ⟨f.hom, f.hom.continuous⟩

theorem simplexIncrement_map (hg : ∀ y, g y ≠ 0)
    (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0) (σ : (TopCat.toSSet.obj Y') _⦋1⦌) :
    simplexIncrement g hg ((TopCat.toSSet.map f).app _ σ) =
      simplexIncrement (g.comp (topMap f)) hgf σ :=
  logIncrement_congr _ _ (by ext t; rfl) _ _

theorem chainComplexMap_comp_windingCochain (hg : ∀ y, g y ≠ 0)
    (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 1 ≫ windingCochain g hg =
      windingCochain (g.comp (topMap f)) hgf := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, ιChainComplex_comp_windingCochain,
    ιChainComplex_comp_windingCochain, simplexIncrement_map g f hg hgf σ]

theorem homologyMap_comp_windingPeriodHom (hg : ∀ y, g y ≠ 0)
    (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0) :
    HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)) 1 ≫
        windingPeriodHom g hg =
      windingPeriodHom (g.comp (topMap f)) hgf := by
  rw [← cancel_epi ((singularChains Y').homologyπ 1), ← Category.assoc,
    HomologicalComplex.homologyπ_naturality, Category.assoc,
    homologyπ_comp_windingPeriodHom, homologyπ_comp_windingPeriodHom, ← Category.assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc,
    chainComplexMap_comp_windingCochain g f hg hgf]

theorem windingPeriod_map (hg : ∀ y, g y ≠ 0) (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0)
    (z : AlgebraicTopology.Singular.Homology ℚ Y' 1) :
    windingPeriod (g.comp (topMap f)) hgf z =
      windingPeriod g hg (AlgebraicTopology.Singular.homologyMap ℚ 1 f z) :=
  congrFun (congrArg (fun h : _ ⟶ ModuleCat.of ℚ ℂ => (ModuleCat.Hom.hom h).toFun)
    (homologyMap_comp_windingPeriodHom g f hg hgf).symm) z

end Naturality

end ChernWinding
