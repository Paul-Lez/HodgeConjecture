/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingBoundary

/-!
# Integrality of the winding periods

`ChernWinding.windingPeriod` takes complex values, and the repository's supported cohomology is
rational; `ChernWinding.HasRationalWindingPeriod` isolated the resulting obligation.  This file
**discharges it unconditionally**.

The argument is the classical one, carried out on singular cochains.  Fix the pointwise principal
branch `λ y := Complex.log (g y)` — no continuity is required of it, because a `0`-cochain is
just a function on `0`-simplices.  For a singular `1`-simplex `σ` both `exp` of the logarithmic
increment of `g` along `σ` and `exp` of `λ(σ v₁) - λ(σ v₀)` are `g(σ v₁) / g(σ v₀)`, so the two
differ by an element of `2πi ℤ`:

  `simplexIncrement g σ = (λ(σ v₁) - λ(σ v₀)) + 2πi · windingIndex g σ`, `windingIndex g σ : ℤ`.

Therefore the winding cochain is the sum of the coboundary of the `0`-cochain `λ / 2πi` and the
**integer-valued** cochain `windingIndex`.  The latter is automatically a cocycle (the other two
are), so it descends to a *rational* class

  `ChernWinding.windingRationalPeriod g hg : Cohomology ℚ Y 1`

whose complexification is `windingPeriod g hg` (`rationalPeriod_windingRationalPeriod`), because
the two cochains differ by a coboundary and coboundaries die on cycles.

Consequences: `ChernWinding.hasRationalWindingPeriod` (the obligation of
`ChernWindingBoundary.lean`, now a theorem) and, in
`Other/AlgebraicGeometry/ChernWindingChartPeriods.lean`, the corresponding chart-level statement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial AlgebraicTopology.Singular

namespace ChernWinding

variable {Y : TopCat.{0}} (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)

/-! ### The integer winding index of a singular `1`-simplex -/

/-- The pointwise principal logarithm of `g`; no continuity is claimed. -/
abbrev pointLog (y : Y) : ℂ := Complex.log (g y)

include hg in
theorem exp_pointLog (y : Y) : Complex.exp (pointLog g y) = g y := Complex.exp_log (hg y)

/-- The logarithmic increment of `g` along a singular `1`-simplex differs from the difference of
the principal logarithms at its endpoints by an integer multiple of `2πi`. -/
theorem exists_int_simplexIncrement (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    ∃ n : ℤ, simplexIncrement g hg σ =
      (pointLog g (simplexMap σ (stdSimplex.vertex 1)) -
        pointLog g (simplexMap σ (stdSimplex.vertex 0))) + (n : ℂ) * twoPiI := by
  obtain ⟨L, hL⟩ := exists_expLift (simplexPullback g σ) (simplexPullback_ne_zero g hg σ)
    (stdSimplex.vertex 0)
  obtain ⟨n₁, hn₁⟩ := Complex.exp_eq_exp_iff_exists_int.1
    (((hL (stdSimplex.vertex 1)).trans
      (exp_pointLog g hg (simplexMap σ (stdSimplex.vertex 1))).symm))
  obtain ⟨n₀, hn₀⟩ := Complex.exp_eq_exp_iff_exists_int.1
    (((hL (stdSimplex.vertex 0)).trans
      (exp_pointLog g hg (simplexMap σ (stdSimplex.vertex 0))).symm))
  refine ⟨n₁ - n₀, ?_⟩
  rw [simplexIncrement, logIncrement_eq _ _ L hL, hn₁, hn₀]
  push_cast
  ring

/-- The integer winding index of `g` along a singular `1`-simplex. -/
def windingIndex (σ : (TopCat.toSSet.obj Y) _⦋1⦌) : ℤ :=
  (exists_int_simplexIncrement g hg σ).choose

theorem simplexIncrement_eq_pointLog_add_windingIndex (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    simplexIncrement g hg σ =
      (pointLog g (simplexMap σ (stdSimplex.vertex 1)) -
        pointLog g (simplexMap σ (stdSimplex.vertex 0))) +
      (windingIndex g hg σ : ℂ) * twoPiI :=
  (exists_int_simplexIncrement g hg σ).choose_spec

/-! ### The integer cochain and the rational class -/

/-- The `0`-cochain attached to an arbitrary complex function, normalised by `2πi`.  Continuity
is irrelevant: a `0`-cochain is a function on points. -/
def vertexCochainFun (f : Y → ℂ) : (singularChains Y).X 0 ⟶ ModuleCat.of ℚ ℂ :=
  Limits.Cofan.IsColimit.desc
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 0)
    fun v => scalarHom (f (simplexMap v default) / twoPiI)

@[reassoc] theorem ιChainComplex_comp_vertexCochainFun (f : Y → ℂ)
    (v : (TopCat.toSSet.obj Y) _⦋0⦌) :
    (TopCat.toSSet.obj Y).ιChainComplex v ≫ vertexCochainFun f =
      scalarHom (f (simplexMap v default) / twoPiI) :=
  Limits.Cofan.IsColimit.fac
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 0) _ v

/-- The scalar `q`, as an endomorphism of `ℚ`. -/
abbrev scalarHomRat (q : ℚ) : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℚ q)

/-- The inclusion `ℚ ⟶ ℂ` of rational vector spaces. -/
abbrev ratToComplex : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℂ :=
  ModuleCat.ofHom (Algebra.linearMap ℚ ℂ)

theorem scalarHomRat_comp_ratToComplex (q : ℚ) :
    scalarHomRat q ≫ ratToComplex = scalarHom ((q : ℂ)) := by
  ext
  simp [LinearMap.toSpanSingleton, Algebra.linearMap, Algebra.smul_def]

instance : Mono ratToComplex :=
  (ModuleCat.mono_iff_injective _).2 (fun a b h => by
    simpa [Algebra.linearMap] using (Rat.cast_injective (α := ℂ) h))

/-- **The integer winding cochain.**  Its value on a singular `1`-simplex is the integer winding
index. -/
def windingIntegerCochain : (singularChains Y).X 1 ⟶ ModuleCat.of ℚ ℚ :=
  Limits.Cofan.IsColimit.desc
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 1)
    fun σ => scalarHomRat ((windingIndex g hg σ : ℚ))

@[reassoc] theorem ιChainComplex_comp_windingIntegerCochain (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    (TopCat.toSSet.obj Y).ιChainComplex σ ≫ windingIntegerCochain g hg =
      scalarHomRat ((windingIndex g hg σ : ℚ)) :=
  Limits.Cofan.IsColimit.fac
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 1) _ σ

/-- **The winding cochain is an integral cochain up to a coboundary.** -/
theorem windingCochain_eq_coboundary_add_integer :
    windingCochain g hg =
      (singularChains Y).d 1 0 ≫ vertexCochainFun (pointLog g) +
        windingIntegerCochain g hg ≫ ratToComplex := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [Preadditive.comp_add, ιChainComplex_comp_windingCochain, ← Category.assoc,
    ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp,
    ιChainComplex_comp_windingIntegerCochain, scalarHomRat_comp_ratToComplex]
  have hterm : ∀ i : Fin 2,
      ((-1 : ℤ) ^ (i : ℕ) • (TopCat.toSSet.obj Y).ιChainComplex
          ((TopCat.toSSet.obj Y).δ i σ)) ≫ vertexCochainFun (pointLog g) =
        scalarHom (((-1 : ℂ) ^ (i : ℕ) *
          pointLog g (simplexMap σ (stdSimplex.vertex (i.succAbove 0)))) / twoPiI) := by
    intro i
    rw [Preadditive.zsmul_comp, ιChainComplex_comp_vertexCochainFun, simplexMap_δ_default]
    rw [show (((-1 : ℂ) ^ (i : ℕ) *
        pointLog g (simplexMap σ (stdSimplex.vertex (i.succAbove 0)))) / twoPiI) =
      (((-1 : ℤ) ^ (i : ℕ) : ℤ) : ℂ) *
        (pointLog g (simplexMap σ (stdSimplex.vertex (i.succAbove 0))) / twoPiI) by
      push_cast; ring]
    exact (scalarHom_zsmul _ _).symm
  simp_rw [hterm, ← scalarHomDiv_apply]
  rw [← map_sum scalarHomDiv]
  have e0 : (0 : Fin 2).succAbove 0 = 1 := by decide
  have e1 : (1 : Fin 2).succAbove 0 = 0 := by decide
  rw [Fin.sum_univ_two, e0, e1, scalarHomDiv_apply,
    simplexIncrement_eq_pointLog_add_windingIndex g hg σ]
  have hsplit : ((pointLog g (simplexMap σ (stdSimplex.vertex 1)) -
        pointLog g (simplexMap σ (stdSimplex.vertex 0))) +
        (windingIndex g hg σ : ℂ) * twoPiI) / twoPiI =
      ((-1 : ℂ) ^ (0 : ℕ) * pointLog g (simplexMap σ (stdSimplex.vertex 1)) +
        (-1 : ℂ) ^ (1 : ℕ) * pointLog g (simplexMap σ (stdSimplex.vertex 0))) / twoPiI +
      ((windingIndex g hg σ : ℚ) : ℂ) := by
    field_simp
    push_cast
    ring
  rw [hsplit, scalarHom_add, scalarHomDiv_apply]

/-- The integer winding cochain is a cocycle. -/
theorem d_comp_windingIntegerCochain :
    (singularChains Y).d 2 1 ≫ windingIntegerCochain g hg = 0 := by
  rw [← cancel_mono ratToComplex, zero_comp, Category.assoc]
  have h := d_comp_windingCochain g hg
  rw [windingCochain_eq_coboundary_add_integer g hg, Preadditive.comp_add, ← Category.assoc,
    HomologicalComplex.d_comp_d, zero_comp, zero_add] at h
  exact h

/-- **The rational winding class.** -/
def windingRationalPeriodHom : (singularChains Y).homology 1 ⟶ ModuleCat.of ℚ ℚ :=
  (Limits.CokernelCofork.IsColimit.desc'
    ((singularChains Y).homologyIsCokernel 2 1 (by simp))
    ((singularChains Y).iCycles 1 ≫ windingIntegerCochain g hg)
    (by rw [← Category.assoc, HomologicalComplex.toCycles_i, d_comp_windingIntegerCochain])).1

theorem homologyπ_comp_windingRationalPeriodHom :
    (singularChains Y).homologyπ 1 ≫ windingRationalPeriodHom g hg =
      (singularChains Y).iCycles 1 ≫ windingIntegerCochain g hg :=
  (Limits.CokernelCofork.IsColimit.desc'
    ((singularChains Y).homologyIsCokernel 2 1 (by simp))
    ((singularChains Y).iCycles 1 ≫ windingIntegerCochain g hg)
    (by rw [← Category.assoc, HomologicalComplex.toCycles_i, d_comp_windingIntegerCochain])).2

/-- The winding class of `g`, as an honest *rational* singular cohomology class. -/
def windingRationalPeriod : AlgebraicTopology.Singular.Cohomology ℚ Y 1 :=
  (windingRationalPeriodHom g hg).hom

/-- **The winding period is rational.**  Its complexification is the complex winding period. -/
theorem rationalPeriod_windingRationalPeriod :
    rationalPeriod (AlgebraicTopology.Singular.Homology ℚ Y 1) (windingRationalPeriod g hg) =
      windingPeriod g hg := by
  have hcat : windingRationalPeriodHom g hg ≫ ratToComplex = windingPeriodHom g hg := by
    rw [← cancel_epi ((singularChains Y).homologyπ 1), ← Category.assoc,
      homologyπ_comp_windingRationalPeriodHom, homologyπ_comp_windingPeriodHom,
      windingCochain_eq_coboundary_add_integer g hg, Preadditive.comp_add, ← Category.assoc,
      HomologicalComplex.iCycles_d, zero_comp, zero_add, Category.assoc]
  ext z
  exact congrArg (fun h : _ ⟶ ModuleCat.of ℚ ℂ => (ModuleCat.Hom.hom h) z) hcat

/-! ### The obligation of `ChernWindingBoundary.lean`, discharged -/

section Relative

variable {M : Type} [TopologicalSpace M] (W S : Set M)

/-- **The relative winding period is rational** — unconditionally.  This discharges
`ChernWinding.HasRationalWindingPeriod`, the only hypothesis of the construction of the winding
homomorphism. -/
theorem hasRationalWindingPeriod (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0) :
    HasRationalWindingPeriod W S g hg := by
  refine ⟨(windingRationalPeriod g hg).comp
    (relativeSingularBoundary (supportPair W S) 1).hom, ?_⟩
  ext z
  exact LinearMap.congr_fun (rationalPeriod_windingRationalPeriod g hg)
    ((relativeSingularBoundary (supportPair W S) 1).hom z)

/-- The winding class of a nowhere vanishing continuous function on `W ∖ S`, as a rational
relative cohomology class of the pair `(W, W ∖ S)`, with no hypothesis. -/
abbrev windingClass (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0) :
    RelativeCohomology ℚ (supportPair W S) 2 :=
  windingRelativeClass W S (hasRationalWindingPeriod W S g hg)

end Relative

end ChernWinding
