/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.WindingCochain
public import Other.AlgebraicTopology.ExplicitCochainClass
public import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality
public import HodgeConjecture.Lemmas.AlgebraicTopology.LinearDualHomologyNaturality

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

/-- Extend rational-valued functionals to complex-valued periods. -/
def rationalPeriod (M : Type) [AddCommGroup M] [Module ℚ M] :
    Module.Dual ℚ M →ₗ[ℚ] (M →ₗ[ℚ] ℂ) where
  toFun φ := (Algebra.linearMap ℚ ℂ).comp φ
  map_add' φ ψ := by
    ext x
    simp
  map_smul' q φ := by
    ext x
    simp [Algebra.smul_def]

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

/-- The rational singular cohomology class obtained directly from the literal integer winding
cochain, through the ordinary singular-cochain complex. -/
def windingRationalCochainClass : AlgebraicTopology.Singular.Cohomology ℚ Y 1 :=
  AlgebraicTopology.Singular.singularCohomologyClassOfCochain ℚ Y 1
    (windingIntegerCochain g hg).hom (by
      change ((singularChains Y).d 2 1 ≫ windingIntegerCochain g hg).hom = 0
      rw [d_comp_windingIntegerCochain]
      rfl)

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

/-- The universal-coefficient class of the literal integer winding cochain is exactly the
period functional obtained by letting that cochain evaluate on cycles. -/
theorem windingRationalCochainClass_eq_windingRationalPeriod :
    windingRationalCochainClass g hg = windingRationalPeriod g hg := by
  apply LinearMap.ext
  intro z
  let K := singularChains Y
  let S := K.sc 1
  obtain ⟨x, rfl⟩ := S.moduleCatHomologyClass_surjective z
  let phi : S.linearDual.cycles :=
    (AlgebraicTopology.Singular.cochainCycle ℚ Y 1
      (windingIntegerCochain g hg).hom (by
        change ((singularChains Y).d 2 1 ≫ windingIntegerCochain g hg).hom = 0
        rw [d_comp_windingIntegerCochain]
        rfl)).hom 1
  let zeta := S.moduleCatCyclesIso.inv x
  have hphi : S.linearDual.homologyπ phi =
      AlgebraicTopology.Singular.cochainCohomologyClass ℚ Y 1
        (windingIntegerCochain g hg).hom (by
          change ((singularChains Y).d 2 1 ≫ windingIntegerCochain g hg).hom = 0
          rw [d_comp_windingIntegerCochain]
          rfl) := by rfl
  have hzeta : S.homologyπ zeta = S.moduleCatHomologyClass x := by rfl
  have hclosed : ((singularChains Y).linearDualCochainComplex).d 1 2
      (windingIntegerCochain g hg).hom = 0 := by
    change ((singularChains Y).d 2 1 ≫ windingIntegerCochain g hg).hom = 0
    rw [d_comp_windingIntegerCochain]
    rfl
  have hphi_value : S.linearDual.iCycles phi = (windingIntegerCochain g hg).hom := by
    change ((singularChains Y).linearDualCochainComplex.iCycles 1).hom
      ((AlgebraicTopology.Singular.cochainCycle ℚ Y 1
        (windingIntegerCochain g hg).hom _).hom 1) = _
    change ((singularChains Y).linearDualCochainComplex.iCycles 1).hom
      ((HomologicalComplex.liftCycles
        (singularChains Y).linearDualCochainComplex
        (AlgebraicTopology.Singular.cochainElementHom ℚ Y 1
          (windingIntegerCochain g hg).hom) 2 _ _).hom 1) = _
    have h := HomologicalComplex.liftCycles_i
      ((singularChains Y).linearDualCochainComplex)
      (AlgebraicTopology.Singular.cochainElementHom ℚ Y 1
        (windingIntegerCochain g hg).hom) 2 (by simp) (by
          ext
          change ((singularChains Y).linearDualCochainComplex).d 1 2
            (LinearMap.toSpanSingleton ℚ _ ((windingIntegerCochain g hg).hom) 1) = 0
          simpa using hclosed)
    have h' := ConcreteCategory.congr_hom h 1
    change ((singularChains Y).linearDualCochainComplex.iCycles 1).hom
      ((HomologicalComplex.liftCycles
        (singularChains Y).linearDualCochainComplex
        (AlgebraicTopology.Singular.cochainElementHom ℚ Y 1
          (windingIntegerCochain g hg).hom) 2 _ _).hom 1) =
      (AlgebraicTopology.Singular.cochainElementHom ℚ Y 1
        (windingIntegerCochain g hg).hom).hom 1 at h'
    rw [h']
    change LinearMap.toSpanSingleton ℚ _ ((windingIntegerCochain g hg).hom) 1 = _
    simp
  have h := CategoryTheory.ShortComplex.linearDualHomologyEquiv_homologyπ_apply S phi zeta
  change S.linearDualHomologyEquiv
    (AlgebraicTopology.Singular.cochainCohomologyClass ℚ Y 1
      (windingIntegerCochain g hg).hom _) (S.moduleCatHomologyClass x) =
    (windingRationalPeriodHom g hg).hom (S.moduleCatHomologyClass x)
  rw [← hphi, ← hzeta]
  rw [show (windingRationalPeriodHom g hg).hom (S.homologyπ zeta) =
      (windingIntegerCochain g hg).hom (S.iCycles zeta) by
    exact ConcreteCategory.congr_hom
      (homologyπ_comp_windingRationalPeriodHom g hg) zeta]
  rw [← hphi_value]
  exact h

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

/-! ### Naturality of the literal integer cochain -/

section IntegerNaturality

variable {Y' : TopCat.{0}} (f : Y' ⟶ Y)

/-- The integer winding index is natural under pullback of a nonvanishing function.  This is
proved directly from the defining principal-log formula, so it applies to the literal cochain,
not merely to its cohomology class. -/
theorem windingIndex_map (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0)
    (σ : (TopCat.toSSet.obj Y') _⦋1⦌) :
    windingIndex g hg ((TopCat.toSSet.map f).app _ σ) =
      windingIndex (g.comp (topMap f)) hgf σ := by
  have hleft := simplexIncrement_eq_pointLog_add_windingIndex g hg
    ((TopCat.toSSet.map f).app _ σ)
  have hright := simplexIncrement_eq_pointLog_add_windingIndex (g.comp (topMap f)) hgf σ
  rw [simplexIncrement_map g f hg hgf σ] at hleft
  have hvertices (i : Fin 2) :
      pointLog g (simplexMap ((TopCat.toSSet.map f).app _ σ) (stdSimplex.vertex i)) =
        pointLog (g.comp (topMap f)) (simplexMap σ (stdSimplex.vertex i)) := by
    rfl
  rw [hvertices 1, hvertices 0] at hleft
  have hcast : (windingIndex g hg ((TopCat.toSSet.map f).app _ σ) : ℂ) =
      (windingIndex (g.comp (topMap f)) hgf σ : ℂ) := by
    apply mul_right_cancel₀ twoPiI_ne_zero
    calc
      (windingIndex g hg ((TopCat.toSSet.map f).app _ σ) : ℂ) * twoPiI =
          simplexIncrement (g.comp (topMap f)) hgf σ -
            (pointLog (g.comp (topMap f)) (simplexMap σ (stdSimplex.vertex 1)) -
              pointLog (g.comp (topMap f)) (simplexMap σ (stdSimplex.vertex 0))) := by
            rw [hleft]
            ring
      _ = (windingIndex (g.comp (topMap f)) hgf σ : ℂ) * twoPiI := by
            rw [hright]
            ring
  exact_mod_cast hcast

/-- Pulling an integer winding cochain back along a continuous map is literally the integer
winding cochain of the pulled-back function. -/
theorem chainComplexMap_comp_windingIntegerCochain (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 1 ≫
      windingIntegerCochain g hg =
        windingIntegerCochain (g.comp (topMap f)) hgf := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    ιChainComplex_comp_windingIntegerCochain,
    ιChainComplex_comp_windingIntegerCochain,
    windingIndex_map g hg f hgf σ]

end IntegerNaturality
