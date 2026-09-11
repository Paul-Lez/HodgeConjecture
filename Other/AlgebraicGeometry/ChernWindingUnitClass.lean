/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingBoundary
public import Other.AlgebraicGeometry.ChernLocalModelWinding
public import Other.AlgebraicGeometry.UnitExtensionCorrectedLiftsOfIso

/-!
# The winding homomorphism of an analytic chart

This file turns the topological winding class of `ChernWindingBoundary.lean` into the
`winding` field of `AlgebraicGeometry.ComplexPoint.ChernWindingChart`.

Fix an analytic open `V` of `X^an` and a closed support `S`.  A section of
`holomorphicUnitSheaf X d` over the punctured chart `V ∖ S` is, concretely, an invertible element
of the ring of holomorphic functions on `V ∖ S`, so it has an underlying continuous nowhere
vanishing complex function, and the winding class of that function is a class in
`H²(V, V ∖ S; ℚ)`, hence, after sheafification, a section over `V` of
`supportRelativeCohomologySheaf`.  The assignment is an additive map because the group law of
`holomorphicUnitSheaf` is multiplication of functions and the winding period is additive under
multiplication.

The only hypothesis is `HasWindingPeriods`, the rationality of the winding periods on the chart
(the integrality of the periods of the winding cocycle); see `ChernWindingBoundary.lean`.

`windingSheafHom_restrict_eq_zero` is the proof of `ChernWindingChart.HasTrivialUnitWinding` for
this homomorphism: a unit that extends across the support and has a holomorphic logarithm on the
whole chart has vanishing winding class, because its restriction to the punctured chart then has
a continuous logarithm there.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance chernWindingUnitClassTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable (V : Opens (TopCat.of (ComplexPoint X))) (S : Closeds (ComplexPoint X))

/-- The punctured chart, as an analytic open. -/
abbrev windingPuncturedOpen : Opens (TopCat.of (ComplexPoint X)) := V ⊓ S.compl

/-- The tautological identification of the space `V ∖ S` of the topological pair with the
analytic open `V ⊓ Sᶜ`. -/
def windingPuncturedMap :
    C(ChernWinding.puncturedSpace (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X)),
      ↥(windingPuncturedOpen X V S)) :=
  ⟨fun w => ⟨w.1.1, ⟨w.1.2, w.2⟩⟩,
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _⟩

/-- The invertible holomorphic function underlying a section of the unit sheaf on the punctured
chart, read as a continuous function on the space `V ∖ S` of the topological pair. -/
def windingUnitFunction
    (u : (holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S))) :
    C(ChernWinding.puncturedSpace (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X)), ℂ) :=
  ⟨fun w => (unitOf u).val (windingPuncturedMap X V S w),
    ((unitOf u).val.2.continuous).comp (windingPuncturedMap X V S).continuous⟩

theorem windingUnitFunction_apply
    (u : (holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S)))
    (w : ChernWinding.puncturedSpace (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) :
    windingUnitFunction X d V S u w = (unitOf u).val (windingPuncturedMap X V S w) := rfl

theorem windingUnitFunction_ne_zero
    (u : (holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S)))
    (w : ChernWinding.puncturedSpace (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) :
    windingUnitFunction X d V S u w ≠ 0 := by
  intro hz
  have h : ((unitOf u).val * (unitOf u).inv) (windingPuncturedMap X V S w) =
      (1 : C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥(windingPuncturedOpen X V S); 𝓘(ℂ, ℂ), ℂ⟯)
        (windingPuncturedMap X V S w) := by
    rw [(unitOf u).val_inv]
  rw [show (((unitOf u).val * (unitOf u).inv) (windingPuncturedMap X V S w)) =
      (unitOf u).val (windingPuncturedMap X V S w) *
        (unitOf u).inv (windingPuncturedMap X V S w) from rfl] at h
  rw [show (unitOf u).val (windingPuncturedMap X V S w) = windingUnitFunction X d V S u w from rfl,
    hz, zero_mul] at h
  exact zero_ne_one h

theorem windingUnitFunction_add
    (a b : (holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S)))
    (w : ChernWinding.puncturedSpace (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) :
    windingUnitFunction X d V S (a + b) w =
      windingUnitFunction X d V S a w * windingUnitFunction X d V S b w := rfl

/-! ### The winding homomorphism -/

/-- **The rationality obligation on a chart.**  Every invertible holomorphic function on the
punctured chart has rational winding periods.  See
`ChernWinding.HasRationalWindingPeriod`. -/
def HasWindingPeriods : Prop :=
  ∀ u : (holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S)),
    ChernWinding.HasRationalWindingPeriod (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))
      (windingUnitFunction X d V S u) (windingUnitFunction_ne_zero X d V S u)

variable {X d V S}

/-- **The winding homomorphism**, with values in the honest relative cohomology of the pair
`(V, V ∖ S)`. -/
def windingRelativeHom (h : HasWindingPeriods X d V S) :
    ((holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S))) →+
      RelativeCohomology ℚ
        (ChernWinding.supportPair (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) 2 where
  toFun u := ChernWinding.windingRelativeClass _ _ (h u)
  map_zero' := by
    refine ChernWinding.windingRelativeClass_eq_zero_of_exp _ _ (0 : C(_, ℂ)) ?_ (h 0)
    intro y
    rw [ContinuousMap.zero_apply, Complex.exp_zero]
    rfl
  map_add' a b := by
    exact ChernWinding.windingRelativeClass_mul _ _
      (fun w => windingUnitFunction_add X d V S a b w) (h a) (h b) (h (a + b))

theorem windingRelativeHom_apply (h : HasWindingPeriods X d V S)
    (u : (holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S))) :
    windingRelativeHom h u = ChernWinding.windingRelativeClass _ _ (h u) := rfl

/-- **The winding homomorphism**, with values in the sections over `V` of the local
relative-cohomology sheaf with support in `S`.  This is the `winding` field of a
`ChernWindingChart`. -/
def windingSheafHom (h : HasWindingPeriods X d V S) :
    ((holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S))) →+
      ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (S : Set (ComplexPoint X)) 2).obj.obj (op V)) :=
  AddMonoidHom.comp
    ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X)) 2).app (op V)).hom
    (windingRelativeHom h)

theorem windingSheafHom_apply (h : HasWindingPeriods X d V S)
    (u : (holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S))) :
    windingSheafHom h u =
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
        (S : Set (ComplexPoint X)) 2).app (op V)
        (ChernWinding.windingRelativeClass _ _ (h u)) := rfl

/-! ### Units with a holomorphic logarithm on the whole chart -/

/-- **Triviality on extendable units.**  If a unit on the whole chart `V` is `exp(2πi f)` for a
holomorphic `f` on `V`, then its restriction to the punctured chart has vanishing winding class:
the continuous function `2πi f` is a global logarithm of it there. -/
theorem windingRelativeHom_restrict_eq_zero (h : HasWindingPeriods X d V S)
    (u : (holomorphicUnitSheaf X d).obj.obj (op V))
    (f : (holomorphicAdditiveSheaf X d).obj.obj (op V))
    (hf : (holomorphicExponential X d).hom.app (op V) f = u) :
    windingRelativeHom h ((holomorphicUnitSheaf X d).obj.map
      (homOfLE (inf_le_left : windingPuncturedOpen X V S ≤ V)).op u) = 0 := by
  subst hf
  refine ChernWinding.windingRelativeClass_eq_zero_of_exp _ _
    (⟨fun w => 2 * (Real.pi : ℂ) * Complex.I *
        (show C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥V; 𝓘(ℂ, ℂ), ℂ⟯ from f) w.1, by
      exact continuous_const.mul
        ((show C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥V; 𝓘(ℂ, ℂ), ℂ⟯ from f).2.continuous.comp
          continuous_subtype_val)⟩) (fun w => rfl) _

theorem windingSheafHom_restrict_eq_zero (h : HasWindingPeriods X d V S)
    (u : (holomorphicUnitSheaf X d).obj.obj (op V))
    (f : (holomorphicAdditiveSheaf X d).obj.obj (op V))
    (hf : (holomorphicExponential X d).hom.app (op V) f = u) :
    windingSheafHom h ((holomorphicUnitSheaf X d).obj.map
      (homOfLE (inf_le_left : windingPuncturedOpen X V S ≤ V)).op u) = 0 := by
  have hz := windingRelativeHom_restrict_eq_zero h u f hf
  show ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X)) 2).app (op V)).hom
    (windingRelativeHom h ((holomorphicUnitSheaf X d).obj.map
      (homOfLE (inf_le_left : windingPuncturedOpen X V S ≤ V)).op u)) = 0
  rw [hz]
  exact AddMonoidHom.map_zero _

end AlgebraicGeometry.ComplexPoint
