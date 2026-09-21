/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf
/-!
# The global normalized smooth-support coclass section

Holomorphic normal charts supply local relative coclasses whose ambient overlap agreement
identifies their sheaf germs, and those germs vanish off the closed image because the
relative complexes do. Unique sheaf gluing then produces the global section, with its
complex normalization.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open TopCat.Presheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- Let `i : Y → X` be a closed immersion of smooth complex schemes of respective dimensions `m` and
`d`, and put `S = i(Y(ℂ))` and `c = d-m`. For `z ∈ Y(ℂ)`, this is the source of a chosen
holomorphic chart near `i(z)` with coordinates in `ℂ^m × ℂ^c` in which `S` is the zero set of
the normal coordinate. -/
def smoothClosedSupportChartOpen (z : ComplexPoint Y) :
    Opens (ComplexPoint X) :=
  ⟨(closedImmersionHolomorphicFlatteningChart X Y i m d z).source,
    (closedImmersionHolomorphicFlatteningChart X Y i m d z).open_source⟩

theorem mem_smoothClosedSupportChartOpen (z : ComplexPoint Y) :
    Point.map i z ∈ smoothClosedSupportChartOpen X Y i m d z :=
  closedImmersionHolomorphicFlatteningChart_mem_source X Y i m d z

/-- Let `i : Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. This is the sheafification on `X(ℂ)` of the relative singular cohomology
presheaf `V ↦ H^{2c}(V,V \ S;ℚ)`, considered as abelian groups. -/
abbrev smoothClosedSupportCoclassSheaf : TopCat.Sheaf AddCommGrpCat
    (TopCat.of (ComplexPoint X)) :=
  -- The support is `Y(ℂ) ⊆ X(ℂ)`, the image of the closed immersion `i`; the degree is twice
  -- the codimension of `Y` in `X`.
  𝓗_[Set.range (Point.map i)]^(2 * (d - m))(TopCat.of (ComplexPoint X); ℚ)

/-- Let `i : Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. On the chosen normal chart at `i(z)`, with `z ∈ Y(ℂ)`, this is a section
of the sheafification of `V ↦ H^{2c}(V,V \ S;ℚ)`. It is obtained by pulling back the class in
`H^{2c}(ℂ^c,ℂ^c \ {0};ℚ)` evaluating to `1` on the complex orientation class along the normal
coordinate and sheafifying. -/
def smoothClosedSupportChartSheafSection (z : ComplexPoint Y) :
    (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj
      (op (smoothClosedSupportChartOpen X Y i m d z)) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * (d - m))).app _
      (smoothClosedSupportChartCoclass X Y i m d z
        (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))

/-- Let `i : Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. For `z ∈ Y(ℂ)` and `x` in the chosen normal chart at `i(z)`, this is a
germ in the sheafification of `V ↦ H^{2c}(V,V \ S;ℚ)`. It is the germ at `x` of the pullback
along the normal coordinate of the class in `H^{2c}(ℂ^c,ℂ^c \ {0};ℚ)` evaluating to `1` on the
complex orientation class. -/
def smoothClosedSupportChartCoclassGerm (z : ComplexPoint Y)
    (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.stalk x :=
  supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * (d - m))
    (smoothClosedSupportChartOpen X Y i m d z) x hx
    (smoothClosedSupportChartCoclass X Y i m d z
      (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))

set_option backward.isDefEq.respectTransparency false in
/-- The ambient overlap theorem proves equality of chart germs on support. -/
private theorem smoothClosedSupportChartCoclassGerm_eq
    (z z' : ComplexPoint Y) (x : ComplexPoint X)
    (hxS : x ∈ Set.range (Point.map i))
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z)
    (hx' : x ∈ smoothClosedSupportChartOpen X Y i m d z') :
    smoothClosedSupportChartCoclassGerm X Y i m d z x hx =
      smoothClosedSupportChartCoclassGerm X Y i m d z' x hx' := by
  obtain ⟨W, hW, hW', hxW, heq⟩ := exists_open_smoothClosedSupportChartCoclass_eq
    X Y i m d z z' x hxS hx hx'
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
    (U := smoothClosedSupportChartOpen X Y i m d z)
    (V := smoothClosedSupportChartOpen X Y i m d z')
    hW hW' x hxW
  simpa only [smoothClosedSupportChartCoclass_restrict] using heq

/-- Away from the closed image, the chart coclass germ is zero. -/
private theorem smoothClosedSupportChartCoclassGerm_eq_zero
    (z : ComplexPoint Y) (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z)
    (hxS : x ∉ Set.range (Point.map i)) :
    smoothClosedSupportChartCoclassGerm X Y i m d z x hx = 0 :=
  supportRelativeCohomologyGerm_eq_zero_of_not_mem
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
    (isClosed_range_map_of_closedImmersion i)
    (smoothClosedSupportChartOpen X Y i m d z) x hx hxS
    (smoothClosedSupportChartCoclass X Y i m d z
      (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))

open scoped Classical in
/-- Let `i : Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. This element of the stalk at `x` of the sheafification of `V ↦
H^{2c}(V,V \ S;ℚ)` is zero off `S`. On `S`, it is the germ of the pullback, in a chosen normal
chart at `x`, of the class in `H^{2c}(ℂ^c,ℂ^c \ {0};ℚ)` evaluating to `1` on the complex
orientation class. -/
def smoothClosedSupportCoclassStalk (x : ComplexPoint X) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.stalk x :=
  if hxS : x ∈ Set.range (Point.map i) then
    smoothClosedSupportChartCoclassGerm X Y i m d hxS.choose x
      (by simpa only [hxS.choose_spec] using
        mem_smoothClosedSupportChartOpen X Y i m d hxS.choose)
  else 0

/-- The normalized germ family agrees with every chart, including at points outside the
support. -/
theorem smoothClosedSupportCoclassStalk_eq_chartGerm
    (z : ComplexPoint Y) (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z) :
    smoothClosedSupportCoclassStalk X Y i m d x =
      smoothClosedSupportChartCoclassGerm X Y i m d z x hx := by
  by_cases hxS : x ∈ Set.range (Point.map i)
  · rw [smoothClosedSupportCoclassStalk, dif_pos hxS]
    exact smoothClosedSupportChartCoclassGerm_eq X Y i m d
      hxS.choose z x hxS _ hx
  · rw [smoothClosedSupportCoclassStalk, dif_neg hxS]
    exact (smoothClosedSupportChartCoclassGerm_eq_zero X Y i m d z x hx hxS).symm

@[simp] theorem smoothClosedSupportCoclassStalk_eq_zero
    (x : ComplexPoint X) (hxS : x ∉ Set.range (Point.map i)) :
    smoothClosedSupportCoclassStalk X Y i m d x = 0 := by
  rw [smoothClosedSupportCoclassStalk, dif_neg hxS]

/-- The charts and the open support complement prove local representability
of the entire normalized stalk family. -/
theorem smoothClosedSupportCoclassStalk_locallyRepresentable :
    ∀ x : ComplexPoint X,
      ∃ (U : Opens (ComplexPoint X)) (_ : x ∈ U)
        (s : (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj (op U)),
        ∀ (y : ComplexPoint X) (hy : y ∈ U),
          (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.germ U y hy s =
            smoothClosedSupportCoclassStalk X Y i m d y := by
  intro x
  by_cases hxS : x ∈ Set.range (Point.map i)
  · obtain ⟨z, rfl⟩ := hxS
    refine ⟨smoothClosedSupportChartOpen X Y i m d z,
      mem_smoothClosedSupportChartOpen X Y i m d z,
      smoothClosedSupportChartSheafSection X Y i m d z, ?_⟩
    exact fun y hy ↦ (smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z y hy).symm
  · let U : Opens (ComplexPoint X) :=
      ⟨(Set.range (Point.map i))ᶜ, (isClosed_range_map_of_closedImmersion i).isOpen_compl⟩
    refine ⟨U, hxS, 0, ?_⟩
    intro y hy
    rw [map_zero, smoothClosedSupportCoclassStalk_eq_zero X Y i m d y hy]

/-- Let `i : Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. This global section of the sheafification of `V ↦ H^{2c}(V,V \ S;ℚ)`
glues the zero section off `S` with pullbacks in normal charts of the class in `H^{2c}(ℂ^c,ℂ^c \
{0};ℚ)` evaluating to `1` on the complex orientation class. -/
def smoothClosedSupportCoclassSection :
    -- A global section of `𝓗^{2(d-m)}_{Y(ℂ)}` on `X(ℂ)`.
    (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj
      -- All of `X(ℂ)`.
      (op ⊤) :=
  TopCat.Sheaf.sectionOfLocallyRepresentable _
    (smoothClosedSupportCoclassStalk X Y i m d)
    (smoothClosedSupportCoclassStalk_locallyRepresentable X Y i m d)

end AlgebraicGeometry.ComplexPoint
