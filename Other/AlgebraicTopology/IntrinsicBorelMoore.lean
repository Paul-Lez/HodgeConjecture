/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularChainSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Intrinsic chain-sheaf Borel–Moore homology

`BorelMooreHomology R X n` is `𝕳⁻ⁿ(X, 𝒞_X)`, where `𝒞_X` is the actual
sheafification of relative singular chains on `X`, in cohomological grading.
Hypercohomology is defined by morphisms from the constant integer sheaf in the
unbounded derived category. In particular, the definition does not choose an
ambient embedding, a compactification, an orientation, or a bounded replacement.
It applies to the chain sheaf of a singular space as well as a smooth space.

The output is an abelian group with field-valued chains as coefficients. It is
deliberately distinct from the relative homology of a compactification pair.
Comparisons with compactification-relative homology and with ambient derived
support require comparison theorems; they are not definitional equalities.

The chain-sheaf construction is described in Baumann–Kamnitzer–Knutson,
*The Mirković–Vilonen basis and Duistermaat–Heckman measures*, §5.1.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (X : TopCat.{u})

local instance intrinsicBorelMooreHasDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

/-- The constant integer sheaf in degree zero. The universe lift lets the
coefficient sheaf live in the same universe as the chain sheaf. -/
def borelMooreIntegerComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ :=
  (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat.{u} X) 0).obj
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- Unbounded hypercohomology as additive derived Hom from the integer sheaf.
Taking global sections is represented by that sheaf; shifting the target by
`n` gives hypercohomological degree `n`. -/
def borelMooreHypercohomologyFunctor (n : ℤ) :
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} X) ⥤ AddCommGrpCat.{u + 1} :=
  shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op (DerivedCategory.Q.obj (borelMooreIntegerComplex X)))

/-- Hypercohomology of the specified coefficient complex, without any lower
cohomological bound or smoothness assumption. -/
abbrev BorelMooreHypercohomology
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ) (n : ℤ) :
    AddCommGrpCat.{u + 1} :=
  (borelMooreHypercohomologyFunctor X n).obj (DerivedCategory.Q.obj K)

/-- A quasi-isomorphism of actual coefficient complexes induces a canonical
hypercohomology isomorphism. The comparison is obtained by localization. -/
def borelMooreHypercohomologyIsoOfQuasiIso
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ}
    (f : K ⟶ L) [QuasiIso f] (n : ℤ) :
    BorelMooreHypercohomology X K n ≅ BorelMooreHypercohomology X L n :=
  (borelMooreHypercohomologyFunctor X n).mapIso (asIso (DerivedCategory.Q.map f))

/-- The isomorphism uses the actual map on derived Hom. -/
@[simp]
theorem borelMooreHypercohomologyIsoOfQuasiIso_hom
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ}
    (f : K ⟶ L) [QuasiIso f] (n : ℤ) :
    (borelMooreHypercohomologyIsoOfQuasiIso X f n).hom =
      (borelMooreHypercohomologyFunctor X n).map (DerivedCategory.Q.map f) := rfl

/-- Hypercohomology transport also allows the degree to change, provided an
isomorphism of the actual shifted coefficient objects has been proved. -/
def borelMooreHypercohomologyIsoOfShiftedIso
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ}
    {n m : ℤ} (e : (DerivedCategory.Q.obj K)⟦n⟧ ≅ (DerivedCategory.Q.obj L)⟦m⟧) :
    BorelMooreHypercohomology X K n ≅ BorelMooreHypercohomology X L m :=
  (preadditiveCoyoneda.obj
    (op (DerivedCategory.Q.obj (borelMooreIntegerComplex X)))).mapIso e

/-- Intrinsic Borel–Moore homology: hypercohomology of the chain sheaf on the
space itself. Homological degree `n` is cohomological degree `-n`. -/
abbrev BorelMooreHomology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℤ) :
    AddCommGrpCat.{u + 1} :=
  BorelMooreHypercohomology X (singularChainSheafCochainComplex R X) (-n)

/-- The intrinsic group uses precisely the constructed chain-sheaf complex. -/
theorem borelMooreHomology_eq_hypercohomology (R : Type u) [Field R] (n : ℤ) :
    BorelMooreHomology R X n =
      BorelMooreHypercohomology X (singularChainSheafCochainComplex R X) (-n) := rfl

end AlgebraicTopology.Singular
