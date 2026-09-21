/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization

/-!
# The localization sequence on injective coefficient complexes

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- Let `U` be open in a topological space `X` and `F` a sheaf of abelian groups. This is the
sequence `Γ_{X \ U}(F) → F → j_*(F|_U)`, where `j : U → X` is inclusion. The maps include
sections vanishing on `U` and restrict to `U`. -/
def supportRestrictionShortComplex (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk ((sheafSectionsSupportedOutsideInclusion X U).app F)
    ((toOpenRestrictionPushforward X U).app F)
    (sheafSectionsSupportedOutsideInclusion_restriction X U F)

/-- Let `U,V` be open in a topological space `X` and `F` a sheaf of abelian groups. This sequence
takes sections on `V` of `Γ_{X \ U}(F) → F → j_*(F|_U)`. Under the intersection identification
it is `ker(F(V) → F(V ∩ U)) → F(V) → F(V ∩ U)`. -/
def supportRestrictionSectionsShortComplex (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) : ShortComplex AddCommGrpCat.{u} :=
  (supportRestrictionShortComplex X U F).map (supportEvaluation X V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For injective coefficients, evaluation on every open set preserves this localization
sequence. -/
private lemma supportRestrictionSectionsShortComplex_shortExact (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    (supportRestrictionSectionsShortComplex X U V F).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _
    (KernelFork.mapIsLimit _ (kernelIsKernel _) (supportEvaluation X V))
  mono_f := mono_of_isLimit_fork
    (KernelFork.mapIsLimit _ (kernelIsKernel _) (supportEvaluation X V))
  epi_g := toOpenRestrictionPushforward_app_epi X U F V

/-- The support/restriction sequence is short exact even after taking sections
on an arbitrary open set, for a termwise injective coefficient complex. -/
lemma supportRestrictionSectionsComplexShortComplex_shortExact (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    (supportRestrictionSectionsComplexShortComplex X U V K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    supportRestrictionSectionsShortComplex_shortExact X U V (K.X n)

end TopCat.Sheaf

end
