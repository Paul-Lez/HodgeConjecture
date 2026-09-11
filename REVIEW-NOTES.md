# Review notes: items not turned into pull requests

From a review of the Hodge conjecture statement and its supporting library, 2026-09-11. PRs #62-69,
#74, #79 and #80 came out of the same review. Everything below is what was left over.

## Needs a human decision first

**#79 and #80 are the same change, twice.** #79 moves the complex-point existence instance to a new
file and weakens its hypothesis; #80 weakens the hypothesis in place, which is the better form. One
of the two should be closed. #79 was closed and then reopened, so its history reads oddly; that is
my error, not a signal about the content.

## Open mathematics, in rough order of value

1. **Nonvanishing of the constructed cycle class.** Nothing proves
   `cycleComponentSheafClass X x hx ≠ 0`, and nothing links it to `IsRationalComponentCycleClass`
   (`HodgeConjecture/Definitions/AlgebraicGeometry/Coniveau.lean`). `HodgeGuide/FundamentalClass.lean`
   names this as the crux ("purity alone fixes a line but not the multiplicity-one generator that a
   cycle class map needs"), but it is absent from the guide's list of open items.
   At `p = 0` it is decidable today: `hodgeClasses_zero_eq_top` proves `Hdg^0(ℚ; X) = ⊤`, so the
   statement at `p = 0` asserts that `H^0` is spanned by one component class. If that class were
   zero the statement would be false rather than vacuous.
   `Other/AlgebraicGeometry/HodgeCodimensionZero.lean` already reduces the case to
   `hcompare : algebraicCycleClassSpan X 0 = codimensionZeroCycleClassSpan X`, which is exactly the
   comparison of the constructed class against `fieldCohomologyUnit`. Nothing proves `hcompare`.
   The two codimension-zero constructions in the library are never compared to each other.

   **Partly done, unpushed.** Local branch `codim-zero-compare` (worktree `/home/bmehta/hodge-codim0`,
   two commits, `lake build` clean, layer check clean, no `sorry` or axiom) reduces `hcompare` to a
   single concrete nonvanishing statement and settles it in dimension zero. It adds
   `Other/AlgebraicGeometry/CodimensionZeroClassComparison.lean`, which proves that the codimension-zero
   span is the line on the generic-point class, that `forgetSupport` at support `Set.univ` is injective,
   and hence that on a connected analytification
   `algebraicCycleClassSpan X 0 = codimensionZeroCycleClassSpan X` holds if and only if
   `cycleComponentSmoothSupportCoclassSection X (genericPoint X.left) _ ≠ 0`; and
   `Other/AlgebraicGeometry/CodimensionZeroDimensionZero.lean`, which proves that nonvanishing when
   `dim X.left = 0` (there the generic point also has maximal codimension, so the existing point
   normalization applies), giving `hcompare` outright and
   `Hdg^p(ℚ; X) ≤ algebraicCycleClassSpan X p` in every codimension for a dimension-zero variety.
   For `dim X.left > 0` the chain stops at the sheafification unit `supportRelativeCohomologyToSheaf`:
   `chartNormalProjectionCoclass` is normalized to one on the normal class, but nothing shows its germ
   in the sheafified relative-cohomology presheaf is nonzero. Two routes were examined and not
   completed: local injectivity of `toSheafify` in degree zero, and a codimension-zero analogue of
   `CycleComponentPointCoclassSectionNormalization.lean`.

2. **`ConnectedSpace (ComplexPoint X)`**, proved so far only for `dim = 0`
   (`connectedSpaceOfDimensionEqZero`). Discharging it makes `HodgeCodimensionZero.lean`
   unconditional. It reduces to

   ```lean
   theorem eq_const_of_isLocallyConstant (X : Over (Spec ↧ℂ))
       [IsIntegral X.left] [IsProjective X.hom]
       (f : ComplexPoint X → ℂ) (hf : IsLocallyConstant f) :
       ∃ c, f = Function.const _ c
   ```

   together with `instNonemptyComplexPoint`: a clopen set with both parts nonempty gives a
   nonconstant locally constant indicator. The algebraic half (properness and `IsIntegral` giving
   `Γ(X.left, ⊤) = ℂ`) looks tractable in Lean; the analytic half is a GAGA statement with no
   Mathlib support found.

3. **`hprincipal` and Chow descent.** `Other/AlgebraicGeometry/PrincipalDivisorCycleClass.lean`
   already splits it into a Gysin/pushforward theorem and a codimension-one principal-divisor
   theorem, either of which stands alone.

4. **Purity beyond `p = d`, and compatibility of the Betti comparison with forgetting support.**
   Both are real and both are recorded only in `Other/` docstrings, which the published site never
   links, so a reader of the roadmap will not learn they are open.

## Library cleanup not attempted

5. **`Lemmas/Algebra/PolynomialCatenary.lean`** copies about 110 lines from
   `Mathlib/RingTheory/NoetherNormalization.lean`, where eight of the nine declarations are
   `private`. #65 records the provenance. The copy goes away once Mathlib makes `T` and
   `T_leadingcoeff_isUnit` public, which is a small Mathlib PR.

6. **`Lemmas/AlgebraicTopology/SheafCohomologyWithSupport.lean`**, about 310 lines, has one
   consumer: a 58-line file in `Other/`. It computes `Ext(i_*ℤ_Z, F)`, a different object from the
   other two support constructions, and has no comparison with either. Worth relocating or
   renaming so the three are told apart; they should not be merged, since
   `CohomologyWithSupport.lean` and `DerivedSheafSupport.lean` are a deliberate pair, proved
   equivalent at `DerivedSupportRationalConeComparison.lean:322`.

7. **Escape hatches, which block the Mathlib plan**: 473 `set_option backward.*` across 103 files
   (against 7 in all of `formal-conjectures`), nine `maxHeartbeats` up to 2000000, one
   `maxRecDepth 4000`, 25 `linter.style.haveILetI` disabled, and
   `HodgeFiltration.lean:296-298,319-322` depending on compiler-generated
   `TopCat.instCategorySheaf._aux_1/_3/_5` with `linter.auxLemma` off, which will break on a
   Mathlib bump.

8. **Duplicate instances.** `Point.analyticTopology` is a global instance needing no side
   conditions, yet 20 files redeclare it `local` and three declare global duplicates
   (`IntegralProjectiveVariety.lean:77`, `ComplexAffineSpace.lean:266`,
   `ProjectiveAnalytification.lean:1431`); about 20 `HasDerivedCategory` instances are redeclared
   under different names, which `Points.lean:268` acknowledges in prose. The bodies agree, so there
   is no live defect, but mixing two of them is what forces the `set_option backward.*` lines at
   those sites.

9. **Statement presentation.** `Over (Spec ↧ℂ)` puts `X.left` and `X.hom` in the statement, and the
   docstring has to explain them. Mathlib's idiom is `(X : Scheme) [X.Over S]` with `X ↘ S`. This
   is a repo-wide change (234 occurrences of the `Over` form, none of the typeclass form), so it is
   a decision rather than a patch.

10. **Prose.** #67 rewrote the 33 module docstrings whose titles began "Actual". Declaration
    docstrings were left alone, and "actual" still appears about 640 times across 124 files, with
    221 of 250 module docstrings longer than three lines.

11. **Headers.** Two copyright header styles are in use (155 files short, 212 long).
    `Definitions/AlgebraicGeometry/ProjectiveSpace.lean` is dated 2025 where every other file says
    2026. One file carries `(c) 2026 Michael Lee. All rights reserved.`, which differs from the
    project's Apache notice and is the author's to settle.

## Guide claims worth re-checking

12. `HodgeGuide/Statement.lean` says nothing is lost by using the span of component classes. That
    is unproved, and it is where the vacuity risk in item 1 sits.
13. The guide's list of open items has three entries; items 1 and 4 above are missing from it.
14. Both source tours in the guide omit `Coniveau.lean`, the home of `algebraicCycleClassSpan`.
15. The two sanity checks in `HodgeSide.lean` carry no declaration names, so the guide's `rfl`
    certification does not cover them.
16. The site never mentions `HodgeCodimensionZero.lean`, the one case of the conjecture proved
    unconditionally (given connectedness).

## Review claims that turned out to be wrong

Recorded so nobody spends time re-checking them. Several were artifacts of reviewing the
`formal-conjectures` port, which carries `HodgeConjecture/` without `Other/` or `HodgeGuide/`.

- `Nonempty (ComplexPoint X)` is proved, in `Other/AlgebraicGeometry/ProjectiveAnalytificationConnected.lean`.
- The constant-sheaf to singular comparison is proved, and its additive upgrade
  `rationalCohomologyAddEquivSingularCohomology` is in
  `Other/AlgebraicGeometry/BettiGlobalSectionsAdditivity.lean`.
- `Definitions/Algebra/Homology/LinearDual.lean` does not duplicate `Functor.mapHomotopy` or
  `ChainComplex.linearYonedaObj`; Mathlib has no `ModuleCat` dual functor.
- `Lemmas/Analysis/NormedSpace/WedgeCovectors.lean` already calls Mathlib's determinant lemmas. The
  real overlap was nine lines, handled in #68. `alternatization_smul` is genuinely absent from
  Mathlib, whose `alternatization` is only an `AddMonoidHom`.
- `RightDerivedFunctorPlusNaturality.lean` calls `Functor.rightDerivedNatTrans` rather than
  duplicating it.
- `Definitions/Algebra/DeRham/Basic.lean` was rebuilt on `KaehlerDifferential` in #24.
- Deleting `globalSectionsFunctor` in favour of Mathlib's `sheafSections` is a non-change: the two
  are `rfl`-equal but the `TopCat.Sheaf` spelling in its type is load-bearing, since that is a
  semireducible `def`, so inlining would need an ascription at each of 82 use sites and both of its
  instances restated. #74 keeps the name and type and routes the body through Mathlib.
