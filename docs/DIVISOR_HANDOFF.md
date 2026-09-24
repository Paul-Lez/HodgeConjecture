# Divisor–Chern handoff

For an integral, smooth, projective complex scheme `X`,
`AlgebraicGeometry.ComplexPoint.hasDivisorClassOfCartierData` in
`Other/AlgebraicGeometry/ChernRelativeFinalAssembly.lean` proves the uniform
divisor–Chern identity. The full build passes (5343 jobs), and the comparison
audit checks 471 distinct declarations with only `propext`, `Classical.choice`,
and `Quot.sound`. The independent correctness and code-quality review is pending.

The proved proposition is the existing definition

```lean
def HasDivisorClassOfCartierData : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      sheafCycleClassOnCycles { scheme := X.left, structureMap := X.hom } 1 c.divisor =
        integralToRationalCohomology X 2 E.firstChernClass
```

The proof has no GAGA hypothesis. GAGA is developed separately in
[PR41](https://github.com/Paul-Lez/HodgeConjecture/pull/41) for the Lefschetz `(1,1)` application.

The established route is:

1. `ChernWindingGenericChartAlgebraic.lean` constructs normalized generic
   winding charts inside the required local lift opens.
2. `ChernRelativeCanonicalLift.lean` constructs the compatible Cartier lift and
   the supported relative Chern class, preserving the ambient `c₁` comparison.
3. `SupportSheafConeQuasiIso.lean`, `SupportSheafConeNormalization.lean`, and
   `SupportSheafConeSectionTransport.lean` identify the original support
   normalization with the fixed cone inverse, degree shift, and final sign.
4. `SupportAmbientSectionDerivedSquare.lean` and
   `RelativeChernOriginalAmbientDerivedBoundary.lean` transport the original
   supported class through an actual K-injective cocycle and the original
   boundary square.
5. `OriginalChernRawWinding.lean`, `OriginalChernRawWindingClassMap.lean`, and
   `OriginalChernRawWindingSection.lean` compute the local boundary on the
   canonical integer input as the literal raw winding class.
6. `OriginalChernAmbientSectionShift.lean` and
   `OriginalChernAmbientRawSection.lean` transport that computation to the
   ambient cohomology-sheaf section on the image of the chart open.
7. `ChernOriginalRawAmbientTransport.lean` compares the resulting raw cone map
   with the direct ambient map and transports its section from the restricted
   image of `⊤` to the literal ambient chart open.
8. `ChernRelativeSupportNormalized.lean`,
   `ChernRelativeSupportGenericUnit.lean`,
   `OriginalChernRawWindingNormalizationOnOpen.lean`,
   `SupportSheafConeRestrictionNaturality.lean`,
   `ChernComponentLocalIsolation.lean`,
   `ChernComponentSectionExtraction.lean`, and
   `ChernComponentRecovery.lean` provide the support enlargement, component
   isolation, and multiplicity extraction needed for chart gluing.
9. `ChernRelativeChartFormulaAssembly.lean` passes the proved local formula
   to `HasChernLocalModel`. The final reduction uses
   `hasDivisorClassOfCartierData_of_localModel` together with the unconditional
   `hasComponentSupportDecomposition_unconditional` theorem from
   `ClosedSupportCoheightDimension.lean`.

`ChernRelativeFinalAssembly.lean` composes these comparisons using the
compatible Cartier frame, original boundary maps, and fixed support normalization.
The result applies to every Cartier datum representing the given line bundle.

Validation after each substantive change:

```text
lake build
lake env lean scripts/lefschetz_axiom_audit.lean
lake exe lint-style HodgeConjecture Other HodgeGuide
python3 scripts/check_import_layers.py
git diff --check
```

The comparison audit includes the full uniform theorem and should report only
`propext`, `Classical.choice`, and `Quot.sound`. The remaining completion step is
independent review. Other Lefschetz and GAGA obligations are tracked separately.
