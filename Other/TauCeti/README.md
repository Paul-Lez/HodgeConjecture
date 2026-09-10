# Tau Ceti sheaf interfaces

These three files are adapted from [Tau Ceti](https://github.com/TauCetiProject/TauCeti/tree/b8d215394069a6c5713292fadcfa49746702a0eb/TauCeti/Algebra/Category/ModuleCat/Sheaf)
at commit `b8d215394069a6c5713292fadcfa49746702a0eb`, under its Apache 2.0 license.
Their copyright headers and the `TauCeti` namespaces are retained.

They provide the rank-one local-generator predicate, its local-trivialization interface,
and the identification of the free sheaf on one generator with the structure sheaf.
The holomorphic line-bundle construction uses these interfaces without changing this
repository's Lean or Mathlib versions. Local import paths and module documentation are
adapted; any further compatibility changes remain visible in the corresponding files.

`Other/TauCeti/SheafOfModules/Restriction.lean` is additionally adapted from Tau Ceti commit
`6b10e2573adea2abab44b08630b9c69e73048090`. It adds restriction and cover-refinement operations
for local trivialization atlases, while retaining Tau Ceti's copyright header and namespace.
The same current commit supplies the locally-free and invertible finite-presentation results in
`FinitePresentation.lean` and `InvertibleFinitePresentation.lean`.

`FiniteLocalTriviality.lean` and `CechTransition.lean` are original downstream interfaces in this
repository (and therefore carry the Formal Conjectures copyright). They use the adapted Tau Ceti
atlas API to select finite trivializing subcovers on compact spaces and to package their
change-of-frame cocycles.
