/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import HodgeGuide.Overview
import HodgeGuide.HodgeSide
import HodgeGuide.CycleSide
import HodgeGuide.FundamentalClass
import HodgeGuide.Statement
import HodgeGuide.References
import HodgeGuide.Provenance

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Hodge Conjecture Formalization" =>

%%%
authors := ["The HodgeConjecture contributors"]
%%%

:::fcProvenance
:::

This guide explains the formalization of the Hodge conjecture in the
[`HodgeConjecture`](https://github.com/Paul-Lez/HodgeConjecture) repository, which will eventually
appear in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures). The goal is
to faithfully encode the statement of the
[Clay Millennium Prize Problem](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=56)
in Lean.

The conjecture is stated, not proved. A few classical theorems surrounding the statement are not
yet formalized either; {ref "scope-and-status"}[Scope and status] lists them.

The Lean code in this guide, including the terms that appear inside sentences, is elaborated when
the site is built. Definitions are quoted in full, and the build checks that each quotation is
definitionally equal to the declaration in the repository; theorems are listed with `#check`, and
their statements appear on hover, as do the types and docstrings of all names. Names defined
in this repository are underlined with dots wherever they appear, in code, in hovers, and in
the text; every other name comes from Mathlib or from Lean itself, and the guide does not
re-explain those. The site is generated with [Verso](https://github.com/leanprover/verso).

{include 1 HodgeGuide.Overview}

{include 1 HodgeGuide.HodgeSide}

{include 1 HodgeGuide.CycleSide}

{include 1 HodgeGuide.FundamentalClass}

{include 1 HodgeGuide.Statement}

{include 1 HodgeGuide.References}
