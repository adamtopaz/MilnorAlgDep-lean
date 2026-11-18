module

public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Mathlib files used by the companion text

Documents of the companion text are not modules (see `site/README.md`), and Mathlib warns about
every non-module file that imports one of its modules directly. Documents therefore never import
Mathlib themselves: add the Mathlib files whose declarations the text shows (with `{docstring}`
or `{name}`) to this module instead.
-/
