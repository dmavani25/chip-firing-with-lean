import ChipFiringWithLean.CFGraph
import ChipFiringWithLean.RRGHelpers
import Mathlib.Algebra.Ring.Int

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

-- Proof of Riemann-Roch for graphs goes here
