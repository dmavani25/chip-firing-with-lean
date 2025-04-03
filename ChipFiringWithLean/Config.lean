import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import ChipFiringWithLean.Basic
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A configuration on a graph G with respect to a distinguished vertex q.
    Represents an element of ℤ(V\{q}) ⊆ ℤV with non-negativity constraints on V\{q}.

    Fields:
    * vertex_degree - Assignment of integers to vertices
    * non_negative_except_q - Proof that all values except at q are non-negative -/
structure Config (V : Type) (q : V) :=
  /-- Assignment of integers to vertices representing the number of chips at each vertex -/
  (vertex_degree : V → ℤ)
  /-- Proof that all vertices except q have non-negative values -/
  (non_negative_except_q : ∀ v : V, v ≠ q → vertex_degree v ≥ 0)

/-- The degree of a configuration is the sum of all values except at q.
    deg(c) = ∑_{v ∈ V\{q}} c(v) -/
def config_degree {q : V} (c : Config V q) : ℤ :=
  ∑ v in (univ.filter (λ v => v ≠ q)), c.vertex_degree v

/-- Ordering on configurations: c ≥ c' if c(v) ≥ c'(v) for all v ∈ V.
    This is a pointwise comparison of the number of chips at each vertex. -/
def config_ge {q : V} (c c' : Config V q) : Prop :=
  ∀ v : V, c.vertex_degree v ≥ c'.vertex_degree v

/-- A configuration is non-negative if all vertices (including q) have non-negative values.
    This is stronger than the basic Config constraint which only requires non-negativity on V\{q}. -/
def config_nonnegative {q : V} (c : Config V q) : Prop :=
  ∀ v : V, c.vertex_degree v ≥ 0

/-- Linear equivalence of configurations: c ∼ c' if they can be transformed into one another
    through a sequence of lending and borrowing operations. The difference between configurations
    must be in the subgroup generated by firing moves. -/
def config_linear_equiv {q : V} (G : CFGraph V) (c c' : Config V q) : Prop :=
  let diff := λ v => c'.vertex_degree v - c.vertex_degree v
  diff ∈ AddSubgroup.closure (Set.range (λ v => λ w => if w = v then -vertex_degree G v else num_edges G v w))

-- Definition of the out-degree of a vertex v ∈ S with respect to a subset S ⊆ V \ {q}
-- This counts edges from v to vertices *outside* S (but not q).
-- outdeg_S(v) = |{ (v, w) ∈ E | w ∈ (V \ {q}) \ S }|
def outdeg_S (G : CFGraph V) (q : V) (S : Finset V) (v : V) : ℤ :=
  -- Sum num_edges from v to w, where w is not in S and not q.
  ∑ w in (univ.filter (λ x => x ≠ q)).filter (λ x => x ∉ S), (num_edges G v w : ℤ)

-- Standard definition of Superstability:
-- A configuration c is superstable w.r.t. q if for every non-empty subset S of V \ {q},
-- there is at least one vertex v in S that cannot fire without borrowing,
-- meaning its chip count c(v) is strictly less than its out-degree w.r.t. S.
def superstable (G : CFGraph V) (q : V) (c : Config V q) : Prop :=
  ∀ S : Finset V, S ⊆ univ.filter (λ x => x ≠ q) → S.Nonempty →
    ∃ v ∈ S, c.vertex_degree v < outdeg_S G q S v

/-- A maximal superstable configuration has no legal firings and dominates all other superstable configs -/
def maximal_superstable {q : V} (G : CFGraph V) (c : Config V q) : Prop :=
  superstable G q c ∧ ∀ c' : Config V q, superstable G q c' → config_ge c' c

/-- Axiom: Defining winnability of configurations through linear equivalence and chip addition.
    Used to show that adding a chip at any non-q vertex results in a winnable configuration
    when starting from a linearly equivalent divisor to a maximal superstable configuration.
    Proving this inductively is a bit tricky at the moment, and we ran into infinite recursive loop,
    thus we are declaring this as an axiom. -/
axiom winnable_through_equiv_and_chip (G : CFGraph V) (q : V) (D : CFDiv V) (c : Config V q) :
  linear_equiv G D (λ v => c.vertex_degree v - if v = q then 1 else 0) →
  maximal_superstable G c →
  ∀ v : V, v ≠ q →
  winnable G (λ w => D w + if w = v then 1 else 0)
