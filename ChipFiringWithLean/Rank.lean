import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Definition of maximal winnable divisor -/
def maximal_winnable (G : CFGraph V) (D : CFDiv V) : Prop :=
  winnable G D ∧ ∀ v : V, ¬winnable G (λ w => D w + if w = v then 1 else 0)

/-- A divisor is maximal unwinnable if it is unwinnable but adding
    a chip to any vertex makes it winnable -/
def maximal_unwinnable (G : CFGraph V) (D : CFDiv V) : Prop :=
  ¬winnable G D ∧ ∀ v : V, winnable G (λ w => D w + if w = v then 1 else 0)

/-- Check if there are edges in both directions between two vertices -/
def has_bidirectional_edges (G : CFGraph V) (O : Orientation G) (u v : V) : Prop :=
  ∃ e₁ e₂, e₁ ∈ O.directed_edges ∧ e₂ ∈ O.directed_edges ∧ e₁ = (u, v) ∧ e₂ = (v, u)

/-- All multiple edges between same vertices point in same direction -/
def consistent_edge_directions (G : CFGraph V) (O : Orientation G) : Prop :=
  ∀ u v : V, ¬has_bidirectional_edges G O u v

/-- An orientation is acyclic if it has no directed cycles and
    maintains consistent edge directions between vertices -/
def is_acyclic (G : CFGraph V) (O : Orientation G) : Prop :=
  consistent_edge_directions G O ∧
  ¬∃ p : DirectedPath G O,
    p.vertices.length > 0 ∧
    match (p.vertices.get? 0, p.vertices.get? (p.vertices.length - 1)) with
    | (some u, some v) => u = v
    | _ => False

/-- Given an acyclic orientation O with source q, returns a configuration c(O) -/
def orientation_to_config (G : CFGraph V) (O : Orientation G) (q : V)
    (h_acyclic : is_acyclic G O) (h_source : is_source G O q) : Config V q :=
  config_of_source G O q h_source

/-- The genus of a graph is its cycle rank: |E| - |V| + 1 -/
def genus (G : CFGraph V) : ℤ :=
  Multiset.card G.edges - Fintype.card V + 1

/-- A divisor has rank -1 if it is not winnable -/
def rank_eq_neg_one_wrt_winnability (G : CFGraph V) (D : CFDiv V) : Prop :=
  ¬(winnable G D)

/-- A divisor has rank -1 if its complete linear system is empty -/
def rank_eq_neg_one_wrt_complete_linear_system (G : CFGraph V) (D : CFDiv V) : Prop :=
  complete_linear_system G D = ∅

/-- Given a divisor D and amount k, returns all possible ways
    to remove k dollars from D (i.e. all divisors E where D-E has degree k) -/
def remove_k_dollars (D : CFDiv V) (k : ℕ) : Set (CFDiv V) :=
  {E | effective E ∧ deg E = k}

/-- A divisor D has rank ≥ k if the game is winnable after removing any k dollars -/
def rank_geq (G : CFGraph V) (D : CFDiv V) (k : ℕ) : Prop :=
  ∀ E ∈ remove_k_dollars D k, winnable G (λ v => D v - E v)

/-- Helper to check if a divisor has exactly k chips removed at some vertex -/
def has_k_chips_removed (D : CFDiv V) (E : CFDiv V) (k : ℕ) : Prop :=
  ∃ v : V, E = (λ w => D w - if w = v then k else 0)

/-- Helper to check if all k-chip removals are winnable -/
def all_k_removals_winnable (G : CFGraph V) (D : CFDiv V) (k : ℕ) : Prop :=
  ∀ E : CFDiv V, has_k_chips_removed D E k → winnable G E

/-- Helper to check if there exists an unwinnable configuration after removing k+1 chips -/
def exists_unwinnable_removal (G : CFGraph V) (D : CFDiv V) (k : ℕ) : Prop :=
  ∃ E : CFDiv V, effective E ∧ deg E = k + 1 ∧ ¬(winnable G (λ v => D v - E v))

/-- Axiom: If a divisor is winnable, there exists an effective divisor linearly equivalent to it -/
axiom winnable_iff_exists_effective (G : CFGraph V) (D : CFDiv V) :
  winnable G D ↔ ∃ D' : CFDiv V, effective D' ∧ linear_equiv G D D'

/-- Axiom: Rank existence and uniqueness -/
axiom rank_exists_unique (G : CFGraph V) (D : CFDiv V) :
  ∃! r : ℤ, (r = -1 ∧ rank_eq_neg_one_wrt_winnability G D) ∨
    (r ≥ 0 ∧ rank_geq G D r.toNat ∧ exists_unwinnable_removal G D r.toNat ∧
     ∀ k' : ℕ, k' > r.toNat → ¬(rank_geq G D k'))

/-- The rank function for divisors -/
noncomputable def rank (G : CFGraph V) (D : CFDiv V) : ℤ :=
  Classical.choose (rank_exists_unique G D)

/-- Rank satisfies the defining properties -/
axiom rank_spec (G : CFGraph V) (D : CFDiv V) :
  let r := rank G D
  (r = -1 ↔ rank_eq_neg_one_wrt_winnability G D) ∧
  (∀ k : ℕ, r ≥ k ↔ rank_geq G D k) ∧
  (∀ k : ℤ, k ≥ 0 → r = k ↔
    rank_geq G D k.toNat ∧
    exists_unwinnable_removal G D k.toNat ∧
    ∀ k' : ℕ, k' > k.toNat → ¬(rank_geq G D k'))

/-- Helpful corollary: rank = -1 exactly when divisor is not winnable -/
theorem rank_neg_one_iff_unwinnable (G : CFGraph V) (D : CFDiv V) :
  rank G D = -1 ↔ ¬(winnable G D) := by
  exact (rank_spec G D).1
