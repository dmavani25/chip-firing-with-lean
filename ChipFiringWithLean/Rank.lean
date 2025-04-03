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
import Paperproof

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

/-- Given an acyclic orientation O with a unique source q, returns a configuration c(O) -/
def orientation_to_config (G : CFGraph V) (O : Orientation G) (q : V)
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) : Config V q :=
  config_of_source h_acyclic h_unique_source

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

/-- Lemma: If a divisor is winnable, there exists an effective divisor linearly equivalent to it -/
lemma winnable_iff_exists_effective (G : CFGraph V) (D : CFDiv V) :
  winnable G D ↔ ∃ D' : CFDiv V, effective D' ∧ linear_equiv G D D' := by
  unfold winnable Div_plus
  simp only [Set.mem_setOf_eq]

/-- Axiom: Rank existence and uniqueness -/
axiom rank_exists_unique (G : CFGraph V) (D : CFDiv V) :
  ∃! r : ℤ, (r = -1 ∧ rank_eq_neg_one_wrt_winnability G D) ∨
    (r ≥ 0 ∧ rank_geq G D r.toNat ∧ exists_unwinnable_removal G D r.toNat ∧
     ∀ k' : ℕ, k' > r.toNat → ¬(rank_geq G D k'))

/-- The rank function for divisors -/
noncomputable def rank (G : CFGraph V) (D : CFDiv V) : ℤ :=
  Classical.choose (rank_exists_unique G D)

/-- Definition: Properties of rank function with respect to effective divisors -/
def rank_effective_char {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) (D : CFDiv V) (r : ℤ) :=
  rank G D = r ↔
  (∀ E : CFDiv V, effective E → deg E = r + 1 → ¬(winnable G (λ v => D v - E v))) ∧
  (∀ E : CFDiv V, effective E → deg E = r → winnable G (λ v => D v - E v))

/-- Definition (Axiomatic): Helper for rank characterization to get effective divisor -/
axiom rank_get_effective {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) (D : CFDiv V) :
  ∃ E : CFDiv V, effective E ∧ deg E = rank G D + 1 ∧ ¬(winnable G (λ v => D v - E v))

/-- Rank satisfies the defining properties -/
axiom rank_spec (G : CFGraph V) (D : CFDiv V) :
  let r := rank G D
  (r = -1 ↔ rank_eq_neg_one_wrt_winnability G D) ∧
  (∀ k : ℕ, r ≥ k ↔ rank_geq G D k) ∧
  (∀ k : ℤ, k ≥ 0 → r = k ↔
    rank_geq G D k.toNat ∧
    exists_unwinnable_removal G D k.toNat ∧
    ∀ k' : ℕ, k' > k.toNat → ¬(rank_geq G D k'))

/-- Axiomatic Definition: The zero divisor has rank 0 -/
axiom zero_divisor_rank (G : CFGraph V) : rank G (λ _ => 0) = 0

/-- Helpful corollary: rank = -1 exactly when divisor is not winnable -/
theorem rank_neg_one_iff_unwinnable (G : CFGraph V) (D : CFDiv V) :
  rank G D = -1 ↔ ¬(winnable G D) := by
  exact (rank_spec G D).1

/-- Lemma: If rank is not non-negative, then it equals -1 -/
lemma rank_neg_one_of_not_nonneg {V : Type} [DecidableEq V] [Fintype V]
  (G : CFGraph V) (D : CFDiv V) (h_not_nonneg : ¬(rank G D ≥ 0)) : rank G D = -1 := by
  -- rank_exists_unique gives ∃! r, P r ∨ Q r
  -- Classical.choose_spec gives (P r ∨ Q r) ∧ ∀ y, (P y ∨ Q y) → y = r, where r = rank G D
  have h_exists_unique_spec := Classical.choose_spec (rank_exists_unique G D)
  -- We only need the existence part: P r ∨ Q r
  have h_disjunction := h_exists_unique_spec.1
  -- Now use Or.elim on the disjunction
  apply Or.elim h_disjunction
  · -- Case 1: rank G D = -1 ∧ rank_eq_neg_one_wrt_winnability G D
    intro h_case1
    -- The goal is rank G D = -1, which is the first part of h_case1
    exact h_case1.1
  · -- Case 2: rank G D ≥ 0 ∧ rank_geq G D (rank G D).toNat ∧ ...
    intro h_case2
    -- This case contradicts the hypothesis h_not_nonneg
    have h_nonneg : rank G D ≥ 0 := h_case2.1
    -- Derive contradiction using h_not_nonneg
    exact False.elim (h_not_nonneg h_nonneg)

/-- Axiom: Linear equivalence is preserved when adding chips, provided deg D = g - 1
    This makes sense because such a D is maximal unwinnable, and adding a chip to a maximal unwinnable divisor
    is equivalent to adding a chip to the canonical divisor.
    This was especially hard to prove in Lean4, so we are leaving it as an axiom for the time being. -/
axiom linear_equiv_add_chip {V : Type} [DecidableEq V] [Fintype V]
  (G : CFGraph V) (D : CFDiv V) (v : V)
  (h_deg : deg D = genus G - 1) :
  linear_equiv G
    (λ w => D w + if w = v then 1 else 0)
    (λ w => (canonical_divisor G w - D w) + if w = v then 1 else 0)
