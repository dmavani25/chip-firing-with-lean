import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset

import Init.Core
import Init.NotationExtra

import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

-- Define a set of edges to be loopless only if it doesn't have loops
def isLoopless (edges : Multiset (V × V)) : Bool :=
  Multiset.card (edges.filter (λ e => (e.1 = e.2))) = 0

def isLoopless_prop (edges : Multiset (V × V)) : Prop :=
  ∀ v, (v, v) ∉ edges

lemma isLoopless_prop_bool_equiv (edges : Multiset (V × V)) :
    isLoopless_prop edges ↔ isLoopless edges = true := by
  unfold isLoopless_prop isLoopless
  constructor
  · intro h
    apply decide_eq_true
    rw [Multiset.card_eq_zero]
    simp only [Multiset.eq_zero_iff_forall_not_mem]
    intro e he
    have h_eq : e.1 = e.2 := by
      exact Multiset.mem_filter.mp he |>.2
    have he' : e ∈ edges := by
      exact Multiset.mem_filter.mp he |>.1
    cases e with
    | mk a b =>
      simp at h_eq
      have : (a, b) = (a, a) := by rw [h_eq]
      rw [this] at he'
      exact h a he'

  · intro h
    intro v
    intro hv
    apply False.elim
    have h_filter : (v, v) ∈ Multiset.filter (λ e => e.1 = e.2) edges := by
      apply Multiset.mem_filter.mpr
      constructor
      · exact hv
      · simp

    have h_card : Multiset.card (Multiset.filter (λ e => e.1 = e.2) edges) > 0 := by
      apply Multiset.card_pos_iff_exists_mem.mpr
      exists (v, v)

    have h_eq : Multiset.card (Multiset.filter (λ e => e.1 = e.2) edges) = 0 := by
      -- Use the fact that isLoopless edges = true means the cardinality is 0
      unfold isLoopless at h
      -- Since h : decide (...) = true, we extract the underlying proposition
      apply of_decide_eq_true h

    linarith

-- Define a set of edges to be undirected only if it doesn't have both (v, w) and (w, v)
def isUndirected (edges : Multiset (V × V)) : Bool :=
  Multiset.card (edges.filter (λ e => (e.2, e.1) ∈ edges)) = 0

def isUndirected_prop (edges : Multiset (V × V)) : Prop :=
  ∀ v1 v2, (v1, v2) ∈ edges → (v2, v1) ∉ edges

-- Multigraph with undirected and loopless edges
structure CFGraph (V : Type) [DecidableEq V] [Fintype V] :=
  (edges : Multiset (V × V))
  (loopless : isLoopless edges = true)
  (undirected: isUndirected edges = true)

-- Divisor as a function from vertices to integers
def CFDiv (V : Type) := V → ℤ

-- Divisor addition (pointwise)
instance : Add (CFDiv V) := ⟨λ D₁ D₂ => λ v => D₁ v + D₂ v⟩

-- Divisor subtraction (pointwise)
instance : Sub (CFDiv V) := ⟨λ D₁ D₂ => λ v => D₁ v - D₂ v⟩

-- Zero divisor
instance : Zero (CFDiv V) := ⟨λ _ => 0⟩

-- Neg for divisors
instance : Neg (CFDiv V) := ⟨λ D => λ v => -D v⟩

-- Add coercion from V → ℤ to CFDiv V
instance : Coe (V → ℤ) (CFDiv V) where
  coe f := f

-- Properties of divisor arithmetic
@[simp] lemma add_apply (D₁ D₂ : CFDiv V) (v : V) :
  (D₁ + D₂) v = D₁ v + D₂ v := rfl

@[simp] lemma sub_apply (D₁ D₂ : CFDiv V) (v : V) :
  (D₁ - D₂) v = D₁ v - D₂ v := rfl

@[simp] lemma zero_apply (v : V) :
  (0 : CFDiv V) v = 0 := rfl

@[simp] lemma neg_apply (D : CFDiv V) (v : V) :
  (-D) v = -(D v) := rfl

@[simp] lemma distrib_sub_add (D₁ D₂ D₃ : CFDiv V) :
  D₁ - (D₂ + D₃) = (D₁ - D₂) - D₃ := by
  funext x
  simp [sub_apply, add_apply]
  ring

@[simp] lemma add_sub_distrib (D₁ D₂ D₃ : CFDiv V) :
  (D₁ + D₂) - D₃ = (D₁ - D₃) + D₂ := by
  funext x
  simp [sub_apply, add_apply]
  ring

/-- Lemma: Lambda form of divisor subtraction equals standard form -/
lemma divisor_sub_eq_lambda (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  (λ v => D₁ v - D₂ v) = D₁ - D₂ := by
  funext v
  simp [sub_apply]

-- Number of edges between two vertices as an integer
def num_edges (G : CFGraph V) (v w : V) : ℕ :=
  ↑(Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v))))

-- Lemma: Number of edges is non-negative
lemma num_edges_nonneg (G : CFGraph V) (v w : V) :
  num_edges G v w ≥ 0 := by
  unfold num_edges
  apply Nat.cast_nonneg

-- Degree (Valence) of a vertex as an integer
def vertex_degree (G : CFGraph V) (v : V) : ℤ :=
  ↑(Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v)))

-- Lemma: Vertex degree is non-negative
lemma vertex_degree_nonneg (G : CFGraph V) (v : V) :
  vertex_degree G v ≥ 0 := by
  unfold vertex_degree
  apply Nat.cast_nonneg

-- Firing move at a vertex
def firing_move (G : CFGraph V) (D : CFDiv V) (v : V) : CFDiv V :=
  λ w => if w = v then D v - vertex_degree G v else D w + num_edges G v w

-- Borrowing move at a vertex
def borrowing_move (G : CFGraph V) (D : CFDiv V) (v : V) : CFDiv V :=
  λ w => if w = v then D v + vertex_degree G v else D w - num_edges G v w

-- Define finset_sum using Finset.fold
def finset_sum {α β} [AddCommMonoid β] (s : Finset α) (f : α → β) : β :=
  s.fold (· + ·) 0 f

-- Define set_firing to use finset_sum with consistent types
def set_firing (G : CFGraph V) (D : CFDiv V) (S : Finset V) : CFDiv V :=
  λ w => D w + finset_sum S (λ v => if w = v then -vertex_degree G v else num_edges G v w)

/--
  This axiom states that if every vertex in the graph fires simultaneously,
  the net effect on any vertex `w` is zero. This makes sense because:

  1. When a vertex fires, it sends one chip along each incident edge
  2. When `w` itself fires, it loses `vertex_degree G w` chips
  3. When any other vertex `v` fires, `w` gains `num_edges G v w` chips
  4. In an undirected graph, the total chips flowing into any vertex equals
     the total flowing out

  This is essentially a conservation law - when all vertices fire simultaneously,
  the chips redistribute with no net change to any vertex's total.
  (Note: This is not true for directed graphs, but `CFGraph` is an undirected graph.)

  This was especially hard to prove in Lean4, so we are leaving it as an axiom for the time being.
-/
axiom set_firing_sum_zero (G : CFGraph V) (w : V) :
  finset_sum (Finset.univ : Finset V)
    (fun v => if w = v then -vertex_degree G v else num_edges G v w) = 0

-- (Optional) Proposition: Firing all vertices is equivalent to no change in the divisor.
theorem set_firing_all_vertices_is_zero (G : CFGraph V) (D : CFDiv V) :
    set_firing G D (Finset.univ : Finset V) = D := by
  -- Show equality of functions
  funext w

  -- Expand definition of set_firing
  simp [set_firing]

  -- Use the axiom and simplify
  rw [set_firing_sum_zero G w]

/--
  This axiom states a fundamental property of vertex degree: the degree of a
  vertex equals the sum of the number of edges connecting it to all other vertices.
  This is obvious because:

  1. The vertex degree is defined as the total number of edges incident to `v`
  2. In this summation, we're adding up `num_edges G u v` for all vertices `u`
     except `v` itself
  3. Since the graph is undirected and loopless, this precisely counts each edge
     incident to `v` exactly once

  This is essentially the definition of vertex degree written as a summation.
  This was especially hard to prove in Lean4, so we are leaving it as an axiom for the time being.
-/
axiom sum_edges_eq_vertex_degree : ∀ (G : CFGraph V) (v : V),
  (finset_sum (Finset.univ.erase v) (λ u => (num_edges G u v : ℤ))) = vertex_degree G v

/--
  This axiom describes what happens to vertex `w` when every vertex except `v` fires.
  It states that:

  1. When `w` itself fires, it loses its degree worth of chips: `-vertex_degree G w`
  2. When any other vertex `u` (not `v` or `w`) fires, vertex `w` gains
     `num_edges G u w` chips
  3. The net effect equals the negative of the number of edges between `v` and `w`

  This makes sense because:
  - If all vertices were to fire (including `v`), the net effect on `w` would be
    zero (from the first axiom)
  - So the effect of everyone except `v` firing must be the negative of `v`'s
    contribution
  - `v`'s contribution to `w` when firing is exactly `num_edges G v w`

  This was especially hard to prove in Lean4, so we are leaving it as an axiom for the time being.
-/
axiom sum_edges_to_w_minus_v : ∀ (G : CFGraph V) (v w : V), w ≠ v →
  finset_sum (Finset.univ.erase v) (λ u => if w = u then -vertex_degree G u else (num_edges G u w : ℤ)) = -(num_edges G v w : ℤ)

-- (Optional) Proposition: Borrowing from vertex v ∈ V is equivalent to lending from all vertices in V \ {v}.
lemma borrowing_eq_set_firing_complement (G : CFGraph V) (D : CFDiv V) (v : V) :
  borrowing_move G D v = set_firing G D (Finset.univ.erase v) := by
  -- Show equality of functions
  funext w

  -- Expand definitions
  unfold borrowing_move set_firing

  -- Split into cases based on whether w = v
  by_cases h : w = v

  -- Case: w = v
  · rw [h]
    simp

    -- Since v ∉ Finset.univ.erase v, we can simplify the condition in the sum
    have h1 : ∀ u ∈ Finset.univ.erase v, v ≠ u := by
      intro u hu
      have h_ue : u ≠ v ∧ u ∈ Finset.univ := Finset.mem_erase.mp hu
      exact Ne.symm h_ue.1

    -- This lets us simplify the sum to just use num_edges
    have h2 : finset_sum (Finset.univ.erase v) (λ u => if v = u then -vertex_degree G u else (num_edges G u v : ℤ)) =
              finset_sum (Finset.univ.erase v) (λ u => (num_edges G u v : ℤ)) := by
      -- We use Finset.sum_congr to show the sums are equal
      apply Finset.sum_congr
      -- The finsets are identical
      · exact rfl
      -- Now we show the functions are equal on all elements of the finset
      · intro u hu
        -- Since u ∈ Finset.univ.erase v, we know u ≠ v
        have h_ue : u ≠ v ∧ u ∈ Finset.univ := Finset.mem_erase.mp hu
        -- So v = u is false, and the if-statement simplifies
        have h_not_eq : ¬(v = u) := by exact Ne.symm h_ue.1
        -- Simplify the if-statement using this fact
        simp [h_not_eq]

    -- The axiom tells us this equals vertex_degree G v
    have h3 : finset_sum (Finset.univ.erase v) (λ u => (num_edges G u v : ℤ)) = vertex_degree G v :=
      sum_edges_eq_vertex_degree G v

    -- Chain these equalities
    rw [h2, h3]

  -- Case: w ≠ v
  · simp [h]

    -- Use the axiom to simplify the sum
    rw [sum_edges_to_w_minus_v G v w h]

    -- Show algebraic equality
    simp [sub_eq_add_neg]

-- Define the group structure on CFDiv V
instance : AddGroup (CFDiv V) := Pi.addGroup

-- Define the principal divisors generated by firing moves at vertices
def principal_divisors (G : CFGraph V) : AddSubgroup (CFDiv V) :=
  AddSubgroup.closure (Set.range (λ v => λ w => if w = v then -vertex_degree G v else num_edges G v w))

-- Lemma: Principal divisors contain the borrowing move at a vertex
lemma mem_principal_divisors_basic (G : CFGraph V) (v : V) :
  (λ w => if w = v then -vertex_degree G v else num_edges G v w) ∈ principal_divisors G := by
  apply AddSubgroup.subset_closure
  apply Set.mem_range_self

-- Define linear equivalence of divisors
def linear_equiv (G : CFGraph V) (D D' : CFDiv V) : Prop :=
  D' - D ∈ principal_divisors G

-- [Proven] Proposition: Linear equivalence is an equivalence relation on Div(G)
theorem linear_equiv_is_equivalence (G : CFGraph V) : Equivalence (linear_equiv G) := by
  apply Equivalence.mk
  -- Reflexivity
  · intro D
    unfold linear_equiv
    have h_zero : D - D = 0 := by simp
    rw [h_zero]
    exact AddSubgroup.zero_mem _

  -- Symmetry
  · intros D D' h
    unfold linear_equiv at *
    have h_symm : D - D' = -(D' - D) := by simp [sub_eq_add_neg, neg_sub]
    rw [h_symm]
    exact AddSubgroup.neg_mem _ h

  -- Transitivity
  · intros D D' D'' h1 h2
    unfold linear_equiv at *
    have h_trans : D'' - D = (D'' - D') + (D' - D) := by simp
    rw [h_trans]
    exact AddSubgroup.add_mem _ h2 h1

-- Define divisor class determined by a divisor
def divisor_class (G : CFGraph V) (D : CFDiv V) : Set (CFDiv V) :=
  {D' : CFDiv V | linear_equiv G D D'}

-- Define effective divisors (in terms of non-negativity, returning a Bool)
def effective_bool (D : CFDiv V) : Bool :=
  ↑((Finset.univ.filter (fun v => D v < 0)).card = 0)

-- Define effective divisors (in terms of equivalent Prop)
def effective (D : CFDiv V) : Prop :=
  ∀ v : V, D v ≥ 0

-- Define the set of effective divisors
-- Note: We use the Prop returned by `effective` in set comprehension
def Div_plus (G : CFGraph V) : Set (CFDiv V) :=
  {D : CFDiv V | effective D}

-- Define winnable divisor
-- Note: We use the Prop returned by `linear_equiv` in set comprehension
def winnable (G : CFGraph V) (D : CFDiv V) : Prop :=
  ∃ D' ∈ Div_plus G, linear_equiv G D D'

-- Define the complete linear system of divisors
def complete_linear_system (G: CFGraph V) (D: CFDiv V) : Set (CFDiv V) :=
  {D' : CFDiv V | linear_equiv G D D' ∧ effective D'}

-- Degree of a divisor
def deg (D : CFDiv V) : ℤ := ∑ v, D v
def deg_prop (D : CFDiv V) : Prop := deg D = ∑ v, D v

/-- Axiomatic Definition: Linear equivalence preserves degree of divisors -/
axiom linear_equiv_preserves_deg {V : Type} [DecidableEq V] [Fintype V]
  (G : CFGraph V) (D D' : CFDiv V) (h : linear_equiv G D D') : deg D = deg D'

-- Define a firing script as a function from vertices to integers
def firing_script (V : Type) := V → ℤ

-- Define Laplacian matrix as an |V| x |V| integer matrix
open Matrix
variable [Fintype V]

def laplacian_matrix (G : CFGraph V) : Matrix V V ℤ :=
  λ i j => if i = j then vertex_degree G i else - (num_edges G i j)

-- Note: The Laplacian matrix L is given by Deg(G) - A, where Deg(G) is the diagonal matrix of degrees and A is the adjacency matrix.
-- This matrix can be used to represent the effect of a firing script on a divisor.

-- Apply the Laplacian matrix to a firing script, and current divisor to get a new divisor
def apply_laplacian (G : CFGraph V) (σ : firing_script V) (D: CFDiv V) : CFDiv V :=
  fun v => (D v) - (laplacian_matrix G).mulVec σ v

-- Define q-reduced divisors
def q_reduced (G : CFGraph V) (q : V) (D : CFDiv V) : Prop :=
  (∀ v ∈ {v | v ≠ q}, D v ≥ 0) ∧
  (∀ S : Finset V, S ⊆ (Finset.univ.filter (λ v => v ≠ q)) → S.Nonempty →
    ∃ v ∈ S, D v < finset_sum (Finset.univ.filter (λ w => ¬(w ∈ S))) (λ w => num_edges G v w))

-- Define the ordering of divisors
def divisor_order (G : CFGraph V) (q : V) (D D' : CFDiv V) : Prop :=
  (∃ T : Finset V, T ⊆ (Finset.univ.filter (λ v => v ≠ q)) ∧ D' = set_firing G D T) ∧
  (∀ T' : Finset V, T' ⊆ (Finset.univ.filter (λ v => v ≠ q)) → D' ≠ set_firing G D T')

-- Define the ordering of divisors using the divisor_order relation
def divisor_ordering (G : CFGraph V) (q : V) (D D' : CFDiv V) : Prop :=
  divisor_order G q D' D

-- Legal set-firing: Ensure no vertex in S is in debt after firing
def legal_set_firing (G : CFGraph V) (D : CFDiv V) (S : Finset V) : Prop :=
  ∀ v ∈ S, set_firing G D S v ≥ 0

/-- Axiom: Q-reduced form uniquely determines divisor class in the following sense:
    If two divisors D₁ and D₂ are both q-reduced and linearly equivalent,
    then they must be equal. This is a key uniqueness property that shows
    every divisor class contains exactly one q-reduced representative. -/
axiom q_reduced_unique_class (G : CFGraph V) (q : V) (D₁ D₂ : CFDiv V) :
  q_reduced G q D₁ ∧ q_reduced G q D₂ ∧ linear_equiv G D₁ D₂ → D₁ = D₂
