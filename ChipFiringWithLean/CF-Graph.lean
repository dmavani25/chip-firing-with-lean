import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Fintype.Basic

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

-- Multigraph with undirected and loopless edges
structure CFGraph (V : Type) [DecidableEq V] [Fintype V] :=
  (edges : Multiset (V × V))
  (loopless : ∀ e ∈ edges, e.fst ≠ e.snd)
  (undirected : ∀ e ∈ edges, (e.snd, e.fst) ∈ edges)

-- Divisor as a function from vertices to integers
def CFDiv (V : Type) := V → ℤ

-- Number of edges between two vertices
def num_edges (G : CFGraph V) (v w : V) : ℕ :=
  Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v)))

-- Degree of a vertex
def degG (G : CFGraph V) (v : V) : ℤ :=
  Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))

-- Firing move at a vertex
def firing_move (G : CFGraph V) (D : CFDiv V) (v : V) : CFDiv V :=
  λ w => if w = v then D v - degG G v else D w + num_edges G v w

-- Borrowing move at a vertex
def borrowing_move (G : CFGraph V) (D : CFDiv V) (v : V) : CFDiv V :=
  λ w => if w = v then D v + degG G v else D w - num_edges G v w

-- Define finset_sum using Finset.fold
def finset_sum {α β} [AddCommMonoid β] (s : Finset α) (f : α → β) : β :=
  s.fold (· + ·) 0 f

-- Update set_firing to use finset_sum
def set_firing (G : CFGraph V) (D : CFDiv V) (S : Finset V) : CFDiv V :=
  λ w => D w + finset_sum S (λ v => if w = v then - (degG G v) else num_edges G v w)

-- Lemma: Number of edges from a vertex to itself is zero (since the graph is loopless)
lemma num_edges_self_zero (G : CFGraph V) (v : V) : num_edges G v v = 0 := by
  unfold num_edges
  -- Simplify the filter predicate
  have h_filter : G.edges.filter (λ e => e = (v, v) ∨ e = (v, v)) = G.edges.filter (λ e => e = (v, v)) := by
    ext e
    simp only [or_self]
  rw [h_filter]
  -- We need to show that the cardinality of this filtered multiset is zero
  rw [Multiset.card_eq_zero]
  -- So we need to show that the filtered multiset is empty
  apply Multiset.filter_eq_nil.mpr
  -- For all e ∈ G.edges, e ≠ (v, v)
  intro e h_e_in_edges
  -- We need to show that e ≠ (v, v)
  -- Suppose for contradiction that e = (v, v)
  by_contra h
  -- Then e = (v, v)
  have h_e_eq : e = (v, v) := h
  -- But G.loopless says e.fst ≠ e.snd
  have h_loopless := G.loopless e h_e_in_edges
  -- Substitute e = (v, v) into h_loopless
  rw [h_e_eq] at h_loopless
  -- Then h_loopless becomes v ≠ v, which is false
  exact h_loopless rfl
  -- So we have a contradiction, and e ≠ (v, v)
  -- This completes the proof

-- Lemma: The sum over all vertices of num_edges G v w equals degG G w

-- Lemma: The sum over v ≠ w of num_edges G v w equals degG G w

-- Lemma: Performing set-firing from all vertices leaves the divisor unchanged
