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
def fn_Div (V : Type) := V → ℤ

-- Number of edges between two vertices
def num_edges (G : CFGraph V) (v w : V) : ℕ :=
  Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v)))

-- Degree of a vertex
def degG (G : CFGraph V) (v : V) : ℤ :=
  Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))

-- Firing move at a vertex
def firing_move (G : CFGraph V) (D : fn_Div V) (v : V) : fn_Div V :=
  λ w => if w = v then D v - degG G v else D w + num_edges G v w

-- Borrowing move at a vertex
def borrowing_move (G : CFGraph V) (D : fn_Div V) (v : V) : fn_Div V :=
  λ w => if w = v then D v + degG G v else D w - num_edges G v w

-- Define finset_sum using Finset.fold
def finset_sum {α β} [AddCommMonoid β] (s : Finset α) (f : α → β) : β :=
  s.fold (· + ·) 0 f

-- Update set_firing to use finset_sum
def set_firing (G : CFGraph V) (D : fn_Div V) (S : Finset V) : fn_Div V :=
  λ w => D w + finset_sum S (λ v => if w = v then - (degG G v) else num_edges G v w)
