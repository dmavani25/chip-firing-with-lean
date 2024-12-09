import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

-- Define a set of edges to be loopless only if it doesn't have loops
def isLoopless (edges : Multiset (V × V)) : Bool :=
  Multiset.card (edges.filter (λ e => (e.1 = e.2))) = 0

-- Define a set of edges to be undirected only if it doesn't have both (v, w) and (w, v)
def isUndirected (edges : Multiset (V × V)) : Bool :=
  Multiset.card (edges.filter (λ e => (e.2, e.1) ∈ edges)) = 0

-- Multigraph with undirected and loopless edges
structure CFGraph (V : Type) [DecidableEq V] [Fintype V] :=
  (edges : Multiset (V × V))
  (loopless : isLoopless edges = true)
  (undirected: isUndirected edges = true)

-- Divisor as a function from vertices to integers
def CFDiv (V : Type) := V → ℤ

-- Number of edges between two vertices as an integer
def num_edges (G : CFGraph V) (v w : V) : ℤ :=
  ↑(Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v))))

-- Degree (Valence) of a vertex as an integer
def vertex_degree (G : CFGraph V) (v : V) : ℤ :=
  ↑(Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v)))

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

-- Helpers: Add new axioms for the sum being zero
axiom vertex_degree_eq_sum_edges (G : CFGraph V) (w : V) :
    vertex_degree G w = finset_sum (Finset.univ : Finset V) (fun v => num_edges G v w) --:= by
  --sorry  -- Proof would go here
axiom num_edges_comm (G : CFGraph V) (v w : V) :
    num_edges G v w = num_edges G w v --:= by
  --sorry  -- Proof would go here
axiom set_firing_sum_zero (G : CFGraph V) (w : V) :
  finset_sum (Finset.univ : Finset V)
    (fun v => if w = v then -vertex_degree G v else num_edges G v w) = 0

-- (Optional) Proposition using the axiom
theorem set_firing_all_vertices_is_zero (G : CFGraph V) (D : CFDiv V) :
    set_firing G D (Finset.univ : Finset V) = D := by
  -- Show equality of functions
  funext w

  -- Expand definition of set_firing
  simp [set_firing]

  -- Use the axiom and simplify
  rw [set_firing_sum_zero G w]

-- (Optional) Proposition: Borrowing from vertex v ∈ V is equivalent to lending from all vertices in V \ {v}.
axiom borrowing_eq_set_firing_complement (G : CFGraph V) (D : CFDiv V) (v : V) :
  borrowing_move G D v = set_firing G D (Finset.univ.erase v)

instance : AddGroup (CFDiv V) := Pi.addGroup

-- Define the principal divisors generated by firing moves at vertices
def principal_divisors (G : CFGraph V) : AddSubgroup (CFDiv V) :=
  AddSubgroup.closure (Set.range (λ v => λ w => if w = v then -vertex_degree G v else num_edges G v w))

-- Define linear equivalence of divisors
def linear_equiv (G : CFGraph V) (D D' : CFDiv V) : Prop :=
  D' - D ∈ principal_divisors G

-- [Proven] Proposition: Linear equivalence is an equivalence relation on Div(G)
theorem linear_equiv_is_equivalence (G : CFGraph V) : Equivalence (linear_equiv G) := by
  apply Equivalence.mk
  -- Reflexivity
  {
    intro D
    unfold linear_equiv
    have h_zero : D - D = 0 := by simp
    rw [h_zero]
    exact AddSubgroup.zero_mem _
  }
  -- Symmetry
  {
    intros D D' h
    unfold linear_equiv at *
    have h_symm : D - D' = -(D' - D) := by simp [sub_eq_add_neg, neg_sub]
    rw [h_symm]
    exact AddSubgroup.neg_mem _ h
  }
  -- Transitivity
  {
    intros D D' D'' h1 h2
    unfold linear_equiv at *
    have h_trans : D'' - D = (D'' - D') + (D' - D) := by
      { -- Use the simp tactic to simplify the expression
        simp
      }
    rw [h_trans]
    exact AddSubgroup.add_mem _ h2 h1
  }

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
  (∀ S ⊆ {v | v ≠ q}, S ≠ ∅ → ∃ v ∈ S, D v < vertex_degree G v - finset_sum (Finset.univ.filter (λ v' => v' ≠ v)) (λ w => num_edges G w v))

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

/-- A configuration is superstable if it has no legal nonempty set-firings.
    Equivalently, for all nonempty S ⊆ V\{q}, there exists v ∈ S such that
    c(v) < outdeg_S(v), meaning firing S would make v negative. -/
def superstable (G : CFGraph V) (q : V) (c : Config V q) : Prop :=
  ∀ S ⊆ (univ.filter (λ v => v ≠ q)), S ≠ ∅ → ∃ v ∈ S, set_firing G c.vertex_degree S v < c.vertex_degree v

/-- An orientation of a graph assigns a direction to each edge.
    The consistent field ensures each undirected edge corresponds to exactly
    one directed edge in the orientation. -/
structure Orientation (G : CFGraph V) :=
  /-- The set of directed edges in the orientation -/
  (directed_edges : Multiset (V × V))
  /-- Proof that each undirected edge corresponds to exactly one directed edge -/
  (consistent : ∀ e ∈ G.edges, e ∈ directed_edges ∨ (e.snd, e.fst) ∈ directed_edges)

/-- Reverse orientation swaps the direction of all edges by mapping each edge (u,v) to (v,u) -/
def reverse_orientation (G : CFGraph V) (O : Orientation G) : Orientation G :=
  ⟨O.directed_edges.map (λ e => (e.snd, e.fst)), λ e h => by
    cases O.consistent e h with
    | inl _ => exact Or.inr (Multiset.mem_map_of_mem _ ‹_›)
    | inr _ => exact Or.inl (Multiset.mem_map_of_mem _ ‹_›)⟩

/-- Number of edges directed into a vertex under an orientation -/
def indeg (G : CFGraph V) (O : Orientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.snd = v))

/-- Number of edges directed out of a vertex under an orientation -/
def outdeg (G : CFGraph V) (O : Orientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.fst = v))

/-- A vertex is a source if it has no incoming edges (indegree = 0) -/
def is_source (G : CFGraph V) (O : Orientation G) (v : V) : Prop :=
  indeg G O v = 0

/-- A vertex is a sink if it has no outgoing edges (outdegree = 0) -/
def is_sink (G : CFGraph V) (O : Orientation G) (v : V) : Prop :=
  outdeg G O v = 0

/-- Axiom: For any vertex v ≠ q in an orientation O where q is a source,
    the indegree of v is at least 1 -/
axiom non_source_positive_indeg (G : CFGraph V) (O : Orientation G) (q v : V) :
  v ≠ q → is_source G O q → indeg G O v ≥ 1

/-- Axiom: Indegree minus one is non-negative for non-source vertices -/
axiom indeg_minus_one_nonneg (G : CFGraph V) (O : Orientation G) (q v : V) :
  v ≠ q → is_source G O q → 0 ≤ (indeg G O v : ℤ) - 1

/-- Configuration associated with a source vertex q under orientation O.
    For each vertex v ≠ q, assigns indegree(v) - 1 chips. -/
def config_of_source (G : CFGraph V) (O : Orientation G) (q : V)
    (h_source : is_source G O q) : Config V q :=
  { vertex_degree := λ v => if v = q then 0 else (indeg G O v : ℤ) - 1,
    non_negative_except_q := λ v hv => by
      simp [vertex_degree]
      split_ifs with h
      · contradiction
      · exact indeg_minus_one_nonneg G O q v hv h_source
  }

/-- Helper function to check if two consecutive vertices form a directed edge -/
def is_directed_edge (G : CFGraph V) (O : Orientation G) (u : V) (v : V) : Prop :=
  (u, v) ∈ O.directed_edges

/-- Axiom: For list indexing with bounds checking -/
axiom list_index_valid {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
  ∃ x : α, l.get ⟨i, h⟩ = x

/-- Helper function for safe list access -/
def list_get_safe {α : Type} (l : List α) (i : Nat) : Option α :=
  l.get? i

/-- Axiom: For path properties -/
axiom path_properties (G : CFGraph V) (O : Orientation G) (vs : List V) :
  ∀ (i : Nat), i + 1 < vs.length →
    match (list_get_safe vs i, list_get_safe vs (i + 1)) with
    | (some u, some v) => is_directed_edge G O u v
    | _ => False

/-- Axiom: For vertex distinctness in paths -/
axiom vertex_distinctness (G : CFGraph V) (O : Orientation G) (vs : List V) :
  ∀ (i j : Nat), i < vs.length → j < vs.length → i ≠ j →
    vs.getD i ≠ vs.getD j

/-- Axiom: For vertex distinctness in paths -/
axiom vertex_distinctness_equivalent_declaration (G : CFGraph V) (O : Orientation G) (vs : List V) :
  ∀ (i j : Nat), i < vs.length → j < vs.length → i ≠ j →
    match (list_get_safe vs i, list_get_safe vs j) with
    | (some u, some v) => u ≠ v
    | _ => True

/-- A directed path in a graph under an orientation -/
structure DirectedPath (G : CFGraph V) (O : Orientation G) where
  /-- The sequence of vertices in the path -/
  vertices : List V
  /-- Every consecutive pair forms a directed edge -/
  valid_edges : ∀ (i : Nat), i + 1 < vertices.length →
    match (vertices.get? i, vertices.get? (i + 1)) with
    | (some u, some v) => is_directed_edge G O u v
    | _ => False
  /-- All vertices in the path are distinct -/
  distinct_vertices : ∀ (i j : Nat), i < vertices.length → j < vertices.length → i ≠ j →
    match (vertices.get? i, vertices.get? j) with
    | (some u, some v) => u ≠ v
    | _ => True

/-- A directed cycle is a directed path whose first and last vertices coincide.
    Apart from the repetition of the first/last vertex, all other vertices in the cycle are distinct. -/
structure DirectedCycle (G : CFGraph V) (O : Orientation G) :=
  (vertices : List V)
  /-- Every consecutive pair of vertices forms a directed edge in the orientation. -/
  (valid_edges : ∀ (i : Nat), i + 1 < vertices.length →
    match (vertices.get? i, vertices.get? (i + 1)) with
    | (some u, some v) => is_directed_edge G O u v
    | _ => False)
  /-- The cycle condition: the first vertex equals the last, ensuring a closed loop. -/
  (cycle_condition : vertices.length > 0 ∧ vertices.get? 0 = vertices.get? (vertices.length - 1))
  /-- All internal vertices (ignoring the last vertex which is the same as the first)
      are distinct from each other. This ensures there are no other repeated vertices
      besides the repetition at the end forming the cycle. -/
  (distinct_internal_vertices : ∀ (i j : Nat),
    i < vertices.length - 1 →
    j < vertices.length - 1 →
    i ≠ j →
    match (vertices.get? i, vertices.get? j) with
    | (some u, some v) => u ≠ v
    | _ => True)

-- Axiom: Existence of directed paths between vertices -/
axiom path_exists (G : CFGraph V) (O : Orientation G) (u v : V) :
  ∃ (p : DirectedPath G O),
    p.vertices.length > 0 ∧
    p.vertices.get? 0 = some u ∧
    p.vertices.get? (p.vertices.length - 1) = some v

/-- A maximal superstable configuration has no legal firings and dominates all other superstable configs -/
def maximal_superstable {q : V} (G : CFGraph V) (c : Config V q) : Prop :=
  superstable G q c ∧ ∀ c' : Config V q, superstable G q c' → config_ge c' c

/-- The divisor associated with an orientation assigns indegree - 1 to each vertex -/
def divisor_of_orientation (G : CFGraph V) (O : Orientation G) : CFDiv V :=
  λ v => indeg G O v - 1

/-- The canonical divisor assigns degree - 2 to each vertex.
    This is independent of orientation and equals D(O) + D(reverse(O)) -/
def canonical_divisor (G : CFGraph V) : CFDiv V :=
  λ v => (vertex_degree G v) - 2

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

/-- The genus of a graph is its cycle rank: |E| - |V| + 1 -/
def genus (G : CFGraph V) : ℤ :=
  Multiset.card G.edges - Fintype.card V + 1

/-- A divisor has rank -1 if it is not winnable -/
def rank_eq_neg_one_wrt_winnability (G : CFGraph V) (D : CFDiv V) : Prop :=
  ¬(winnable G D)

/-- A divisor has rank -1 if its complete linear system is empty -/
def rank_eq_neg_one_wrt_complete_linear_system (G : CFGraph V) (D : CFDiv V) : Prop :=
  complete_linear_system G D = ∅
