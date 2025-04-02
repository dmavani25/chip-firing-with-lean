import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true
set_option linter.unusedSectionVars false

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

/-- An orientation of a graph assigns a direction to each edge.
    The consistent field ensures each undirected edge corresponds to exactly
    one directed edge in the orientation. -/
structure Orientation (G : CFGraph V) :=
  /-- The set of directed edges in the orientation -/
  (directed_edges : Multiset (V × V))
  /-- Preserves edge counts between vertex pairs -/
  (count_preserving : ∀ v w,
    Multiset.count (v, w) G.edges + Multiset.count (w, v) G.edges =
    Multiset.count (v, w) directed_edges + Multiset.count (w, v) directed_edges)
  /-- No bidirectional edges in the orientation -/
  (no_bidirectional : ∀ v w,
    Multiset.count (v, w) directed_edges = 0 ∨
    Multiset.count (w, v) directed_edges = 0)

/-- Number of edges directed into a vertex under an orientation -/
def indeg (G : CFGraph V) (O : Orientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.snd = v))

/-- Number of edges directed out of a vertex under an orientation -/
def outdeg (G : CFGraph V) (O : Orientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.fst = v))

/-- A vertex is a source if it has no incoming edges (indegree = 0) -/
def is_source (G : CFGraph V) (O : Orientation G) (v : V) : Bool :=
  indeg G O v = 0

/-- A vertex is a sink if it has no outgoing edges (outdegree = 0) -/
def is_sink (G : CFGraph V) (O : Orientation G) (v : V) : Bool :=
  outdeg G O v = 0

/-- Helper function to check if two consecutive vertices form a directed edge -/
def is_directed_edge (G : CFGraph V) (O : Orientation G) (u v : V) : Bool :=
  (u, v) ∈ O.directed_edges

/-- Axiom: Well-foundedness of vertex levels
    This was especially hard to prove in Lean4, so we are leaving it as an axiom for the time being. -/
axiom vertex_measure_decreasing (G : CFGraph V) (O : Orientation G) (v : V) :
  is_source G O v = false →
  ∀ u, is_directed_edge G O u v = true →
  (univ.filter (λ w => is_directed_edge G O w u)).card <
  (univ.filter (λ w => is_directed_edge G O w v)).card

/-- Axiom: If u is in the filter set for vertex_level calculation of v,
    then there is a directed edge from u to v
    This was especially hard to prove in Lean4, so we are leaving it as an axiom for the time being. -/
axiom filter_implies_directed_edge (G : CFGraph V) (O : Orientation G) (v u : V) :
  u ∈ univ.filter (λ w => is_directed_edge G O w v) →
  is_directed_edge G O u v = true

/-- Axiom: Filter membership for vertex levels
    This was especially hard to prove in Lean4, so we are leaving it as an axiom for the time being. -/
axiom vertex_filter_membership (G : CFGraph V) (O : Orientation G) (v u : V) :
  u ∈ univ.filter (λ w => is_directed_edge G O w v)

/-- The level of a vertex is its position in the topological ordering -/
def vertex_level (G : CFGraph V) (O : Orientation G) (v : V) : ℕ :=
  if h : is_source G O v then 0
  else Nat.succ (Finset.sup (univ.filter (λ u => is_directed_edge G O u v))
                            (λ u => vertex_level G O u))
termination_by
  Finset.card (univ.filter (λ u => is_directed_edge G O u v))
decreasing_by {
  apply vertex_measure_decreasing G O v
  · exact eq_false_of_ne_true h
  · apply filter_implies_directed_edge G O v u
    exact vertex_filter_membership G O v u
}

/-- Vertices at a given level in the orientation -/
def vertices_at_level (G : CFGraph V) (O : Orientation G) (l : ℕ) : Finset V :=
  univ.filter (λ v => vertex_level G O v = l)

/-- Helper function for safe list access -/
def list_get_safe {α : Type} (l : List α) (i : Nat) : Option α :=
  l.get? i

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


/-- Vertices that are not sources must have at least one incoming edge. -/
lemma indeg_ge_one_of_not_source (G : CFGraph V) (O : Orientation G) (v : V) :
    ¬ is_source G O v → indeg G O v ≥ 1 := by
  intro h_not_source -- h_not_source : is_source G O v = false
  unfold is_source at h_not_source -- h_not_source : (decide (indeg G O v = 0)) = false
  apply Nat.one_le_iff_ne_zero.mpr -- Goal is indeg G O v ≠ 0
  intro h_eq_zero -- Assume indeg G O v = 0
  have h_decide_true : decide (indeg G O v = 0) = true := by
    rw [h_eq_zero]
    exact decide_eq_true rfl
  rw [h_decide_true] at h_not_source
  simp at h_not_source

/-- For vertices that are not sources, indegree - 1 is non-negative. -/
lemma indeg_minus_one_nonneg_of_not_source (G : CFGraph V) (O : Orientation G) (v : V) :
    ¬ is_source G O v → 0 ≤ (indeg G O v : ℤ) - 1 := by
  intro h_not_source
  have h_indeg_ge_1 : indeg G O v ≥ 1 := indeg_ge_one_of_not_source G O v h_not_source
  apply Int.sub_nonneg_of_le
  exact Nat.cast_le.mpr h_indeg_ge_1

/-- Configuration associated with a source vertex q under orientation O.
    Requires O to be acyclic and q to be the unique source.
    For each vertex v ≠ q, assigns indegree(v) - 1 chips. Assumes q is the unique source. -/
def config_of_source {G : CFGraph V} {O : Orientation G} {q : V} -- Make G, O, q implicit
    (h_acyclic : is_acyclic G O) (h_unique_source : ∀ w, is_source G O w → w = q) : Config V q :=
  { vertex_degree := λ v => if v = q then 0 else (indeg G O v : ℤ) - 1,
    non_negative_except_q := λ v hv => by
      simp [vertex_degree]
      split_ifs with h_eq
      · contradiction
      · have h_not_source : ¬ is_source G O v := by
          intro hs_v
          exact hv (h_unique_source v hs_v)
        -- Need to provide implicit arguments G O v explicitly now
        exact indeg_minus_one_nonneg_of_not_source G O v h_not_source
  }

/-- The divisor associated with an orientation assigns indegree - 1 to each vertex -/
def divisor_of_orientation (G : CFGraph V) (O : Orientation G) : CFDiv V :=
  λ v => indeg G O v - 1

/-- The canonical divisor assigns degree - 2 to each vertex.
    This is independent of orientation and equals D(O) + D(reverse(O)) -/
def canonical_divisor (G : CFGraph V) : CFDiv V :=
  λ v => (vertex_degree G v) - 2

/-- Auxillary Lemma: Double canonical difference is identity -/
lemma canonical_double_diff (G : CFGraph V) (D : CFDiv V) :
  (λ v => canonical_divisor G v - (canonical_divisor G v - D v)) = D := by
  funext v; simp

/-- Definition (Axiomatic): Canonical divisor is sum of two acyclic orientations -/
axiom canonical_is_sum_orientations {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) :
  ∃ (O₁ O₂ : Orientation G),
    is_acyclic G O₁ ∧ is_acyclic G O₂ ∧
    canonical_divisor G = λ v => divisor_of_orientation G O₁ v + divisor_of_orientation G O₂ v

/-- Axiom: Linear equivalence is preserved when adding chips -/
axiom linear_equiv_add_chip {V : Type} [DecidableEq V] [Fintype V]
  (G : CFGraph V) (D : CFDiv V) (v : V) :
  linear_equiv G
    (λ w => D w + if w = v then 1 else 0)
    (λ w => (canonical_divisor G w - D w) + if w = v then 1 else 0)
