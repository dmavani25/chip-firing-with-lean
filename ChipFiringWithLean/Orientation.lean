import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.WellFounded
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Cycle
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
structure CFOrientation (G : CFGraph V) :=
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
def indeg (G : CFGraph V) (O : CFOrientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.snd = v))

/-- Number of edges directed out of a vertex under an orientation -/
def outdeg (G : CFGraph V) (O : CFOrientation G) (v : V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.fst = v))

/-- A vertex is a source if it has no incoming edges (indegree = 0) -/
def is_source (G : CFGraph V) (O : CFOrientation G) (v : V) : Bool :=
  indeg G O v = 0

/-- A vertex is a sink if it has no outgoing edges (outdegree = 0) -/
def is_sink (G : CFGraph V) (O : CFOrientation G) (v : V) : Bool :=
  outdeg G O v = 0

/-- Helper function to check if two consecutive vertices form a directed edge -/
def is_directed_edge (G : CFGraph V) (O : CFOrientation G) (u v : V) : Bool :=
  (u, v) ∈ O.directed_edges

/-- Helper function for safe list access -/
def list_get_safe {α : Type} (l : List α) (i : Nat) : Option α :=
  l.get? i

/-- A directed path in a graph under an orientation -/
structure DirectedPath (G : CFGraph V) (O : CFOrientation G) where
  /-- The sequence of vertices in the path -/
  vertices : List V
  /-- Path must not be empty (at least one vertex) -/
  non_empty : vertices.length > 0
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
structure DirectedCycle (G : CFGraph V) (O : CFOrientation G) :=
  (vertices : List V)
  /-- Every consecutive pair of vertices forms a directed edge in the orientation. -/
  (valid_edges : ∀ (i : Nat), i + 1 < vertices.length →
    match (vertices.get? i, vertices.get? (i + 1)) with
    | (some u, some v) => is_directed_edge G O u v
    | _ => False)
  /-- The cycle condition: first vertex equals last, and at least one edge.
      Length > 1 means at least 2 vertices, e.g., [v, v] for a self-loop (1 edge). -/
  (cycle_condition : vertices.length > 1 ∧
    match (vertices.get? 0, vertices.get? (vertices.length - 1)) with
    | (some start_node, some end_node) => start_node = end_node
    | _ => False) -- Should not be hit if vertices.length > 1
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
def has_bidirectional_edges (G : CFGraph V) (O : CFOrientation G) (u v : V) : Prop :=
  ∃ e₁ e₂, e₁ ∈ O.directed_edges ∧ e₂ ∈ O.directed_edges ∧ e₁ = (u, v) ∧ e₂ = (v, u)

/-- All multiple edges between same vertices point in same direction -/
def consistent_edge_directions (G : CFGraph V) (O : CFOrientation G) : Prop :=
  ∀ u v : V, ¬has_bidirectional_edges G O u v

/-- An orientation is acyclic if it has no directed cycles and
    maintains consistent edge directions between vertices -/
def is_acyclic (G : CFGraph V) (O : CFOrientation G) : Prop :=
  consistent_edge_directions G O ∧
  ¬∃ (c : DirectedCycle G O), True

/-- The set of ancestors of a vertex v (nodes x such that there is a path x -> ... -> v) -/
noncomputable def ancestors (G : CFGraph V) (O : CFOrientation G) (v : V) : Finset V :=
  let R : V → V → Prop := fun a b => is_directed_edge G O a b = true
  open Classical in univ.filter (fun x => Relation.TransGen R x v)

/-- Measure for vertex_level termination: number of ancestors. -/
noncomputable def vertexLevelMeasure (G : CFGraph V) (O : CFOrientation G) (v : V) : Nat :=
  (ancestors G O v).card

/-- Axiom: No acyclic orientation has a transitive self-loop. (This is true, but not proven here.)-/
axiom not_trans_gen_self_of_acyclic (G : CFGraph V) (O : CFOrientation G) (h_acyclic : is_acyclic G O) (v_node : V) :
    ¬Relation.TransGen (fun a b => is_directed_edge G O a b = true) v_node v_node

/-- Key lemma for vertex_level termination -/
lemma ancestors_card_lt_of_pred_of_acyclic
    (G : CFGraph V) (O : CFOrientation G) (h_acyclic : is_acyclic G O)
    {u v_call : V} (u_is_pred_of_v_call : is_directed_edge G O u v_call = true) :
    vertexLevelMeasure G O u < vertexLevelMeasure G O v_call := by
  let R := fun a b => is_directed_edge G O a b = true
  apply Finset.card_lt_card
  -- Goal: ancestors G O u ⊂ ancestors G O v_call
  apply Finset.ssubset_def.mpr
  constructor
  · -- 1. ancestors G O u ⊆ ancestors G O v_call
    intros x hx_mem_anc_u
    simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and] at hx_mem_anc_u ⊢
    exact Relation.TransGen.trans hx_mem_anc_u (Relation.TransGen.single u_is_pred_of_v_call)
  · -- 2. ¬ (ancestors G O v_call ⊆ ancestors G O u)
    --    This is equiv to ∃ k, k ∈ (ancestors G O v_call) ∧ k ∉ (ancestors G O u)
    --    We pick k = u.
    intro h_contra_subset_rev -- Assume for contradiction: ancestors G O v_call ⊆ ancestors G O u
    have u_in_anc_v_call : u ∈ ancestors G O v_call := by {
      simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single u_is_pred_of_v_call
    }
    have u_in_anc_u_from_contra : u ∈ ancestors G O u := h_contra_subset_rev u_in_anc_v_call
    have u_not_in_anc_u_from_acyclic : u ∉ ancestors G O u := by {
      simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_trans_gen_self_of_acyclic G O h_acyclic u
    }
    exact u_not_in_anc_u_from_acyclic u_in_anc_u_from_contra

/-- The level of a vertex is its position in the topological ordering -/
noncomputable def vertex_level (G : CFGraph V) (O : CFOrientation G) (h_acyclic : is_acyclic G O) : V → Nat :=
  let R_measure_lt (y x : V) : Prop := vertexLevelMeasure G O y < vertexLevelMeasure G O x
  have wf_R_measure_lt : WellFounded R_measure_lt := -- Proof that the relation is well-founded
    (InvImage.wf (vertexLevelMeasure G O) Nat.lt_wfRel.wf) -- Corrected to Nat.lt_wfRel.wf
  WellFounded.fix wf_R_measure_lt
    (fun (v : V) (recursive_call_handler : Π (u_rec : V), R_measure_lt u_rec v → Nat) =>
      let predecessors := univ.filter (fun u_filter_pred => is_directed_edge G O u_filter_pred v = true)
      predecessors.attach.sup
        (fun (u_attached : {x // x ∈ predecessors}) =>
          let u_val := u_attached.val
          let proof_u_in_predecessors := u_attached.property
          have edge_proof : is_directed_edge G O u_val v = true :=
            (Finset.mem_filter.mp proof_u_in_predecessors).2
          recursive_call_handler u_val (ancestors_card_lt_of_pred_of_acyclic G O h_acyclic edge_proof) + 1
        )
    )

/-- Vertices at a given level in the orientation -/
noncomputable def vertices_at_level (G : CFGraph V) (O : CFOrientation G) (h_acyclic : is_acyclic G O) (l : ℕ) : Finset V :=
  univ.filter (λ v => vertex_level G O h_acyclic v = l)


/-- Vertices that are not sources must have at least one incoming edge. -/
lemma indeg_ge_one_of_not_source (G : CFGraph V) (O : CFOrientation G) (v : V) :
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
lemma indeg_minus_one_nonneg_of_not_source (G : CFGraph V) (O : CFOrientation G) (v : V) :
    ¬ is_source G O v → 0 ≤ (indeg G O v : ℤ) - 1 := by
  intro h_not_source
  have h_indeg_ge_1 : indeg G O v ≥ 1 := indeg_ge_one_of_not_source G O v h_not_source
  apply Int.sub_nonneg_of_le
  exact Nat.cast_le.mpr h_indeg_ge_1

/-- Configuration associated with a source vertex q under orientation O.
    Requires O to be acyclic and q to be the unique source.
    For each vertex v ≠ q, assigns indegree(v) - 1 chips. Assumes q is the unique source. -/
def config_of_source {G : CFGraph V} {O : CFOrientation G} {q : V} -- Make G, O, q implicit
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
def divisor_of_orientation (G : CFGraph V) (O : CFOrientation G) : CFDiv V :=
  λ v => indeg G O v - 1

/-- The canonical divisor assigns degree - 2 to each vertex.
    This is independent of orientation and equals D(O) + D(reverse(O)) -/
def canonical_divisor (G : CFGraph V) : CFDiv V :=
  λ v => (vertex_degree G v) - 2

/-- Auxillary Lemma: Double canonical difference is identity -/
lemma canonical_double_diff (G : CFGraph V) (D : CFDiv V) :
  (λ v => canonical_divisor G v - (canonical_divisor G v - D v)) = D := by
  funext v; simp

/- Helper: Definition of reversing an orientation -/
def CFOrientation.reverse (G : CFGraph V) (O : CFOrientation G) : CFOrientation G where
  directed_edges := O.directed_edges.map Prod.swap -- Use Prod.swap directly
  count_preserving v w := by
    rw [O.count_preserving v w]

    have h_vw_rev_eq_wv_orig :
        Multiset.count (v,w) (O.directed_edges.map Prod.swap) = Multiset.count (w,v) O.directed_edges := by
      rw [Multiset.count_map (f := Prod.swap)]
      rw [Multiset.count_eq_card_filter_eq] -- Or Multiset.count, Multiset.countP_eq_card_filter
      apply congr_arg Multiset.card
      ext e
      simp only [Multiset.mem_filter, and_congr_left_iff, Prod.ext_iff, Prod.fst_swap, Prod.snd_swap, eq_comm, and_comm]

    have h_wv_rev_eq_vw_orig :
        Multiset.count (w,v) (O.directed_edges.map Prod.swap) = Multiset.count (v,w) O.directed_edges := by
      rw [Multiset.count_map (f := Prod.swap)]
      rw [Multiset.count_eq_card_filter_eq]
      apply congr_arg Multiset.card
      ext e
      simp only [Multiset.mem_filter, and_congr_left_iff, Prod.ext_iff, Prod.fst_swap, Prod.snd_swap, eq_comm, and_comm]

    conv_rhs =>
      congr
      · change Multiset.count (v,w) (O.directed_edges.map Prod.swap)
        rw [h_vw_rev_eq_wv_orig]
      · change Multiset.count (w,v) (O.directed_edges.map Prod.swap)
        rw [h_wv_rev_eq_vw_orig]

    rw [add_comm (Multiset.count (w,v) O.directed_edges)]
  no_bidirectional v w := by -- The `directed_edges` for this proof is O.directed_edges.map Prod.swap
    cases O.no_bidirectional v w with
    | inl h_vw_O_zero => -- Multiset.count (v, w) O.directed_edges = 0
      apply Or.inr
      rw [Multiset.count_eq_zero]
      intro h_wv_mem_rev_contra
      have h_vw_mem_O_derived : (v,w) ∈ O.directed_edges := by
        obtain ⟨p, h_p_mem_O, h_swap_p_eq_wv⟩ := Multiset.mem_map.mp h_wv_mem_rev_contra
        have h_p_is_vw : p = (v,w) := by { apply Prod.ext; exact (Prod.mk.inj h_swap_p_eq_wv).2; exact (Prod.mk.inj h_swap_p_eq_wv).1 }
        rwa [h_p_is_vw] at h_p_mem_O
      exact (Multiset.count_eq_zero.mp h_vw_O_zero) h_vw_mem_O_derived
    | inr h_wv_O_zero => -- Multiset.count (w, v) O.directed_edges = 0
      apply Or.inl
      rw [Multiset.count_eq_zero]
      intro h_vw_mem_rev_contra
      have h_wv_mem_O_derived : (w,v) ∈ O.directed_edges := by
        obtain ⟨p, h_p_mem_O, h_swap_p_eq_vw⟩ := Multiset.mem_map.mp h_vw_mem_rev_contra
        have h_p_is_wv : p = (w,v) := by { apply Prod.ext; exact (Prod.mk.inj h_swap_p_eq_vw).2; exact (Prod.mk.inj h_swap_p_eq_vw).1 }
        rwa [h_p_is_wv] at h_p_mem_O
      exact (Multiset.count_eq_zero.mp h_wv_O_zero) h_wv_mem_O_derived

/- Helper: indegree in reversed orientation equals outdegree in original -/
lemma indeg_reverse_eq_outdeg (G : CFGraph V) (O : CFOrientation G) (v : V) :
  indeg G (O.reverse G) v = outdeg G O v := by
  classical
  simp only [indeg, outdeg]
  rw [← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter]
  -- Explicitly state and use the definition of the reversed edges
  let O_rev_edges_def : (CFOrientation.reverse G O).directed_edges = O.directed_edges.map Prod.swap := by rfl
  conv_lhs => rw [O_rev_edges_def]
  rw [Multiset.countP_map]
  simp only [Function.comp_apply, Prod.snd_swap]
  simp only [Multiset.countP_eq_card_filter]

axiom canonical_is_sum_orientations {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) :
  ∃ (O₁ O₂ : CFOrientation G),
    is_acyclic G O₁ ∧ is_acyclic G O₂ ∧
    canonical_divisor G = λ v => divisor_of_orientation G O₁ v + divisor_of_orientation G O₂ v
