import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import Mathlib.Algebra.Ring.Int

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]




/-
# Helpers for Proposition 3.2.4
-/

-- Axiom: Every divisor is linearly equivalent to exactly one q-reduced divisor
axiom helper_unique_q_reduced (G : CFGraph V) (q : V) (D : CFDiv V) :
  ∃! D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D'

-- Axiom: Effectiveness preservation under linear equivalence
axiom helper_effective_linear_equiv (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  linear_equiv G D₁ D₂ → effective D₁ → effective D₂




/-
# Helpers for Lemma 4.1.10
-/

/-- Axiom: A non-empty graph with an acyclic orientation must have at least one source -/
axiom helper_acyclic_has_source (G : CFGraph V) (O : Orientation G) :
  is_acyclic G O → ∃ v : V, is_source G O v

/-- Axiom: Two orientations are equal if they have same directed edges -/
axiom helper_orientation_eq_of_directed_edges {G : CFGraph V}
  (O O' : Orientation G) :
  O.directed_edges = O'.directed_edges → O = O'

/-- Axiom: Given a list of disjoint vertex sets that form a partition of V,
    this axiom states that an acyclic orientation is uniquely determined
    by this partition where each set contains vertices with same indegree -/
axiom helper_orientation_determined_by_levels {G : CFGraph V}
  (O O' : Orientation G) :
  is_acyclic G O → is_acyclic G O' →
  (∀ v : V, indeg G O v = indeg G O' v) →
  O = O'




/-
# Helpers for Proposition 4.1.11
-/

/-- Axiom: Every configuration from an acyclic orientation with source q is superstable -/
axiom helper_orientation_config_superstable (G : CFGraph V) (O : Orientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_src : is_source G O q) :
    superstable G q (orientation_to_config G O q h_acyc h_src)

/-- Axiom: Every configuration from an acyclic orientation with source q is maximal superstable -/
axiom helper_orientation_config_maximal (G : CFGraph V) (O : Orientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_src : is_source G O q) :
    maximal_superstable G (orientation_to_config G O q h_acyc h_src)

/-- Axiom: Converting orientation to config and back gives same orientation -/
axiom helper_config_to_orientation_unique (G : CFGraph V) (q : V)
    (c : Config V q)
    (h_super : superstable G q c)
    (h_max : maximal_superstable G c)
    (O₁ O₂ : Orientation G)
    (h_acyc₁ : is_acyclic G O₁)
    (h_acyc₂ : is_acyclic G O₂)
    (h_src₁ : is_source G O₁ q)
    (h_src₂ : is_source G O₂ q)
    (h_eq₁ : orientation_to_config G O₁ q h_acyc₁ h_src₁ = c)
    (h_eq₂ : orientation_to_config G O₂ q h_acyc₂ h_src₂ = c) :
    O₁ = O₂

/-- Axiom: Orientation to config preserves indegrees -/
axiom helper_orientation_to_config_indeg (G : CFGraph V) (O : Orientation G) (q : V)
    (h_acyclic : is_acyclic G O) (h_source : is_source G O q) (v : V) :
    (orientation_to_config G O q h_acyclic h_source).vertex_degree v =
    if v = q then 0 else (indeg G O v : ℤ) - 1

/-- Helper Lemma to convert between configuration equality forms -/
lemma helper_config_eq_of_subtype_eq {G : CFGraph V} {q : V}
    {O₁ O₂ : {O : Orientation G // is_acyclic G O ∧ is_source G O q}}
    (h : orientation_to_config G O₁.val q O₁.prop.1 O₁.prop.2 =
         orientation_to_config G O₂.val q O₂.prop.1 O₂.prop.2) :
    orientation_to_config G O₂.val q O₂.prop.1 O₂.prop.2 =
    orientation_to_config G O₁.val q O₁.prop.1 O₁.prop.2 := by
  exact h.symm

/-- Axiom: Every superstable configuration extends to a maximal superstable configuration -/
axiom helper_maximal_superstable_exists (G : CFGraph V) (q : V) (c : Config V q)
    (h_super : superstable G q c) :
    ∃ c' : Config V q, maximal_superstable G c' ∧ config_ge c' c

/-- Axiom: Every maximal superstable configuration comes from an acyclic orientation -/
axiom helper_maximal_superstable_orientation (G : CFGraph V) (q : V) (c : Config V q)
    (h_max : maximal_superstable G c) :
    ∃ (O : Orientation G) (h_acyc : is_acyclic G O) (h_src : is_source G O q),
      orientation_to_config G O q h_acyc h_src = c

/-- Axiom: Maximal superstable configurations are uniquely determined by their orientations -/
axiom helper_maximal_superstable_unique (G : CFGraph V) (q : V) (c : Config V q)
  (h_max : maximal_superstable G c)
  (O : Orientation G) (h_acyc : is_acyclic G O) (h_src : is_source G O q) :
  orientation_to_config G O q h_acyc h_src = c →
  ∀ (O' : Orientation G) (h_acyc' : is_acyclic G O' ) (h_src' : is_source G O' q),
  orientation_to_config G O' q h_acyc' h_src' = c → O = O'

/-- Axiom: If c' dominates c and c' is maximal superstable, then c = c' -/
axiom helper_maximal_superstable_unique_dominates (G : CFGraph V) (q : V)
    (c c' : Config V q)
    (h_max' : maximal_superstable G c')
    (h_ge : config_ge c' c) : c' = c

/-- Axiom: Every configuration is superstable -/
axiom helper_config_superstable (G : CFGraph V) (q : V) (c : Config V q) :
    superstable G q c




/-
# Helpers for Corollary 4.2.2
-/

/-- Axiom: A divisor can be decomposed into parts of specific degrees -/
axiom helper_divisor_decomposition (G : CFGraph V) (E'' : CFDiv V) (k₁ k₂ : ℕ)
  (h_effective : effective E'') (h_deg : deg E'' = k₁ + k₂) :
  ∃ (E₁ E₂ : CFDiv V),
    effective E₁ ∧ effective E₂ ∧
    deg E₁ = k₁ ∧ deg E₂ = k₂ ∧
    E'' = λ v => E₁ v + E₂ v

/-- Axiom: Winnability is preserved under addition -/
axiom helper_winnable_add (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  winnable G D₁ → winnable G D₂ → winnable G (λ v => D₁ v + D₂ v)




/-
# Helpers for Corollary 4.2.3
-/

/--
theorem helper_sum_vertex_degrees (G : CFGraph V) :
  ∑ v, vertex_degree G v = 2 * ↑(Multiset.card G.edges) := by
  unfold vertex_degree

  -- For each edge e, count how many times it appears in each vertex's filter (Working)
  have h_count : ∀ e ∈ G.edges,
    (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card = 2 := by
    intro e he
    -- Prove endpoints are distinct using loopless property (Working)
    have h_ne : e.1 ≠ e.2 := by
      by_contra h
      have : isLoopless G.edges = true := G.loopless
      unfold isLoopless at this
      have h_loop : Multiset.card (G.edges.filter (λ e => e.1 = e.2)) = 0 := by
        simp only [decide_eq_true_eq] at this
        exact this
      have h_mem : e ∈ Multiset.filter (λ e' => e'.1 = e'.2) G.edges := by
        simp [he, h]
      have h_card : 0 < Multiset.card (G.edges.filter (λ e' => e'.1 = e'.2)) := by
        exact Multiset.card_pos_iff_exists_mem.mpr ⟨e, h_mem⟩
      exact h_card.ne' h_loop

    -- Show filter contains exactly two vertices (Working)
    rw [Finset.card_eq_two]
    exists e.1
    exists e.2
    constructor
    · exact h_ne
    · ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton]
      constructor
      · intro h
        cases h with
        | inl h => exact Or.inl (Eq.symm h)
        | inr h => exact Or.inr (Eq.symm h)
      · intro h
        cases h with
        | inl h => exact Or.inl (Eq.symm h)
        | inr h => exact Or.inr (Eq.symm h)

  admit
-/
-- Axiom: Sum of vertex degrees equals 2|E| (handshake lemma)
axiom helper_sum_vertex_degrees (G : CFGraph V) :
  ∑ v, vertex_degree G v = 2 * ↑(Multiset.card G.edges)




/-
# Helpers for Proposition 4.1.13 Part (1)
-/

/-- Axiom: Superstable configuration degree is bounded by genus -/
axiom helper_superstable_degree_bound (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → config_degree c ≤ genus G

/-- Axiom: Every maximal superstable configuration has degree at least g -/
axiom helper_maximal_superstable_degree_lower_bound (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → maximal_superstable G c → config_degree c ≥ genus G

/-- Axiom: If a superstable configuration has degree equal to g, it is maximal -/
axiom helper_degree_g_implies_maximal (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → config_degree c = genus G → maximal_superstable G c




/-
# Helpers for Proposition 4.1.13 Part (2)
-/

/-- Axiom: Q-reduced form uniquely determines divisor class -/
axiom helper_q_reduced_unique_class (G : CFGraph V) (q : V) (D₁ D₂ : CFDiv V) :
  q_reduced G q D₁ ∧ q_reduced G q D₂ ∧ linear_equiv G D₁ D₂ → D₁ = D₂

/-- Axiom: A q-reduced divisor corresponds to a superstable configuration minus q -/
axiom helper_q_reduced_superstable_form (G : CFGraph V) (q : V) (D : CFDiv V) :
  q_reduced G q D → ∃ c : Config V q, superstable G q c ∧
  D = λ v => c.vertex_degree v - if v = q then 1 else 0

/-- Axiom: Superstabilization of configuration with degree g+1 sends chip to q -/
axiom helper_superstabilize_sends_to_q (G : CFGraph V) (q : V) (c : Config V q) :
  maximal_superstable G c → config_degree c = genus G →
  ∀ v : V, v ≠ q → winnable G (λ w => c.vertex_degree w + if w = v then 1 else 0 - if w = q then 1 else 0)

/-- Axiom: Configuration minus q is q-reduced if configuration is superstable -/
axiom helper_superstable_minus_q_reduced (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → q_reduced G q (λ v => c.vertex_degree v - if v = q then 1 else 0)

/-- Axiom: Linear equivalence preserved under domination for q-reduced forms -/
axiom helper_q_reduced_linear_equiv_dominates (G : CFGraph V) (q : V) (c c' : Config V q) :
  superstable G q c → superstable G q c' → config_ge c' c →
  linear_equiv G
    (λ v => c.vertex_degree v - if v = q then 1 else 0)
    (λ v => c'.vertex_degree v - if v = q then 1 else 0)

/-- Axiom: If c' is maximal superstable and D corresponds to c'-q,
    then winnability of c'+v-q implies winnability of D -/
axiom helper_maximal_superstable_winnability (G : CFGraph V) (q : V) (c' : Config V q) (D : CFDiv V) :
  maximal_superstable G c' →
  linear_equiv G D (λ v => c'.vertex_degree v - if v = q then 1 else 0) →
  (∀ v : V, v ≠ q → winnable G (λ w => c'.vertex_degree w + if w = v then 1 else 0 - if w = q then 1 else 0)) →
  winnable G D

/-- Axiom: Linear equivalence preserves winnability -/
axiom helper_linear_equiv_preserves_winnability (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  linear_equiv G D₁ D₂ → (winnable G D₁ ↔ winnable G D₂)

/-- Axiom: Superstable configuration has value 0 at q -/
axiom helper_superstable_zero_at_q (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → c.vertex_degree q = 0

/-- Axiom: Winnability through linear equivalence and chip addition -/
axiom helper_winnable_through_equiv_and_chip (G : CFGraph V) (q : V) (D : CFDiv V) (c : Config V q) :
  linear_equiv G D (λ v => c.vertex_degree v - if v = q then 1 else 0) →
  maximal_superstable G c →
  ∀ v : V, v ≠ q →
  winnable G (λ w => D w + if w = v then 1 else 0)

/-- Axiom: Winnability at q vertex -/
axiom helper_winnable_when_adding_at_q (G : CFGraph V) (q : V) (D : CFDiv V) (c : Config V q) :
  maximal_superstable G c →
  linear_equiv G D (λ v => c.vertex_degree v - if v = q then 1 else 0) →
  winnable G (λ w => D w + if w = q then 1 else 0)

/-- Axiom: Winnability at non-q vertex -/
axiom helper_winnable_when_adding_not_q (G : CFGraph V) (q v : V) (D : CFDiv V) (c : Config V q) :
  maximal_superstable G c →
  linear_equiv G D (λ w => c.vertex_degree w - if w = q then 1 else 0) →
  v ≠ q →
  winnable G (λ w => D w + if w = v then 1 else 0)
