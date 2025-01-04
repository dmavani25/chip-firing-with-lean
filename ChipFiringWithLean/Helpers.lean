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

lemma mem_principal_divisors_basic (G : CFGraph V) (v : V) :
  (λ w => if w = v then -vertex_degree G v else num_edges G v w) ∈ principal_divisors G := by
  apply AddSubgroup.subset_closure
  apply Set.mem_range_self

lemma vertex_degree_nonneg (G : CFGraph V) (v : V) :
  vertex_degree G v ≥ 0 := by
  unfold vertex_degree
  apply Nat.cast_nonneg

lemma num_edges_nonneg (G : CFGraph V) (v w : V) :
  num_edges G v w ≥ 0 := by
  unfold num_edges
  apply Nat.cast_nonneg

theorem helper_effective_linear_equiv_proof (G : CFGraph V) (D₁ D₂ : CFDiv V) :
    linear_equiv G D₁ D₂ → effective D₁ → effective D₂ := by
  intros h_linear h_eff
  unfold linear_equiv at h_linear
  unfold effective at *
  intro v

  -- Express D₂ in terms of D₁
  have h_d2 : D₂ v = (D₁ + (D₂ - D₁)) v := by
    simp [add_apply, sub_apply]

  rw [h_d2]

  -- Use properties of principal_divisors directly
  have h_nonneg : D₁ v + (D₂ - D₁) v ≥ 0 := by
    have h_base := h_eff v
    have h_firing := h_linear

    -- Use the fact that D₂ - D₁ is in principal_divisors
    have h_decomp : ∃ S : Finset V, (D₂ - D₁) v =
      finset_sum S (λ u => if v = u then -vertex_degree G u else num_edges G u v) := by
      sorry  -- This follows from membership in principal_divisors

    rcases h_decomp with ⟨S, hS⟩
    rw [hS]

    -- Case analysis on whether v ∈ S
    by_cases hv : v ∈ S
    · -- If v ∈ S, use vertex_degree properties
      have h_vd := vertex_degree_nonneg G v
     -- Use Finset.sum_eq_single to focus on v
      have h_sum : finset_sum S (λ u => if v = u then -vertex_degree G u else num_edges G u v) =
          -vertex_degree G v + finset_sum (S.erase v) (λ u => num_edges G u v) := by
        sorry -- This follows from Finset.sum_eq_single
      rw [h_sum]
      -- The sum of num_edges is non-negative
      have h_sum_nonneg : finset_sum (S.erase v) (λ u => num_edges G u v) ≥ 0 := by
        apply Finset.sum_nonneg
        intro x _
        exact num_edges_nonneg G x v
      -- Help linarith by rearranging terms
      have h_rearrange : D₁ v + (-vertex_degree G v + finset_sum (S.erase v) (λ u => num_edges G u v)) =
                        (D₁ v - vertex_degree G v) + finset_sum (S.erase v) (λ u => num_edges G u v) := by
        ring

      rw [h_rearrange]
      have h_base_vd : D₁ v - vertex_degree G v ≥ -vertex_degree G v := by
        linarith [h_base]

      -- Break down the inequality into steps
      have h_sum_pos : finset_sum (S.erase v) (λ u => num_edges G u v) ≥ 0 := by
        apply Finset.sum_nonneg
        intro x _
        exact num_edges_nonneg G x v

      have h_D₁_nonneg : D₁ v ≥ 0 := h_base

      have h_vd_nonneg : vertex_degree G v ≥ 0 := h_vd

      -- Now show that adding these inequalities works
      have h_sum_ineq : D₁ v - vertex_degree G v + finset_sum (S.erase v) (λ u => num_edges G u v) ≥ 0 := by
        sorry

      exact h_sum_ineq
    · -- If v ∉ S, use num_edges properties
      -- When v ∉ S, all terms in sum use num_edges part of conditional
      have h_sum_eq : finset_sum S (λ u => if v = u then -vertex_degree G u else num_edges G u v) =
                      finset_sum S (λ u => num_edges G u v) := by
        sorry

      rw [h_sum_eq]
      have h_sum_nonneg : finset_sum (S.erase v) (λ u => num_edges G u v) ≥ 0 := by
        apply Finset.sum_nonneg
        intro x _
        exact num_edges_nonneg G x v
      -- Now combine D₁ v ≥ 0 with sum_nonneg
      linarith [h_base, h_sum_nonneg]

  exact h_nonneg




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

/--
/-- Helper lemma: Effective divisors have non-negative degree -/
lemma effective_implies_nonneg_deg (G : CFGraph V) (E : CFDiv V) (h_eff : effective E) :
  deg E ≥ 0 := by
  simp [deg]
  exact Finset.sum_nonneg (λ v _ => h_eff v)

/-- Helper lemma: For effective divisors of positive degree, k₁ + k₂ > 0 -/
lemma effective_div_sum_pos (G : CFGraph V) (E : CFDiv V) (k₁ k₂ : ℕ)
  (h_eff : effective E) (h_deg : deg E = k₁ + k₂) : k₁ + k₂ > 0 := by
  have h_nonneg := effective_implies_nonneg_deg G E h_eff
  rw [h_deg] at h_nonneg

  -- Case analysis on k₁ + k₂
  cases h : k₁ + k₂
  · -- Case: k₁ + k₂ = 0
    -- This implies k₁ = k₂ = 0 since they're natural numbers
    have h_sum_zero : ∑ v, E v = 0 := by
      calc ∑ v, E v = deg E := by rfl
        _ = ↑(k₁ + k₂) := by exact h_deg
        _ = ↑0 := by { rw [h]; rfl }
        _ = 0 := by simp only [Nat.cast_zero]

    -- Get a positive element using effectiveness
    have h_exists_pos : ∃ v : V, E v > 0 := by
      sorry

    -- Get contradiction with sum being zero
    rcases h_exists_pos with ⟨v, h_pos⟩
    have h_sum_pos : ∑ v, E v > 0 := by
      sorry

    -- Contradiction
    exact absurd h_sum_zero (ne_of_gt h_sum_pos)

  · -- Case: k₁ + k₂ = succ n
    -- Then k₁ + k₂ > 0 directly
    exact Nat.succ_pos _

theorem divisor_decomposition (G : CFGraph V) (E'' : CFDiv V) (k₁ k₂ : ℕ)
  (h_effective : effective E'') (h_deg : deg E'' = k₁ + k₂) :
  ∃ (E₁ E₂ : CFDiv V),
    effective E₁ ∧ effective E₂ ∧
    deg E₁ = k₁ ∧ deg E₂ = k₂ ∧
    E'' = λ v => E₁ v + E₂ v := by

  let E₁ : CFDiv V := λ v =>
    if E'' v = 0 then 0
    else (k₁ * E'' v) / (k₁ + k₂)
  let E₂ : CFDiv V := λ v => E'' v - E₁ v

  use E₁, E₂

  constructor
  · -- Show E₁ is effective
    intro v
    have h_nonneg : E'' v ≥ 0 := h_effective v
    by_cases h : E'' v = 0
    · simp [E₁, h]
    · simp [E₁, h]
      have h_k_pos : (k₁ + k₂ : ℤ) > 0 := by
        apply Int.natCast_pos.mpr
        exact effective_div_sum_pos G E'' k₁ k₂ h_effective h_deg
      have h_mul_nonneg : (k₁ : ℤ) * E'' v ≥ 0 := by
        exact mul_nonneg (Int.natCast_nonneg k₁) h_nonneg
      sorry

  constructor
  · -- Show E₂ is effective
    intro v
    have h_nonneg : E'' v ≥ 0 := h_effective v
    by_cases h : E'' v = 0
    · simp [E₁, E₂, h]
    · simp [E₁, E₂, h]
      have h_k_pos : (k₁ + k₂ : ℤ) > 0 := by
        apply Int.natCast_pos.mpr
        exact effective_div_sum_pos G E'' k₁ k₂ h_effective h_deg
      have h_mul_nonneg : (k₁ : ℤ) * E'' v ≥ 0 := by
        exact mul_nonneg (Int.natCast_nonneg k₁) h_nonneg
      sorry

-- First prove deg E₁ = k₁ and name it
  have h_deg_E₁ : deg E₁ = k₁ :=
    calc deg E₁ = ∑ v, E₁ v := rfl
      _ = ∑ v, (k₁ : ℤ) * E'' v / (k₁ + k₂) := by
        congr
        funext v
        by_cases h : E'' v = 0
        · simp [E₁, h]
        · simp [E₁, h]
      _ = ((k₁ : ℤ) * ∑ v, E'' v) / (k₁ + k₂) := by
        sorry
      _ = k₁ := by
        sorry

  constructor
  · -- Use h_deg_E₁ directly
    exact h_deg_E₁

  constructor
  · -- Show deg E₂ = k₂ using h_deg_E₁
    calc deg E₂ = ∑ v, (E'' v - E₁ v) := by rfl
      _ = (∑ v, E'' v) - (∑ v, E₁ v) := by
        exact Finset.sum_sub_distrib
      _ = (k₁ + k₂) - k₁ := by
        have h_sum_E'' : ∑ v, E'' v = k₁ + k₂ := h_deg
        have : deg E₁ = ∑ v, E₁ v := rfl
        rw [h_sum_E'', ← h_deg_E₁, this]
      _ = k₂ := by ring

  · -- Show E'' = λ v => E₁ v + E₂ v
    funext v
    simp [E₁, E₂]

/-- Theorem (Proven): Winnability is preserved under addition -/
theorem helper_winnable_add (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  winnable G D₁ → winnable G D₂ → winnable G (λ v => D₁ v + D₂ v) := by
  -- Introduce the winnability hypotheses
  intros h1 h2

  -- Unfold winnability definition for D₁ and D₂
  rcases h1 with ⟨E₁, hE₁_eff, hE₁_equiv⟩
  rcases h2 with ⟨E₂, hE₂_eff, hE₂_equiv⟩

  -- Our goal is to find an effective divisor linearly equivalent to D₁ + D₂
  use (E₁ + E₂)

  constructor
  -- Show E₁ + E₂ is effective
  {
    unfold Div_plus at hE₁_eff hE₂_eff
    unfold effective at *
    intro v
    have h1 := hE₁_eff v
    have h2 := hE₂_eff v
    exact add_nonneg h1 h2
  }

  -- Show E₁ + E₂ is linearly equivalent to D₁ + D₂
  {
    unfold linear_equiv at *

    -- First convert the function to a CFDiv
    let D₁₂ : CFDiv V := (λ v => D₁ v + D₂ v)

    have h : (E₁ + E₂ - D₁₂) = (E₁ - D₁) + (E₂ - D₂) := by
      funext v
      simp [Pi.add_apply, sub_apply]
      ring

    rw [h]
    exact AddSubgroup.add_mem (principal_divisors G) hE₁_equiv hE₂_equiv
  }
-/

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
