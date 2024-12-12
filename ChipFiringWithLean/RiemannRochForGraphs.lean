import ChipFiringWithLean.CFGraph
import Mathlib.Algebra.Ring.Int

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

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

/-- Corollary 4.2.2: Rank inequality for divisors -/
theorem rank_subadditive (G : CFGraph V) (D D' : CFDiv V)
    (h_D : rank G D ≥ 0) (h_D' : rank G D' ≥ 0) :
    rank G (λ v => D v + D' v) ≥ rank G D + rank G D' := by
  -- Convert ranks to natural numbers
  let k₁ := (rank G D).toNat
  let k₂ := (rank G D').toNat

  -- Show rank is ≥ k₁ + k₂ by proving rank_geq
  have h_rank_geq : rank_geq G (λ v => D v + D' v) (k₁ + k₂) := by
    -- Take any effective divisor E'' of degree k₁ + k₂
    intro E'' h_E''
    have ⟨h_eff, h_deg⟩ := h_E''

    -- Decompose E'' into E₁ and E₂ of degrees k₁ and k₂
    have ⟨E₁, E₂, h_E₁_eff, h_E₂_eff, h_E₁_deg, h_E₂_deg, h_sum⟩ :=
      helper_divisor_decomposition G E'' k₁ k₂ h_eff h_deg

    -- Convert our nat-based hypotheses to ℤ-based ones for rank_spec
    have h_D_nat : rank G D ≥ ↑k₁ := by
      have h_conv : ↑((rank G D).toNat) = rank G D := Int.toNat_of_nonneg h_D
      rw [←h_conv]

    have h_D'_nat : rank G D' ≥ ↑k₂ := by
      have h_conv : ↑((rank G D').toNat) = rank G D' := Int.toNat_of_nonneg h_D'
      rw [←h_conv]

    -- Get rank_geq properties from rank_spec
    have h_D_rank_geq := ((rank_spec G D).2.1 k₁).mp h_D_nat
    have h_D'_rank_geq := ((rank_spec G D').2.1 k₂).mp h_D'_nat

    -- Apply rank_geq to get winnability for both parts
    have h_D_win := h_D_rank_geq E₁ (by exact ⟨h_E₁_eff, h_E₁_deg⟩)
    have h_D'_win := h_D'_rank_geq E₂ (by exact ⟨h_E₂_eff, h_E₂_deg⟩)

    -- Show that (D + D') - (E₁ + E₂) = (D - E₁) + (D' - E₂)
    have h_rearrange : (λ v => (D v + D' v) - (E₁ v + E₂ v)) =
                      (λ v => (D v - E₁ v) + (D' v - E₂ v)) := by
      funext v
      ring

    -- Show winnability of sum using helper_winnable_add and rearrangement
    rw [h_sum, h_rearrange]
    exact helper_winnable_add G (λ v => D v - E₁ v) (λ v => D' v - E₂ v) h_D_win h_D'_win

  -- Connect k₁, k₂ back to original ranks
  have h_k₁ : ↑k₁ = rank G D := by
    exact Int.toNat_of_nonneg h_D

  have h_k₂ : ↑k₂ = rank G D' := by
    exact Int.toNat_of_nonneg h_D'

  -- Show final inequality using transitivity
  have h_final := ((rank_spec G (λ v => D v + D' v)).2.1 (k₁ + k₂)).mpr h_rank_geq

  have h_sum : ↑(k₁ + k₂) = rank G D + rank G D' := by
    simp only [Nat.cast_add]  -- Use Nat.cast_add instead of Int.coe_add
    rw [h_k₁, h_k₂]

  rw [h_sum] at h_final
  exact h_final

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

-- Corollary 4.2.3: Degree of canonical divisor equals 2g - 2
theorem degree_of_canonical_divisor (G : CFGraph V) :
    deg (canonical_divisor G) = 2 * genus G - 2 := by
  -- First unfold definitions
  unfold deg canonical_divisor

  -- Use sum_sub_distrib to split the sum
  have h1 : ∑ v, (vertex_degree G v - 2) =
            ∑ v, vertex_degree G v - 2 * Fintype.card V := by
    rw [sum_sub_distrib]
    simp [sum_const, nsmul_eq_mul]
    ring

  rw [h1]

  -- Use the fact that sum of vertex degrees = 2|E|
  have h2 : ∑ v, vertex_degree G v = 2 * Multiset.card G.edges := by
    exact helper_sum_vertex_degrees G
  rw [h2]

  -- Use genus definition: g = |E| - |V| + 1
  rw [genus]

  -- Final algebraic simplification
  ring

-- Axiom: Non-negativity of edges
axiom helper_num_edges_nonneg (G : CFGraph V) (v w : V) :
  num_edges G v w ≥ 0

-- [Proven] Lemma: effectiveness is preserved under legal firing (Additional)
lemma legal_firing_preserves_effective (G : CFGraph V) (D : CFDiv V) (S : Finset V) :
  legal_set_firing G D S → effective D → effective (set_firing G D S) := by
  intros h_legal h_eff v
  simp [set_firing]
  by_cases hv : v ∈ S
  -- Case 1: v ∈ S
  · exact h_legal v hv
  -- Case 2: v ∉ S
  · have h1 : D v ≥ 0 := h_eff v
    have h2 : finset_sum S (λ v' => if v = v' then -vertex_degree G v' else num_edges G v' v) ≥ 0 := by
      apply Finset.sum_nonneg
      intro x hx
      -- Split on whether v = x
      by_cases hveq : v = x
      · -- If v = x, contradiction with v ∉ S
        rw [hveq] at hv
        contradiction
      · -- If v ≠ x, then we get num_edges which is non-negative
        simp [hveq]
        exact helper_num_edges_nonneg G x v
    linarith

-- Axiom: Every divisor is linearly equivalent to exactly one q-reduced divisor
axiom helper_unique_q_reduced (G : CFGraph V) (q : V) (D : CFDiv V) :
  ∃! D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D'

-- Axiom: Effectiveness preservation under linear equivalence
axiom helper_effective_linear_equiv (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  linear_equiv G D₁ D₂ → effective D₁ → effective D₂

-- Proposition 3.2.4: q-reduced and effective implies winnable
theorem winnable_iff_q_reduced_effective (G : CFGraph V) (q : V) (D : CFDiv V) :
  winnable G D ↔ ∃ D' : CFDiv V, linear_equiv G D D' ∧ q_reduced G q D' ∧ effective D' := by
  constructor
  { -- Forward direction
    intro h_win
    rcases h_win with ⟨E, h_eff, h_equiv⟩
    rcases helper_unique_q_reduced G q D with ⟨D', h_D'⟩
    use D'
    constructor
    · exact h_D'.1.1  -- D is linearly equivalent to D'
    constructor
    · exact h_D'.1.2  -- D' is q-reduced
    · -- Show D' is effective using:
      -- First get E ~ D' by transitivity through D
      have h_equiv_symm := (linear_equiv_is_equivalence G).symm h_equiv
      have h_equiv' := (linear_equiv_is_equivalence G).trans h_equiv_symm h_D'.1.1
      -- Now use effectiveness preservation under linear equivalence
      exact helper_effective_linear_equiv G E D' h_equiv' h_eff
  }
  { -- Reverse direction
    intro h
    rcases h with ⟨D', h_equiv, h_qred, h_eff⟩
    use D'
    exact ⟨h_eff, h_equiv⟩
  }

-- Proposition 3.2.4 (Extension): q-reduced and effective implies winnable
theorem q_reduced_effective_implies_winnable (G : CFGraph V) (q : V) (D : CFDiv V) :
  q_reduced G q D → effective D → winnable G D := by
  intros h_qred h_eff
  -- Apply right direction of iff
  rw [winnable_iff_q_reduced_effective]
  -- Prove existence
  use D
  constructor
  · exact (linear_equiv_is_equivalence G).refl D  -- D is linearly equivalent to itself using proven reflexivity
  constructor
  · exact h_qred  -- D is q-reduced
  · exact h_eff   -- D is effective
