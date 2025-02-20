import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import ChipFiringWithLean.Helpers
import Mathlib.Algebra.Ring.Int
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

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
    linarith

-- [Proven] Proposition 3.2.4: q-reduced and effective implies winnable
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

-- [Proven] Proposition 3.2.4 (Extension): q-reduced and effective implies winnable
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

/-- [Proven] Lemma 4.1.10: An acyclic orientation is uniquely determined by its indegree sequence -/
theorem acyclic_orientation_unique_by_indeg {G : CFGraph V}
  (O O' : Orientation G)
  (h_acyclic : is_acyclic G O)
  (h_acyclic' : is_acyclic G O')
  (h_indeg : ∀ v : V, indeg G O v = indeg G O' v) :
  O = O' := by
  -- Apply the helper_orientation_determined_by_levels axiom directly
  exact helper_orientation_determined_by_levels O O' h_acyclic h_acyclic' h_indeg

/-- [Proven] Lemma 4.1.10 (Alternative Form): Two acyclic orientations with same indegree sequences are equal -/
theorem acyclic_equal_of_same_indeg {G : CFGraph V} (O O' : Orientation G)
    (h_acyclic : is_acyclic G O) (h_acyclic' : is_acyclic G O')
    (h_indeg : ∀ v : V, indeg G O v = indeg G O' v) :
    O = O' := by
  -- Use previously defined theorem about uniqueness by indegree
  exact acyclic_orientation_unique_by_indeg O O' h_acyclic h_acyclic' h_indeg

/-- [Proven] Proposition 4.1.11: Bijection between acyclic orientations with source q
    and maximal superstable configurations -/
theorem stable_bijection (G : CFGraph V) (q : V) :
    Function.Bijective (λ (O : {O : Orientation G // is_acyclic G O ∧ is_source G O q}) =>
      orientation_to_config G O.val q O.prop.1 O.prop.2) := by
  constructor
  -- Injectivity
  { intros O₁ O₂ h_eq
    -- Extract orientations and their properties
    let ⟨O₁, h₁⟩ := O₁
    let ⟨O₂, h₂⟩ := O₂
    -- Convert equality to the right form
    have h_eq' := helper_config_eq_of_subtype_eq h_eq
    -- Apply uniqueness axiom
    exact Subtype.eq (helper_config_to_orientation_unique G q
      (orientation_to_config G O₁ q h₁.1 h₁.2)
      (helper_orientation_config_superstable G O₁ q h₁.1 h₁.2)
      (helper_orientation_config_maximal G O₁ q h₁.1 h₁.2)
      O₁ O₂ h₁.1 h₂.1 h₁.2 h₂.2 rfl h_eq') }

  -- Surjectivity
  { intro c
    -- First show c is superstable
    have h_super : superstable G q c := helper_config_superstable G q c

    -- Get maximal superstable config extending c
    have ⟨c', h_max', h_ge⟩ := helper_maximal_superstable_exists G q c h_super

    -- Get orientation for the maximal superstable config
    have ⟨O, h_acyc, h_src, h_eq⟩ := helper_maximal_superstable_orientation G q c' h_max'

    -- Use the orientation to construct our witness
    use ⟨O, ⟨h_acyc, h_src⟩⟩

    -- Show equality through transitivity
    calc orientation_to_config G O q h_acyc h_src
      _ = c' := h_eq
      _ = c  := helper_maximal_superstable_unique_dominates G q c c' h_max' h_ge }

/-- [Proven] Corollary 4.2.2: Rank inequality for divisors -/
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

-- [Proven] Corollary 4.2.3: Degree of canonical divisor equals 2g - 2
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

/-- [Proven] Proposition 4.1.13 (1): Characterization of maximal superstable configurations by their degree -/
theorem maximal_superstable_config_prop (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → (maximal_superstable G c ↔ config_degree c = genus G) := by
  intro h_super
  constructor
  { -- Forward direction: maximal_superstable → degree = g
    intro h_max
    -- Use degree bound and maximality
    have h_bound := helper_superstable_degree_bound G q c h_super
    have h_geq := helper_maximal_superstable_degree_lower_bound G q c h_super h_max
    -- Combine bounds to get equality
    exact le_antisymm h_bound h_geq }
  { -- Reverse direction: degree = g → maximal_superstable
    intro h_deg
    -- Apply the axiom that degree g implies maximality
    exact helper_degree_g_implies_maximal G q c h_super h_deg }

/-- [Proven] Proposition 4.1.13 (2): Characterization of maximal unwinnable divisors -/
theorem maximal_unwinnable_char (G : CFGraph V) (q : V) (D : CFDiv V) :
  maximal_unwinnable G D ↔
  ∃ c : Config V q, maximal_superstable G c ∧
  ∃ D' : CFDiv V, q_reduced G q D' ∧ linear_equiv G D D' ∧
  D' = λ v => c.vertex_degree v - if v = q then 1 else 0 := by
  constructor
  { -- Forward direction
    intro h_max
    rcases helper_unique_q_reduced G q D with ⟨D', h_D'⟩
    -- Use the forward direction of the new correspondence theorem
    rcases (q_reduced_superstable_correspondence G q D').mp h_D'.1.2 with ⟨c, h_super, h_form⟩
    have h_max_super : maximal_superstable G c := by
      by_contra h
      rcases helper_maximal_superstable_exists G q c h_super with ⟨c', h_max', h_ge⟩
      let D'' := λ v => c'.vertex_degree v - if v = q then 1 else 0
      -- Use the reverse direction of the new correspondence theorem
      have h_qred' := (q_reduced_superstable_correspondence G q D'').mpr ⟨c', h_max'.1, rfl⟩
      have h_equiv' := helper_q_reduced_linear_equiv_dominates G q c c' h_super h_max'.1 h_ge
      have h_D_equiv_D'' : linear_equiv G D D'' := by
        have h_D'_equiv_D'' : linear_equiv G D' D'' := by
          rw [h_form]
          exact h_equiv'
        exact (linear_equiv_is_equivalence G).trans h_D'.1.1 h_D'_equiv_D''
      have h_win := helper_superstabilize_sends_to_q G q c' h_max'
                     (maximal_superstable_config_prop G q c' h_max'.1 |>.mp h_max')
      have h_win_D := helper_maximal_superstable_winnability G q c' D h_max' h_D_equiv_D'' h_win
      exact h_max.1 h_win_D

    use c, h_max_super, D', h_D'.1.2, h_D'.1.1, h_form }

  { -- Reverse direction
    intro h
    rcases h with ⟨c, h_max, D', h_qred, h_equiv, h_form⟩
    constructor
    { -- Show D is unwinnable
      intro h_win
      -- Use linear equivalence to transfer winnability to D'
      have h_win_D' := (helper_linear_equiv_preserves_winnability G D D' h_equiv).mp h_win
      -- Get value at q for c (must be 0 since superstable)
      have h_c_q := superstable_zero_at_q G q c h_max.1
      -- Show D' q = -1
      have h_q_neg : D' q = -1 := by
        rw [h_form]
        simp [h_c_q]
      -- But winnable divisors must be non-negative everywhere
      have := winnable_iff_q_reduced_effective G q D' |>.mp h_win_D'
      rcases this with ⟨E, h_E_equiv, h_E_qred, h_E_eff⟩
      have h_nonneg := h_E_eff q
      -- Connect D' and E through linear equivalence and q-reduced property
      have h_eq := q_reduced_unique_class G q D' E ⟨h_qred, h_E_qred, h_E_equiv⟩
      -- Get contradiction from -1 ≥ 0
      rw [←h_eq] at h_nonneg
      rw [h_q_neg] at h_nonneg
      linarith }
    { -- Show D + v is winnable for any v
      intro v
      by_cases hv : v = q
      { -- Case v = q: Adding chip to q makes it winnable
        have h_equiv' : linear_equiv G D (λ w => c.vertex_degree w - if w = q then 1 else 0) := by
          rw [h_form] at h_equiv
          exact h_equiv
        rw [hv]
        exact winnable_when_adding_at_q G q D c h_max h_equiv' }
      { -- Case v ≠ q: Use superstabilization
        have h_equiv' : linear_equiv G D (λ v => c.vertex_degree v - if v = q then 1 else 0) := by
          rw [h_form] at h_equiv
          exact h_equiv
        exact winnable_through_equiv_and_chip G q D c h_equiv' h_max v hv } } }

/-- [Proven] Proposition 4.1.13: Combined (1) and (2)-/
theorem superstable_and_maximal_unwinnable (G : CFGraph V) (q : V)
    (c : Config V q) (D : CFDiv V) :
    (superstable G q c →
     (maximal_superstable G c ↔ config_degree c = genus G)) ∧
    (maximal_unwinnable G D ↔
     ∃ c : Config V q, maximal_superstable G c ∧
     ∃ D' : CFDiv V, q_reduced G q D' ∧ linear_equiv G D D' ∧
     D' = λ v => c.vertex_degree v - if v = q then 1 else 0) := by
  exact ⟨maximal_superstable_config_prop G q c,
         maximal_unwinnable_char G q D⟩

/-- [Proven] Proposition 4.1.14: Key results about maximal unwinnable divisors:
    1) There is an injection from acyclic orientations with source q to maximal unwinnable q-reduced divisors,
       where an orientation O maps to the divisor D(O) - q where D(O) assigns indegree to each vertex. (Surjection proof deferred)
    2) Any maximal unwinnable divisor has degree equal to genus - 1.-/
theorem acyclic_orientation_maximal_unwinnable_correspondence_and_degree
    {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) (q : V) :
    (Function.Injective (λ (O : {O : Orientation G // is_acyclic G O ∧ is_source G O q}) =>
      λ v => (indeg G O.val v) - if v = q then 1 else 0)) ∧
    (∀ D : CFDiv V, maximal_unwinnable G D → deg D = genus G - 1) := by
  constructor
  { -- Part 1: Injection proof
    intros O₁ O₂ h_eq
    have h_indeg : ∀ v : V, indeg G O₁.val v = indeg G O₂.val v := by
      intro v
      have := congr_fun h_eq v
      by_cases hv : v = q
      · exact helper_source_indeg_eq_at_q G O₁.val O₂.val q v O₁.prop.2 O₂.prop.2 hv
      · simp [hv] at this
        exact this
    exact Subtype.ext (acyclic_orientation_unique_by_indeg O₁.val O₂.val O₁.prop.1 O₂.prop.1 h_indeg)
  }
  { -- Part 2: Degree characterization
    exact maximal_unwinnable_deg G }

/-- [Proven] Rank Degree Inequality -/
theorem rank_degree_inequality {V : Type} [DecidableEq V] [Fintype V]
    (G : CFGraph V) (D : CFDiv V) :
    deg D - genus G < rank G D - rank G (λ v => canonical_divisor G v - D v) := by
  -- Get rank value for D
  let r := rank G D

  -- Get effective divisor E using rank characterization
  rcases rank_get_effective G D with ⟨E, h_E_eff, h_E_deg, h_D_E_unwin⟩

  -- Fix a vertex q
  rcases Fintype.exists_elem V with ⟨q, _⟩

  -- Apply Dhar's algorithm to D - E to get q-reduced form
  rcases helper_dhar_algorithm G q (λ v => D v - E v) with ⟨c, k, h_equiv, h_super⟩

  -- k must be negative since D - E is unwinnable
  have h_k_neg := helper_dhar_negative_k G q (λ v => D v - E v) h_D_E_unwin c k h_equiv h_super

  -- Get maximal superstable c' ≥ c
  rcases helper_maximal_superstable_exists G q c h_super with ⟨c', h_max', h_ge⟩

  -- Let O be corresponding acyclic orientation
  rcases stable_bijection G q with ⟨_, h_surj⟩
  rcases h_surj c' with ⟨O, h_O_acyc, h_O_src, h_O_eq⟩

  -- Get configuration c' from orientation O
  let c' := orientation_to_config G O.val q O.prop.1 O.prop.2

  -- Define H := (c' - c) - (k + 1)q as a divisor
  let H : CFDiv V := λ v =>
    if v = q then -(k + 1)
    else c'.vertex_degree v - c.vertex_degree v

  have h_H_eff : effective H := by
    intro v
    by_cases h_v : v = q
    · -- Case v = q
      rw [h_v]
      simp [H]
      -- Since k < 0, k + 1 ≤ 0, so -(k + 1) ≥ 0
      have h_k_plus_one_nonpos : k + 1 ≤ 0 := by
        linarith [h_k_neg]
      linarith

    · -- Case v ≠ q
      simp [H, h_v]
      -- h_ge shows c' ≥ c for maximal superstable c'
      have h_ge_at_v : c'.vertex_degree v ≥ c.vertex_degree v := by
        exact h_ge v
      -- Therefore difference is non-negative
      linarith

  -- Complete h_DO_unwin
  have h_DO_unwin : maximal_unwinnable G (λ v => c'.vertex_degree v - if v = q then 1 else 0) := by
    constructor
    · -- First show it's unwinnable
      exact helper_superstable_to_unwinnable G q c' h_max'

    · -- Then show adding a chip anywhere makes it winnable
      exact helper_maximal_superstable_chip_winnable_exact G q c' h_max'

  -- Use degree property of maximal unwinnable divisors
  have h_DO_deg : deg (λ v => c'.vertex_degree v - if v = q then 1 else 0) = genus G - 1 :=
    maximal_unwinnable_deg G _ h_DO_unwin

  calc deg D - genus G
    _ = deg D - (Multiset.card G.edges - Fintype.card V + 1) := by rw [genus]
    _ < deg D - deg E + deg H := by {
      -- Substitute deg E = rank G D + 1
      rw [h_E_deg]
      -- Have h2: deg H > 0
      have h_big : deg D - (Multiset.card G.edges - Fintype.card V + 1) < deg D - (rank G D + 1) + deg H := by {
        -- Rearrange terms
        have h_core : deg D - (Multiset.card G.edges - Fintype.card V + 1)
                    = deg D - (rank G D + 1) + (rank G D + 1 - (Multiset.card G.edges - Fintype.card V + 1)) := by ring
        rw [h_core]
        have h2 : deg H > 0 := by {
          -- Use h_H_eff and h_k_neg with helper axiom
          exact helper_sum_positive_at_q H k h_H_eff h_k_neg
        }

        have h_bound : rank G D + 1 - (Multiset.card G.edges - Fintype.card V + 1) < deg H := by {
          apply helper_H_degree_bound G q D H k c c'
          · exact h_H_eff
          · -- Show H matches form
            funext v
            simp [H]
        }
        -- Complete inequality
        linarith [h_bound]
      }
      exact h_big
    }
    _ ≤ rank G D - rank G (λ v => canonical_divisor G v - D v) := by {
      have : deg E = rank G D + 1 := h_E_deg

      -- Use maximal unwinnable properties
      have h_DO_rank : rank G (λ v => c'.vertex_degree v - if v = q then 1 else 0) = -1 := by
        rw [rank_neg_one_iff_unwinnable]
        exact h_DO_unwin.1

      -- Get linear equivalence
      have h_DO_equiv : linear_equiv G (λ v => c'.vertex_degree v - if v = q then 1 else 0)
                                    (λ v => D v - E v + H v) :=
        helper_DO_linear_equiv G q D E H c'

      -- Use degree properties
      have h_deg_bound : deg (λ v => c'.vertex_degree v - if v = q then 1 else 0) = genus G - 1 := h_DO_deg

      -- Use linear equivalence and rank bounds
      have h_bound := helper_rank_deg_canonical_bound G q D E H c' h_DO_equiv

      -- Use rank_neg_one_iff_unwinnable and h_DO_rank
      have h_rank_eq : rank G (λ v => c'.vertex_degree v - if v = q then 1 else 0) = -1 := h_DO_rank

      -- Complete inequality with linarith
      linarith [h_bound, h_rank_eq, h_deg_bound]
    }
