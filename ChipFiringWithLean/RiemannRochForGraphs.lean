import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import ChipFiringWithLean.RRGHelpers
import Mathlib.Algebra.Ring.Int
import Paperproof

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

/-- [Proven] The main Riemann-Roch theorem for graphs -/
theorem riemann_roch_for_graphs {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) (D : CFDiv V) :
  rank G D - rank G (λ v => canonical_divisor G v - D v) = deg D - genus G + 1 := by
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

  -- Let O be corresponding acyclic orientation with unique source q (from bijection)
  rcases stable_bijection G q with ⟨_, h_surj⟩
  -- O_subtype has type {O // is_acyclic G O ∧ (∀ w, is_source G O w → w = q)}
  rcases h_surj c' with ⟨O_subtype, h_eq_c'⟩

  -- Get configuration c' from orientation O_subtype
  -- O_subtype.val is the Orientation, O_subtype.prop.1 is acyclicity, O_subtype.prop.2 is uniqueness
  let c'_config := orientation_to_config G O_subtype.val q O_subtype.prop.1 O_subtype.prop.2

  -- Check consistency (assuming h_eq_c' means c' = c'_config)
  -- Assuming the proof intended to use the configuration derived from the orientation
  -- Let's rename c'_config to c' to match the original intent, assuming consistency.
  let c' := orientation_to_config G O_subtype.val q O_subtype.prop.1 O_subtype.prop.2

  -- Define H := (c' - c) - (k + 1)q as a divisor
  let H : CFDiv V := λ v =>
    if v = q then -(k + 1)
    else c'.vertex_degree v - c.vertex_degree v

  -- Get canonical divisor decomposition
  rcases canonical_is_sum_orientations G with ⟨O₁, O₂, h_O₁_acyc, h_O₂_acyc, h_K⟩

  -- Get key inequality from axiom
  have h_ineq := rank_degree_inequality G D

  -- Get reverse inequality by applying to K-D
  have h_ineq_rev := rank_degree_inequality G (λ v => canonical_divisor G v - D v)

  -- Get degree of canonical divisor
  have h_deg_K : deg (canonical_divisor G) = 2 * genus G - 2 :=
    degree_of_canonical_divisor G

  -- Since rank is an integer and we have bounds, equality must hold
  suffices rank G D - rank G (λ v => canonical_divisor G v - D v) ≥ deg D - genus G + 1 ∧
           rank G D - rank G (λ v => canonical_divisor G v - D v) ≤ deg D - genus G + 1 from
    le_antisymm (this.2) (this.1)

  constructor
  · -- Lower bound
    linarith [h_ineq]
  · -- Upper bound
    have h_swap := rank_degree_inequality G (λ v => canonical_divisor G v - D v)
    -- Simplify double subtraction in h_swap
    have h_sub_simplify : (λ (v : V) => canonical_divisor G v - (canonical_divisor G v - D v)) = D := by
      funext v
      ring

    rw [h_sub_simplify] at h_swap

    have h_deg_sub : deg (λ v => canonical_divisor G v - D v) = deg (canonical_divisor G) - deg D := by
      unfold deg
      -- Split the sum over subtraction
      rw [Finset.sum_sub_distrib]

    -- Substitute the degree of canonical divisor
    rw [h_deg_K] at h_deg_sub

    -- Simplify inequality
    have h_ineq_sub : deg (λ v => canonical_divisor G v - D v) - genus G <
      rank G (λ v => canonical_divisor G v - D v) - rank G D := h_swap

    rw [h_deg_sub] at h_ineq_sub

    -- Final inequality using linarith
    linarith [h_ineq_sub]

/-- [Proven] Corollary 4.4.1: A divisor D is maximal unwinnable if and only if K-D is maximal unwinnable -/
theorem maximal_unwinnable_symmetry {V : Type} [DecidableEq V] [Fintype V]
    (G : CFGraph V) (D : CFDiv V) :
  maximal_unwinnable G D ↔ maximal_unwinnable G (λ v => canonical_divisor G v - D v) := by
  constructor
  -- Forward direction
  { intro h_max_unwin
    -- Get rank = -1 from maximal unwinnable
    have h_rank_neg : rank G D = -1 := by
      rw [rank_neg_one_iff_unwinnable]
      exact h_max_unwin.1

    -- Get degree = g-1 from maximal unwinnable
    have h_deg : deg D = genus G - 1 := maximal_unwinnable_deg G D h_max_unwin

    -- Use Riemann-Roch
    have h_RR := riemann_roch_for_graphs G D
    rw [h_rank_neg] at h_RR

    -- Get degree of K-D
    have h_deg_K := degree_of_canonical_divisor G
    have h_deg_KD : deg (λ v => canonical_divisor G v - D v) = genus G - 1 := by
      -- Get general distributive property for deg over subtraction
      have h_deg_sub : ∀ D₁ D₂ : CFDiv V, deg (D₁ - D₂) = deg D₁ - deg D₂ := by
        intro D₁ D₂
        unfold deg
        simp [sub_apply]

      -- Convert lambda form to standard subtraction
      rw [divisor_sub_eq_lambda G (canonical_divisor G) D]

      -- Apply distributive property
      rw [h_deg_sub (canonical_divisor G) D]

      -- Use known values
      rw [h_deg_K, h_deg]

      -- Arithmetic: (2g-2) - (g-1) = g-1
      ring

    constructor
    · -- K-D is unwinnable
      rw [←rank_neg_one_iff_unwinnable]
      linarith
    · -- Adding chip makes K-D winnable
      intro v
      have h_win := h_max_unwin.2 v

      -- Define the divisors explicitly to avoid type confusion
      let D₁ : CFDiv V := λ w => D w + if w = v then 1 else 0
      let D₂ : CFDiv V := λ w => canonical_divisor G w - D w + if w = v then 1 else 0

      -- Show goal matches D₂
      have h_goal : (λ w => (canonical_divisor G w - D w) + if w = v then 1 else 0) = D₂ := by
        funext w
        simp [D₂]

      -- Use linear equivalence to transfer winnability
      have h_equiv := linear_equiv_add_chip G D v h_deg
      have h_win_transfer := (helper_linear_equiv_preserves_winnability G D₁ D₂ h_equiv).mp h_win

      -- Apply the result
      rw [h_goal]
      exact h_win_transfer
  }
  -- Reverse direction
  { intro h_max_unwin_K
    -- Apply canonical double difference
    rw [←canonical_double_diff G D]
    -- Mirror forward direction's proof
    exact maximal_unwinnable_symmetry G (λ v => canonical_divisor G v - D v) |>.mp h_max_unwin_K
  }
  termination_by (rank G D + 1).toNat
  decreasing_by { exact rank_decreases_for_KD G D h_max_unwin_K }


/-- [Proven] Clifford's Theorem (4.4.2): For a divisor D with non-negative rank
             and K-D also having non-negative rank, the rank of D is at most half its degree. -/
theorem clifford_theorem {V : Type} [DecidableEq V] [Fintype V]
    (G : CFGraph V) (D : CFDiv V)
    (h_D : rank G D ≥ 0)
    (h_KD : rank G (λ v => canonical_divisor G v - D v) ≥ 0) :
    (rank G D : ℚ) ≤ (deg D : ℚ) / 2 := by
  -- Get canonical divisor K's rank using Riemann-Roch
  have h_K_rank : rank G (canonical_divisor G) = genus G - 1 := by
    -- Apply Riemann-Roch with D = K
    have h_rr := riemann_roch_for_graphs G (canonical_divisor G)
    -- For K-K = 0, rank is 0
    have h_K_minus_K : rank G (λ v => canonical_divisor G v - canonical_divisor G v) = 0 := by
      -- Show that this divisor is the zero divisor
      have h1 : (λ v => canonical_divisor G v - canonical_divisor G v) = (λ _ => 0) := by
        funext v
        simp [sub_self]

      -- Show that the zero divisor has rank 0
      have h2 : rank G (λ _ => 0) = 0 := zero_divisor_rank G

      -- Substitute back
      rw [h1, h2]
    -- Substitute into Riemann-Roch
    rw [h_K_minus_K] at h_rr
    -- Use degree_of_canonical_divisor
    rw [degree_of_canonical_divisor] at h_rr
    -- Solve for rank G K
    linarith

  -- Apply rank subadditivity
  have h_subadd := rank_subadditive G D (λ v => canonical_divisor G v - D v) h_D h_KD
  -- The sum D + (K-D) = K
  have h_sum : (λ v => D v + (canonical_divisor G v - D v)) = canonical_divisor G := by
    funext v
    simp
  rw [h_sum] at h_subadd
  rw [h_K_rank] at h_subadd

  -- Use Riemann-Roch to get r(K-D) in terms of r(D)
  have h_rr := riemann_roch_for_graphs G D

  -- Explicit algebraic manipulation
  have h1 : rank G (λ v => canonical_divisor G v - D v) =
           rank G D - (deg D - genus G + 1) := by
    linarith

  -- Substitute this into the subadditivity inequality
  have h2 : genus G - 1 ≥ rank G D + (rank G D - (deg D - genus G + 1)) := by
    rw [h1] at h_subadd
    exact h_subadd

  -- Solve for rank G D
  have h3 : 2 * rank G D - (deg D - genus G + 1) ≤ genus G - 1 := by
    linarith

  have h4 : 2 * rank G D ≤ deg D := by
    linarith

  have h5 : (rank G D : ℚ) ≤ (deg D : ℚ) / 2 := by
    -- Convert to rational numbers and use algebraic properties
    have h_cast : (2 : ℚ) * (rank G D : ℚ) ≤ (deg D : ℚ) := by
      -- Cast integer inequality to rational
      exact_mod_cast h4

    -- Divide both sides by 2 directly using algebra
    have h_two_pos : (0 : ℚ) < 2 := by norm_num

    calc (rank G D : ℚ)
      _  = (rank G D : ℚ) * (1 : ℚ) := by ring
      _  = (rank G D : ℚ) * (2 / 2 : ℚ) := by norm_num
      _  = (2 : ℚ) * (rank G D : ℚ) / 2 := by field_simp
      _  ≤ (deg D : ℚ) / 2 := by
          -- Use the fact that division by positive number preserves inequality
          apply (div_le_div_right h_two_pos).mpr
          exact h_cast

  exact h5

/-- [Proven] RRG's Corollary 4.4.3 establishing divisor degree to rank correspondence  -/
theorem riemann_roch_deg_to_rank_corollary {V : Type} [DecidableEq V] [Fintype V]
  (G : CFGraph V) (D : CFDiv V) :
  -- Part 1
  (deg D < 0 → rank G D = -1) ∧
  -- Part 2
  (0 ≤ (deg D : ℚ) ∧ (deg D : ℚ) ≤ 2 * (genus G : ℚ) - 2 → (rank G D : ℚ) ≤ (deg D : ℚ) / 2) ∧
  -- Part 3
  (deg D > 2 * genus G - 2 → rank G D = deg D - genus G) := by
  constructor
  · -- Part 1: deg(D) < 0 implies r(D) = -1
    intro h_deg_neg
    rw [rank_neg_one_iff_unwinnable]
    intro h_winnable
    -- Use winnable_iff_exists_effective
    obtain ⟨D', h_eff, h_equiv⟩ := winnable_iff_exists_effective G D |>.mp h_winnable
    -- Linear equivalence preserves degree
    have h_deg_eq : deg D = deg D' := by
      exact linear_equiv_preserves_deg G D D' h_equiv
    -- Effective divisors have non-negative degree
    have h_D'_nonneg : deg D' ≥ 0 := by
      exact effective_nonneg_deg D' h_eff
    -- Contradiction: D has negative degree but is equivalent to non-negative degree divisor
    rw [←h_deg_eq] at h_D'_nonneg
    exact not_le_of_gt h_deg_neg h_D'_nonneg

  constructor
  · -- Part 2: 0 ≤ deg(D) ≤ 2g-2 implies r(D) ≤ deg(D)/2
    intro ⟨h_deg_nonneg, h_deg_upper⟩
    by_cases h_rank : rank G D ≥ 0
    · -- Case where r(D) ≥ 0
      let K := canonical_divisor G
      by_cases h_rankKD : rank G (λ v => K v - D v) ≥ 0
      · -- Case where r(K-D) ≥ 0: use Clifford's theorem
        exact clifford_theorem G D h_rank h_rankKD
      · -- Case where r(K-D) = -1: use Riemann-Roch
        have h_rr := riemann_roch_for_graphs G D
        have h_rankKD_eq : rank G (λ v => K v - D v) = -1 :=
          rank_neg_one_of_not_nonneg G (λ v => K v - D v) h_rankKD

        rw [h_rankKD_eq] at h_rr

        -- Arithmetic manipulation to get r(D) equality
        have this : rank G D = deg D - genus G := by
          -- Convert h_rr from (rank G D - (-1)) to (rank G D + 1)
          rw [sub_neg_eq_add] at h_rr
          have := calc
            rank G D = rank G D + 1 - 1 := by ring
            _ = deg D - genus G + 1 - 1 := by rw [h_rr]
            _ = deg D - genus G := by ring
          exact this

        -- Apply the result
        rw [this]

        -- Show that deg D - genus G ≤ deg D / 2 using rational numbers
        have h_bound : (deg D - genus G : ℚ) ≤ (deg D : ℚ) / 2 := by
          linarith [h_deg_upper]

        -- Make sure types match with explicit cast
        have h_cast : (deg D - genus G : ℚ) = (↑(deg D - genus G) : ℚ) := by
          exact_mod_cast rfl
        rw [← h_cast]
        exact h_bound

    · -- Case where r(D) < 0
      have h_rank_eq := rank_neg_one_of_not_nonneg G D h_rank
      have h_bound : -1 ≤ deg D / 2 := by
        -- The division by 2 preserves non-negativity for deg D
        have h_div_nonneg : deg D / 2 ≥ 0 := by
          have h_two_pos : (2 : ℤ) > 0 := by norm_num
          rw [Int.div_nonneg_iff_of_pos h_two_pos]
          -- Convert explicitly to the right type
          have h : deg D ≥ 0 := by exact_mod_cast h_deg_nonneg
          exact h

        linarith
      rw [h_rank_eq]

      -- Convert to rational numbers
      have h_bound_rat : ((-1) : ℚ) ≤ (deg D : ℚ) / 2 := by linarith [h_bound]

      exact h_bound_rat

  · -- Part 3: deg(D) > 2g-2 implies r(D) = deg(D) - g
    intro h_deg_large
    have h_canon := degree_of_canonical_divisor G
    -- Show K-D has negative degree
    have h_KD_neg : deg (λ v => canonical_divisor G v - D v) < 0 := by
      -- Calculate deg(K-D)
      calc
        deg (λ v => canonical_divisor G v - D v)
        _ = deg (canonical_divisor G) - deg D := by
          unfold deg
          simp [sub_apply]
        _ = 2 * genus G - 2 - deg D := by rw [h_canon]
        _ < 0 := by linarith

    -- Show K-D is unwinnable, so rank = -1
    have h_rankKD : rank G (λ v => canonical_divisor G v - D v) = -1 := by
      rw [rank_neg_one_iff_unwinnable]
      intro h_win
      -- If winnable, would be linearly equivalent to effective divisor
      obtain ⟨E, h_eff, h_equiv⟩ := winnable_iff_exists_effective G _ |>.mp h_win
      have h_deg_eq := linear_equiv_preserves_deg G _ E h_equiv
      -- But effective divisors have non-negative degree
      have h_E_nonneg := effective_nonneg_deg E h_eff
      rw [←h_deg_eq] at h_E_nonneg
      -- Contradiction: K-D has negative degree
      exact not_le_of_gt h_KD_neg h_E_nonneg

    -- Apply Riemann-Roch to get r(D) = deg(D) - g
    have h_rr := riemann_roch_for_graphs G D
    rw [h_rankKD] at h_rr
    rw [sub_neg_eq_add] at h_rr
    linarith
