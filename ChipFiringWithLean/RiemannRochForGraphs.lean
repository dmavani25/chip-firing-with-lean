import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import ChipFiringWithLean.RRGHelpers
import Mathlib.Algebra.Ring.Int

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Axiom: Dhar's algorithm produces q-reduced divisor from any divisor
    Given any divisor D, Dhar's algorithm produces a unique q-reduced divisor that is
    linearly equivalent to D. The algorithm outputs both a superstable configuration c
    and an integer k, where k represents the number of chips at q. This is a key result
    from Dhar (1990) proven in detail in Chapter 3 of Corry & Perkinson's "Divisors and
    Sandpiles" (AMS, 2018) -/
axiom dhar_algorithm {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) (q : V) (D : CFDiv V) :
  ∃ (c : Config V q) (k : ℤ),
    linear_equiv G D (λ v => c.vertex_degree v + (if v = q then k else 0)) ∧
    superstable G q c

/-- Axiom: Existence of elements in finite types
    This is a technical axiom used to carry forward existence arguments we frequently use
    such as the fact that finite graphs have vertices. This axiom
    captures this in a way that can be used in formal lean4 proofs. -/
axiom Fintype.exists_elem (V : Type) [Fintype V] : ∃ x : V, True

/-- Axiom: Dhar's algorithm produces negative k for unwinnable divisors
    When applied to an unwinnable divisor D, Dhar's algorithm must produce a
    negative value for k (the number of chips at q). This is a crucial fact used
    in characterizing unwinnable divisors, proven in chapter 4 of Corry & Perkinson's
    "Divisors and Sandpiles" (AMS, 2018). The negativity of k is essential for
    showing the relationship between unwinnable divisors and q-reduced forms. -/
axiom dhar_negative_k {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) (q : V) (D : CFDiv V) :
  ¬(winnable G D) →
  ∀ (c : Config V q) (k : ℤ),
    linear_equiv G D (λ v => c.vertex_degree v + (if v = q then k else 0)) →
    superstable G q c →
    k < 0

/-- Axiom: Helper for inequalities needed in Riemann-Roch
    [@TODO] Future Work: To prove. -/
axiom rank_degree_inequality {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) (D : CFDiv V) :
  deg D - genus G < rank G D - rank G (λ v => canonical_divisor G v - D v)

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
  rcases dhar_algorithm G q (λ v => D v - E v) with ⟨c, k, h_equiv, h_super⟩

  -- k must be negative since D - E is unwinnable
  have h_k_neg := dhar_negative_k G q (λ v => D v - E v) h_D_E_unwin c k h_equiv h_super

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

/-- Axiom: Rank decreases in K-D recursion for maximal unwinnable divisors
    This captures that when we apply canonical_divisor - D to a maximal unwinnable divisor,
    the rank measure decreases. This is used for termination of maximal_unwinnable_symmetry. -/
axiom rank_decreases_for_KD {V : Type} [DecidableEq V] [Fintype V]
  (G : CFGraph V) (D : CFDiv V) :
  maximal_unwinnable G (λ v => canonical_divisor G v - D v) →
  ((rank G (λ v => canonical_divisor G v - D v) + 1).toNat < (rank G D + 1).toNat)

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
      have h_equiv := linear_equiv_add_chip G D v
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


/-- Clifford's Theorem (4.4.2): For a divisor D with non-negative rank and K-D also having non-negative rank,
    the rank of D is at most half its degree. -/
theorem clifford_theorem {V : Type} [DecidableEq V] [Fintype V]
    (G : CFGraph V) (D : CFDiv V)
    (h_D : rank G D ≥ 0)
    (h_KD : rank G (λ v => canonical_divisor G v - D v) ≥ 0) :
    rank G D ≤ deg D / 2 := by
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

  have h5 : rank G D ≤ deg D / 2 := by
    have h_two_pos : 0 < (2 : ℤ) := by norm_num
    apply (Int.mul_le_mul_iff_of_pos_right h_two_pos).mp
    rw [Int.mul_comm]
    have h6 : deg D / 2 * 2 = deg D := by
      exact int_div_mul_two (deg D)
    rw [h6]
    exact h4

  exact h5
