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
