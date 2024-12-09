import ChipFiringWithLean.CFGraph
import Mathlib.Algebra.Ring.Int

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

-- Assume V is a finite type with decidable equality
variable {V : Type} [DecidableEq V] [Fintype V]

-- Result: Sum of vertex degrees equals 2|E|
/--
theorem sum_vertex_degrees (G : CFGraph V) :
  ∑ v, vertex_degree G v = 2 * ↑(Multiset.card G.edges) := by
  -- Unfold definitions
  unfold vertex_degree

  -- Convert the sum
  have h1 : ∑ v, ↑(Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))) =
           2 * ↑(Multiset.card G.edges) := by
    -- Convert natural numbers to integers
    simp only [Nat.cast_sum, Nat.cast_mul]

    -- Show edge counting correspondence
    have h_count : ∀ e ∈ G.edges,
      (Finset.univ.filter (λ v => e.fst = v ∨ e.snd = v)).card = 2 := by
      intro e he
      simp [G.loopless]
      split
      . exact dec_trivial
      . rfl

    -- Convert counts to integers and sum
    have h_sum : ∑ v, (Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))) =
                 2 * Multiset.card G.edges := by
      exact Nat.cast_inj.mp (by exact h_count)

    exact h_sum

  -- Apply the equality
  exact h1
-/

axiom sum_vertex_degrees (G : CFGraph V) :
  ∑ v, vertex_degree G v = 2 * ↑(Multiset.card G.edges)

-- Corollary: Degree of canonical divisor equals 2g - 2
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
    exact sum_vertex_degrees G
  rw [h2]

  -- Use genus definition: g = |E| - |V| + 1
  rw [genus]

  -- Final algebraic simplification
  ring
