import ChipFiringWithLean.CFGraph
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option linter.unusedVariables false
set_option trace.split.failure true

open Multiset Finset

inductive Person : Type
  | A | B | C | E
  deriving DecidableEq

instance : Fintype Person where
  elems := {Person.A, Person.B, Person.C, Person.E}
  complete := by {
    intro x
    cases x
    all_goals { simp }
  }

def example_graph : CFGraph Person := {
  edges := Multiset.sum $ Multiset.map (fun p => Multiset.replicate 1 p) [
    (Person.A, Person.B), (Person.B, Person.C),
    (Person.A, Person.C), (Person.A, Person.E),
    (Person.A, Person.E), (Person.E, Person.C)
  ]
}

def initial_wealth : CFDiv Person :=
  fun v => match v with
  | Person.A => 2
  | Person.B => -3
  | Person.C => 4
  | Person.E => -1

-- Test vertex degrees
theorem vertex_degree_A : vertex_degree example_graph Person.A = 4 := by rfl
theorem vertex_degree_B : vertex_degree example_graph Person.B = 2 := by rfl
theorem vertex_degree_C : vertex_degree example_graph Person.C = 3 := by rfl
theorem vertex_degree_E : vertex_degree example_graph Person.E = 3 := by rfl

-- Test edge counts
theorem edge_count_AB : num_edges example_graph Person.A Person.B = 1 := by rfl
theorem edge_count_BA : num_edges example_graph Person.B Person.A = 1 := by rfl
theorem edge_count_BC : num_edges example_graph Person.B Person.C = 1 := by rfl
theorem edge_count_CB : num_edges example_graph Person.C Person.B = 1 := by rfl
theorem edge_count_AC : num_edges example_graph Person.A Person.C = 1 := by rfl
theorem edge_count_CA : num_edges example_graph Person.C Person.A = 1 := by rfl
theorem edge_count_AE : num_edges example_graph Person.A Person.E = 2 := by rfl
theorem edge_count_EA : num_edges example_graph Person.E Person.A = 2 := by rfl
theorem edge_count_EC : num_edges example_graph Person.E Person.C = 1 := by rfl
theorem edge_count_CE : num_edges example_graph Person.C Person.E = 1 := by rfl
theorem edge_count_BE : num_edges example_graph Person.B Person.E = 0 := by rfl
theorem edge_count_EB : num_edges example_graph Person.E Person.B = 0 := by rfl

-- Test No self-loops
theorem edge_count_AA : num_edges example_graph Person.A Person.A = 0 := by rfl
theorem edge_count_BB : num_edges example_graph Person.B Person.B = 0 := by rfl
theorem edge_count_CC : num_edges example_graph Person.C Person.C = 0 := by rfl
theorem edge_count_EE : num_edges example_graph Person.E Person.E = 0 := by rfl

-- Test Charlie lending through an individual firing move
def after_charlie_lends := firing_move example_graph initial_wealth Person.C
theorem charlie_wealth_after_lending : after_charlie_lends Person.C = 1 := by rfl
theorem bob_wealth_after_charlie_lends : after_charlie_lends Person.B = -2 := by rfl

-- Test set firing W₁ = {A,E,C}
def W₁ : Finset Person := {Person.A, Person.E, Person.C}
def after_W₁_firing := set_firing example_graph initial_wealth W₁
theorem alice_wealth_after_W₁ : after_W₁_firing Person.A = 1 := by rfl
theorem bob_wealth_after_W₁ : after_W₁_firing Person.B = -1 := by rfl
theorem charlie_wealth_after_W₁ : after_W₁_firing Person.C = 3 := by rfl
theorem elise_wealth_after_W₁ : after_W₁_firing Person.E = -1 := by rfl

-- Test set firing W₂ = {A,E,C}
def W₂ : Finset Person := W₁
def after_W₂_firing := set_firing example_graph after_W₁_firing W₂
theorem alice_wealth_after_W₂ : after_W₂_firing Person.A = 0 := by rfl
theorem bob_wealth_after_W₂ : after_W₂_firing Person.B = 1 := by rfl
theorem charlie_wealth_after_W₂ : after_W₂_firing Person.C = 2 := by rfl
theorem elise_wealth_after_W₂ : after_W₂_firing Person.E = -1 := by rfl

-- Test set firing W₃ = {B,C}
def W₃ : Finset Person := {Person.B, Person.C}
def after_W₃_firing := set_firing example_graph after_W₂_firing W₃
theorem alice_wealth_after_W₃ : after_W₃_firing Person.A = 2 := by rfl
theorem bob_wealth_after_W₃ : after_W₃_firing Person.B = 0 := by rfl
theorem charlie_wealth_after_W₃ : after_W₃_firing Person.C = 0 := by rfl
theorem elise_wealth_after_W₃ : after_W₃_firing Person.E = 0 := by rfl

-- Test borrowing moves
def after_bob_borrows := borrowing_move example_graph initial_wealth Person.B
theorem bob_wealth_after_borrowing : after_bob_borrows Person.B = -1 := by rfl
theorem alice_wealth_after_bob_borrows : after_bob_borrows Person.A = 1 := by rfl
theorem charlie_wealth_after_bob_borrows : after_bob_borrows Person.C = 3 := by rfl

-- Test degree of divisors
theorem initial_wealth_degree : deg initial_wealth = 2 := by rfl
theorem after_W₁_degree : deg after_W₁_firing = 2 := by rfl
theorem after_W₂_degree : deg after_W₂_firing = 2 := by rfl
theorem after_W₃_degree : deg after_W₃_firing = 2 := by rfl

-- Test effectiveness of divisors
theorem initial_not_effective : ¬effective initial_wealth := by {
  intro h
  have hB := h Person.B
  have h_neg : initial_wealth Person.B = -3 := by rfl
  have h_lt : -3 < 0 := by norm_num
  exact not_le.mpr h_lt hB
}
theorem initial_not_effective_bool : effective_bool initial_wealth = false := by rfl
-- Note: ¬effective_bool initial_wealth = true can't be resolved by rfl because
-- it requires both sides of the equation to be definitionally equal, and
-- the negation operator (¬) is not reducible to a simple syntactic equality.
theorem after_W₃_firing_effective : effective_bool after_W₃_firing = true := by rfl

-- Test Laplacian matrix properties
def example_laplacian := laplacian_matrix example_graph
theorem laplacian_diagonal_A : example_laplacian Person.A Person.A = 4 := by rfl
theorem laplacian_diagonal_B : example_laplacian Person.B Person.B = 2 := by rfl
theorem laplacian_diagonal_C : example_laplacian Person.C Person.C = 3 := by rfl
theorem laplacian_diagonal_E : example_laplacian Person.E Person.E = 3 := by rfl
theorem laplacian_off_diagonal_AB : example_laplacian Person.A Person.B = -1 := by rfl
theorem laplacian_off_diagonal_AC : example_laplacian Person.A Person.C = -1 := by rfl
theorem laplacian_off_diagonal_AE : example_laplacian Person.A Person.E = -2 := by rfl
theorem laplacian_off_diagonal_BC : example_laplacian Person.B Person.C = -1 := by rfl
theorem laplacian_off_diagonal_BE : example_laplacian Person.B Person.E = 0 := by rfl
theorem laplacian_off_diagonal_CE : example_laplacian Person.C Person.E = -1 := by rfl
theorem check_example_laplacian_symmetry : Matrix.IsSymm example_laplacian := by
  apply Matrix.IsSymm.ext
  intros i j
  cases i <;> cases j
  all_goals {
    rfl
  }

-- Test script firing through laplacians (Needs more thought)
def firing_script_1 : firing_script Person := fun v => match v with
  | Person.A => 0
  | Person.B => -1
  | Person.C => 1
  | Person.E => 0
def result_1 := apply_laplacian example_graph firing_script_1
theorem laplacian_preserves_degree : deg result_1 = 0 := by rfl
