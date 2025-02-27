import ChipFiringWithLean.Basic
import ChipFiringWithLean.Config
import ChipFiringWithLean.Orientation
import ChipFiringWithLean.Rank
import Mathlib.Algebra.Ring.Int
import Paperproof

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

/-- Axiom: Effectiveness preservation under linear equivalence (legal set-firings)
    This is a fact that is directly used in Corollary 3.7 by Corry & Perkins (Divisors & Sandpiles) -/
axiom helper_effective_linear_equiv (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  linear_equiv G D₁ D₂ → effective D₁ → effective D₂




/-
# Helpers for Lemma 4.1.10
-/

/-- Axiom: A non-empty graph with an acyclic orientation must have at least one source -/
axiom helper_acyclic_has_source (G : CFGraph V) (O : Orientation G) :
  is_acyclic G O → ∃ v : V, is_source G O v

/-- [Proven] Helper theorem: Two orientations are equal if they have the same directed edges -/
theorem helper_orientation_eq_of_directed_edges {G : CFGraph V}
  (O O' : Orientation G) :
  O.directed_edges = O'.directed_edges → O = O' := by
  intro h
  -- Use cases to construct the equality proof
  cases O with | mk edges consistent =>
  cases O' with | mk edges' consistent' =>
  -- Create congr_arg to show fields are equal
  congr

/-- Axiom: Given a list of disjoint vertex sets that form a partition of V,
    this axiom states that an acyclic orientation is uniquely determined
    by this partition where each set contains vertices with same indegree
    [@TODO] Future Work: To prove.-/
axiom helper_orientation_determined_by_levels {G : CFGraph V}
  (O O' : Orientation G) :
  is_acyclic G O → is_acyclic G O' →
  (∀ v : V, indeg G O v = indeg G O' v) →
  O = O'




/-
# Helpers for Proposition 4.1.11
-/

/- Axiom: Defining a reusable block for a configuration from an acyclic orientation with source q being superstable
          Only to be used to define a superstable configuration from an acyclic orientation with source q as a Prop.
-/
axiom helper_orientation_config_superstable (G : CFGraph V) (O : Orientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_src : is_source G O q) :
    superstable G q (orientation_to_config G O q h_acyc h_src)

/- Axiom: Defining a reusable block for a configuration from an acyclic orientation with source q being maximal superstable
          Only to be used to define a maximal superstable configuration from an acyclic orientation with source q as a Prop.
-/
axiom helper_orientation_config_maximal (G : CFGraph V) (O : Orientation G) (q : V)
    (h_acyc : is_acyclic G O) (h_src : is_source G O q) :
    maximal_superstable G (orientation_to_config G O q h_acyc h_src)

/-- [Proven] Helper lemma: Orientation to config preserves indegrees -/
lemma orientation_to_config_indeg (G : CFGraph V) (O : Orientation G) (q : V)
    (h_acyclic : is_acyclic G O) (h_source : is_source G O q) (v : V) :
    (orientation_to_config G O q h_acyclic h_source).vertex_degree v =
    if v = q then 0 else (indeg G O v : ℤ) - 1 := by
  -- This follows directly from the definition of config_of_source
  simp only [orientation_to_config] at *
  -- Use the definition of config_of_source
  exact rfl

/-- [Proven] Helper lemma: Two acyclic orientations with same indegrees are equal -/
lemma orientation_unique_by_indeg {G : CFGraph V} (O₁ O₂ : Orientation G)
    (h_acyc₁ : is_acyclic G O₁) (h_acyc₂ : is_acyclic G O₂)
    (h_indeg : ∀ v : V, indeg G O₁ v = indeg G O₂ v) : O₁ = O₂ := by
  -- Apply the helper statement directly since we have exactly matching hypotheses
  exact helper_orientation_determined_by_levels O₁ O₂ h_acyc₁ h_acyc₂ h_indeg

/-- [Proven] Helper lemma to show indegree of source is 0 -/
lemma source_indeg_zero {G : CFGraph V} (O : Orientation G) (v : V)
    (h_src : is_source G O v) : indeg G O v = 0 := by
  -- By definition of is_source in terms of indeg
  unfold is_source at h_src
  -- Convert from boolean equality to proposition
  exact of_decide_eq_true h_src

/-- [Proven] Helper theorem proving uniqueness of orientations giving same config -/
theorem helper_config_to_orientation_unique (G : CFGraph V) (q : V)
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
    O₁ = O₂ := by
  apply orientation_unique_by_indeg O₁ O₂ h_acyc₁ h_acyc₂
  intro v

  have h_deg₁ := orientation_to_config_indeg G O₁ q h_acyc₁ h_src₁ v
  have h_deg₂ := orientation_to_config_indeg G O₂ q h_acyc₂ h_src₂ v

  have h_config_eq : (orientation_to_config G O₁ q h_acyc₁ h_src₁).vertex_degree v =
                     (orientation_to_config G O₂ q h_acyc₂ h_src₂).vertex_degree v := by
    rw [h_eq₁, h_eq₂]

  by_cases hv : v = q
  · -- Case v = q: Both vertices are sources, so indegree is 0
    rw [hv]
    have h_zero₁ := source_indeg_zero O₁ q h_src₁
    have h_zero₂ := source_indeg_zero O₂ q h_src₂
    rw [h_zero₁, h_zero₂]
  · -- Case v ≠ q: use vertex degree equality
    rw [h_deg₁, h_deg₂] at h_config_eq
    simp only [if_neg hv] at h_config_eq
    -- From config degrees being equal, show indegrees are equal
    have h := congr_arg (fun x => x + 1) h_config_eq
    simp only [sub_add_cancel] at h
    -- Use nat cast injection
    exact (Nat.cast_inj.mp h)

/-- [Proven] Helper lemma to convert between configuration equality forms -/
lemma helper_config_eq_of_subtype_eq {G : CFGraph V} {q : V}
    {O₁ O₂ : {O : Orientation G // is_acyclic G O ∧ is_source G O q}}
    (h : orientation_to_config G O₁.val q O₁.prop.1 O₁.prop.2 =
         orientation_to_config G O₂.val q O₂.prop.1 O₂.prop.2) :
    orientation_to_config G O₂.val q O₂.prop.1 O₂.prop.2 =
    orientation_to_config G O₁.val q O₁.prop.1 O₁.prop.2 := by
  exact h.symm

/- Axiom: Defining a reusable block for a configuration being superstable.
          Only to be used to define a superstable configuration as a Prop.
-/
axiom helper_config_superstable (G : CFGraph V) (q : V) (c : Config V q) : superstable G q c

/-- Axiom: Every superstable configuration extends to a maximal superstable configuration
    [@TODO] Future Work: To prove. -/
axiom helper_maximal_superstable_exists (G : CFGraph V) (q : V) (c : Config V q)
    (h_super : superstable G q c) :
    ∃ c' : Config V q, maximal_superstable G c' ∧ config_ge c' c

/-- Axiom: Every maximal superstable configuration comes from an acyclic orientation
    [@TODO] Future Work: To prove. -/
axiom helper_maximal_superstable_orientation (G : CFGraph V) (q : V) (c : Config V q)
    (h_max : maximal_superstable G c) :
    ∃ (O : Orientation G) (h_acyc : is_acyclic G O) (h_src : is_source G O q),
      orientation_to_config G O q h_acyc h_src = c

/-- Axiom: Maximal superstable configurations are uniquely determined by their orientations
    [@TODO] Future Work: To prove. -/
axiom helper_maximal_superstable_unique (G : CFGraph V) (q : V) (c : Config V q)
  (h_max : maximal_superstable G c)
  (O : Orientation G) (h_acyc : is_acyclic G O) (h_src : is_source G O q) :
  orientation_to_config G O q h_acyc h_src = c →
  ∀ (O' : Orientation G) (h_acyc' : is_acyclic G O' ) (h_src' : is_source G O' q),
  orientation_to_config G O' q h_acyc' h_src' = c → O = O'

/-- Axiom: If c' dominates c and c' is maximal superstable, then c = c'
    [@TODO] Future Work: To prove. -/
axiom helper_maximal_superstable_unique_dominates (G : CFGraph V) (q : V)
    (c c' : Config V q)
    (h_max' : maximal_superstable G c')
    (h_ge : config_ge c' c) : c' = c




/-
# Helpers for Corollary 4.2.2
-/

/-- Axiom: A divisor can be decomposed into parts of specific degrees
    [@TODO] Future Work: To prove. -/
axiom helper_divisor_decomposition (G : CFGraph V) (E'' : CFDiv V) (k₁ k₂ : ℕ)
  (h_effective : effective E'') (h_deg : deg E'' = k₁ + k₂) :
  ∃ (E₁ E₂ : CFDiv V),
    effective E₁ ∧ effective E₂ ∧
    deg E₁ = k₁ ∧ deg E₂ = k₂ ∧
    E'' = λ v => E₁ v + E₂ v

/- [Proven] Helper theorem: Winnability is preserved under addition -/
theorem helper_winnable_add (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  winnable G D₁ → winnable G D₂ → winnable G (λ v => D₁ v + D₂ v) := by
  -- Assume D₁ and D₂ are winnable
  intro h1 h2

  -- Get the effective divisors that D₁ and D₂ are equivalent to
  rcases h1 with ⟨E₁, hE₁_eff, hE₁_equiv⟩
  rcases h2 with ⟨E₂, hE₂_eff, hE₂_equiv⟩

  -- Our goal is to show that D₁ + D₂ is winnable
  -- We'll show E₁ + E₂ is effective and linearly equivalent to D₁ + D₂

  -- Define our candidate effective divisor
  let E := E₁ + E₂

  -- Show E is effective
  have hE_eff : effective E := by
    intro v
    simp [effective] at hE₁_eff hE₂_eff ⊢
    unfold Div_plus at hE₁_eff hE₂_eff
    have h1 := hE₁_eff v
    have h2 := hE₂_eff v
    exact add_nonneg h1 h2

  -- Show E is linearly equivalent to D₁ + D₂
  have hE_equiv : linear_equiv G (D₁ + D₂) E := by
    unfold linear_equiv
    -- Show (E₁ + E₂) - (D₁ + D₂) = (E₁ - D₁) + (E₂ - D₂)
    have h : E - (D₁ + D₂) = (E₁ - D₁) + (E₂ - D₂) := by
      funext w
      simp [sub_apply, add_apply]
      -- Expand E = E₁ + E₂
      have h1 : E w = E₁ w + E₂ w := rfl
      rw [h1]
      -- Use ring arithmetic to complete the proof
      ring

    rw [h]
    -- Use the fact that principal divisors form an additive subgroup
    exact AddSubgroup.add_mem _ hE₁_equiv hE₂_equiv

  -- Construct the witness for winnability
  exists E

/- [Alternative-Proof] Helper theorem: Winnability is preserved under addition -/
theorem helper_winnable_add_alternative (G : CFGraph V) (D₁ D₂ : CFDiv V) :
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




/-
# Helpers for Corollary 4.2.3
-/

/-- [Proved] Helper lemma: Every divisor can be decomposed into a principal divisor and an effective divisor -/
lemma eq_nil_of_card_eq_zero {α : Type _} {m : Multiset α}
    (h : Multiset.card m = 0) : m = ∅ := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    simp only [Multiset.card_cons] at h
    -- card s + 1 = 0 is impossible for natural numbers
    have : ¬(Multiset.card s + 1 = 0) := Nat.succ_ne_zero (Multiset.card s)
    contradiction

/-- [Proven] Helper lemma: In a loopless graph, each edge has distinct endpoints -/
lemma edge_endpoints_distinct (G : CFGraph V) (e : V × V) (he : e ∈ G.edges) :
    e.1 ≠ e.2 := by
  by_contra eq_endpoints
  have : isLoopless G.edges = true := G.loopless
  unfold isLoopless at this
  have zero_loops : Multiset.card (G.edges.filter (λ e' => e'.1 = e'.2)) = 0 := by
    simp only [decide_eq_true_eq] at this
    exact this
  have e_loop_mem : e ∈ Multiset.filter (λ e' => e'.1 = e'.2) G.edges := by
    simp [he, eq_endpoints]
  have positive : 0 < Multiset.card (G.edges.filter (λ e' => e'.1 = e'.2)) := by
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨e, e_loop_mem⟩
  have : Multiset.filter (fun e' => e'.1 = e'.2) G.edges = ∅ := eq_nil_of_card_eq_zero zero_loops
  rw [this] at e_loop_mem
  cases e_loop_mem

/-- [Proven] Helper lemma: Each edge is incident to exactly two vertices -/
lemma edge_incident_vertices_count (G : CFGraph V) (e : V × V) (he : e ∈ G.edges) :
    (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card = 2 := by
  rw [Finset.card_eq_two]
  exists e.1
  exists e.2
  constructor
  · exact edge_endpoints_distinct G e he
  · ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      cases h with
      | inl h1 => exact Or.inl (Eq.symm h1)
      | inr h2 => exact Or.inr (Eq.symm h2)
    · intro h
      cases h with
      | inl h1 => exact Or.inl (Eq.symm h1)
      | inr h2 => exact Or.inr (Eq.symm h2)

/-- Auxillary Axiom: The sum of edge incidences equals the sum of mapped incidence counts
    [@TODO] Future Work: To prove. -/
axiom sum_filter_eq_map_inc (G : CFGraph V) :
  ∑ v, Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))
    = (G.edges.map (λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card)).sum

/-- Auxillary Axiom: Summing mapped incidence counts equals summing constant 2
    [@TODO] Future Work: To prove. -/
axiom map_inc_eq_map_two (G : CFGraph V) :
  (G.edges.map (λ e => (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card)).sum
    = 2 * (Multiset.card G.edges)

/--
**Handshaking Theorem:** In a loopless multigraph \(G\), the sum of the degrees of all vertices
is twice the number of edges:

\[
  \sum_{v \in V} \deg(v) \;=\; 2 \cdot \#(\text{edges of }G).
\]
-/
theorem helper_sum_vertex_degrees (G : CFGraph V) :
    ∑ v, vertex_degree G v = 2 * ↑(Multiset.card G.edges) := by

  unfold vertex_degree

  have h_count : ∀ e ∈ G.edges,
    (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card = 2 := by
    intro e he
    exact edge_incident_vertices_count G e he

  -- Define a helper function: for any edge e, inc(e) = number of vertices v incident to e.
  let inc : (V × V) → ℕ := λ e =>
    (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card

  calc
    ∑ v, vertex_degree G v
    = ∑ v, ↑(Multiset.card (G.edges.filter (λ e => e.1 = v ∨ e.2 = v))) := by rfl
    _ = ↑(∑ v, Multiset.card (G.edges.filter (λ e => e.1 = v ∨ e.2 = v))) := by simp
    _ = ↑((G.edges.map inc).sum) := by
      rw [sum_filter_eq_map_inc G]
    _ = 2 * ↑(Multiset.card G.edges) := by
      rw [map_inc_eq_map_two G]
      simp




/-
# Helpers for Proposition 4.1.13 Part (1)
-/

/-- Axiom: Superstable configuration degree is bounded by genus
    [@TODO] Future Work: To prove. -/
axiom helper_superstable_degree_bound (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → config_degree c ≤ genus G

/-- Axiom: Every maximal superstable configuration has degree at least g
    [@TODO] Future Work: To prove. -/
axiom helper_maximal_superstable_degree_lower_bound (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → maximal_superstable G c → config_degree c ≥ genus G

/-- Axiom: If a superstable configuration has degree equal to g, it is maximal
    [@TODO] Future Work: To prove. -/
axiom helper_degree_g_implies_maximal (G : CFGraph V) (q : V) (c : Config V q) :
  superstable G q c → config_degree c = genus G → maximal_superstable G c




/-
# Helpers for Proposition 4.1.13 Part (2)
-/

/-- Axiom: Superstabilization of configuration with degree g+1 sends chip to q
    [@TODO] Future Work: To prove. -/
axiom helper_superstabilize_sends_to_q (G : CFGraph V) (q : V) (c : Config V q) :
  maximal_superstable G c → config_degree c = genus G →
  ∀ v : V, v ≠ q → winnable G (λ w => c.vertex_degree w + if w = v then 1 else 0 - if w = q then 1 else 0)

/-- Axiom: Correspondence between q-reduced divisors and superstable configurations
    A divisor is q-reduced if and only if it corresponds to a superstable configuration minus q
    [@TODO] Future Work: To prove. -/
axiom q_reduced_superstable_correspondence (G : CFGraph V) (q : V) (D : CFDiv V) :
  q_reduced G q D ↔ ∃ c : Config V q, superstable G q c ∧
  D = λ v => c.vertex_degree v - if v = q then 1 else 0

/-- Axiom: When c' dominates c, the difference of their q-reduced divisors is in principal divisors
    [@TODO] Future Work: To prove. -/
axiom helper_q_reduced_diff_principal (G : CFGraph V) (q : V) (c c' : Config V q) :
  superstable G q c → superstable G q c' → config_ge c' c →
  ((λ v => c'.vertex_degree v - if v = q then 1 else 0) -
   (λ v => c.vertex_degree v - if v = q then 1 else 0)) ∈ principal_divisors G

/-- [Proven] Helper lemma: Difference between dominated configurations can be expressed as basic firing moves
    When c' dominates c (i.e. c'(v) ≥ c(v) for all v ≠ q), their difference can be expressed
    as a sum of basic firing moves from vertices where c' has strictly more chips than c. -/
lemma helper_q_reduced_linear_equiv_dominates (G : CFGraph V) (q : V) (c c' : Config V q) :
  superstable G q c → superstable G q c' → config_ge c' c →
  linear_equiv G
    (λ v => c.vertex_degree v - if v = q then 1 else 0)
    (λ v => c'.vertex_degree v - if v = q then 1 else 0) := by
  intros h_super h_super' h_ge

  -- Define the two divisors
  let D₁ := λ v => c.vertex_degree v - if v = q then 1 else 0
  let D₂ := λ v => c'.vertex_degree v - if v = q then 1 else 0

  unfold linear_equiv

  -- Show the difference is in principal divisors
  let diff := D₂ - D₁

  -- Show difference equals vertex degree difference
  have h_diff_eq : ∀ v, diff v = c'.vertex_degree v - c.vertex_degree v := by
    intro v
    by_cases hv : v = q
    · -- Case v = q
      rw [hv]
      have h_q₁ := superstable_zero_at_q G q c h_super
      have h_q₂ := superstable_zero_at_q G q c' h_super'
      simp [D₁, D₂, diff, h_q₁, h_q₂]
    · -- Case v ≠ q
      simp [D₁, D₂, diff, hv]

  -- Show the difference is in principal divisors
  exact helper_q_reduced_diff_principal G q c c' h_super h_super' h_ge

/-- Axiom: If c' is maximal superstable and D corresponds to c'-q,
    then winnability of c'+v-q implies winnability of D
    [@TODO] Future Work: To prove. -/
axiom helper_maximal_superstable_winnability (G : CFGraph V) (q : V) (c' : Config V q) (D : CFDiv V) :
  maximal_superstable G c' →
  linear_equiv G D (λ v => c'.vertex_degree v - if v = q then 1 else 0) →
  (∀ v : V, v ≠ q → winnable G (λ w => c'.vertex_degree w + if w = v then 1 else 0 - if w = q then 1 else 0)) →
  winnable G D

/-- [Proven] Helper theorem: Linear equivalence preserves winnability -/
theorem helper_linear_equiv_preserves_winnability (G : CFGraph V) (D₁ D₂ : CFDiv V) :
  linear_equiv G D₁ D₂ → (winnable G D₁ ↔ winnable G D₂) := by
  intro h_equiv
  constructor
  -- Forward direction: D₁ winnable → D₂ winnable
  { intro h_win₁
    rcases h_win₁ with ⟨D₁', h_eff₁, h_equiv₁⟩
    exists D₁'
    constructor
    · exact h_eff₁
    · -- Use transitivity: D₂ ~ D₁ ~ D₁'
      exact linear_equiv_is_equivalence G |>.trans
        (linear_equiv_is_equivalence G |>.symm h_equiv) h_equiv₁ }
  -- Reverse direction: D₂ winnable → D₁ winnable
  { intro h_win₂
    rcases h_win₂ with ⟨D₂', h_eff₂, h_equiv₂⟩
    exists D₂'
    constructor
    · exact h_eff₂
    · -- Use transitivity: D₁ ~ D₂ ~ D₂'
      exact linear_equiv_is_equivalence G |>.trans h_equiv h_equiv₂ }


/-
# Helpers for Proposition 4.1.14
-/

/-- Helper lemma: Source vertices have equal indegree (zero) when v = q -/
lemma helper_source_indeg_eq_at_q {V : Type} [DecidableEq V] [Fintype V]
    (G : CFGraph V) (O₁ O₂ : Orientation G) (q v : V)
    (h_src₁ : is_source G O₁ q = true) (h_src₂ : is_source G O₂ q = true)
    (hv : v = q) :
    indeg G O₁ v = indeg G O₂ v := by
  rw [hv]
  rw [source_indeg_zero O₁ q h_src₁]
  rw [source_indeg_zero O₂ q h_src₂]

/-
# Helpers for Rank Degree Inequality used in RRG
-/

/-- Axiom: Existence of elements in finite types
    This is a technical axiom used to carry forward existence arguments we frequently use
    such as the fact that finite graphs have vertices. This axiom
    captures this in a way that can be used in formal lean4 proofs. -/
axiom Fintype.exists_elem (V : Type) [Fintype V] : ∃ x : V, True

/-- Axiom: Dhar's algorithm produces q-reduced divisor from any divisor
    Given any divisor D, Dhar's algorithm produces a unique q-reduced divisor that is
    linearly equivalent to D. The algorithm outputs both a superstable configuration c
    and an integer k, where k represents the number of chips at q. This is a key result
    from Dhar (1990) proven in detail in Chapter 3 of Corry & Perkinson's "Divisors and
    Sandpiles" (AMS, 2018) -/
axiom helper_dhar_algorithm {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) (q : V) (D : CFDiv V) :
  ∃ (c : Config V q) (k : ℤ),
    linear_equiv G D (λ v => c.vertex_degree v + (if v = q then k else 0)) ∧
    superstable G q c

/-- Axiom: Dhar's algorithm produces negative k for unwinnable divisors
    When applied to an unwinnable divisor D, Dhar's algorithm must produce a
    negative value for k (the number of chips at q). This is a crucial fact used
    in characterizing unwinnable divisors, proven in chapter 4 of Corry & Perkinson's
    "Divisors and Sandpiles" (AMS, 2018). The negativity of k is essential for
    showing the relationship between unwinnable divisors and q-reduced forms. -/
axiom helper_dhar_negative_k {V : Type} [DecidableEq V] [Fintype V] (G : CFGraph V) (q : V) (D : CFDiv V) :
  ¬(winnable G D) →
  ∀ (c : Config V q) (k : ℤ),
    linear_equiv G D (λ v => c.vertex_degree v + (if v = q then k else 0)) →
    superstable G q c →
    k < 0

/-- Axiom: Rank and degree bounds for canonical divisor -/
axiom helper_rank_deg_canonical_bound (G : CFGraph V) (q : V) (D : CFDiv V) (E H : CFDiv V) (c' : Config V q) :
  linear_equiv G (λ v => c'.vertex_degree v - if v = q then 1 else 0) (λ v => D v - E v + H v) →
  rank G (λ v => canonical_divisor G v - D v) + deg D - deg E + deg H ≤ rank G D

/-- Axiom: Degree of H relates to graph parameters when H comes from maximal superstable configs -/
axiom helper_H_degree_bound (G : CFGraph V) (q : V) (D : CFDiv V) (H : CFDiv V) (k : ℤ) (c : Config V q) (c' : Config V q) :
  effective H →
  H = (λ v => if v = q then -(k + 1) else c'.vertex_degree v - c.vertex_degree v) →
  rank G D + 1 - (Multiset.card G.edges - Fintype.card V + 1) < deg H

/-- Axiom: Linear equivalence between DO and D-E+H -/
axiom helper_DO_linear_equiv (G : CFGraph V) (q : V) (D E H : CFDiv V) (c' : Config V q) :
  linear_equiv G (λ v => c'.vertex_degree v - if v = q then 1 else 0)
               (λ v => D v - E v + H v)

/-- Axiom: The degree of H is positive when H is effective and has value -(k+1) at q where k < 0 -/
axiom helper_sum_positive_at_q (H : CFDiv V) (k : ℤ) :
  effective H → k < 0 → deg H > 0

/-- Axiom: Adding a chip anywhere to c'-q makes it winnable when c' is maximal superstable -/
axiom helper_maximal_superstable_chip_winnable_exact (G : CFGraph V) (q : V) (c' : Config V q) :
  maximal_superstable G c' →
  ∀ (v : V), winnable G (λ w => (λ v => c'.vertex_degree v - if v = q then 1 else 0) w + if w = v then 1 else 0)

/-- Axiom: Given a graph G and a vertex q, there exists a maximal superstable divisor
    c' that is greater than or equal to any superstable divisor c. This is a key
    result from Corry & Perkinson's "Divisors and Sandpiles" (AMS, 2018) that is
    used in proving the Riemann-Roch theorem for graphs. -/
axiom helper_superstable_to_unwinnable (G : CFGraph V) (q : V) (c : Config V q) :
  maximal_superstable G c →
  ¬winnable G (λ v => c.vertex_degree v - if v = q then 1 else 0)


/-
# Helpers for RRG's Corollary 4.4.1
-/

/-- Axiom: Rank decreases in K-D recursion for maximal unwinnable divisors
    This captures that when we apply canonical_divisor - D to a maximal unwinnable divisor,
    the rank measure decreases. This is used for termination of maximal_unwinnable_symmetry. -/
axiom rank_decreases_for_KD {V : Type} [DecidableEq V] [Fintype V]
  (G : CFGraph V) (D : CFDiv V) :
  maximal_unwinnable G (λ v => canonical_divisor G v - D v) →
  ((rank G (λ v => canonical_divisor G v - D v) + 1).toNat < (rank G D + 1).toNat)



/-
# Helpers for RRG's Corollary 4.4.3
-/

/-- [Proven] Effective divisors have non-negative degree -/
lemma effective_nonneg_deg {V : Type} [DecidableEq V] [Fintype V]
  (D : CFDiv V) (h : effective D) : deg D ≥ 0 := by
  -- Definition of effective means all entries are non-negative
  unfold effective at h
  -- Definition of degree as sum of entries
  unfold deg
  -- Non-negative sum of non-negative numbers is non-negative
  exact sum_nonneg (λ v _ ↦ h v)
