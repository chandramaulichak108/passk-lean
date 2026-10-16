import PassK.Coverage

/-!
# Greedy-coverage lemma derived from a finite candidate family

`PassK.Coverage` proves the full weighted set algebra and the potential
change identity. This file bridges the greedy `max over candidate sets`
condition to the premise used in that theorem.

The candidate family must contain the demonstration's coverage set.
This is the reduction used in Section 3 of the paper.
-/

namespace PassK

variable {α : Type*} [DecidableEq α]

/-- Greedy optimality among an admissible family implies the per-step
comparison with the demonstration. -/
theorem greedy_premise_from_candidates
    (w : α → ℝ) (A : ℕ → Finset α) (D : Finset α)
    (candidates : Finset (Finset α)) (k : ℕ)
    (hD : D ∈ candidates)
    (hmax : ∀ i < k, ∀ C ∈ candidates,
      weight w (C \ coveragePrefix A i) ≤ weight w (A i \ coveragePrefix A i)) :
    ∀ i < k,
      weight w (D \ coveragePrefix A i) ≤ weight w (A i \ coveragePrefix A i) := by
  intro i hi
  exact hmax i hi D hD

/-- The weighted pass@k comparison from exact greedy selection. -/
theorem greedy_weight_comparison_of_maximality
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (A : ℕ → Finset α) (D : Finset α)
    (candidates : Finset (Finset α)) (k : ℕ)
    (hD : D ∈ candidates)
    (hmax : ∀ i < k, ∀ C ∈ candidates,
      weight w (C \ coveragePrefix A i) ≤ weight w (A i \ coveragePrefix A i)) :
    (k : ℝ) * weight w (D \ coveragePrefix A k) ≤
      weight w (coveragePrefix A k \ D) := by
  apply greedy_weight_comparison w hw A D k
  exact greedy_premise_from_candidates w A D candidates k hD hmax

section FiniteUniverse

variable [Fintype α]

/-- Exact greedy selection yields a non-increasing weight potential
for one round of the multiplicative update. -/
theorem greedy_total_le_of_maximality
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (A : ℕ → Finset α) (D : Finset α)
    (candidates : Finset (Finset α)) (k : ℕ)
    (hD : D ∈ candidates)
    (hmax : ∀ i < k, ∀ C ∈ candidates,
      weight w (C \ coveragePrefix A i) ≤ weight w (A i \ coveragePrefix A i)) :
    weight (update k D (coveragePrefix A k) w) (Finset.univ : Finset α) ≤
      weight w (Finset.univ : Finset α) := by
  exact update_total_le k D (coveragePrefix A k) w
    (greedy_weight_comparison_of_maximality w hw A D candidates k hD hmax)

end FiniteUniverse
end PassK
