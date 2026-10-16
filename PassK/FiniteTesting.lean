import PassK.FiniteTail

/-!
# Finite two-point testing bound

This is the nonasymptotic testing reduction used in Le Cam-style
minimax arguments.  It is a substantive lower-bound ingredient, but does
NOT construct the specific hard distributions required for the paper's
sample-complexity results.

For laws `p₀,p₁` and a randomized test `q : Ω → [0,1]` encoded as
`0 ≤ q ω ≤ 1`, the sum of both testing errors is at least the
probability overlap `∑ ω, min (p₀ ω) (p₁ ω)`.
-/

noncomputable section

namespace PassK.Finite

variable {Ω : Type*} [Fintype Ω]

/-- Overlap of two discrete probability distributions. -/
def distributionOverlap (p₀ p₁ : FiniteDistribution Ω) : ℝ :=
  ∑ ω : Ω, min (p₀.prob ω) (p₁.prob ω)

/-- The overlap is nonnegative. -/
theorem distributionOverlap_nonneg (p₀ p₁ : FiniteDistribution Ω) :
    0 ≤ distributionOverlap p₀ p₁ := by
  unfold distributionOverlap
  apply Finset.sum_nonneg
  intro ω _
  exact le_min (p₀.nonneg ω) (p₁.nonneg ω)

/-- Overlap is at most one. -/
theorem distributionOverlap_le_one (p₀ p₁ : FiniteDistribution Ω) :
    distributionOverlap p₀ p₁ ≤ 1 := by
  unfold distributionOverlap
  calc
    (∑ ω : Ω, min (p₀.prob ω) (p₁.prob ω))
        ≤ ∑ ω : Ω, p₀.prob ω := by
          apply Finset.sum_le_sum
          intro ω _
          exact min_le_left _ _
    _ = 1 := p₀.total

/-- The overlap is symmetric. -/
theorem distributionOverlap_comm (p₀ p₁ : FiniteDistribution Ω) :
    distributionOverlap p₀ p₁ = distributionOverlap p₁ p₀ := by
  unfold distributionOverlap
  apply Finset.sum_congr rfl
  intro ω _
  exact min_comm _ _

/-- Every randomized binary test has combined error at least the
probability overlap of the two laws.  `q ω` is the chance of selecting
hypothesis zero; the two error probabilities are `E₀[1-q]` and `E₁[q]`. -/
theorem distributionOverlap_le_testing_error
    (p₀ p₁ : FiniteDistribution Ω) (q : Ω → ℝ)
    (hq₀ : ∀ ω, 0 ≤ q ω) (hq₁ : ∀ ω, q ω ≤ 1) :
    distributionOverlap p₀ p₁ ≤
      expectedValue p₀ (fun ω => 1 - q ω) + expectedValue p₁ q := by
  unfold distributionOverlap expectedValue
  calc
    (∑ ω : Ω, min (p₀.prob ω) (p₁.prob ω))
        ≤ ∑ ω : Ω, (p₀.prob ω * (1 - q ω) + p₁.prob ω * q ω) := by
          apply Finset.sum_le_sum
          intro ω _
          rcases le_total (p₀.prob ω) (p₁.prob ω) with h | h
          · rw [min_eq_left h]
            have hprod : 0 ≤ (p₁.prob ω - p₀.prob ω) * q ω :=
              mul_nonneg (sub_nonneg.mpr h) (hq₀ ω)
            nlinarith
          · rw [min_eq_right h]
            have hprod : 0 ≤ (p₀.prob ω - p₁.prob ω) * (1 - q ω) :=
              mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (hq₁ ω))
            nlinarith
    _ = (∑ ω : Ω, p₀.prob ω * (1 - q ω)) +
        (∑ ω : Ω, p₁.prob ω * q ω) := by
          rw [Finset.sum_add_distrib]

/-- At least one of the two testing errors is at least half the
probability overlap. -/
theorem half_overlap_le_max_testing_error
    (p₀ p₁ : FiniteDistribution Ω) (q : Ω → ℝ)
    (hq₀ : ∀ ω, 0 ≤ q ω) (hq₁ : ∀ ω, q ω ≤ 1) :
    distributionOverlap p₀ p₁ / 2 ≤
      max (expectedValue p₀ (fun ω => 1 - q ω)) (expectedValue p₁ q) := by
  have h := distributionOverlap_le_testing_error p₀ p₁ q hq₀ hq₁
  have h₀ : expectedValue p₀ (fun ω => 1 - q ω) ≤
      max (expectedValue p₀ (fun ω => 1 - q ω)) (expectedValue p₁ q) :=
    le_max_left _ _
  have h₁ : expectedValue p₁ q ≤
      max (expectedValue p₀ (fun ω => 1 - q ω)) (expectedValue p₁ q) :=
    le_max_right _ _
  linarith

/-- Two identical sampling laws have overlap one, forcing testing
error at least one-half in one of the two worlds. -/
theorem identical_laws_half_testing_error
    (p : FiniteDistribution Ω) (q : Ω → ℝ)
    (hq₀ : ∀ ω, 0 ≤ q ω) (hq₁ : ∀ ω, q ω ≤ 1) :
    (1 / 2 : ℝ) ≤
      max (expectedValue p (fun ω => 1 - q ω)) (expectedValue p q) := by
  have hident : distributionOverlap p p = 1 := by
    unfold distributionOverlap
    simpa using p.total
  simpa [hident] using half_overlap_le_max_testing_error p p q hq₀ hq₁

end PassK.Finite
