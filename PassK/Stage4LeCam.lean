import PassK.FiniteTesting

/-!
# Stage 4: a finite Le Cam lower bound in terms of total variation

The paper's minimax lower bounds use several different hard constructions.
Here we derive the exact elementary two-point testing inequality
  max(error at world 0, error at world 1) ≥ (1 - TV(P0,P1))/2.

This is a genuine lower-bound ingredient. It does NOT yet prove the
list-Fano and Assouad constructions needed for the paper's sample rates.
-/

noncomputable section

namespace PassK.Finite

variable {Ω : Type*} [Fintype Ω]

/-- Total variation for explicit laws on a finite sample space. -/
def finiteTotalVariation (p₀ p₁ : FiniteDistribution Ω) : ℝ :=
  (∑ ω : Ω, |p₀.prob ω - p₁.prob ω|) / 2

/-- Minimum of two reals expressed with an absolute value. -/
theorem min_eq_half_add_sub_abs (a b : ℝ) :
    min a b = (a + b - |a - b|) / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The overlap between two probability laws equals `1 - TV`. -/
theorem overlap_eq_one_sub_totalVariation
    (p₀ p₁ : FiniteDistribution Ω) :
    distributionOverlap p₀ p₁ = 1 - finiteTotalVariation p₀ p₁ := by
  have hsum :
      distributionOverlap p₀ p₁ =
        ((∑ ω : Ω, p₀.prob ω) + (∑ ω : Ω, p₁.prob ω) -
          (∑ ω : Ω, |p₀.prob ω - p₁.prob ω|)) / 2 := by
    unfold distributionOverlap
    calc
      (∑ ω : Ω, min (p₀.prob ω) (p₁.prob ω)) =
        ∑ ω : Ω, (p₀.prob ω + p₁.prob ω -
          |p₀.prob ω - p₁.prob ω|) / 2 := by
            apply Finset.sum_congr rfl
            intro ω _
            exact min_eq_half_add_sub_abs _ _
      _ = ((∑ ω : Ω, p₀.prob ω) + (∑ ω : Ω, p₁.prob ω) -
          (∑ ω : Ω, |p₀.prob ω - p₁.prob ω|)) / 2 := by
            rw [← Finset.sum_div, Finset.sum_sub_distrib,
              Finset.sum_add_distrib]
  rw [p₀.total, p₁.total] at hsum
  unfold finiteTotalVariation
  linarith

/-- Le Cam's two-point randomized testing lower bound. The test is
allowed to randomize, and the sample distributions may be arbitrary. -/
theorem le_cam_testing_lower_bound
    (p₀ p₁ : FiniteDistribution Ω) (q : Ω → ℝ)
    (hq₀ : ∀ ω, 0 ≤ q ω) (hq₁ : ∀ ω, q ω ≤ 1) :
    (1 - finiteTotalVariation p₀ p₁) / 2 ≤
      max (expectedValue p₀ (fun ω => 1 - q ω)) (expectedValue p₁ q) := by
  rw [← overlap_eq_one_sub_totalVariation p₀ p₁]
  exact half_overlap_le_max_testing_error p₀ p₁ q hq₀ hq₁

end PassK.Finite
