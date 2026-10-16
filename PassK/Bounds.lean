import Mathlib

/-!
# Algebraic lemmas used in the pass@k regret analysis

These are deterministic building blocks for the analysis in Section 3:
  * signed-regret decomposition and asymmetric log-weight increments;
  * quantization-to-original-regret error accumulation;
  * the square-root inequality that gives the logarithmic k gain.

This does not formalize the probabilistic exponential-supermartingale
argument or the minimax lower bounds.
-/

namespace PassK

/-- The positive and negative parts give a signed decomposition. -/
theorem signed_parts (z : ℝ) : z = max z 0 - max (-z) 0 := by
  by_cases hz : 0 ≤ z
  · have hn : -z ≤ 0 := by linarith
    rw [max_eq_left hz, max_eq_right hn]
    ring
  · have hn : z ≤ 0 := le_of_lt (lt_of_not_ge hz)
    have hp : 0 ≤ -z := by linarith
    rw [max_eq_right hn, max_eq_left hp]
    ring

/-- Larger upweighting coefficients control *signed* shortfalls, including
    the rounds on which the learner outperforms the demonstrator. -/
theorem signed_increment_bound (a b z : ℝ) (hba : b ≤ a) :
    a * z ≤ a * max z 0 - b * max (-z) 0 := by
  have hn : 0 ≤ max (-z) 0 := le_max_right _ _
  calc
    a * z = a * (max z 0 - max (-z) 0) := by rw [signed_parts z]
    _ = a * max z 0 - a * max (-z) 0 := by ring
    _ ≤ a * max z 0 - b * max (-z) 0 := by
      have hh := mul_le_mul_of_nonneg_right hba hn
      linarith

/-- Sum of asymmetric increments dominates scaled cumulative signed regret. -/
theorem summed_signed_increment_bound (T : ℕ) (a b : ℝ) (hba : b ≤ a)
    (ell : Fin T → ℝ) :
    a * (∑ t : Fin T, ell t) ≤
      ∑ t : Fin T, (a * max (ell t) 0 - b * max (-(ell t)) 0) := by
  calc
    a * (∑ t : Fin T, ell t) = ∑ t : Fin T, a * ell t := by
      rw [Finset.mul_sum]
    _ ≤ ∑ t : Fin T,
        (a * max (ell t) 0 - b * max (-(ell t)) 0) := by
          apply Finset.sum_le_sum
          intro t _
          exact signed_increment_bound a b (ell t) hba

/-- A one-round quantization comparison: the demonstrator is rounded
    down by at most `η`, while rounding the learner down can only
    increase the upper bound on regret. -/
theorem quantization_round (demo learner qDemo qLearner η : ℝ)
    (hdemo : demo ≤ qDemo + η) (hlearner : qLearner ≤ learner) :
    demo - learner ≤ qDemo - qLearner + η := by
  linarith

/-- Accumulating the per-round quantization loss over `T` rounds. -/
theorem quantization_round_sum (T : ℕ) (demo learner qDemo qLearner : Fin T → ℝ)
    (η : ℝ) (h : ∀ t,
      demo t - learner t ≤ qDemo t - qLearner t + η) :
    (∑ t : Fin T, (demo t - learner t)) ≤
      (∑ t : Fin T, (qDemo t - qLearner t)) + (T : ℝ) * η := by
  have hs :
      (∑ t : Fin T, (demo t - learner t)) ≤
        (∑ t : Fin T, (qDemo t - qLearner t + η)) := by
    apply Finset.sum_le_sum
    intro t _
    exact h t
  calc
    (∑ t : Fin T, (demo t - learner t)) ≤
        (∑ t : Fin T, (qDemo t - qLearner t + η)) := hs
    _ = (∑ t : Fin T, (qDemo t - qLearner t)) + (T : ℝ) * η := by
      simp [Finset.sum_add_distrib, nsmul_eq_mul]

/-- The elementary square identity behind `1 + k/4 ≥ √k`.
    Used in the manuscript to obtain the `1/log k` dependence. -/
theorem sqrt_le_one_add_div_four (k : ℕ) :
    Real.sqrt (k : ℝ) ≤ 1 + (k : ℝ) / 4 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hs : (Real.sqrt (k : ℝ)) ^ 2 = (k : ℝ) := Real.sq_sqrt hk
  nlinarith [sq_nonneg (Real.sqrt (k : ℝ) - 2)]

end PassK
