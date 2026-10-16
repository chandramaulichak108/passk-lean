import PassK.Bounds

/-!
# Algebraic preliminaries

`PassK.Bounds` contains the proofs for the signed-parts decomposition,
signed increments, quantization error accumulation and the elementary
square-root inequality.  This file assembles a useful deterministic
online-to-batch *arithmetic* consequence; no probability argument is
claimed here.
-/

namespace PassK

/-- A deterministic way to combine a bound on quantized regret with
an additive per-round quantization error. -/
theorem original_regret_le_of_quantized
    (T : ℕ) (demo learner qDemo qLearner : Fin T → ℝ)
    (η B : ℝ)
    (hround : ∀ t, demo t - learner t ≤ qDemo t - qLearner t + η)
    (hquant : (∑ t : Fin T, (qDemo t - qLearner t)) ≤ B) :
    (∑ t : Fin T, (demo t - learner t)) ≤ B + (T : ℝ) * η := by
  have hsum := quantization_round_sum T demo learner qDemo qLearner η hround
  linarith only [hsum, hquant]

/-- Controlling signed regret by an asymmetric log-increment budget.
The hypotheses represent the yet-to-be-formalized log-weight calculation. -/
theorem signed_regret_le_of_increment_budget
    (T : ℕ) (a b B : ℝ) (ha : 0 < a) (hba : b ≤ a)
    (ell : Fin T → ℝ)
    (hbudget :
      (∑ t : Fin T,
        (a * max (ell t) 0 - b * max (-(ell t)) 0)) ≤ B) :
    (∑ t : Fin T, ell t) ≤ B / a := by
  have h := (summed_signed_increment_bound T a b hba ell).trans hbudget
  apply (le_div_iff₀ ha).2
  simpa only [mul_comm] using h

end PassK
