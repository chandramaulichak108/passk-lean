import PassK.LowerBounds
import PassK.Stage4LeCam

/-!
# Stage 5: combining upper and lower minimax bounds

The main theorem of a minimax analysis combines a hard-instance lower
bound with an explicit learner's upper bound. The following finite-game
result formalizes that *combination*, including the need for an actual
adversarial witness for every algorithm. It is not a proof that the
paper's particular hard families satisfy these premises.
-/

namespace PassK.FiniteGame

variable {Alg Instance : Type*}

/-- When an algorithm uniformly incurs loss at most `C`, the minimax
risk is at most `C` (provided the algorithm is admissible). -/
theorem minimax_upper_bound_of_algorithm
    (algorithms : Finset Alg) (hA : algorithms.Nonempty)
    (instances : Finset Instance) (hI : instances.Nonempty)
    (loss : Alg → Instance → ℝ) (C : ℝ)
    (algorithm : Alg) (halg : algorithm ∈ algorithms)
    (hgood : ∀ instance₀ ∈ instances, loss algorithm instance₀ ≤ C) :
    minimaxRisk algorithms hA instances hI loss ≤ C := by
  have hmax : worstCaseLoss instances hI loss algorithm ≤ C := by
    unfold worstCaseLoss
    apply Finset.sup'_le hI
    intro instance₀ hi
    exact hgood instance₀ hi
  exact (minimax_le_algorithm_worstCase algorithms hA instances hI
    loss algorithm halg).trans hmax

/-- Precise sandwich from a hard-instance family and a uniformly good
learning rule. The lower and upper hypotheses are intentionally *not*
assumed equal, and neither is manufactured by the conclusion. -/
theorem minimax_sandwich
    (algorithms : Finset Alg) (hA : algorithms.Nonempty)
    (instances : Finset Instance) (hI : instances.Nonempty)
    (loss : Alg → Instance → ℝ) (c C : ℝ)
    (hard : ∀ algorithm ∈ algorithms,
      ∃ instance₀ ∈ instances, c ≤ loss algorithm instance₀)
    (goodAlgorithm : Alg) (hgoodAlg : goodAlgorithm ∈ algorithms)
    (hgood : ∀ instance₀ ∈ instances,
      loss goodAlgorithm instance₀ ≤ C) :
    c ≤ minimaxRisk algorithms hA instances hI loss ∧
      minimaxRisk algorithms hA instances hI loss ≤ C := by
  constructor
  · exact minimax_lower_bound algorithms hA instances hI loss c hard
  · exact minimax_upper_bound_of_algorithm algorithms hA instances hI
      loss C goodAlgorithm hgoodAlg hgood

/-- Combining two nonnegative obstructions loses at most a factor two.
Used in the manuscript to combine class-size and confidence terms. -/
theorem half_sum_le_max (a b : ℝ) : (a + b) / 2 ≤ max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

/-- If either of two hard-instance arguments applies, the larger
lower-bound term gives at least half their sum. -/
theorem additive_lower_bound_from_max (risk a b : ℝ)
    (ha : a ≤ risk) (hb : b ≤ risk) :
    (a + b) / 2 ≤ risk := by
  exact (half_sum_le_max a b).trans (max_le ha hb)

end PassK.FiniteGame
