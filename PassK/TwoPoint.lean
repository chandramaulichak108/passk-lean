import PassK.LowerBounds

/-!
# A genuinely proved two-world lower-bound example

With no informative observation, suppose an algorithm places probability
`p` on response 0. If the correct answer is respectively 0 or 1 in two
indistinguishable worlds, the losses are `1-p` and `p`. One of the two
losses is at least 1/2. This is a concrete two-point obstruction, not
the manuscript's finite-sample Fano/Assouad minimax rate.
-/

namespace PassK.FiniteGame

/-- An uninformed randomized choice cannot have error less than 1/2
in both of two conflicting worlds. -/
theorem two_point_no_information (p : ℝ) :
    (1 / 2 : ℝ) ≤ max p (1 - p) := by
  rcases le_total (1 / 2 : ℝ) p with h | h
  · exact h.trans (le_max_left _ _)
  · have h' : (1 / 2 : ℝ) ≤ 1 - p := by linarith
    exact h'.trans (le_max_right _ _)

/-- The simple lower bound is sharp for equal randomization. -/
theorem two_point_balanced :
    max (1 / 2 : ℝ) (1 - 1 / 2) = 1 / 2 := by
  norm_num

end PassK.FiniteGame
