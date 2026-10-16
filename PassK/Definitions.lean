import PassK.Values

/-!
# Definitions corresponding to Section 2 of the paper

This file collects the statistical objectives in a finite setting.
The probability law of the entire `Fin k → Y` response tuple is used;
independence of the k responses is **not** assumed.

This is a finite-space encoding, not a formalization of general
measurable spaces or arbitrary learning rules.
-/

noncomputable section

namespace PassK.Finite

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The best possible reward for one context, taken over all responses.
The finitary supremum is zero if the response type is empty. -/
def pointwiseOptimal (r : X → Y → NNReal) (x : X) : NNReal :=
  (Finset.univ : Finset Y).sup (fun y => r x y)

/-- Population value of a pointwise optimal response. -/
def optimalValue (contexts : FiniteDistribution X)
    (r : X → Y → NNReal) : ℝ :=
  ∑ x : X, contexts.prob x * (pointwiseOptimal r x : ℝ)

/-- Demonstrator suboptimality `Δ_r = V_r^* - V_r(demo)`.
The nonnegativity proof is a separate mathematical obligation. -/
def demonstratorGap (contexts : FiniteDistribution X)
    (demo : X → FiniteDistribution Y) (r : X → Y → NNReal) : ℝ :=
  optimalValue contexts r - demonstratorValue contexts demo r

/-- Standard evaluation: the signed excess is at most `ε` for `r`. -/
def StandardGood {k : ℕ} (contexts : FiniteDistribution X)
    (demo : X → FiniteDistribution Y)
    (policy : X → FiniteDistribution (Fin k → Y))
    (r : X → Y → NNReal) (ε : ℝ) : Prop :=
  excess contexts demo policy r ≤ ε

/-- Robust evaluation: the signed excess is at most `ε` for every reward. -/
def RobustGood {k : ℕ}
    (rewards : Finset (X → Y → NNReal)) (hne : rewards.Nonempty)
    (contexts : FiniteDistribution X) (demo : X → FiniteDistribution Y)
    (policy : X → FiniteDistribution (Fin k → Y)) (ε : ℝ) : Prop :=
  robustExcess rewards hne contexts demo policy ≤ ε

end PassK.Finite
