import PassK.Definitions
import PassK.OnlineRegret

/-!
# Standard and robust upper-bound interfaces

This file proves that a robust finite-class bound implies each fixed
reward bound and that controlling every reward is equivalent to
controlling their finite supremum.

These deterministic implications are NOT the paper's statistical
high-probability theorems. Proving those theorems additionally requires
formalized sample distributions, learning rules, and tail bounds.
-/

namespace PassK.Finite

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A robust guarantee entails every standard fixed-reward guarantee. -/
theorem robustGood_implies_standardGood {k : ℕ}
    (rewards : Finset (X → Y → NNReal)) (hne : rewards.Nonempty)
    (contexts : FiniteDistribution X) (demo : X → FiniteDistribution Y)
    (policy : X → FiniteDistribution (Fin k → Y)) (ε : ℝ)
    (hrobust : RobustGood rewards hne contexts demo policy ε)
    (r : X → Y → NNReal) (hr : r ∈ rewards) :
    StandardGood contexts demo policy r ε := by
  exact (excess_le_robust rewards hne contexts demo policy r hr).trans hrobust

/-- In a finite reward class, robust excess is no more than ε exactly
when each of its constituent signed excess values is no more than ε. -/
theorem robustGood_iff_forall_standardGood {k : ℕ}
    (rewards : Finset (X → Y → NNReal)) (hne : rewards.Nonempty)
    (contexts : FiniteDistribution X) (demo : X → FiniteDistribution Y)
    (policy : X → FiniteDistribution (Fin k → Y)) (ε : ℝ) :
    RobustGood rewards hne contexts demo policy ε ↔
      ∀ r ∈ rewards, StandardGood contexts demo policy r ε := by
  constructor
  · intro hrobust r hr
    exact robustGood_implies_standardGood rewards hne contexts demo policy
      ε hrobust r hr
  · intro hall
    unfold RobustGood robustExcess
    apply Finset.sup'_le hne
    intro r hr
    exact hall r hr

end PassK.Finite
