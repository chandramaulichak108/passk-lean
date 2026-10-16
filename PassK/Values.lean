import Mathlib

/-!
# Finite-space semantics of pass@k evaluation

A `FiniteDistribution` is an explicit probability mass function.
The pass@k policy is a distribution over the *whole tuple* `Fin k → Y`:
its responses need not be independent.  This matches the evaluation
protocol in Section 2.1 of the manuscript for finite spaces.

Rewards are nonnegative real numbers (`NNReal`); the intended bounded case
adds the assumption `r x y ≤ 1`.  Signed excess values live in `ℝ`.
-/

noncomputable section

namespace PassK
namespace Finite

/-- A discrete probability distribution on a finite type. -/
structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ prob ω
  total : (∑ ω : Ω, prob ω) = 1

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Reward of the best of `k` potentially dependent candidate responses. -/
def bestReward {k : ℕ} (r : X → Y → NNReal) (x : X)
    (ys : Fin k → Y) : NNReal :=
  (Finset.univ : Finset (Fin k)).sup (fun i => r x (ys i))

/-- Any selected response has reward at most the best-of-k reward. -/
theorem reward_le_best {k : ℕ} (r : X → Y → NNReal) (x : X)
    (ys : Fin k → Y) (i : Fin k) :
    r x (ys i) ≤ bestReward r x ys := by
  unfold bestReward
  exact Finset.le_sup
    (s := (Finset.univ : Finset (Fin k)))
    (f := fun j : Fin k => r x (ys j))
    (Finset.mem_univ i)

/-- The pass@k payoff lies in `[0,1]` when every reward does. -/
theorem best_le_one {k : ℕ} (r : X → Y → NNReal)
    (hr : ∀ x y, r x y ≤ 1) (x : X) (ys : Fin k → Y) :
    bestReward r x ys ≤ 1 := by
  unfold bestReward
  apply Finset.sup_le
  intro i _
  exact hr x (ys i)

/-- Single-response value of the demonstrator. -/
def demonstratorValue (contexts : FiniteDistribution X)
    (demo : X → FiniteDistribution Y) (r : X → Y → NNReal) : ℝ :=
  ∑ x : X, contexts.prob x *
    (∑ y : Y, (demo x).prob y * (r x y : ℝ))

/-- Evaluation value of a policy on full `k`-tuples; arbitrary dependence
    between candidates is permitted. -/
def passKValue {k : ℕ} (contexts : FiniteDistribution X)
    (policy : X → FiniteDistribution (Fin k → Y))
    (r : X → Y → NNReal) : ℝ :=
  ∑ x : X, contexts.prob x *
    (∑ ys : (Fin k → Y), (policy x).prob ys * (bestReward r x ys : ℝ))

/-- Signed excess value: demonstrator pass@1 minus learner pass@k. -/
def excess {k : ℕ} (contexts : FiniteDistribution X)
    (demo : X → FiniteDistribution Y)
    (policy : X → FiniteDistribution (Fin k → Y))
    (r : X → Y → NNReal) : ℝ :=
  demonstratorValue contexts demo r - passKValue contexts policy r

/-- Robust excess is the maximum excess over a *nonempty* finite reward class. -/
noncomputable def robustExcess {k : ℕ}
    (rewards : Finset (X → Y → NNReal)) (hne : rewards.Nonempty)
    (contexts : FiniteDistribution X) (demo : X → FiniteDistribution Y)
    (policy : X → FiniteDistribution (Fin k → Y)) : ℝ :=
  rewards.sup' hne (fun r => excess contexts demo policy r)

/-- Fixed-reward excess is bounded above by robust excess. -/
theorem excess_le_robust {k : ℕ}
    (rewards : Finset (X → Y → NNReal)) (hne : rewards.Nonempty)
    (contexts : FiniteDistribution X) (demo : X → FiniteDistribution Y)
    (policy : X → FiniteDistribution (Fin k → Y))
    (r : X → Y → NNReal) (hr : r ∈ rewards) :
    excess contexts demo policy r ≤
      robustExcess rewards hne contexts demo policy := by
  unfold robustExcess
  exact Finset.le_sup' _ hr

end Finite
end PassK
