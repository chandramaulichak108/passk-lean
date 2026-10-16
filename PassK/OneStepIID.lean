import PassK.Values

/-!
# One-round conditional-value identity (finite spaces)

For a learner snapshot fixed before the next example, the demonstrator
response and the learner's full k-tuple are sampled according to their
respective kernels at an independent fresh context. The expected signed
round regret equals the population excess of the snapshot.

This module proves the *one-round algebraic identity*. A complete
online-to-batch theorem still needs the i.i.d. law of sample histories,
measurability/adaptedness of snapshots and iterated conditioning.
-/

noncomputable section

namespace PassK.Finite

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Expected one-round signed regret for a fixed policy snapshot.
The demonstrator and tuple draws are conditionally independent given
`x`, and the distribution of tuples can have arbitrary dependence
between its coordinates. -/
def oneStepExpectedRegret {k : ℕ}
    (contexts : FiniteDistribution X)
    (demo : X → FiniteDistribution Y)
    (snapshot : X → FiniteDistribution (Fin k → Y))
    (r : X → Y → NNReal) : ℝ :=
  ∑ x : X, contexts.prob x *
    (∑ y : Y, (demo x).prob y *
      (∑ ys : Fin k → Y, (snapshot x).prob ys *
        ((r x y : ℝ) - (bestReward r x ys : ℝ))))

/-- Conditional round regret equals population excess of the same
snapshot, including for dependent tuple coordinates. -/
theorem oneStepExpectedRegret_eq_excess {k : ℕ}
    (contexts : FiniteDistribution X)
    (demo : X → FiniteDistribution Y)
    (snapshot : X → FiniteDistribution (Fin k → Y))
    (r : X → Y → NNReal) :
    oneStepExpectedRegret contexts demo snapshot r =
      excess contexts demo snapshot r := by
  have hinner (x : X) (y : Y) :
      (∑ ys : Fin k → Y, (snapshot x).prob ys *
        ((r x y : ℝ) - (bestReward r x ys : ℝ))) =
      (r x y : ℝ) -
        (∑ ys : Fin k → Y, (snapshot x).prob ys *
          (bestReward r x ys : ℝ)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
        (snapshot x).total, one_mul]
  have houter (x : X) :
      (∑ y : Y, (demo x).prob y *
        ((r x y : ℝ) -
          (∑ ys : Fin k → Y, (snapshot x).prob ys *
            (bestReward r x ys : ℝ)))) =
      (∑ y : Y, (demo x).prob y * (r x y : ℝ)) -
        (∑ ys : Fin k → Y, (snapshot x).prob ys *
          (bestReward r x ys : ℝ)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
        (demo x).total, one_mul]
  unfold oneStepExpectedRegret excess demonstratorValue passKValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  calc
    contexts.prob x *
      (∑ y : Y, (demo x).prob y *
        (∑ ys : Fin k → Y, (snapshot x).prob ys *
          ((r x y : ℝ) - (bestReward r x ys : ℝ))))
        = contexts.prob x *
            (∑ y : Y, (demo x).prob y *
              ((r x y : ℝ) -
                (∑ ys : Fin k → Y, (snapshot x).prob ys *
                  (bestReward r x ys : ℝ)))) := by
            congr 1
            apply Finset.sum_congr rfl
            intro y _
            rw [hinner x y]
    _ = contexts.prob x *
          ((∑ y : Y, (demo x).prob y * (r x y : ℝ)) -
            (∑ ys : Fin k → Y, (snapshot x).prob ys *
              (bestReward r x ys : ℝ))) := by
          rw [houter x]
    _ = contexts.prob x *
          (∑ y : Y, (demo x).prob y * (r x y : ℝ)) -
        contexts.prob x *
          (∑ ys : Fin k → Y, (snapshot x).prob ys *
            (bestReward r x ys : ℝ)) := by
          ring

end PassK.Finite
