import PassK.FiniteTail

/-!
# Uniform mixtures of full-response policies

An online-to-batch learner samples ONE snapshot uniformly and then draws
its entire tuple from that snapshot.  Mixing tuple distributions this way
retains dependence among responses; it is not the product of marginal
mixtures.

This module formalizes the finite-dimensional probability construction
and the exact linearity of expectations and pass@k values. It does not
prove sample independence or the conditional moment estimate.
-/

noncomputable section

namespace PassK.Finite

variable {Ω : Type*} [Fintype Ω]

/-- Uniform mixture of `m` laws. The index is sampled once, not once
for each coordinate of a multi-response output. -/
def uniformMixture (m : ℕ) (hm : 0 < m)
    (p : Fin m → FiniteDistribution Ω) : FiniteDistribution Ω where
  prob := fun ω => (∑ t : Fin m, (p t).prob ω) / (m : ℝ)
  nonneg := by
    intro ω
    exact div_nonneg
      (Finset.sum_nonneg (fun t _ => (p t).nonneg ω))
      (Nat.cast_nonneg _)
  total := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    calc
      (∑ ω : Ω, (∑ t : Fin m, (p t).prob ω) / (m : ℝ))
          = (∑ ω : Ω, ∑ t : Fin m, (p t).prob ω) / (m : ℝ) := by
            rw [Finset.sum_div]
      _ = (∑ t : Fin m, ∑ ω : Ω, (p t).prob ω) / (m : ℝ) := by
            rw [Finset.sum_comm]
      _ = (m : ℝ) / (m : ℝ) := by
            have htotal (t : Fin m) :
                (∑ ω : Ω, (p t).prob ω) = 1 := (p t).total
            simp [htotal]
      _ = 1 := div_self hm0

/-- Expectation under a uniform mixture is the average of the
expectations.  No independence hypotheses are needed. -/
theorem expectedValue_uniformMixture
    (m : ℕ) (hm : 0 < m) (p : Fin m → FiniteDistribution Ω)
    (Z : Ω → ℝ) :
    expectedValue (uniformMixture m hm p) Z =
      (∑ t : Fin m, expectedValue (p t) Z) / (m : ℝ) := by
  unfold expectedValue
  change (∑ ω : Ω, ((∑ t : Fin m, (p t).prob ω) / (m : ℝ)) * Z ω) =
    (∑ t : Fin m, ∑ ω : Ω, (p t).prob ω * Z ω) / (m : ℝ)
  calc
    (∑ ω : Ω, (∑ t : Fin m, (p t).prob ω) / (m : ℝ) * Z ω)
        = (∑ ω : Ω, ∑ t : Fin m, (p t).prob ω * Z ω) / (m : ℝ) := by
          rw [Finset.sum_div]
          congr 1
          funext ω
          rw [← Finset.sum_mul]
          ring
    _ = (∑ t : Fin m, ∑ ω : Ω, (p t).prob ω * Z ω) / (m : ℝ) := by
          rw [Finset.sum_comm]

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Mixture of full `Fin k → Y` tuple policies, at each context. -/
def averagedPolicy {k : ℕ} (m : ℕ) (hm : 0 < m)
    (snapshots : Fin m → X → FiniteDistribution (Fin k → Y)) :
    X → FiniteDistribution (Fin k → Y) :=
  fun x => uniformMixture m hm (fun t => snapshots t x)

/-- The pass@k value of the mixture is the average pass@k value.
In particular, this statement holds when the k responses within each
snapshot's tuple are arbitrarily dependent. -/
theorem passKValue_averagedPolicy {k : ℕ}
    (m : ℕ) (hm : 0 < m)
    (contexts : FiniteDistribution X)
    (snapshots : Fin m → X → FiniteDistribution (Fin k → Y))
    (r : X → Y → NNReal) :
    passKValue contexts (averagedPolicy m hm snapshots) r =
      (∑ t : Fin m, passKValue contexts (snapshots t) r) / (m : ℝ) := by
  unfold passKValue
  simp only [averagedPolicy]
  simp_rw [show ∀ x : X,
      (∑ ys : Fin k → Y,
        (uniformMixture m hm (fun t => snapshots t x)).prob ys *
          (bestReward r x ys : ℝ)) =
      (∑ t : Fin m,
        ∑ ys : Fin k → Y, (snapshots t x).prob ys *
          (bestReward r x ys : ℝ)) / (m : ℝ) from
    fun x => expectedValue_uniformMixture m hm
      (fun t => snapshots t x) (fun ys => (bestReward r x ys : ℝ))]
  calc
    (∑ x : X, contexts.prob x *
      ((∑ t : Fin m, ∑ ys : Fin k → Y,
        (snapshots t x).prob ys * (bestReward r x ys : ℝ)) / (m : ℝ)))
        = (∑ x : X, ∑ t : Fin m,
            contexts.prob x *
              (∑ ys : Fin k → Y,
                (snapshots t x).prob ys * (bestReward r x ys : ℝ))) /
            (m : ℝ) := by
              rw [Finset.sum_div]
              congr 1
              funext x
              rw [← Finset.mul_sum]
              ring
    _ = (∑ t : Fin m, ∑ x : X,
          contexts.prob x *
            (∑ ys : Fin k → Y,
              (snapshots t x).prob ys * (bestReward r x ys : ℝ))) /
            (m : ℝ) := by
              rw [Finset.sum_comm]

/-- The demonstrator's value remains fixed, so the signed excess value
of the averaged policy is the mean of the snapshot excess values. -/
theorem excess_averagedPolicy {k : ℕ}
    (m : ℕ) (hm : 0 < m)
    (contexts : FiniteDistribution X) (demo : X → FiniteDistribution Y)
    (snapshots : Fin m → X → FiniteDistribution (Fin k → Y))
    (r : X → Y → NNReal) :
    excess contexts demo (averagedPolicy m hm snapshots) r =
      (∑ t : Fin m, excess contexts demo (snapshots t) r) / (m : ℝ) := by
  unfold excess
  rw [passKValue_averagedPolicy]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp [hm0] <;> ring

end PassK.Finite
