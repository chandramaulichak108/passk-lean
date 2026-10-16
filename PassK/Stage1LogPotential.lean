import PassK.OnlineRegret

/-!
# Stage 1: the logarithmic potential argument

The paper's deterministic online-regret proof has two parts:
1. Greedy coverage keeps the *sum* of weights from growing (`OnlineRegret`).
2. A log-sum inequality bounds the average log-weight for a fixed reward.

This module proves part 2 directly from `Real.log_le_sub_one_of_pos` and
combines it with the proved total-weight invariant.  The last theorem is
the exact arithmetic online-regret conclusion, conditional on the still-
needed identification of quantized regret with the log-weight increments.
It does not assert that this last hypothesis is automatically satisfied.
-/

noncomputable section

namespace PassK

/-- Elementary log tangent bound: `log x ≤ log N + x/N - 1`. -/
theorem log_le_scaled_tangent (x N : ℝ) (hx : 0 < x) (hN : 0 < N) :
    Real.log x ≤ Real.log N + x / N - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hN)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hN)] at h
  linarith

/-- Finite log-sum bound, the AM--GM step used in the paper.

If positive weights on `s` have arithmetic mean at most `N`, then
`∑ log w ≤ |s| log N`. This statement does not require independence.
-/
theorem sum_log_le_card_log_of_mass
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (N : ℝ)
    (hN : 0 < N) (hw : ∀ i ∈ s, 0 < w i)
    (hmass : (∑ i ∈ s, w i) ≤ (s.card : ℝ) * N) :
    (∑ i ∈ s, Real.log (w i)) ≤
      (s.card : ℝ) * Real.log N := by
  have hsum :
      (∑ i ∈ s, Real.log (w i)) ≤
        ∑ i ∈ s, (Real.log N + w i / N - 1) := by
    apply Finset.sum_le_sum
    intro i hi
    exact log_le_scaled_tangent (w i) N (hw i hi) hN
  have hmean : (∑ i ∈ s, w i) / N ≤ (s.card : ℝ) := by
    apply (div_le_iff₀ hN).2
    simpa only [mul_comm] using hmass
  have heq :
      (∑ i ∈ s, (Real.log N + w i / N - 1)) =
        (s.card : ℝ) * Real.log N +
          (∑ i ∈ s, w i) / N - (s.card : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, Finset.sum_div]
    ring
  rw [heq] at hsum
  linarith

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The log-weight bound for a fixed subset of thresholds, obtained
from the *actual* non-increasing potential, not from a log-budget axiom.

In the intended instantiation `α = R × Fin L`, `J` is the threshold
fiber associated with one reward, and `N` is the number of rewards.
The remaining mass normalization `hinitial` is a finite cardinality fact.
-/
theorem greedy_final_log_bound
    (k : ℕ) (D U : ℕ → Finset α) (w₀ : α → ℝ)
    (hw₀ : ∀ a, 0 < w₀ a)
    (hcoverage : ∀ t,
      (k : ℝ) * weight (weightsAfter k D U w₀ t) (D t \ U t) ≤
      weight (weightsAfter k D U w₀ t) (U t \ D t))
    (J : Finset α) (N : ℝ) (hN : 0 < N)
    (hinitial : weight w₀ (Finset.univ : Finset α) ≤
      (J.card : ℝ) * N)
    (T : ℕ) :
    (∑ j ∈ J, Real.log (weightsAfter k D U w₀ T j)) ≤
      (J.card : ℝ) * Real.log N := by
  have hpos : ∀ j ∈ J, 0 < weightsAfter k D U w₀ T j := by
    intro j _
    exact weightsAfter_pos k D U w₀ hw₀ T j
  have hnonneg : ∀ j, 0 ≤ weightsAfter k D U w₀ T j := by
    intro j
    exact le_of_lt (weightsAfter_pos k D U w₀ hw₀ T j)
  have hmass :
      (∑ j ∈ J, weightsAfter k D U w₀ T j) ≤
        (J.card : ℝ) * N := by
    calc
      (∑ j ∈ J, weightsAfter k D U w₀ T j)
          = weight (weightsAfter k D U w₀ T) J := rfl
      _ ≤ weight (weightsAfter k D U w₀ T)
          (Finset.univ : Finset α) :=
            weight_mono _ hnonneg (Finset.subset_univ J)
      _ ≤ weight w₀ (Finset.univ : Finset α) :=
            total_weight_le_initial k D U w₀ hcoverage T
      _ ≤ (J.card : ℝ) * N := hinitial
  exact sum_log_le_card_log_of_mass J
    (weightsAfter k D U w₀ T) N hN hpos hmass

/-- Last arithmetic step in the manuscript's online-regret theorem:
quantized regret plus the rounding allowance. The missing premise
`hlogregret` must be *proved from* the threshold-weight update before
calling this a complete verification of Theorem `thm:online-regret`. -/
theorem online_regret_of_log_comparison
    (T L : ℕ) (hL : 0 < L)
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N)
    (demo learner qDemo qLearner : Fin T → ℝ)
    (hround : ∀ t,
      demo t - learner t ≤ qDemo t - qLearner t + 1 / (L : ℝ))
    (hlogregret :
      a * (∑ t : Fin T, (qDemo t - qLearner t)) ≤ Real.log N) :
    (∑ t : Fin T, (demo t - learner t)) ≤
      Real.log N / a + (T : ℝ) / (L : ℝ) := by
  have hsum := quantization_round_sum T demo learner qDemo qLearner
    (1 / (L : ℝ)) hround
  have hquant : (∑ t : Fin T, (qDemo t - qLearner t)) ≤
      Real.log N / a := by
    apply (le_div_iff₀ ha).2
    simpa only [mul_comm] using hlogregret
  calc
    (∑ t : Fin T, (demo t - learner t)) ≤
        (∑ t : Fin T, (qDemo t - qLearner t)) +
          (T : ℝ) * (1 / (L : ℝ)) := hsum
    _ ≤ Real.log N / a + (T : ℝ) * (1 / (L : ℝ)) := by
      exact add_le_add hquant
        (le_refl ((T : ℝ) * (1 / (L : ℝ))))
    _ = Real.log N / a + (T : ℝ) / (L : ℝ) := by
      simp only [div_eq_mul_inv]
      ring

end PassK
