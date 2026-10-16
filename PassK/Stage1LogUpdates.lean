import PassK.Stage1LogPotential

/-!
# Stage 1: exact logarithmic increments of the actual update

This file proves the per-threshold log-weight update and its telescoping
sum across a sequence of rounds. These are the missing log identities
in the deterministic online-regret calculation. The identification of
those threshold memberships with `q_L(r(x,y))` still needs to be made
at the algorithm/problem-setup layer.
-/

noncomputable section

namespace PassK

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Signed logarithmic change at one reward-threshold pair. -/
def logStep (k : ℕ) (D U : Finset α) (a : α) : ℝ :=
  if a ∈ D \ U then Real.log (1 + (k : ℝ) / 4)
  else if a ∈ U \ D then -Real.log (4 / 3 : ℝ)
  else 0

/-- The asymmetric update changes log-weight by precisely `logStep`. -/
theorem log_update_identity
    (k : ℕ) (D U : Finset α) (w : α → ℝ)
    (hw : ∀ a, 0 < w a) (a : α) :
    Real.log (update k D U w a) - Real.log (w a) =
      logStep k D U a := by
  by_cases hd : a ∈ D \ U
  · have hfac : (1 + (k : ℝ) / 4) ≠ 0 := by positivity
    have hu : update k D U w a =
        (1 + (k : ℝ) / 4) * w a := by simp [update, hd]
    rw [hu, Real.log_mul hfac (ne_of_gt (hw a))]
    simp [logStep, hd]
  · by_cases hother : a ∈ U \ D
    · have hfac : (3 / 4 : ℝ) ≠ 0 := by norm_num
      have hu : update k D U w a = (3 / 4 : ℝ) * w a := by
        simp [update, hd, hother]
      have hratio : (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ := by norm_num
      rw [hu, Real.log_mul hfac (ne_of_gt (hw a))]
      rw [hratio, Real.log_inv]
      simp [logStep, hd, hother]
    · have hu : update k D U w a = w a := by
        simp [update, hd, hother]
      rw [hu]
      simp [logStep, hd, hother]

/-- Telescoping the true log update over all `T` online rounds.
No regret or probabilistic inequality is assumed. -/
theorem log_weightsAfter_telescope
    (k : ℕ) (D U : ℕ → Finset α) (w₀ : α → ℝ)
    (hw₀ : ∀ a, 0 < w₀ a) (a : α) (T : ℕ) :
    Real.log (weightsAfter k D U w₀ T a) - Real.log (w₀ a) =
      ∑ t ∈ Finset.range T, logStep k (D t) (U t) a := by
  induction T with
  | zero =>
      simp
  | succ t ih =>
      have hpos : ∀ j, 0 < weightsAfter k D U w₀ t j := by
        intro j
        exact weightsAfter_pos k D U w₀ hw₀ t j
      have hstep := log_update_identity k (D t) (U t)
        (weightsAfter k D U w₀ t) hpos a
      calc
        Real.log (weightsAfter k D U w₀ (t + 1) a) - Real.log (w₀ a) =
            (Real.log (weightsAfter k D U w₀ t a) - Real.log (w₀ a)) +
              logStep k (D t) (U t) a := by
                rw [weightsAfter_succ]
                linarith [hstep]
        _ = (∑ i ∈ Finset.range t, logStep k (D i) (U i) a) +
              logStep k (D t) (U t) a := by rw [ih]
        _ = ∑ i ∈ Finset.range (t + 1), logStep k (D i) (U i) a := by
              rw [Finset.sum_range_succ]

end PassK
