import PassK.FiniteTail

/-!
# From an exponential-moment inequality to PAC bounds

The finite-probability Markov and union-bound steps are proved here.

**Crucial limitation:** the hypothesis `hmoment` is the substantive
exponential-supermartingale lemma of the manuscript. It is NOT derived
from the pass@k online algorithm in this file. This is a conditional
implication, not a proof of the paper's complete Theorem 2.
-/

noncomputable section

namespace PassK.Finite

variable {Ω : Type*} [Fintype Ω]

/-- An exponential-moment budget for `G/3` implies the familiar
`3 (B - log δ)` high-probability threshold. -/
theorem exponentialMoment_implies_tail
    (p : FiniteDistribution Ω) (G : Ω → ℝ)
    (B δ : ℝ) (hδ : 0 < δ)
    (hmoment : expectedValue p (fun ω => Real.exp (G ω / 3)) ≤
      Real.exp B) :
    eventProbability p (fun ω => 3 * (B - Real.log δ) < G ω) ≤ δ := by
  let c : ℝ := Real.exp (B - Real.log δ)
  have hc : 0 < c := Real.exp_pos _
  have hidentity : δ * c = Real.exp B := by
    dsimp [c]
    rw [Real.exp_sub, Real.exp_log hδ]
    field_simp [ne_of_gt hδ]
  have hmean : expectedValue p (fun ω => Real.exp (G ω / 3)) ≤
      δ * c := by
    rw [hidentity]
    exact hmoment
  have hmarkov := eventProbability_le_of_mean p
    (fun ω => Real.exp (G ω / 3))
    (fun ω => le_of_lt (Real.exp_pos _)) c δ hc hmean
  have hevents : (fun ω => c < Real.exp (G ω / 3)) =
      (fun ω => 3 * (B - Real.log δ) < G ω) := by
    funext ω
    apply propext
    change Real.exp (B - Real.log δ) < Real.exp (G ω / 3) ↔
      3 * (B - Real.log δ) < G ω
    rw [Real.exp_lt_exp]
    constructor <;> intro h <;> linarith
  rw [hevents] at hmarkov
  exact hmarkov

/-- Conditional PAC conversion: after establishing the algorithm-specific
moment estimate AND the online-to-batch comparison, this produces the
bound on the excess value of the returned learner. -/
theorem excess_tail_of_moment
    (p : FiniteDistribution Ω) (G excess : Ω → ℝ)
    (m L : ℕ) (hm : 0 < m)
    (B δ : ℝ) (hδ : 0 < δ)
    (hreduction : ∀ ω, excess ω ≤ G ω / (m : ℝ) + 1 / (L : ℝ))
    (hmoment : expectedValue p (fun ω => Real.exp (G ω / 3)) ≤
      Real.exp B) :
    eventProbability p (fun ω =>
        3 * (B - Real.log δ) / (m : ℝ) + 1 / (L : ℝ) < excess ω) ≤ δ := by
  have htail := exponentialMoment_implies_tail p G B δ hδ hmoment
  apply (eventProbability_mono p
    (fun ω => 3 * (B - Real.log δ) / (m : ℝ) + 1 / (L : ℝ) < excess ω)
    (fun ω => 3 * (B - Real.log δ) < G ω) ?_).trans htail
  intro ω hbad
  have hbound := hreduction ω
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hscaled : 3 * (B - Real.log δ) / (m : ℝ) <
      G ω / (m : ℝ) := by linarith
  have hprod := (div_lt_iff₀ hmpos).mp hscaled
  have hcancelLeft : (3 * (B - Real.log δ) / (m : ℝ)) * (m : ℝ) =
      3 * (B - Real.log δ) := by
    field_simp [ne_of_gt hmpos]
  have hcancelRight : (G ω / (m : ℝ)) * (m : ℝ) = G ω := by
    field_simp [ne_of_gt hmpos]
  simpa only [hcancelLeft, hcancelRight] using hprod

end PassK.Finite
