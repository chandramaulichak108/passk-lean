import PassK.MomentToTail

/-!
# The fixed-reward and simultaneous-confidence conversion

These are the *probabilistic implication steps* of the paper's upper-bound
proof. Their hypotheses deliberately include the conditional-excess
reduction and the exponential-moment estimate. Those substantial
algorithm-specific facts are not asserted or proved here.

The simultaneous result uses a union bound and requires no independence
between the different rewards' bad events.
-/

noncomputable section

namespace PassK.Finite

variable {Ω R : Type*} [Fintype Ω]

/-- Conditional standard PAC upper bound, at a fixed reward.
An independent proof of the online learner's moment estimate would be
needed to discharge `hmoment`. -/
theorem standardPAC_from_moment
    (p : FiniteDistribution Ω) (m L : ℕ) (hm : 0 < m)
    (B δ : ℝ) (hδ : 0 < δ) (G E : Ω → ℝ)
    (hreduction : ∀ ω, E ω ≤ G ω / (m : ℝ) + 1 / (L : ℝ))
    (hmoment : expectedValue p (fun ω => Real.exp (G ω / 3)) ≤
      Real.exp B) :
    eventProbability p (fun ω =>
      3 * (B - Real.log δ) / (m : ℝ) + 1 / (L : ℝ) < E ω) ≤ δ := by
  exact excess_tail_of_moment p G E m L hm B δ hδ hreduction hmoment

/-- Conditional robust PAC upper bound obtained by taking a union over
the finite class.  All bad events use the same random sample and may be
arbitrarily dependent. -/
theorem robustPAC_from_moments
    (p : FiniteDistribution Ω) (rewards : Finset R)
    (hne : rewards.Nonempty) (m L : ℕ) (hm : 0 < m)
    (B δ : ℝ) (hδ : 0 < δ)
    (G E : R → Ω → ℝ)
    (hreduction : ∀ r ∈ rewards, ∀ ω,
      E r ω ≤ G r ω / (m : ℝ) + 1 / (L : ℝ))
    (hmoment : ∀ r ∈ rewards,
      expectedValue p (fun ω => Real.exp (G r ω / 3)) ≤ Real.exp B) :
    eventProbability p (fun ω =>
      ∃ r ∈ rewards,
        3 * (B - Real.log (δ / (rewards.card : ℝ))) / (m : ℝ) +
        1 / (L : ℝ) < E r ω) ≤ δ := by
  classical
  have hcard : (0 : ℝ) < rewards.card := by
    exact_mod_cast hne.card_pos
  have hδR : 0 < δ / (rewards.card : ℝ) := div_pos hδ hcard
  exact eventProbability_union_confidence p rewards hne
    (fun r ω =>
      3 * (B - Real.log (δ / (rewards.card : ℝ))) / (m : ℝ) +
      1 / (L : ℝ) < E r ω) δ (by
        intro r hr
        exact standardPAC_from_moment p m L hm B
          (δ / (rewards.card : ℝ)) hδR
          (G r) (E r) (hreduction r hr) (hmoment r hr))

end PassK.Finite
