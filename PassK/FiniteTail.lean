import PassK.Values

/-!
# Finite probability: Markov's inequality and the union bound

These are *proved* finite-sample reduction lemmas.  They do not assert
that the pass@k algorithm satisfies the exponential-moment premise.
-/

noncomputable section

namespace PassK.Finite

variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event on a finite sample space. -/
def eventProbability (p : FiniteDistribution Ω) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω : Ω, if E ω then p.prob ω else 0

/-- Expectation of a real-valued statistic on a finite sample space. -/
def expectedValue (p : FiniteDistribution Ω) (Z : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, p.prob ω * Z ω

/-- Event probabilities are monotone. -/
theorem eventProbability_mono (p : FiniteDistribution Ω)
    (E F : Ω → Prop) (h : ∀ ω, E ω → F ω) :
    eventProbability p E ≤ eventProbability p F := by
  classical
  unfold eventProbability
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω
  · have hf : F ω := h ω he
    simp [he, hf]
  · by_cases hf : F ω
    · simpa [he, hf] using p.nonneg ω
    · simp [he, hf]

/-- The elementary finite probability union bound. -/
theorem eventProbability_or_le (p : FiniteDistribution Ω)
    (E F : Ω → Prop) :
    eventProbability p (fun ω => E ω ∨ F ω) ≤
      eventProbability p E + eventProbability p F := by
  classical
  unfold eventProbability
  -- Combine both sums first to keep the summation variable in scope.
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω <;> by_cases hf : F ω
  all_goals simp [he, hf] <;> linarith [p.nonneg ω]

/-- Union bound over a finite collection of potentially dependent events. -/
theorem eventProbability_exists_le_sum {R : Type*}
    (p : FiniteDistribution Ω) (rewards : Finset R) (Bad : R → Ω → Prop) :
    eventProbability p (fun ω => ∃ r ∈ rewards, Bad r ω) ≤
      ∑ r ∈ rewards, eventProbability p (Bad r) := by
  classical
  induction rewards using Finset.induction_on with
  | empty =>
      simp [eventProbability]
  | @insert r rewards hr ih =>
      have heq : (fun ω => ∃ r' ∈ insert r rewards, Bad r' ω) =
          (fun ω => Bad r ω ∨ ∃ r' ∈ rewards, Bad r' ω) := by
        funext ω
        apply propext
        simp
      rw [heq, Finset.sum_insert hr]
      have hOR := eventProbability_or_le p (Bad r)
        (fun ω => ∃ r' ∈ rewards, Bad r' ω)
      exact hOR.trans (add_le_add
        (le_refl (eventProbability p (Bad r))) ih)

/-- Finite Markov bound stated in a form convenient for moment-to-tail
conversions: if `E Z ≤ δ c` and `Z ≥ 0`, then `P{Z > c} ≤ δ`. -/
theorem eventProbability_le_of_mean (p : FiniteDistribution Ω)
    (Z : Ω → ℝ) (hZ : ∀ ω, 0 ≤ Z ω)
    (c δ : ℝ) (hc : 0 < c)
    (hmean : expectedValue p Z ≤ δ * c) :
    eventProbability p (fun ω => c < Z ω) ≤ δ := by
  classical
  have hpoint (ω : Ω) :
      (if c < Z ω then p.prob ω else 0) * c ≤ p.prob ω * Z ω := by
    by_cases h : c < Z ω
    · simp only [if_pos h]
      exact mul_le_mul_of_nonneg_left (le_of_lt h) (p.nonneg ω)
    · simp only [if_neg h, zero_mul]
      exact mul_nonneg (p.nonneg ω) (hZ ω)
  have hsum :
      (∑ ω : Ω, (if c < Z ω then p.prob ω else 0) * c) ≤
        ∑ ω : Ω, p.prob ω * Z ω := by
    apply Finset.sum_le_sum
    intro ω _
    exact hpoint ω
  have hstep : eventProbability p (fun ω => c < Z ω) * c ≤
      expectedValue p Z := by
    simpa [eventProbability, expectedValue, Finset.sum_mul] using hsum
  -- Positive scaling preserves the strict order.
  have hcompare := hstep.trans hmean
  by_contra hnot
  have hgt : δ < eventProbability p (fun ω => c < Z ω) :=
    lt_of_not_ge hnot
  have hmul : δ * c < eventProbability p (fun ω => c < Z ω) * c :=
    mul_lt_mul_of_pos_right hgt hc
  linarith only [hcompare, hmul]

/-- If each event has probability at most `δ / |R|`, the union
has probability at most `δ`. -/
theorem eventProbability_union_confidence {R : Type*}
    (p : FiniteDistribution Ω) (rewards : Finset R)
    (hne : rewards.Nonempty) (Bad : R → Ω → Prop) (δ : ℝ)
    (heach : ∀ r ∈ rewards,
      eventProbability p (Bad r) ≤ δ / (rewards.card : ℝ)) :
    eventProbability p (fun ω => ∃ r ∈ rewards, Bad r ω) ≤ δ := by
  classical
  have hc : (rewards.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hne.card_pos)
  calc
    eventProbability p (fun ω => ∃ r ∈ rewards, Bad r ω)
        ≤ ∑ r ∈ rewards, eventProbability p (Bad r) :=
          eventProbability_exists_le_sum p rewards Bad
    _ ≤ ∑ _r ∈ rewards, δ / (rewards.card : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact heach r hr
    _ = δ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp [hc] <;> ring

end PassK.Finite
