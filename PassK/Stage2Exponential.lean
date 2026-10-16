import PassK.Stage1LogPotential
import PassK.FiniteTail

/-!
# Stage 2: exponential-moment proof components

The elementary one-step exponential estimates in the paper come from the
convexity of `Real.exp`. They are proved below for every `u ∈ [0,1]`.
The final theorem implements the pathwise-weight/moment comparison.

The *adaptive*, filtration-conditioned supermartingale estimate for the
specific greedy algorithm still needs to be constructed. A bound assumed as
`hKmean` is not a proof of that supermartingale estimate.
-/

noncomputable section

namespace PassK

/-- The exponential lies below its chord between 0 and `b`.
This is the particular convexity fact used in the manuscript. -/
theorem exponential_chord (u b : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (u * b) ≤ 1 - u + u * Real.exp b := by
  have hc := convexOn_exp.2
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ b)
    (sub_nonneg.mpr hu1) hu0 (by ring : (1 - u) + u = 1)
  simpa [smul_eq_mul, Real.exp_zero] using hc

/-- Positive shortfall: the `(2/3)^u` chord bound, in exponential form. -/
theorem exp_shortfall_chord (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (-u * Real.log (3 / 2 : ℝ)) ≤ 1 - u / 3 := by
  have hlog : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
    have hratio : (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ := by norm_num
    rw [hratio, Real.log_inv]
  have hc := exponential_chord u (Real.log (2 / 3 : ℝ)) hu0 hu1
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2 / 3)] at hc
  rw [hlog] at hc
  have h : Real.exp (-u * Real.log (3 / 2 : ℝ)) ≤
      1 - u + u * (2 / 3 : ℝ) := by
    simpa only [mul_neg, neg_mul] using hc
  linarith

/-- Negative shortfall: the scaled `(4/3)^(θu)` chord bound.
The assumption `θ ≤ 1` is exactly the restriction used in the paper. -/
theorem exp_gain_chord (u θ : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.exp (u * (θ * Real.log (4 / 3 : ℝ))) ≤ 1 + u / 3 := by
  have hlog : 0 ≤ Real.log (4 / 3 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hθlog : θ * Real.log (4 / 3 : ℝ) ≤
      Real.log (4 / 3 : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ1 hlog
  have hexp : Real.exp (θ * Real.log (4 / 3 : ℝ)) ≤ (4 / 3 : ℝ) := by
    calc
      Real.exp (θ * Real.log (4 / 3 : ℝ)) ≤
          Real.exp (Real.log (4 / 3 : ℝ)) :=
            (Real.exp_le_exp).2 hθlog
      _ = (4 / 3 : ℝ) := Real.exp_log (by norm_num)
  have hc := exponential_chord u (θ * Real.log (4 / 3 : ℝ)) hu0 hu1
  have hs := mul_le_mul_of_nonneg_left hexp hu0
  linarith

/-- The scaled log update of the paper, expressed as a function of a
signed quantized one-step shortfall. -/
def scaledLogIncrement (θ ell : ℝ) : ℝ :=
  Real.log (3 / 2 : ℝ) * max ell 0 -
    θ * Real.log (4 / 3 : ℝ) * max (-ell) 0

/-- The full one-step chord inequality for signed shortfalls.
This establishes equation `one_step_exponential` *pointwise* whenever
`|ell| ≤ 1` and `θ ∈ [0,1]`. -/
theorem signed_exponential_chord (θ ell : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : -1 ≤ ell) (hhigh : ell ≤ 1) :
    Real.exp (-scaledLogIncrement θ ell) ≤ 1 - ell / 3 := by
  by_cases hpos : 0 ≤ ell
  · have hneg : -ell ≤ 0 := by linarith
    have hz : scaledLogIncrement θ ell =
        Real.log (3 / 2 : ℝ) * ell := by
      unfold scaledLogIncrement
      rw [max_eq_left hpos, max_eq_right hneg]
      ring
    rw [hz]
    have harg : -(Real.log (3 / 2 : ℝ) * ell) =
        -ell * Real.log (3 / 2 : ℝ) := by ring
    rw [harg]
    exact exp_shortfall_chord ell hpos hhigh
  · have hneg : ell ≤ 0 := le_of_lt (lt_of_not_ge hpos)
    have hu0 : 0 ≤ -ell := by linarith
    have hu1 : -ell ≤ 1 := by linarith
    have hz : scaledLogIncrement θ ell =
        -(θ * Real.log (4 / 3 : ℝ) * (-ell)) := by
      unfold scaledLogIncrement
      rw [max_eq_right hneg, max_eq_left hu0]
      ring
    rw [hz]
    have harg : -(-(θ * Real.log (4 / 3 : ℝ) * (-ell))) =
        (-ell) * (θ * Real.log (4 / 3 : ℝ)) := by ring
    rw [harg]
    have hRHS : 1 + (-ell) / 3 = 1 - ell / 3 := by ring
    rw [← hRHS]
    exact exp_gain_chord (-ell) θ hu0 hu1 hθ0 hθ1

end PassK

namespace PassK.Finite

variable {Ω : Type*} [Fintype Ω]

/-- The probability-normalization algebra behind one-step conditioning.
Whenever the signed one-step shortfall is in `[-1,1]`,
`E[exp(-z)] ≤ 1 - E[ell]/3` follows without any independence assumption. -/
theorem signed_chord_expected
    (p : FiniteDistribution Ω) (θ : ℝ) (ell : Ω → ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : ∀ ω, -1 ≤ ell ω) (hhigh : ∀ ω, ell ω ≤ 1) :
    expectedValue p (fun ω => Real.exp (-scaledLogIncrement θ (ell ω))) ≤
      1 - expectedValue p ell / 3 := by
  have hpoint (ω : Ω) :
      p.prob ω * Real.exp (-scaledLogIncrement θ (ell ω)) ≤
        p.prob ω * (1 - ell ω / 3) :=
    mul_le_mul_of_nonneg_left
      (signed_exponential_chord θ (ell ω) hθ0 hθ1 (hlow ω) (hhigh ω))
      (p.nonneg ω)
  have hsum :
      (∑ ω : Ω, p.prob ω * Real.exp (-scaledLogIncrement θ (ell ω))) ≤
      (∑ ω : Ω, p.prob ω * (1 - ell ω / 3)) := by
    apply Finset.sum_le_sum
    intro ω _
    exact hpoint ω
  have heq :
      (∑ ω : Ω, p.prob ω * (1 - ell ω / 3)) =
        1 - (∑ ω : Ω, p.prob ω * ell ω) / 3 := by
    calc
      (∑ ω : Ω, p.prob ω * (1 - ell ω / 3)) =
          ∑ ω : Ω, (p.prob ω - (p.prob ω * ell ω) / 3) := by
            apply Finset.sum_congr rfl
            intro ω _
            ring
      _ = (∑ ω : Ω, p.prob ω) -
          (∑ ω : Ω, p.prob ω * ell ω) / 3 := by
            rw [Finset.sum_sub_distrib, Finset.sum_div]
      _ = 1 - (∑ ω : Ω, p.prob ω * ell ω) / 3 := by
            rw [p.total]
  unfold expectedValue
  exact hsum.trans (le_of_eq heq)

/-- A true one-step exponential-supermartingale inequality for a *fresh
finite draw* (the adaptive history is held fixed here).

`g` is the mean signed shortfall of that draw. This lemma supplies the
probability calculation that the manuscript iterates conditionally.
The iteration over sample histories is a separate, unfinished step. -/
theorem one_step_exponential_supermartingale
    (p : FiniteDistribution Ω) (θ : ℝ) (ell : Ω → ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : ∀ ω, -1 ≤ ell ω) (hhigh : ∀ ω, ell ω ≤ 1) :
    expectedValue p (fun ω =>
      Real.exp (expectedValue p ell / 3 - scaledLogIncrement θ (ell ω))) ≤ 1 := by
  let g := expectedValue p ell
  have hmean :
      expectedValue p (fun ω => Real.exp (-scaledLogIncrement θ (ell ω))) ≤
        1 - g / 3 :=
    signed_chord_expected p θ ell hθ0 hθ1 hlow hhigh
  have hfactor :
      expectedValue p (fun ω => Real.exp (g / 3 - scaledLogIncrement θ (ell ω))) =
        Real.exp (g / 3) *
          expectedValue p (fun ω => Real.exp (-scaledLogIncrement θ (ell ω))) := by
    unfold expectedValue
    calc
      (∑ ω : Ω, p.prob ω * Real.exp (g / 3 - scaledLogIncrement θ (ell ω))) =
          ∑ ω : Ω, p.prob ω *
            (Real.exp (g / 3) * Real.exp (-scaledLogIncrement θ (ell ω))) := by
              apply Finset.sum_congr rfl
              intro ω _
              rw [sub_eq_add_neg, Real.exp_add]
      _ = Real.exp (g / 3) *
          (∑ ω : Ω, p.prob ω * Real.exp (-scaledLogIncrement θ (ell ω))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω _
            ring
  have hchord : (1 - g / 3) ≤ Real.exp (-g / 3) := by
    have h := Real.add_one_le_exp (-g / 3)
    linarith
  have hmul :
      Real.exp (g / 3) * (1 - g / 3) ≤
        Real.exp (g / 3) * Real.exp (-g / 3) :=
    mul_le_mul_of_nonneg_left hchord (le_of_lt (Real.exp_pos _))
  change expectedValue p (fun ω =>
      Real.exp (g / 3 - scaledLogIncrement θ (ell ω))) ≤ 1
  rw [hfactor]
  calc
    Real.exp (g / 3) *
        expectedValue p (fun ω => Real.exp (-scaledLogIncrement θ (ell ω))) ≤
        Real.exp (g / 3) * (1 - g / 3) :=
          mul_le_mul_of_nonneg_left hmean (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (g / 3) * Real.exp (-g / 3) := hmul
    _ = 1 := by
      rw [← Real.exp_add]
      have hzero : g / 3 + -g / 3 = 0 := by ring
      rw [hzero, Real.exp_zero]

/-- Final algebraic step of the exponential-supermartingale method.
`K` is the final nonnegative supermartingale value. `hKmean` is precisely
the still-missing result that the algorithm's process has expectation ≤ 1.
The conclusion is an actual finite-expectation calculation, not an axiom. -/
theorem exponential_moment_of_supermartingale_budget
    (p : FiniteDistribution Ω) (K G Z : Ω → ℝ) (B : ℝ)
    (hKpos : ∀ ω, 0 ≤ K ω)
    (hKmean : expectedValue p K ≤ 1)
    (hZ : ∀ ω, Z ω ≤ B)
    (hlink : ∀ ω, Real.exp (G ω / 3) = K ω * Real.exp (Z ω)) :
    expectedValue p (fun ω => Real.exp (G ω / 3)) ≤ Real.exp B := by
  have hpoint (ω : Ω) :
      p.prob ω * Real.exp (G ω / 3) ≤
        (p.prob ω * K ω) * Real.exp B := by
    rw [hlink ω]
    have hexp : Real.exp (Z ω) ≤ Real.exp B :=
      (Real.exp_le_exp).2 (hZ ω)
    have hpK : 0 ≤ p.prob ω * K ω :=
      mul_nonneg (p.nonneg ω) (hKpos ω)
    calc
      p.prob ω * (K ω * Real.exp (Z ω)) =
          (p.prob ω * K ω) * Real.exp (Z ω) := by ring
      _ ≤ (p.prob ω * K ω) * Real.exp B :=
          mul_le_mul_of_nonneg_left hexp hpK
  have hsum :
      (∑ ω : Ω, p.prob ω * Real.exp (G ω / 3)) ≤
        (∑ ω : Ω, p.prob ω * K ω) * Real.exp B := by
    calc
      (∑ ω : Ω, p.prob ω * Real.exp (G ω / 3)) ≤
          ∑ ω : Ω, (p.prob ω * K ω) * Real.exp B := by
            apply Finset.sum_le_sum
            intro ω _
            exact hpoint ω
      _ = (∑ ω : Ω, p.prob ω * K ω) * Real.exp B := by
            rw [Finset.sum_mul]
  change (∑ ω : Ω, p.prob ω * Real.exp (G ω / 3)) ≤ Real.exp B
  calc
    _ ≤ (∑ ω : Ω, p.prob ω * K ω) * Real.exp B := hsum
    _ ≤ 1 * Real.exp B :=
      mul_le_mul_of_nonneg_right hKmean (le_of_lt (Real.exp_pos B))
    _ = Real.exp B := one_mul _

end PassK.Finite
