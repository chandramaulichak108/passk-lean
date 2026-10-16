import PassK.StandardRobustPAC
import PassK.Stage2Exponential

/-!
# Stage 3: numerical constants in pass@k PAC rates

The finite Markov / reward-union arguments are in `FiniteTail`,
`MomentToTail` and `StandardRobustPAC`. Here we prove the *numerical*
logarithm inequalities that convert the raw algorithm-dependent bound
into the `log |R| / log k` dependence in the theorem statement.

This module does not supply the missing algorithm-specific moment premise.
-/

noncomputable section

namespace PassK

/-- For every integer k ≥ 2, log(1 + k/4) ≥ (log k)/2. -/
theorem half_log_k_le_log_update (k : ℕ) (hk : 2 ≤ k) :
    Real.log (k : ℝ) / 2 ≤ Real.log (1 + (k : ℝ) / 4) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (show 0 < k by omega)
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkpos
  have hlog := Real.log_le_log hsqrt (sqrt_le_one_add_div_four k)
  rw [Real.log_sqrt (le_of_lt hkpos)] at hlog
  exact hlog

/-- k ≥ 2 makes the upward log-update at least the downward coefficient. -/
theorem log_downweight_le_log_upweight (k : ℕ) (hk : 2 ≤ k) :
    Real.log (4 / 3 : ℝ) ≤ Real.log (1 + (k : ℝ) / 4) := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hbase : (4 / 3 : ℝ) ≤ 1 + (k : ℝ) / 4 := by
    linarith
  exact Real.log_le_log (by norm_num : (0 : ℝ) < 4 / 3) hbase

/-- The manuscript uses 2 log(3/2) < 1 to simplify the leading constant. -/
theorem two_log_three_halves_lt_one :
    2 * Real.log (3 / 2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 3 / 2)
    (by norm_num : (3 / 2 : ℝ) ≠ 1)
  norm_num at h
  linarith

/-- The logarithmic improvement is positive, so division is meaningful. -/
theorem log_update_pos (k : ℕ) (hk : 2 ≤ k) :
    0 < Real.log (1 + (k : ℝ) / 4) := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  apply Real.log_pos
  linarith

end PassK
