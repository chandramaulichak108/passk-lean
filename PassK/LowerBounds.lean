import PassK.UpperBounds

/-!
# Finite minimax setup and a lower-bound proof principle

The paper contains lower bounds that require explicit hard instances,
KL bounds, Fano/list-decoding or Assouad reductions. Those arguments
are not yet formalized in this project.

Instead, the declarations below give a precise finite minimax risk and
prove a general, useful lower-bound principle: if every algorithm
suffers loss at least `c` on some instance, minimax risk is at least `c`.
This is a correct reduction step, NOT the manuscript's numerical rates.
-/

namespace PassK.FiniteGame

variable {Alg Instance : Type*}

/-- Worst-case loss over a nonempty finite family of instances. -/
noncomputable def worstCaseLoss
    (instances : Finset Instance) (hI : instances.Nonempty)
    (loss : Alg → Instance → ℝ) (algorithm : Alg) : ℝ :=
  instances.sup' hI (loss algorithm)

/-- Finite minimax risk: the best algorithm's worst-case loss. -/
noncomputable def minimaxRisk
    (algorithms : Finset Alg) (hA : algorithms.Nonempty)
    (instances : Finset Instance) (hI : instances.Nonempty)
    (loss : Alg → Instance → ℝ) : ℝ :=
  algorithms.inf' hA (worstCaseLoss instances hI loss)

/-- Every adversarial instance's loss is at most the worst-case loss. -/
theorem loss_le_worstCaseLoss
    (instances : Finset Instance) (hI : instances.Nonempty)
    (loss : Alg → Instance → ℝ) (algorithm : Alg)
    (instance₀ : Instance) (hmem : instance₀ ∈ instances) :
    loss algorithm instance₀ ≤
      worstCaseLoss instances hI loss algorithm := by
  unfold worstCaseLoss
  exact Finset.le_sup' (loss algorithm) hmem

/-- A general minimax lower-bound reduction: every algorithm admits
at least one hard instance. -/
theorem minimax_lower_bound
    (algorithms : Finset Alg) (hA : algorithms.Nonempty)
    (instances : Finset Instance) (hI : instances.Nonempty)
    (loss : Alg → Instance → ℝ) (c : ℝ)
    (hard : ∀ algorithm ∈ algorithms,
      ∃ instance₀ ∈ instances, c ≤ loss algorithm instance₀) :
    c ≤ minimaxRisk algorithms hA instances hI loss := by
  unfold minimaxRisk
  apply Finset.le_inf' hA
  intro algorithm ha
  obtain ⟨instance₀, hi, hc⟩ := hard algorithm ha
  exact hc.trans (loss_le_worstCaseLoss instances hI loss algorithm instance₀ hi)

/-- Any individual admissible algorithm incurs worst-case loss at least
the minimax risk. -/
theorem minimax_le_algorithm_worstCase
    (algorithms : Finset Alg) (hA : algorithms.Nonempty)
    (instances : Finset Instance) (hI : instances.Nonempty)
    (loss : Alg → Instance → ℝ) (algorithm : Alg)
    (ha : algorithm ∈ algorithms) :
    minimaxRisk algorithms hA instances hI loss ≤
      worstCaseLoss instances hI loss algorithm := by
  unfold minimaxRisk
  exact Finset.inf'_le _ ha

end PassK.FiniteGame
