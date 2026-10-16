import PassK.GreedyCoverage
import PassK.Preliminaries

/-!
# Deterministic online-regret proof infrastructure

This module proves preservation of positive weights and the potential
invariant across any finite number of rounds, assuming the explicit
weighted-coverage comparison on each round.

It also supplies an algebraic regret conclusion *conditional on* the
log-weight increment budget.  The full theorem from the manuscript
(`log |R| / log (1+k/4) + T/L`) additionally requires the logarithmic
weight/AM--GM argument, which is not represented as verified here.
-/

noncomputable section

namespace PassK

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Multiplicative weights after `t` online rounds. -/
def weightsAfter (k : ℕ) (D U : ℕ → Finset α) (w₀ : α → ℝ) :
    ℕ → α → ℝ
  | 0 => w₀
  | t + 1 => update k (D t) (U t) (weightsAfter k D U w₀ t)

@[simp] theorem weightsAfter_zero (k : ℕ) (D U : ℕ → Finset α)
    (w₀ : α → ℝ) : weightsAfter k D U w₀ 0 = w₀ := rfl

@[simp] theorem weightsAfter_succ (k : ℕ) (D U : ℕ → Finset α)
    (w₀ : α → ℝ) (t : ℕ) :
    weightsAfter k D U w₀ (t + 1) =
      update k (D t) (U t) (weightsAfter k D U w₀ t) := rfl

/-- All weights remain strictly positive if the initial weights are. -/
theorem weightsAfter_pos (k : ℕ) (D U : ℕ → Finset α)
    (w₀ : α → ℝ) (hw₀ : ∀ a, 0 < w₀ a) :
    ∀ t a, 0 < weightsAfter k D U w₀ t a := by
  intro t
  induction t with
  | zero =>
      intro a
      simpa only [weightsAfter_zero] using hw₀ a
  | succ t ih =>
      intro a
      rw [weightsAfter_succ]
      exact update_pos k (D t) (U t) (weightsAfter k D U w₀ t) ih a

/-- Under the coverage comparison at each time, the total weight
at any later time is bounded by its initial value. -/
theorem total_weight_le_initial
    (k : ℕ) (D U : ℕ → Finset α) (w₀ : α → ℝ)
    (hCoverage : ∀ t,
      (k : ℝ) * weight (weightsAfter k D U w₀ t) (D t \ U t) ≤
      weight (weightsAfter k D U w₀ t) (U t \ D t))
    (T : ℕ) :
    weight (weightsAfter k D U w₀ T) (Finset.univ : Finset α) ≤
      weight w₀ (Finset.univ : Finset α) := by
  induction T with
  | zero =>
      simp only [weightsAfter_zero]
      exact le_refl _
  | succ t ih =>
      rw [weightsAfter_succ]
      exact (update_total_le k (D t) (U t)
        (weightsAfter k D U w₀ t) (hCoverage t)).trans ih

/-- Instantiation of the preceding invariant to roundwise greedy
selection of k responses, with strictly positive initial weights. -/
theorem greedy_total_weight_le_initial
    (k : ℕ) (D : ℕ → Finset α)
    (A : ℕ → ℕ → Finset α) (w₀ : α → ℝ)
    (hw₀ : ∀ a, 0 < w₀ a)
    (hGreedy : ∀ t, ∀ i < k,
      weight (weightsAfter k D (fun s => coveragePrefix (A s) k) w₀ t)
        (D t \ coveragePrefix (A t) i) ≤
      weight (weightsAfter k D (fun s => coveragePrefix (A s) k) w₀ t)
        (A t i \ coveragePrefix (A t) i))
    (T : ℕ) :
    weight (weightsAfter k D (fun s => coveragePrefix (A s) k) w₀ T)
      (Finset.univ : Finset α) ≤
      weight w₀ (Finset.univ : Finset α) := by
  apply total_weight_le_initial k D (fun s => coveragePrefix (A s) k) w₀
  · intro t
    apply greedy_weight_comparison
      (weightsAfter k D (fun s => coveragePrefix (A s) k) w₀ t)
      (fun a => le_of_lt (weightsAfter_pos k D
        (fun s => coveragePrefix (A s) k) w₀ hw₀ t a))
      (A t) (D t) k
    exact hGreedy t

/-- The algebraic step converting a proved signed-regret increment
budget into an upper bound on cumulative signed regret. -/
theorem quantized_regret_of_budget
    (T : ℕ) (a b B : ℝ) (ha : 0 < a) (hba : b ≤ a)
    (ell : Fin T → ℝ)
    (hbudget :
      (∑ t : Fin T,
        (a * max (ell t) 0 - b * max (-(ell t)) 0)) ≤ B) :
    (∑ t : Fin T, ell t) ≤ B / a :=
  signed_regret_le_of_increment_budget T a b B ha hba ell hbudget

end PassK
