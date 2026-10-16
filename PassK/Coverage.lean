import Mathlib

/-!
# The greedy-coverage argument for pass@k

This file formalizes the deterministic coverage lemma and its consequence
for the multiplicative-weight potential in Section 3 of the manuscript.

An element of `α` represents one reward/threshold pair `(r,j)`.
The function `w` assigns its current nonnegative weight.  `D` is the set
covered by the demonstrator, and `A i` is the set covered by the
learner's i-th response (with zero-based indexing).

The `hGreedy` assumption states precisely the uncovered-weight inequality
provided by choosing a maximum-gain response.  It does *not* assume that
the demonstrator is optimal for any reward.
-/

namespace PassK

variable {α : Type*} [DecidableEq α]

/-- Total weight of the reward/threshold pairs in a finite set. -/
def weight (w : α → ℝ) (s : Finset α) : ℝ :=
  ∑ a ∈ s, w a

/-- Coverage accumulated from the first `n` choices. -/
def prefix (A : ℕ → Finset α) : ℕ → Finset α
  | 0 => ∅
  | n + 1 => prefix A n ∪ A n

@[simp] theorem prefix_zero (A : ℕ → Finset α) : prefix A 0 = ∅ := rfl

@[simp] theorem prefix_succ (A : ℕ → Finset α) (n : ℕ) :
    prefix A (n + 1) = prefix A n ∪ A n := rfl

/-- As more responses are selected, coverage can only grow. -/
theorem prefix_mono (A : ℕ → Finset α) : Monotone (prefix A) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [prefix_succ]
  exact Finset.subset_union_left

/-- A nonnegative weighting is monotone under set inclusion. -/
theorem weight_mono (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    {s t : Finset α} (hst : s ⊆ t) : weight w s ≤ weight w t := by
  change (∑ a ∈ s, w a) ≤ ∑ a ∈ t, w a
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (by
    intro a _ _
    exact hw a)

/-- One greedy step: coverage only by the learner is at least the
    remaining demonstrated coverage after that step. -/
theorem greedy_step (w : α → ℝ) (s C D : Finset α)
    (hGreedy : weight w (D \ s) ≤ weight w (C \ s)) :
    weight w (D \ (s ∪ C)) ≤ weight w ((C \ s) \ D) := by
  have h₁ : (C \ s) \ (D \ s) = (C \ s) \ D := by
    ext a
    simp only [Finset.mem_sdiff]
    tauto
  have h₂ : (D \ s) \ (C \ s) = D \ (s ∪ C) := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hid :
      weight w ((C \ s) \ D) - weight w (D \ (s ∪ C)) =
        weight w (C \ s) - weight w (D \ s) := by
    simpa only [weight, h₁, h₂] using
      (Finset.sum_sdiff_sub_sum_sdiff
        (s₁ := D \ s) (s₂ := C \ s) (f := w))
  linarith

/-- The increase in learner-only weight after adding a set. -/
theorem weight_union_increment (w : α → ℝ) (s C D : Finset α) :
    weight w ((s ∪ C) \ D) - weight w (s \ D) =
      weight w ((C \ s) \ D) := by
  have hsub : s \ D ⊆ (s ∪ C) \ D := by
    intro a ha
    rcases Finset.mem_sdiff.mp ha with ⟨has, hanD⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl has), hanD⟩
  have hid : ((s ∪ C) \ D) \ (s \ D) = (C \ s) \ D := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  simpa only [weight, hid] using
    (Finset.sum_sdiff_eq_sub
      (s₁ := s \ D) (s₂ := (s ∪ C) \ D) (f := w) hsub)

/-- One increment in learner-only coverage along the prefix sequence. -/
theorem weight_prefix_increment (w : α → ℝ) (A : ℕ → Finset α)
    (D : Finset α) (i : ℕ) :
    weight w (prefix A (i + 1) \ D) - weight w (prefix A i \ D) =
      weight w ((A i \ prefix A i) \ D) := by
  simpa only [prefix_succ] using
    (weight_union_increment w (prefix A i) (A i) D)

/-- Newly covered sets outside `D` partition final coverage outside `D`.
    This identity is proved, not supplied as an extra premise. -/
theorem weight_prefix_telescoping (w : α → ℝ) (A : ℕ → Finset α)
    (D : Finset α) (k : ℕ) :
    (∑ i ∈ Finset.range k, weight w ((A i \ prefix A i) \ D)) =
      weight w (prefix A k \ D) := by
  induction k with
  | zero =>
      simp [weight]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h := weight_prefix_increment w A D k
      linarith

/-- **Greedy weighted coverage** (Eq. `greedy_weight_comparison`).

If every response selected by greedy has at least as much *new* weighted
coverage as the demonstrated response, then the weight covered only
by the learner is at least `k` times the weight covered only by the
demonstrator.  Crucially, `D` may be completely arbitrary. -/
theorem greedy_weight_comparison (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (A : ℕ → Finset α) (D : Finset α) (k : ℕ)
    (hGreedy : ∀ i < k,
      weight w (D \ prefix A i) ≤ weight w (A i \ prefix A i)) :
    (k : ℝ) * weight w (D \ prefix A k) ≤
      weight w (prefix A k \ D) := by
  have hsum :
      (∑ _i ∈ Finset.range k, weight w (D \ prefix A k)) ≤
        ∑ i ∈ Finset.range k, weight w ((A i \ prefix A i) \ D) := by
    apply Finset.sum_le_sum
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hle : i + 1 ≤ k := Nat.succ_le_iff.mpr hik
    have hmono : prefix A (i + 1) ⊆ prefix A k :=
      prefix_mono A hle
    have hsub : D \ prefix A k ⊆ D \ prefix A (i + 1) := by
      intro a ha
      rcases Finset.mem_sdiff.mp ha with ⟨haD, han⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨haD, ?_⟩
      intro haa
      exact han (hmono haa)
    have hrest : weight w (D \ prefix A k) ≤
        weight w (D \ prefix A (i + 1)) :=
      weight_mono w hw hsub
    have hstep : weight w (D \ prefix A (i + 1)) ≤
        weight w ((A i \ prefix A i) \ D) := by
      simpa only [prefix_succ] using
        (greedy_step w (prefix A i) (A i) D (hGreedy i hik))
    exact hrest.trans hstep
  calc
    (k : ℝ) * weight w (D \ prefix A k) =
        ∑ _i ∈ Finset.range k, weight w (D \ prefix A k) := by
          simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.range k, weight w ((A i \ prefix A i) \ D) := hsum
    _ = weight w (prefix A k \ D) := weight_prefix_telescoping w A D k

/-- The asymmetric multiplicative update from Algorithm 1 of the paper.
    Missed pairs are multiplied by `1 + k/4`, exclusively learner-covered
    pairs by `3/4`, and all other pairs remain unchanged. -/
def update (k : ℕ) (D U : Finset α) (w : α → ℝ) (a : α) : ℝ :=
  if a ∈ D \ U then (1 + (k : ℝ) / 4) * w a
  else if a ∈ U \ D then (3 / 4 : ℝ) * w a
  else w a

/-- Positivity is preserved by the soft update. -/
theorem update_pos (k : ℕ) (D U : Finset α) (w : α → ℝ)
    (hw : ∀ a, 0 < w a) (a : α) : 0 < update k D U w a := by
  by_cases hD : a ∈ D \ U
  · have hfactor : 0 < 1 + (k : ℝ) / 4 := by positivity
    simpa [update, hD] using (mul_pos hfactor (hw a))
  · by_cases hU : a ∈ U \ D
    · have hfactor : (0 : ℝ) < 3 / 4 := by norm_num
      simpa [update, hD, hU] using (mul_pos hfactor (hw a))
    · simpa [update, hD, hU] using hw a

section FiniteUniverse
variable [Fintype α]

/-- Exact potential-change identity (Eq. `online_total_weight`). -/
theorem update_total (k : ℕ) (D U : Finset α) (w : α → ℝ) :
    weight (update k D U w) (Finset.univ : Finset α) =
      weight w (Finset.univ : Finset α) +
      (k : ℝ) / 4 * weight w (D \ U) -
      (1 / 4 : ℝ) * weight w (U \ D) := by
  classical
  have hdisjoint (a : α) (hD : a ∈ D \ U) : a ∉ U \ D := by
    intro hU
    exact (Finset.mem_sdiff.mp hU).2 (Finset.mem_sdiff.mp hD).1
  have hpoint (a : α) :
      update k D U w a = w a +
        (k : ℝ) / 4 * (if a ∈ D \ U then w a else 0) -
        (1 / 4 : ℝ) * (if a ∈ U \ D then w a else 0) := by
    by_cases hD : a ∈ D \ U
    · have hU := hdisjoint a hD
      simp [update, hD, hU]
      ring
    · by_cases hU : a ∈ U \ D
      · simp [update, hD, hU]
        ring
      · simp [update, hD, hU]
  have hsum (s : Finset α) :
      (∑ a : α, if a ∈ s then w a else 0) = weight w s := by
    have hf : (Finset.univ.filter (fun a => a ∈ s)) = s := by
      ext a
      simp
    calc
      (∑ a : α, if a ∈ s then w a else 0) =
          ∑ a ∈ (Finset.univ.filter (fun a => a ∈ s)), w a := by
            rw [Finset.sum_filter]
      _ = weight w s := by rw [hf]; rfl
  calc
    weight (update k D U w) (Finset.univ : Finset α) =
        ∑ a : α, (w a +
          (k : ℝ) / 4 * (if a ∈ D \ U then w a else 0) -
          (1 / 4 : ℝ) * (if a ∈ U \ D then w a else 0)) := by
            unfold weight
            apply Finset.sum_congr rfl
            intro a _
            exact hpoint a
    _ = weight w (Finset.univ : Finset α) +
          (k : ℝ) / 4 * weight w (D \ U) -
          (1 / 4 : ℝ) * weight w (U \ D) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, hsum, hsum]
            rfl

/-- The potential cannot increase whenever greedy coverage holds. -/
theorem update_total_le (k : ℕ) (D U : Finset α) (w : α → ℝ)
    (hCoverage : (k : ℝ) * weight w (D \ U) ≤ weight w (U \ D)) :
    weight (update k D U w) (Finset.univ : Finset α) ≤
      weight w (Finset.univ : Finset α) := by
  rw [update_total]
  nlinarith [hCoverage]

/-- **Algorithm-1 deterministic potential invariant.**  Assuming the
    actual greedy choice condition at each response, one full pass@k
    round of the asymmetric update cannot increase total weight. -/
theorem greedy_update_total_le (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (A : ℕ → Finset α) (D : Finset α) (k : ℕ)
    (hGreedy : ∀ i < k,
      weight w (D \ prefix A i) ≤ weight w (A i \ prefix A i)) :
    weight (update k D (prefix A k) w) (Finset.univ : Finset α) ≤
      weight w (Finset.univ : Finset α) :=
  update_total_le k D (prefix A k) w
    (greedy_weight_comparison w hw A D k hGreedy)

end FiniteUniverse
end PassK
