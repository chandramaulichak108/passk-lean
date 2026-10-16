# Formalization status against `arxiv_main_v2.tex`

**As of 2026-10-16: NOT A COMPLETE MACHINE-CHECKED FORMALIZATION.**
The expanded modules in this delivery were authored and statically inspected but **not executed by Lean**, because `lean`/`lake` are absent from the available runtime and outbound network access is unavailable. Existing user-provided logs validate selected earlier modules, not this expanded project. Compiling the new files is the next requirement.

The README is intentionally precise about the distinction between a mathematical theorem in the manuscript, a Lean proof of its actual statement, and a Lean *conditional reduction* whose hypotheses are not yet discharged.

## Stage 1 — online regret (`thm:online-regret`)

**In Lean source**
- `Coverage.greedy_weight_comparison`: greedy coverage inequality and non-increasing total potential.
- `OnlineRegret.total_weight_le_initial`: roundwise pathwise potential invariant.
- `Stage1LogPotential.log_le_scaled_tangent`: `log x ≤ log N + x/N − 1`.
- `Stage1LogPotential.sum_log_le_card_log_of_mass`: AM–GM/log sum step.
- `Stage1LogPotential.greedy_final_log_bound`: applies the potential invariant to fixed thresholds.
- `Stage1LogUpdates.log_update_identity` and `log_weightsAfter_telescope`: exact per-pair logarithmic increments and telescoping.
- `Stage1LogPotential.online_regret_of_log_comparison`: exact rounding-plus-regret conclusion **assuming** `hlogregret`.

**Still to discharge:** connect reward quantization and the sets of covered `(reward, threshold)` pairs to `logStep`, prove the fixed-reward signed quantized-regret log inequality using the telescoping identity and the nested-threshold property, instantiate cardinality normalization with `R × Fin L`, and prove the binary `L=1` refinement.

## Stage 2 — exponential moment (`lem:exponential_moment`)

**In Lean source**
- `Stage2Exponential.exponential_chord`: convex exponential chord.
- `exp_shortfall_chord`, `exp_gain_chord`, `signed_exponential_chord`: exact one-step exponential inequality for `ell ∈ [-1,1]`.
- `signed_chord_expected`, `one_step_exponential_supermartingale`: one-step finite expected-moment calculation.
- `exponential_moment_of_supermartingale_budget`: pathwise-to-moment conclusion conditional on `hKmean`.

**Still to discharge:** construct finite histories and the adaptive snapshot transition law, prove conditional measurability/independence, iterate the one-step bound to establish `E[K_m] ≤ 1`, connect `Z` with the algorithm's final log weights, and verify the exact coefficient `θ_k` used in the manuscript.

## Stage 3 — high-probability upper bounds (`thm:standard_passk_upper`, `thm:robust_passk_upper`)

**In Lean source**
- `FiniteTail`: finite Markov inequality and finite union bound.
- `MomentToTail`: exponential-moment-to-tail implication.
- `PolicyMixture`, `OneStepIID`: complete-tuple mixture and one-step population regret definitions.
- `StandardRobustPAC`: conditional standard and robust PAC implications.
- `Stage3Rates`: `log(1+k/4) ≥ log k/2`, `2 log(3/2) < 1`, and the update-coefficient comparison.

**Still to discharge:** derive the `hmoment` and `hreduction` hypotheses from the actual learning rule and the fresh IID sample, including the final `L=m` substitution and exact event thresholds. None of the paper's high-probability theorems is currently an unconditional Lean theorem.

## Stage 4 — lower bounds (`thm:standard_passk_lower`, `thm:standard_pass1_lower`, `thm:robust_passk_lower`, `thm:robust_pass1_lower`)

**In Lean source**
- `FiniteTesting`: overlap-based two-point lower bound for arbitrary randomized tests.
- `Stage4LeCam`: finite total variation, exact overlap identity, and Le Cam's `(1-TV)/2` lower bound.

**Still to discharge:** explicitly construct the manuscript's families of distributions, finite reward classes with exactly `N` members, list-Fano inequality, coding/list-decoding arguments, Assouad hypercube, KL computations, confidence terms, demonstrator-optimality and suboptimality constraints, and all integer/ceiling constant manipulations.

## Stage 5 — minimax rates (corollaries of upper/lower theorem statements)

**In Lean source**
- `LowerBounds`: minimax risk and the hard-instance witness principle.
- `Stage5Minimax`: upper bound from a specific algorithm, a two-sided minimax sandwich, and combining two lower components using `max ≥ (a+b)/2`.

**Still to discharge:** actual algorithm construction and actual adversarial witnesses from Stages 1–4; full sample-complexity definitions quantifying over algorithms and all sample counts; final standard/robust rate statements with their exact parameter regimes. Generic sandwich lemmas alone do not prove the paper's rates.

## Verification checks

Run from the repository root:

```bash
lake build
rg -n '\bsorry\b|^axiom\b' PassK --glob '*.lean'
```

This search alone does not establish completeness. Lean does not prove a theorem merely because a file is named `UpperBounds.lean` or `LowerBounds.lean`; the declaration statement must be audited against the LaTeX theorem. As the stages are completed, mark them **machine-checked** only after successful compilation of the corresponding import tree and statement review.
