# Lean 4 project for pass@k imitation/apprenticeship learning

This is a **partial formalization** accompanying `arxiv_main_v2.tex`.

This revision addresses the compiler errors reported on Lean **4.34.1**
by using `NNReal`, renaming the reserved identifier `prefix` to
`coveragePrefix`, correcting the sign of a Finset identity, and
fixing an over-aggressive rewrite in `Bounds.lean`.
It covers the finite-space evaluation objectives and deterministic
components of the greedy, multiplicative-weight online learner.
It **does not** yet formally verify the main high-probability or minimax
sample-complexity claims of the paper.

## Project layout

```text
PassK.lean                  umbrella import
PassK/Values.lean           finite probability distributions; pass@k values;
                            dependent candidate responses; robust excess
PassK/Definitions.lean      pointwise optimal value; demonstrator gap;
                            standard and robust success predicates
PassK/Bounds.lean           signed regret, rounding accumulation, sqrt bound
PassK/Preliminaries.lean    arithmetic regret-bound reductions
PassK/Coverage.lean         greedy-weight comparison; weight-update identity
PassK/GreedyCoverage.lean   maximal-gain candidate selection implies coverage
PassK/OnlineRegret.lean     positivity and cross-round potential invariant;
                            conditional regret-reduction lemma
PassK/UpperBounds.lean      robust bounds imply standard bounds
PassK/LowerBounds.lean      finite minimax definitions and reduction principle
```

## Source-to-Lean correspondence

| Paper component | Lean declaration | Status |
|---|---|---|
| Section 2, `V_r^k` with possibly dependent responses | `PassK.Finite.passKValue` | Defined |
| Section 2, `V_r(demo) - V_r^k(pi)` | `PassK.Finite.excess` | Defined |
| Section 2, robust excess over a finite reward class | `PassK.Finite.robustExcess` | Defined |
| Section 2, `V_r^*` and `Δ_r` | `pointwiseOptimal`, `optimalValue`, `demonstratorGap` | Defined |
| Eq. `greedy_weight_comparison` | `greedy_weight_comparison` | Proof supplied |
| Greedy maximal-gain condition | `greedy_weight_comparison_of_maximality` | Proof supplied |
| Eq. `online_total_weight` | `update_total` | Proof supplied |
| Positive multiplicative weights | `weightsAfter_pos` | Proof supplied |
| Repeated-round potential | `total_weight_le_initial`, `greedy_total_weight_le_initial` | Proof supplied under explicit greedy assumptions |
| Quantization error accumulation | `quantization_round_sum` | Proof supplied under per-round error premise |
| Robust-to-standard implication | `robustGood_implies_standardGood` | Proof supplied |
| Minimax risk and basic adversary reduction | `minimaxRisk`, `minimax_lower_bound` | Definition/proof supplied |
| Full Theorem `online-regret` (sharp `log |R| / log k` rate) | — | **Not yet formalized** |
| Section 2 high-probability bounds | — | **Not yet formalized** |
| Section 2 standard and robust minimax rates | — | **Not yet formalized** |
| Exponential-moment / online-to-batch generalization | — | **Not yet formalized** |

The greedy proof uses `A i : Finset α` for the set covered by response
`i` and `D : Finset α` for coverage by the demonstrator. The weighted
potential inequality does not assume the demonstrator is optimal.

## Build and checking

1. Install [elan](https://github.com/leanprover/elan).
2. In the root directory containing `lakefile.toml` run:

```sh
lake update
lake exe cache get
lake build
```

GitHub Actions also runs `lake build` on a push/pull request.

**Important:** A Lean compiler and Mathlib are not available in the
creation environment. Hence **this revision has not been checked by `lake build`**.
Other compilation failures are possible; do not cite these files as a
completed machine-checked formalization until that check succeeds.
No `sorry`, `admit`, or user-declared `axiom` is used to claim the paper's
main statistical theorems.

## Next steps toward full formalization

1. Confirm compilation and adjust Mathlib API names if required.
2. Prove the log-weight telescoping and AM--GM bounds to close the full
   online-regret theorem (including nested threshold coverage).
3. Define a learning rule on a probability space and formalize
   online-to-batch and concentration arguments.
4. Encode hard families and the KL/Fano/Assouad reductions for each
   finite-sample minimax lower bound.
5. Map each formal theorem statement to the exact LaTeX theorem and
   audit all assumptions before advertising formal verification.

## Compilation notes (October 2026)

The current version uses the Lean 4.34.1 toolchain specified in `lean-toolchain`.
`Values.lean` explicitly supplies the index type and function to `Finset.le_sup`;
`Preliminaries.lean` combines two signed-regret bounds by linear arithmetic.

This environment does not include the Lean compiler, so the updated project
has **not been tested** with `lake build` here. Please compile it locally, and
inspect any remaining messages. Warnings about unused section variables are
nonfatal.
