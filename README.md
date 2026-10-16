# Lean 4 formalization: pass@k greedy coverage

This repository accompanies the manuscript supplied as `arxiv_main_v2.tex`.
It is a **partial formalization**, focused on the deterministic proof core of
Section 3, *Learning algorithm and analysis*.  It is not a formal verification
of the full statistical/minimax results.

## Correspondence with the paper

`PassK/Values.lean` formalizes the **finite-space evaluation definitions**:
`FiniteDistribution`, `bestReward`, `demonstratorValue`, `passKValue`,
`excess`, and `robustExcess`. The policy is a distribution over entire
response tuples, so this model explicitly permits **dependent** responses.


| Lean declaration | Mathematical result |
|---|---|
| `PassK.Finite.excess_le_robust` | Standard excess is bounded by robust excess for any reward in the class. |
| `PassK.greedy_step` | One greedy response's uncovered weighted gain controls the remaining demonstrated mass. |
| `PassK.weight_prefix_telescoping` | Newly covered, learner-only sets partition `U_t \ D_t`. |
| `PassK.greedy_weight_comparison` | Equation `greedy_weight_comparison`: `w(U_t \ D_t) ≥ k · w(D_t \ U_t)`. |
| `PassK.update` | The asymmetric soft-weight update of Algorithm 1: factors `1 + k/4` and `3/4`. |
| `PassK.update_pos` | Strictly positive weights remain strictly positive. |
| `PassK.update_total` | Equation `online_total_weight`: exact change of total weight. |
| `PassK.greedy_update_total_le` | One greedy update does not increase the total potential. |
| `PassK.signed_increment_bound` | Signed-regret control by asymmetric log-weight increments (an algebraic abstraction). |
| `PassK.quantization_round_sum` | Cumulative rounding loss of at most `T η`, with `η = 1/L`. |
| `PassK.sqrt_le_one_add_div_four` | The inequality `√k ≤ 1+k/4` underlying the logarithmic improvement. |

### Meaning of the greedy premise

`A i` is the set of reward-threshold pairs reached by the `(i+1)`-st
response. `prefix A i` is the union of the first `i` selected sets.
The theorem assumes:

```text
for every i < k:
  weight (D \ prefix A i) ≤ weight (A i \ prefix A i)
```

This is the precise greedy marginal-gain inequality. In the paper it follows
from choosing the highest-gain available response, with the special case that
if the demonstrated response was already selected its remaining gain is zero.
The Lean files prove all ensuing finite-set algebra and the resulting
multiplicative potential invariant. The argmax implementation and its tie
breaking are **not yet** mechanically formalized.

## Build

Lean and Mathlib are pinned to version `v4.34.1`.
Install [elan](https://github.com/leanprover/elan) and then run:

```bash
lake update
lake exe cache get
lake build
```

The GitHub Actions workflow in `.github/workflows/lean.yml` builds the project
on every push and pull request.

> **Verification status:** The source was drafted without access to a Lean
> compiler in the authoring environment, so a successful local `lake build`
> has **not been confirmed**. The formalization uses no `sorry`, `admit`,
> or user-declared axioms. Successful Lean compilation, rather than the
> absence of those tokens, is required before calling these proofs verified.

## Not yet formalized

- Derivation of the greedy premise from an executable `argmax` selection.
- The full logarithmic-weight telescoping/AM–GM estimate in Theorem
  `online-regret`.
- Conditional-expectation and exponential-supermartingale arguments in
  Lemma `exponential_moment`.
- Online-to-batch randomized policy construction and the high-probability
  sample-complexity theorems.
- Fano/Assouad minimax lower bounds, standard and robust.

No full-paper theorem is silently represented as already verified.
