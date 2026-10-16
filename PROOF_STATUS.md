# Proof ledger for `arxiv_main_v2.tex`

This ledger distinguishes a **proof of the manuscript theorem** from a **proved implication subject to unproved hypotheses**. The listed main manuscript theorems are *not* yet formalized as complete Lean proofs. The current source is a research formalization in progress, not a verified reproduction of the paper.

Status of the seven main theorems and two additional named results:

| Label in LaTeX | Manuscript statement | Current Lean contribution | Missing proof components |
| --- | --- | --- | --- |
| `thm:standard_passk_upper` | Standard pass@k PAC bound | `PolicyMixture`, `OneStepIID`, `MomentToTail`, `StandardRobustPAC`, `Coverage`, `OnlineRegret` prove or encode some deterministic/conditional steps | Full online-regret log potential, algorithm-specific exponential moment, history conditional-expectation argument, exact sample-complexity constants |
| `thm:standard_passk_lower` | Standard pass@k minimax lower bound | `FiniteTesting` tests two finite worlds; `LowerBounds` generic minimax reduction | Class construction with prescribed cardinality, list-decoding information bound, class/confidence lower components and their combination |
| `thm:standard_pass1_lower` | Standard pass@1 lower bound with suboptimality | `FiniteTesting` overlap testing lower bound; `TwoPoint` zero-information toy example | Class hard instance and KL calculations, list Fano, Assouad and two-point testing for nonzero bias, exact parameter ranges |
| `thm:robust_passk_upper` | Robust pass@k PAC bound | `FiniteTail` union bound, `StandardRobustPAC.robustPAC_from_moments` | Establish the moment estimate for the algorithm, convert to robust supremum and sample-complexity numerical constants |
| `thm:robust_passk_lower` | Robust pass@k minimax lower bound | Generic minimax/testing lemmas | Hard family, coverage/inclusion budget, tail bounds, combine class and confidence components |
| `thm:robust_pass1_lower` | Robust pass@1 minimax lower bound | Generic testing lemma | Hypercube family and Assouad, neighboring KL, suboptimality constraints, confidence family |
| `thm:online-regret` | Pathwise bounded online regret | `Coverage`, `GreedyCoverage`, `OnlineRegret`, `Bounds`, `Preliminaries` | Full reward-threshold log increment identity, AM–GM across L thresholds, exact theorem conclusion and log inequalities |
| `lem:exponential_moment` | Algorithmic exponential-moment inequality | `MomentToTail` proves the *consequence* of a hypothesized moment inequality | One-step exponential chord inequality, filtration/conditional expectation and nonnegative supermartingale with algorithm's weights |
| `thm:list_decoding_fano` | List-decoding Fano inequality (appendix) | No complete counterpart | Entropy/KL formalization and list-Fano proof |

## Implemented building blocks

* `PassK/Values.lean`: finite probability laws and population pass@k value of possibly dependent tuples.
* `PassK/Definitions.lean`: optimal value, demonstrator gap and its nonnegativity, robust and standard criteria.
* `PassK/Coverage.lean`, `PassK/GreedyCoverage.lean`: finite greedy-coverage implications and potential update.
* `PassK/OnlineRegret.lean`: positive-weight and non-increasing total-weight invariants; conditional deterministic regret arithmetic.
* `PassK/Bounds.lean`, `PassK/Preliminaries.lean`: signed-regret and quantization-error arithmetic.
* `PassK/FiniteTail.lean`: finite Markov inequality and union bounds.
* `PassK/MomentToTail.lean`: if the exponential moment bound holds, obtain a tail bound.
* `PassK/PolicyMixture.lean`: a finite uniform mixture of laws over whole k-tuples; its expected value and pass@k value average linearly, and so does signed excess.
* `PassK/OneStepIID.lean`: algebraic expected one-step regret equals population excess for a fixed snapshot and finite fresh-example distribution.
* `PassK/StandardRobustPAC.lean`: fixed-reward and robust high-probability consequences **assuming** an exponential moment and online-to-batch reduction.
* `PassK/FiniteTesting.lean`: finite two-point overlap testing bound and the associated max-error lower bound.
* `PassK/LowerBounds.lean`, `PassK/TwoPoint.lean`: general minimax implication and a zero-information toy lower bound.

## Why these steps do not constitute a proof of all results

The probabilities and bounds in `StandardRobustPAC.lean` include hypotheses named `hmoment` and `hreduction`. Those hypotheses must still be derived from the specific learner and its sampling law. Merely supplying those hypotheses does not prove the manuscript's theorems. Similarly, the `hard` hypothesis in `LowerBounds.lean` demands an adversarial witness for every algorithm; the manuscript constructs those witnesses via nontrivial hard families that are not in the Lean project.

## Verification and build

This delivery was **statically inspected but not compiled**: there is no Lean/Lake executable and no network access for downloading the pinned toolchain in the generation environment. The user's previous build logs validated some earlier files, not the new ones. Do not announce a fully machine-checked result until `lake build` succeeds and the statements have been audited line-by-line for equivalence to the paper. The new files are imported by `PassK.lean`, so `lake build` will check them.

```bash
lake update
lake exe cache get
lake build
```

There are no declared `sorry` or `axiom` shortcuts in these source files. A `sorry`-free project still proves only what its declaration statements actually say.
