# Pass@k Lean Formalization

This repository contains a Lean 4 formalization of mathematical components of [*The Statistical Benefits of Multiple Responses for Learning from Demonstrations*](https://arxiv.org/abs/2609.33291) by Chandramauli Chakraborty and Cong Ma. The public entry point is [`PassK.lean`](PassK.lean); the `PassK/` directory contains finite-space models, greedy-coverage arguments, probabilistic reductions, and testing lemmas.

**Scope:** This is a partial formalization. The paper's complete high-probability, online-regret, and minimax theorems are **not yet machine-verified**. See [`PROOF_STATUS.md`](PROOF_STATUS.md) for a theorem-by-theorem account.

## Formalized components

- [`PassK/Coverage.lean`](PassK/Coverage.lean) contains `PassK.greedy_weight_comparison` and `PassK.greedy_update_total_le`, for the weighted greedy-coverage comparison and one-step potential inequality.
- [`PassK/OnlineRegret.lean`](PassK/OnlineRegret.lean) contains `PassK.total_weight_le_initial`, bounding total multiplicative weight across rounds **assuming** the stated coverage inequalities.
- [`PassK/PolicyMixture.lean`](PassK/PolicyMixture.lean) contains `PassK.Finite.passKValue_averagedPolicy`, showing that the value of a uniform mixture of **whole response tuples** is the average snapshot value; tuple coordinates may be dependent.
- [`PassK/OneStepIID.lean`](PassK/OneStepIID.lean) contains `PassK.Finite.oneStepExpectedRegret_eq_excess`, identifying one-round expected signed regret with population excess for a fixed snapshot.
- [`PassK/FiniteTail.lean`](PassK/FiniteTail.lean) and [`PassK/FiniteTesting.lean`](PassK/FiniteTesting.lean) contain finite probability union/Markov bounds and a two-point testing lower bound.
- [`PassK/MomentToTail.lean`](PassK/MomentToTail.lean), [`PassK/StandardRobustPAC.lean`](PassK/StandardRobustPAC.lean), and [`PassK/LowerBounds.lean`](PassK/LowerBounds.lean) establish **conditional reductions**: their hypotheses include, respectively, the needed moment estimates, online-to-batch bounds, or hard-instance witnesses. They do **not** prove those substantive hypotheses.

The source files do not introduce project-specific axioms or `sorry` placeholders. This does not by itself verify the manuscript's results: the theorem statements and their assumptions must also match the paper, and the project must compile successfully.

## Verification

Install Lean via [`elan`](https://github.com/leanprover/elan), then from the repository root run:

```bash
lake update
lake exe cache get
lake build
```

The Lean toolchain is specified in [`lean-toolchain`](lean-toolchain) (Lean 4.34.1), and Mathlib is declared in [`lakefile.toml`](lakefile.toml). GitHub Actions runs the project build on pushes and pull requests. The current source package has **not yet been confirmed to pass a complete build** with all modules; do not report a fully verified result before the build and theorem-assumption audit succeed.

## Repository structure

```text
PassK.lean             Main import entry point
PassK/                 Definitions, coverage, regret, tail, and testing lemmas
PROOF_STATUS.md        Paper theorem-to-Lean correspondence and open obligations
lakefile.toml          Lake package and Mathlib dependency
lean-toolchain         Pinned Lean version
.github/workflows/     Automated build workflow
```

## License

No repository code license is included at present.
