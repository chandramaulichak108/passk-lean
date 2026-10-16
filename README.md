# Pass@k Lean Formalization

This repository contains a [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4) formalization of mathematical ingredients from [*The Statistical Benefits of Multiple Responses for Learning from Demonstrations*](https://arxiv.org/abs/2609.33291), by Chandramauli Chakraborty and Cong Ma.

The public entry point is [`PassK.lean`](PassK.lean). The files in [`PassK/`](PassK/) cover pass@k values for dependent response tuples, greedy coverage and multiplicative weights, online-to-batch identities, finite probability bounds, and testing-based lower-bound tools.

**Scope.** This is a **partial formalization**, not a machine-checked verification of all the paper's results. The full online-regret theorem, algorithm-specific exponential-moment inequality, high-probability guarantees, and minimax rates remain open. See [`PROOF_STATUS.md`](PROOF_STATUS.md) for the theorem-by-theorem ledger.

## Formalized components

- [`PassK/Coverage.lean`](PassK/Coverage.lean) provides `PassK.greedy_weight_comparison` and `PassK.greedy_update_total_le`, the weighted greedy-coverage comparison and one-step potential inequality.
- [`PassK/OnlineRegret.lean`](PassK/OnlineRegret.lean) proves `PassK.total_weight_le_initial`, the non-increasing total-weight invariant **conditional on** the roundwise coverage inequalities.
- [`PassK/PolicyMixture.lean`](PassK/PolicyMixture.lean) and [`PassK/OneStepIID.lean`](PassK/OneStepIID.lean) formalize averaging entire pass@k response tuples and the one-step expected-regret/population-excess identity. Dependence within each response tuple is allowed.
- [`PassK/FiniteTail.lean`](PassK/FiniteTail.lean) and [`PassK/FiniteTesting.lean`](PassK/FiniteTesting.lean) develop finite-event tail/union bounds and an elementary two-point testing lower bound.
- [`PassK/MomentToTail.lean`](PassK/MomentToTail.lean), [`PassK/StandardRobustPAC.lean`](PassK/StandardRobustPAC.lean), and [`PassK/LowerBounds.lean`](PassK/LowerBounds.lean) give **conditional reductions**. Their assumptions include the moment bounds, generalization steps, or hard-instance witnesses still needed for the paper's main conclusions.

These modules are supporting lemmas rather than complete paper-facing upper- and lower-bound proofs. The source is written without project-specific `axiom` declarations or `sorry` placeholders; that fact alone does not establish that the paper's claims have been proved.

## Verification

Install Lean through [`elan`](https://github.com/leanprover/elan). From the repository root, run:

```bash
lake update
lake exe cache get
lake build
```

The Lean toolchain is specified in [`lean-toolchain`](lean-toolchain), and Mathlib is declared in [`lakefile.toml`](lakefile.toml). A successful build checks the declarations in the imported modules, **not** the unformalized manuscript theorems. Build success for the entire repository has not yet been independently confirmed.

## Repository structure

```text
PassK.lean            Main Lean import entry point
PassK/                Definitions and mathematical proof modules
PROOF_STATUS.md       Theorem correspondence and outstanding proof obligations
lakefile.toml         Lake project configuration and Mathlib dependency
lake-manifest.json    Locked dependency revisions
lean-toolchain        Pinned Lean toolchain
```

## License

No repository-level code license has been added yet.
