# Pass@k Lean Formalization

This repository contains a **Lean 4 formalization** of mathematical results and proof techniques associated with [*The Statistical Benefits of Multiple Responses for Learning from Demonstrations*](https://arxiv.org/abs/2609.33291), by Chandramauli Chakraborty and Cong Ma.

The formalization uses [Mathlib](https://github.com/leanprover-community/mathlib4) and covers pass@k values for potentially dependent response tuples, greedy coverage and multiplicative weights, online-to-batch identities, finite probability inequalities, and tools for minimax lower bounds. The main entry point is [`PassK.lean`](PassK.lean).

## Formalized components

- **Pass@k values and policies.** [`Values.lean`](PassK/Values.lean), [`Definitions.lean`](PassK/Definitions.lean), and [`PolicyMixture.lean`](PassK/PolicyMixture.lean) define pass@k evaluation and policy mixtures over *complete response tuples*, allowing dependence among responses.
- **Greedy coverage and online learning.** [`Coverage.lean`](PassK/Coverage.lean), [`OnlineRegret.lean`](PassK/OnlineRegret.lean), [`Stage1LogPotential.lean`](PassK/Stage1LogPotential.lean), and [`Stage1LogUpdates.lean`](PassK/Stage1LogUpdates.lean) develop weighted-coverage inequalities, the non-increasing potential invariant, and logarithmic weight identities.
- **Probability and generalization.** [`FiniteTail.lean`](PassK/FiniteTail.lean), [`MomentToTail.lean`](PassK/MomentToTail.lean), [`OneStepIID.lean`](PassK/OneStepIID.lean), and [`StandardRobustPAC.lean`](PassK/StandardRobustPAC.lean) contain finite tail bounds, the policy-mixture regret identity, and conditional standard/robust PAC reductions.
- **Information-theoretic lower-bound tools.** [`FiniteTesting.lean`](PassK/FiniteTesting.lean), [`Stage4LeCam.lean`](PassK/Stage4LeCam.lean), [`LowerBounds.lean`](PassK/LowerBounds.lean), and [`Stage5Minimax.lean`](PassK/Stage5Minimax.lean) formalize two-point testing arguments and general minimax comparison principles.

Further staged developments are in [`Stage2Exponential.lean`](PassK/Stage2Exponential.lean) and [`Stage3Rates.lean`](PassK/Stage3Rates.lean).

## Verification

The project targets **Lean 4.34.1**, as specified in [`lean-toolchain`](lean-toolchain). Install Lean with [elan](https://lean-lang.org/install/) and run from the repository root:

```bash
lake update
lake exe cache get
lake build
```

A successful build machine-checks the theorem statements and proofs included in the compiled Lean modules. The [GitHub Actions workflow](.github/workflows/lean.yml) runs the project build on pushes and pull requests.

## Scope

This repository **does contain a formalization**, including proved foundational lemmas and useful reductions. It is **not yet a complete, end-to-end machine-checked verification of every main theorem** in the paper: some paper-level claims still depend on algorithm-specific moment bounds or minimax constructions not yet discharged in Lean. Compilation of all staged modules also remains to be confirmed. See [`PROOF_STATUS.md`](PROOF_STATUS.md) for the detailed theorem-by-theorem correspondence.

## Repository structure

```text
PassK.lean             Main Lean entry point
PassK/                 Definitions, lemmas, and staged proof modules
PROOF_STATUS.md        Theorem correspondence and verification scope
lakefile.toml          Lake and Mathlib configuration
lean-toolchain         Pinned Lean version
.github/workflows/     Automated build checks
```
