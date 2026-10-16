# Lean 4 formalization of pass@k learning

This repository accompanies **[Pass@k Feedback for Apprenticeship Learning](https://arxiv.org/abs/2609.33291)**. It develops a Lean 4 / Mathlib formalization of the paper's deterministic learning argument, exponential-moment method, PAC bounds, and information-theoretic minimax analysis.

**Status: formalization in progress.** The existing finite-space foundation and the staged proof modules below are not equivalent to a machine-checked verification of every manuscript theorem. In particular, several important mathematical dependencies still require Lean proofs. See [PROOF_STATUS.md](PROOF_STATUS.md) for a precise theorem-level ledger.

## Proof organization

| Stage | Main result | Lean files | Scope of current work |
| --- | --- | --- | --- |
| **1** | Online regret | [`Coverage.lean`](PassK/Coverage.lean), [`OnlineRegret.lean`](PassK/OnlineRegret.lean), [`Stage1LogPotential.lean`](PassK/Stage1LogPotential.lean), [`Stage1LogUpdates.lean`](PassK/Stage1LogUpdates.lean) | Greedy weight invariant, log-sum bound, exact log-update telescope, regret arithmetic; threshold-to-regret identification still needed |
| **2** | Exponential moment | [`Stage2Exponential.lean`](PassK/Stage2Exponential.lean), [`MomentToTail.lean`](PassK/MomentToTail.lean) | Exponential chord inequalities, single-step moment calculation, final budget reduction; adaptive conditional iteration not yet proved |
| **3** | Standard / robust PAC upper bounds | [`FiniteTail.lean`](PassK/FiniteTail.lean), [`StandardRobustPAC.lean`](PassK/StandardRobustPAC.lean), [`Stage3Rates.lean`](PassK/Stage3Rates.lean) | Markov, finite union bound, logarithmic constants; PAC implications are conditional on the missing algorithmic moment bound |
| **4** | Minimax lower bounds | [`FiniteTesting.lean`](PassK/FiniteTesting.lean), [`Stage4LeCam.lean`](PassK/Stage4LeCam.lean) | Two-point testing via overlap and total variation; Fano/Assouad and the paper's hard-instance families remain |
| **5** | Minimax rate theorems | [`LowerBounds.lean`](PassK/LowerBounds.lean), [`Stage5Minimax.lean`](PassK/Stage5Minimax.lean) | Finite minimax definitions and explicit upper/lower-bound combination; the paper's rate witnesses are not yet proved |

Other modules define pass@k values for **possibly dependent response tuples**, the mixture of full policy snapshots, and the one-step population-excess identity. The policy-mixture construction samples one snapshot and draws the entire tuple from that snapshot, rather than independently mixing individual responses.

## Build

Install Lean using [elan](https://lean-lang.org/install/). This project pins **Lean 4.34.1** (see `lean-toolchain`). From the repository root:

```bash
lake update
lake exe cache get
lake build
```

The [GitHub Actions workflow](.github/workflows/lean.yml) also runs the build. A successful build verifies the statements implemented in Lean, **not** unimplemented manuscript theorems. This expanded set of modules has not yet been compiled with the pinned toolchain in the authoring environment; further compiler corrections may be needed.

## Research-paper theorem coverage

The paper's primary theorems correspond to `thm:online-regret`, `lem:exponential_moment`, `thm:standard_passk_upper`, `thm:robust_passk_upper`, and the standard/robust minimax lower-bound theorems. The declarations and remaining proof obligations are itemized in [PROOF_STATUS.md](PROOF_STATUS.md).

The project uses neither `sorry` nor new axioms to disguise unfinished arguments. A lemma with a hypothesis such as `hmoment` or `hard` verifies only an implication **from that hypothesis**; it does not prove the hypothesis for the paper's algorithm or hard-instance construction.
