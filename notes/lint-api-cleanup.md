# Full lint and API cleanup

Tracks the all-at-once implementation of issue #525.

The branch will:

1. choose canonical simp normal forms for the remaining targeted `simpNF` suppressions;
2. remove proof witnesses from value-level APIs when they only constrain downstream theorems;
3. make diagram receivers participate meaningfully in their definitions;
4. remove unnecessary `DecidableEq Mode` constraints from public Fock-space aliases and downstream declarations;
5. replace erased convergence/integrability witnesses with an explicit raw/bundled API design;
6. keep style-only linters separate from mathematical/API correctness unless they can be enabled without repository-wide churn.

The temporary inventory workflow will be removed before merge.
