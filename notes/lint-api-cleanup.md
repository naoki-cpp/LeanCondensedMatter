# Full lint and API cleanup

Tracks the all-at-once implementation of issue #525.

The branch:

1. chooses canonical simp normal forms for the remaining targeted `simpNF` suppressions;
2. removes proof witnesses from value-level APIs when they only constrain downstream theorems;
3. makes diagram receivers participate meaningfully in their definitions;
4. removes unnecessary `DecidableEq Mode` constraints from public Fock-space aliases and downstream declarations;
5. replaces erased convergence/integrability witnesses with explicit total value definitions and theorem-level hypotheses;
6. keeps style-only linters separate from mathematical/API correctness.

The cross-cutting refactor and its first downstream compatibility pass have been applied. CI findings are now limited to validating the revised public signatures and remaining section-variable cleanup. The temporary inventory workflow will be removed before merge.
