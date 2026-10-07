# SecondQuantization R2 roll-up

PRs #355, #357, and #359 were originally merged into their preceding feature branches rather than directly into `main`. PR #361 reapplies only the net R2 diff from the #353 head to the final R2 head onto the default branch.

The roll-up contains no new mathematical changes. It preserves the previously validated discrete and continuous Dyson ownership cleanup and exists only to make those merged stack changes part of `main` before R3 begins.
