# MassiveDirac transport context

This context defines the domain language for finite-cutoff MassiveDirac transport calculations and their current-response constructions.

## Current response

**Current-rung**:
A finite-broadening Born-Dyson coefficient describing how an in-plane source current is transferred to measured in-plane directions before it is inserted into a response trace. It is not itself a conductivity or a complete response value.
_Avoid_: conductivity, dressed response, full ladder observable

**Dressed current insertion**:
A source-indexed current operator after the retarded-advanced ladder dressing has been applied. It belongs to the retarded-advanced block; same-side remainders and response normalization remain separate physical contributions.
_Avoid_: full Středa response, exact disorder-averaged current

**Ladder regularity**:
The nonvanishing condition that allows a total algebraic ladder solution to be interpreted as the physical fixed-point solution. The algebraic solution itself exists independently of this interpretation condition.
_Avoid_: existence of the ladder solution, disorder positivity
