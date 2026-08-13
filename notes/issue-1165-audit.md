# Issue #1165: exchange-weight ownership audit

This audit records the declarations that are Statistics-generic in substance and the resulting
Common/Fermionic/Bosonic ownership boundary.

## Quartic

- `QuarticDiagram.pairingInOrder_crossingCount_mod_two_eq_sum_components`
- `QuarticDiagram.pairingInOrder_weight_eq_prod_components`

Their proof uses only Common quartic component/order/pair geometry, perfect-pairing crossing algebra,
and the Common `Statistics` pairing weight. The authoritative owner is
`SecondQuantization.Common.Diagrammatics.Quartic.ComponentGlobalCrossingParity`.

`QuarticDiagram.pairingInOrder_evaluation_eq_prod_components` is the shared scalar endpoint: it keeps
`Combinatorics.Pairing.evaluation` as the unique evaluator and combines the generic weight theorem
with arbitrary pair-kernel reindexing. Bosonic and Fermionic consumers only supply their concrete
pair kernels and kernel-locality theorems.

## TwoPoint crossing and weight

The mixed-time component crossing geometry remains in the Fermionic TwoPoint layer because its
component-pair fibers and stable mixed-event ordering are currently defined there. Moving that
geometry to Common would require a broader mixed-order representation refactor, not merely an
exchange-weight extraction.

The Statistics algebra does not remain duplicated there. Common PairingWeight owns the generic
finite-family statement

- `zetaInt_pow_eq_prod_of_sum_mod_two_eq`,

and both generic `Pairing.weight_eq_prod_of_crossingCount_mod_two_eq` and the TwoPoint
`pairingInMixedOrder_weight_eq_prod_components` reduce to that backend. Thus the TwoPoint layer proves
its own parity statement but does not implement its own finite-product exchange-sign algebra.

Component-time transport, chamber regularity, Gibbs-contraction locality, and the active fiber/LCT
proof remain outside #1165's ownership move.

## External-order factor

`twoPointExternalOrderSign τ τ' = if τ < τ' then ζ_fermion else 1` is correctly interpreted as the
exchange factor for swapping the two odd external fields under the stable mixed-event convention.
Moving an external field past a quartic interaction vertex contributes no factor because the
interaction vertex is exchange-even.

No new Common helper is introduced at this stage. Common already owns the genuinely shared
Statistics-generic two-operator `timeOrderedProduct`, whose equal-time convention is symmetric
(`theta(0) = 1/2`). The mixed-event external sign instead uses the stable-rank convention and has only
a Fermionic two-point consumer today. Extracting a one-use `if τ < τ' then ζ(s) else 1` wrapper would
add API without deleting a parallel implementation. A Common event-parity helper becomes justified
when a Bosonic/Statistics-generic two-point or n-point mixed-event consumer exists.

## Invariants

- `Combinatorics.Pairing.evaluation` remains the unique scalar pairing evaluator.
- `Combinatorics.ExchangeSign` remains the arbitrary involutive-scalar algebra layer; #1165 does not
  generalize diagram APIs from physical `Statistics` to arbitrary `ζ` without a consumer.
- Dyson `(-1)^interactionOrder` remains separate from `Statistics.zeta ^ crossingCount`.
- No CAR/CCR, Gibbs-state, thermal-kernel, or convergence declaration moves into Common.
- #894's active linked-cluster proof route is unchanged; the temporary historical Fermionic quartic
  parity import exists only to avoid changing that route while the Common owner is introduced.
