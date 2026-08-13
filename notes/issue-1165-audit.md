# Issue #1165: exchange-weight ownership audit

This audit records the current declarations that are already Statistics-generic in substance and
therefore belong below the concrete Bosonic/Fermionic realization boundary.

## Quartic

- `QuarticDiagram.pairingInOrder_crossingCount_mod_two_eq_sum_components`
- `QuarticDiagram.pairingInOrder_weight_eq_prod_components`

Their proof uses only Common quartic component/order/pair geometry, perfect-pairing crossing algebra,
and the Common `Statistics` pairing weight. The authoritative owner is now
`SecondQuantization.Common.Diagrammatics.Quartic.ComponentGlobalCrossingParity`.

The fermionic contraction-integrand theorem remains Fermionic because it supplies the concrete
fermionic ordered pair kernel and specializes the generic weight to `Statistics.fermion`.

## TwoPoint candidates for the later T1 package

The current candidate family is centered on:

- `FixedExternalTwoPointWickDiagram.mixedComponentWeight`
- `FixedExternalTwoPointWickDiagram.pairingInMixedOrder_weight_eq_prod_components`

and the crossing-parity lemmas supporting that product. These should only move after the Quartic
boundary is validated. Component-time transport, chamber regularity, and Gibbs-contraction locality
remain outside #1165's generic ownership move.

## External-order factor

The two-point external-order sign remains a T2 follow-up. It should become Statistics-generic only if
it can be stated without importing Fermionic mixed-time/operator machinery into Common.

## Invariants

- `Combinatorics.Pairing.evaluation` remains the unique scalar pairing evaluator.
- Dyson `(-1)^interactionOrder` remains separate from `Statistics.zeta ^ crossingCount`.
- No CAR/CCR, Gibbs-state, thermal-kernel, or convergence declaration moves into Common.
- #894's active linked-cluster proof route is not changed by this audit/extraction.
