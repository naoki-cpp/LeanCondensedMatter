# Common canonical namespace migration

The following root declarations were moved without compatibility aliases:

```text
SecondQuantization.Statistics
  -> SecondQuantization.Common.Statistics

SecondQuantization.orderedQuarticLegEquiv
  -> SecondQuantization.Common.orderedQuarticLegEquiv
SecondQuantization.quarticVertexEquiv
  -> SecondQuantization.Common.quarticVertexEquiv
SecondQuantization.quarticLegEquiv
  -> SecondQuantization.Common.quarticLegEquiv
SecondQuantization.vertexOfLeg
  -> SecondQuantization.Common.vertexOfLeg
SecondQuantization.localLegOfLeg
  -> SecondQuantization.Common.localLegOfLeg
SecondQuantization.legOfVertexLocal
  -> SecondQuantization.Common.legOfVertexLocal
```

The former root `SecondQuantization.modeCount` was initially moved to
`SecondQuantization.Common.modeCount` during namespace consolidation. It has since been removed:
foundational mode labels are arbitrary types, and cardinality belongs only to an explicitly finite
specialization that actually uses it.

The associated quartic-leg inverse lemmas moved with the definitions. All in-repository callers use
the new names. `Combinatorics.Pairing.weight` intentionally remains in `Combinatorics` as an
extension of the pairing type, while its statistics argument is now
`SecondQuantization.Common.Statistics`.

The permanent namespace audit checks every declaration under `SecondQuantization/` against its path
owner and rejects statistic-encoded declaration names. The pairing-weight extension is the only
explicitly allowlisted cross-namespace declaration. A separate mode-boundary audit rejects a global
mode count and finite-mode assumptions in the foundational finite-support algebra.
