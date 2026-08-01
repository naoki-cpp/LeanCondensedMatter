# Common canonical namespace migration

The following root declarations were moved without compatibility aliases:

```text
SecondQuantization.Statistics
  -> SecondQuantization.Common.Statistics

SecondQuantization.modeCount
  -> SecondQuantization.Common.modeCount

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

The associated quartic-leg inverse lemmas moved with the definitions. All in-repository callers use
the new names. `Combinatorics.Pairing.weight` intentionally remains in `Combinatorics` as an
extension of the pairing type, while its statistics argument is now
`SecondQuantization.Common.Statistics`.
