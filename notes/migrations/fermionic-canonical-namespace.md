# Fermionic canonical namespace migration

The fermionic SecondQuantization line now owns its declarations under
`SecondQuantization.Fermionic`. The migration is intentionally breaking and retains no forwarding
aliases.

## Core renames

```text
SecondQuantization.FermionOccupation
  -> SecondQuantization.Fermionic.Occupation

SecondQuantization.FockSpaceFermionic
  -> SecondQuantization.Fermionic.FockSpace

SecondQuantization.fermionVacuum
  -> SecondQuantization.Fermionic.vacuum

SecondQuantization.fermionParticleNumber
  -> SecondQuantization.Fermionic.particleNumber
```

The associated occupation lemmas were renamed consistently inside the Fermionic namespace. All
fermionic algebra, imaginary-time, thermal, perturbative, and diagrammatic declarations moved with
their modules; module import paths were not changed in this package.

The architecture check rejects the four legacy identifiers and any declaration-bearing file under
`SecondQuantization/Fermionic/` that opens only the root `SecondQuantization` namespace.

## Validation history

The repository-wide migration first passed the architecture guard, `lake build --wfail`, and the
no-`sorry` check on its stacked branch. After PR #361 reached `main`, the validated net R3 diff was
reapplied onto the actual default-branch history and the same checks passed again. The final PR CI
therefore validates the rebased commit rather than the former stacked history.
