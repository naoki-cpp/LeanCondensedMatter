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
