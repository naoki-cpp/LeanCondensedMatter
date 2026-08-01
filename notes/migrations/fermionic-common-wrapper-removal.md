# Fermionic Common-wrapper removal

The following fermionic theorem wrappers were removed without compatibility aliases because they
had no in-repository callers and only specialized authoritative `SecondQuantization.Common` results
with `fermionEnergy ε`:

- `Fermionic.interactionPicture_zero`;
- `Fermionic.matrixCoeff_interactionPicture`;
- `Fermionic.intervalIntegrable_matrixCoeff_interactionPicture`;
- `Fermionic.dysonCoeff_eq_of_time_independent`;
- `Fermionic.continuous_matrixCoeff_interactionPicture`.

Use the corresponding `Common` theorem with `fermionEnergy ε` directly.

`Fermionic.interactionPicture` remains as the physics-facing operator name. The quartic
Dyson-diagram continuity proofs now use
`Common.continuous_matrixCoeff_interactionPicture (fermionEnergy ε)` directly.
