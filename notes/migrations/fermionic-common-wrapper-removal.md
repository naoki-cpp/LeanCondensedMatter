# Fermionic Common-wrapper removal

The following fermionic theorem wrappers were removed without compatibility aliases because they
had no in-repository callers and only specialized authoritative `SecondQuantization.Common` results
with `fermionEnergy ε`:

- `Fermionic.interactionPicture_zero`;
- `Fermionic.matrixCoeff_interactionPicture`;
- `Fermionic.intervalIntegrable_matrixCoeff_interactionPicture`;
- `Fermionic.dysonCoeff_eq_of_time_independent`;
- `Fermionic.continuous_matrixCoeff_interactionPicture`;
- `Fermionic.dysonCoeff_interactionHamiltonian_eq`.

Use the corresponding `Common` theorem with `fermionEnergy ε` directly.

`Fermionic.interactionPicture` remains as the physics-facing operator name. The quartic
Dyson-diagram continuity proofs use
`Common.continuous_matrixCoeff_interactionPicture (fermionEnergy ε)` directly.

The former `Fermionic/Perturbation/DysonExpansionVerification.lean` module was removed. Its physical
input, `imaginaryTimeEvolve_interactionHamiltonian`, now lives beside the fermionic evolution API in
`Fermionic/ImaginaryTime/InteractionPicture.lean`; the deleted coefficient theorem is obtained
straight from `Common.dysonCoeff_eq_of_time_independent` when needed.
