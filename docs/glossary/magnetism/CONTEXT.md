# Magnetism and spin waves

This context distinguishes localized quantum spins, magnon descriptions of their
excitations, and macroscopic magnetization dynamics.

**One-magnon sector**:
For the polarized spin-1/2 reference state, the span of configurations with exactly
one reversed spin. Its zero-momentum state can belong to the ground multiplet.
_Avoid_: strictly positive-energy sector

**Holstein-Primakoff representation**:
A representation of spin operators using bosonic occupation and ladder operators,
restricted to at most 2s spin deviations per site for spin s.
_Avoid_: unrestricted equivalence of spins and free bosons

**Linear spin-wave theory**:
The quadratic fluctuation model obtained by expanding about a specified ordered
reference state. An exact solution of this model does not itself bound the approximation error.
_Avoid_: exact many-spin dynamics

**Polder susceptibility**:
The transverse magnetic response tensor obtained from linearized magnetization dynamics
around a specified saturated equilibrium, with field and time conventions fixed.
_Avoid_: microscopic Kubo susceptibility without a comparison theorem

**Cyclic Laplacian**:
The nearest-neighbor difference operator on a periodic ring, sending an amplitude
f at site i to w times (2f(i) - f(i-1) - f(i+1)), with site labels taken modulo
the number of sites. Its real weight w acquires an exchange-energy interpretation
only after identification with a spin or magnon model.
_Avoid_: a full many-spin Hamiltonian

**One-boson sector**:
The subspace of algebraic bosonic occupation states with total particle number one.
It represents a single magnon in the quadratic magnon model after the model's
one-particle operator has been identified. Its state space is distinct from the
one-magnon sector of the exact spin system.
_Avoid_: equality of full spin and bosonic Fock spaces

**Transverse-factor replacement**:
Replacing the transverse Holstein-Primakoff square-root occupation factors by
sqrt(2s), while keeping the longitudinal spin components unchanged. The resulting
exchange operator still contains a longitudinal quartic term; dropping that term
is a separate step toward the quadratic magnon model.
_Avoid_: an exact spin identity or a bound on the approximation error
