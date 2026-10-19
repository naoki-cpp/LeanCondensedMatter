# Bounded linear-response module ownership

`QuantumTheory.LinearResponse` is the public package entry point. Concrete consumers import the
module owning the needed declarations; theorem and definition namespaces are independent of this
directory layout.

```text
LinearResponse/
├── Expectation/    normalized continuous functionals and the density-state bridge
├── Dynamics/       bounded free evolution, pictures, stationarity, equations and conservation
├── Perturbation/   time-dependent Dyson evolution, Hermitian laws and first density variation
├── Response/       Kubo formulas, source substitution, retarded kernels and response channels
├── Frequency/      adiabatic transforms, integrability, observation windows and limit orders
├── Lehmann.lean    coherent scalar/eigenbasis representation package
└── Lehmann/
    ├── Transition.lean
    ├── FiniteTable.lean
    ├── Limits.lean
    └── Eigenbasis/
        ├── Data.lean
        ├── Dynamics.lean
        ├── TimeDomain.lean
        ├── FrequencyDomain.lean
        ├── Table.lean
        └── Limits.lean
```

`Expectation.Basic` is independent of free dynamics. `Expectation.Density` realizes that interface
from a physical density operator. `Dynamics` owns the free system and its action on states and
observables. `Perturbation` supplies time-dependent evolution; `Response` relates its first variation
to measured/source observables, including an explicit affine observable variation.

`Frequency` owns the transform convention, real-valued harmonic profiles, convergence hypotheses
and filter orders. `Lehmann.Transition` is scalar transition data independent of the operator
realization. `Lehmann.Eigenbasis.Data` supplies the basis, energy and state data;
`Lehmann.Eigenbasis.Dynamics` constructs the density state and free phases without importing
frequency integrability. The time-domain and frequency-domain representation modules import the
kernel and integrability owners at their actual use sites.

The directories describe semantic responsibilities, not an assertion of a strict linear import
order. A response kernel depends on free dynamics, while the Kubo theorem also depends on
perturbations. The scalar Lehmann core remains independent of operator frequency-response proofs.
Transport realizations and conductivity normalization remain downstream.
