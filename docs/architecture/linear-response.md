# Bounded linear-response module ownership

`QuantumTheory.LinearResponse` is the public package entry point. Concrete consumers import the
module owning the needed declarations; theorem and definition namespaces are independent of this
directory layout.

```text
LinearResponse/
├── Expectation/    normalized continuous functionals and the density-state bridge
├── Dynamics/       bounded free evolution, pictures, stationarity, equations and conservation
├── Perturbation/   time-dependent Dyson evolution, Hermitian laws and first density variation
├── Response.lean   focused public response-formula package
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

The full entry `QuantumTheory.LinearResponse` continues to expose the complete
framework. Two focused public entry points are available without removing that
compatibility surface:

```lean
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response
-- Kubo/source coupling, causal/density susceptibility, observable/channel response

import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
-- scalar and eigenbasis Lehmann/limit representations
```

The `Response.lean` package imports the six `Response/*` implementation
owners without relocating any declaration. These packages may still import
their shared upstream dynamics, density-state, or perturbation prerequisites:
a smaller project-local closure is **not** proof of a smaller elaboration time
or full Mathlib dependency graph.

`Expectation.Basic` is independent of free dynamics. `Expectation.Density` realizes that interface
from a physical density operator. `Dynamics` owns the free system and its action on states and
observables. `Perturbation` supplies time-dependent evolution, including the perturbed observable map
used independently by `Perturbation.Unitary`. The observable map and its basic zero-coupling
property are owned by `Perturbation.Observable`, not by the Kubo-formula module;
`Response` relates the first variation
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
