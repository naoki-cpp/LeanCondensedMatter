---
status: accepted
---

# Keep generic response separate from physical conductivity and models

Generic Transport owns resolvent, response, disorder, and conductivity interfaces upstream of concrete models and fermionic adapters. Its public umbrella excludes concrete Models and opt-in analytical utilities. Representation-independent operator analysis stays further upstream in Analysis.

A response matrix or trace kernel becomes physical conductivity only after the appropriate normalization and physical assumptions are supplied. `ConductivityTensor` stores the resulting components independently of a Kubo–Bastin or Středa representation; it does not itself certify the derivation or normalization. Keep volume, contact terms, continuum measure, and limiting assumptions explicit at the adapters that need them.

Likewise, distinguish exact disorder averages from Born or self-consistent approximation data. This requires more explicit interfaces than a model-centered implementation, but prevents a calculation for one model or approximation from silently becoming a generic transport assumption.

Evidence: [transport ownership](../../notes/architecture/transport.md), [public imports](../../LeanCondensedMatter/Transport.lean), [conductivity type](../../LeanCondensedMatter/Transport/Core/ConductivityTensor.lean), and [finite conductivity adapter](../../LeanCondensedMatter/Transport/FiniteConductivityTable.lean).
