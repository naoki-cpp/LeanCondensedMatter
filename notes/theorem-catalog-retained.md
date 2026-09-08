# Retained single-consumer theorems

The theorem catalog reports declarations with exactly one distinct compiled project-declaration
consumer as review candidates. A low consumer count is only a structural signal: a theorem remains
public when it is the canonical statement of an independently useful mathematical or physical fact.

Declarations listed here have been semantically reviewed and are intentionally retained even while
they have one compiled project consumer. `scripts/TheoremCatalog.lean` uses this document to keep
such declarations out of the single-consumer review queue. They may still appear inside a
multi-step chain because the chain is a structural view of the dependency graph.

This list is not a compatibility promise. Reassess an entry if its statement, ownership, or consumer
structure changes.

## Retained declarations

- `QuantumTheory.Transport.im_inner_resolvent_spectralParameterOfRegulator_apply_self` — canonical
  dimension-independent signed-regulator Herglotz identity for a self-adjoint resolvent. Consumers
  that need the reversed inner-product orientation should reverse it locally rather than expose a
  second public theorem.
- `QuantumTheory.Transport.Models.MassiveDirac.finiteCutoffContinuumBornSelfEnergyOfRegulator_dissipative`
  — model-level dissipativity statement for the finite-cutoff Born self-energy. It is a physical
  property of the model, not merely an intermediate step in the downstream injectivity proof.
- `QuantumMechanics.SingleParticle.symmetrizedVelocityTransport_decomposition` — canonical algebraic
  decomposition of nested symmetrized transport into the conventional current term and the
  double-commutator correction.
- `QuantumMechanics.SingleParticle.localizationCorrectionFlux_apply` — canonical identification of
  the localization correction with the double commutator; it is also the simplification boundary
  for the corrected-current API.
- `QuantumMechanics.SingleParticle.localizationCorrectionFlux_smul_id_eq_zero` — independently useful
  charge-like specialization stating that the localization correction vanishes for a scalar
  multiple of the identity.
- `QuantumMechanics.SingleParticle.correctedChargeCurrentFlux_eq` — physical charge-current
  specialization identifying the corrected current with the conventional local pairing `q v`.
- `QuantumTheory.Transport.tendsto_lorentzianSpectralTailMass_zero` — model-independent analytic
  approximate-identity result for vanishing Lorentzian mass between fixed nested positive windows.
- `SecondQuantization.Fermionic.fixedExternalFiberEquiv_symm_externalPiece_heq` — structural invariant
  of the fixed-external fiber equivalence: reassembly preserves the standardized connected external
  piece independently of the vacuum component.
