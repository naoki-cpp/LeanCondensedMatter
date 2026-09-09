# Retained theorem audit declarations

The theorem catalog exposes structural review signals such as low compiled-consumer count,
direct-wrapper status, and terminal status. None of these signals is automatic evidence that a
public theorem should be removed. A declaration remains public when it is the canonical statement
of an independently useful mathematical or physical fact, a deliberate simplification boundary, or
a stable domain-level API.

Declarations listed here have been semantically reviewed and are intentionally retained despite one
or more audit signals. `scripts/TheoremCatalog.lean` records exact mentions from this document as the
`retainedMention` attribute. Retained declarations keep their structural attributes in the full
catalog but are omitted from terminal, single-consumer, and direct-wrapper review queues so those
queues represent unresolved audit work.

This list is not a compatibility promise. Reassess an entry if its statement, ownership, attributes,
or consumer structure changes.

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
- `SecondQuantization.Fermionic.orderedSimplexContribution_eq_pairingEvaluation` — canonical
  representation theorem identifying one Wick diagram's fixed-order ordered-simplex contribution
  with the flattened pairing evaluator after transport to a chosen vertex order.
- `SecondQuantization.Fermionic.sum_couplingWeight_mul_orderedSimplexContribution_eq_pairingEvaluation`
  — canonical reindexing theorem converting the full fixed-order Wick-diagram sum into the
  vertex-label/pairing double sum used by the Dyson-to-Wick expansion.
- `Combinatorics.permutationConnectedCycleSeries_eq_neg_inv_smul_traceLog` — canonical
  statistics-independent trace-log identity for a finite kernel at nonzero exchange weight; the
  remaining diagonal-kernel consumer is a specialization of this reusable formal-series boundary.
- `QuantumMechanics.SingleParticle.Continuum.l2MultiplicationOperator1D_apply` — deliberate `[simp]`
  boundary for the continuum-domain multiplication-operator vocabulary. The proof delegates to the
  analysis-level operator theorem, but the specialization is the normalization rule for this API.
- `SecondQuantization.Bosonic.exchangeCommutator_annihilate_create_self` — canonical bosonic CCR
  statement at the bosonic algebra layer. Its generic exchange-algebra proof does not make the
  named bosonic commutator identity redundant as a physical API result.
- `SecondQuantization.Bosonic.numberOperator_basisState` — canonical number-operator eigenvalue
  equation `N_i |n⟩ = n_i |n⟩`; this is a physical statement about the named number operator rather
  than proof-routing around `create_annihilate_basisState_same`.
- `SecondQuantization.Fermionic.Transport.TracedStredaAnalyticData.staticKuboBastinConductivity_eq_surface_add_sea`
  — named physical endpoint identifying the finite static Kubo–Bastin conductivity with the Středa
  surface-plus-sea split under the explicit analytic and Ward assumptions.
