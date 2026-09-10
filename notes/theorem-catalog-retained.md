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
- `Finset.card_filter_product_eq_sum_card_filter` — canonical generic double-counting identity for a
  filtered finite self-product. Its remaining crossing-count consumer is a domain specialization,
  while the theorem itself is independent of pairing or crossing structure.
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
- `QuantumTheory.Transport.FiniteDisorderEnsemble.retardedAdvancedLadderCLM_apply` — canonical
  evaluation rule identifying the bundled retarded-advanced ladder action with the physical
  covariance insertion `C₂(Gᴿ Γ Gᴬ)`; it is the stable simplification boundary for the ladder API.
- `QuantumMechanics.SingleParticle.currentEquivalent_correctedSymmetrizedVelocity` — canonical
  corrected-current equivalence theorem: any full current representing the intrinsic transport is
  equivalent on exact differentials to the symmetrized current plus localization correction.
- `QuantumMechanics.SingleParticle.exists_current_eq_symmetrized_add_correction_add_invisible` —
  physics-facing representation theorem `J = J_sym + J_corr + K` with `K` invisible on exact
  differentials; it is the explicit extension-ambiguity endpoint of the corrected-current API.
- `SecondQuantization.Common.TwoPointDiagram.isSplit_ofSlotSplit` — canonical constructor invariant
  stating that a diagram rebuilt from slot-split pieces is split by that same slot decomposition;
  it is the evidence used to place reconstructed diagrams in the split-diagram subtype.
- `SecondQuantization.Common.dysonTraceCoeff_eq_weightedTrace` — canonical interpretation of the
  named Dyson trace coefficient as the Boltzmann-weighted diagonal functional of the corresponding
  bare Dyson coefficient.
- `SecondQuantization.Fermionic.completedFreeHamiltonian_denseDomain` — standard analytic property of
  the named completed free Hamiltonian; the common diagonal-operator proof does not make the
  fermionic physical endpoint redundant.
- `SecondQuantization.Fermionic.completedFreeHamiltonian_isClosed` — standard analytic property of
  the named completed free Hamiltonian, retained alongside its self-adjointness endpoint.
- `SecondQuantization.Fermionic.timeOrderedExternalFields_swap` — canonical fermionic exchange law
  for the named time-ordered external-field construction: swapping both fields and times produces
  the fermionic statistics sign.
- `ConservationLaw.linearCommutator_orbitalAngularMomentumZ_continuum_sign` — physics-facing continuum
  specialization fixing the derivative-localizer coefficient to `iℏ`; it records the expected
  orbital-angular-momentum localization commutator rather than a proof-routing alias.
- `LinearPMap.resolventApproximationEvolution_continuous` — canonical operator-norm continuity
  property of the named bounded resolvent-approximation evolution used in the Stone construction.
- `LinearPMap.resolventApproximationEvolution_hasDerivAt` — canonical differential equation for the
  named bounded resolvent-approximation evolution, exposing its generator at the construction API.
- `QuantumMechanics.SingleParticle.Continuum.continuumRealPotentialSchrodingerHamiltonian1D_isClosed`
  — physical real-scalar-potential closedness theorem for the named continuum Hamiltonian; the
  generic complex-multiplier proof does not make the real-potential endpoint redundant.
- `QuantumTheory.Transport.bandStateOccupation_zeroTemperature_eq_zero_of_isEmptyBand` — canonical
  zero-temperature occupation statement that every state in an empty band has zero occupation.
- `SecondQuantization.Bosonic.annihilate_fockVacuum` — canonical `[simp]` vacuum identity stating that
  every bosonic annihilation operator kills the Fock vacuum.
- `SecondQuantization.Bosonic.freeGibbsDysonCoeff_succ` — canonical recursive scalar-integral equation
  for the named Gibbs-evaluated Dyson coefficient under its explicit analytic boundary.
- `SecondQuantization.Bosonic.particleNumber_vacuum` — canonical `[simp]` statement that the bosonic
  vacuum has zero total occupation number.
- `SecondQuantization.Common.finiteGibbsExpectation_comp_eq_div_of_exchangeCommutator` — deliberate
  `Statistics`-indexed Gibbs two-point API for callers that already work with `exchangeCommutator`,
  rather than the lower-level raw-`ζ` presentation.
- `SecondQuantization.Fermionic.annihilate_fockVacuum` — canonical `[simp]` CAR vacuum identity that
  every fermionic annihilation operator kills the Fock vacuum.
- `ContinuousLinearMap.unitaryConjugate_rankOne` — canonical rank-one covariance identity under
  bounded unitary conjugation. The current single consumer is a density-operator specialization,
  while the statement itself is general operator infrastructure.
- `ContinuousLinearMap.eigenspace_unitaryConjugate` — canonical eigenspace transport theorem under
  unitary conjugation. It identifies the full eigenspace submodule, not merely the finite-dimensional
  rank consequence used downstream.
- `ContinuousLinearMap.hasSummableRealEigenvalues_unitaryConjugate` — independently useful invariance
  of absolute summability of real eigenvalues with multiplicity under unitary conjugation; it is the
  analytic input for bundled spectral trace-class transport.
- `ContinuousLinearMap.spectralTrace_unitaryConjugate` — canonical unbundled trace-invariance theorem
  `Tr(U T U†) = Tr(T)` for the project's spectral trace under explicit summability hypotheses.
- `ContinuousLinearMap.isCompactOperator_unitaryConjugate` — standard operator-theory fact that
  compactness is preserved by bounded conjugation; the current bundled trace-class consumer does not
  make this general result proof-routing.
- `ContinuousLinearMap.IsPositive.unitaryConjugate` — standard positivity-preservation theorem for
  conjugation by an arbitrary bounded operator. It is independently meaningful even when no compiled
  project declaration currently retains it.
- `ContinuousLinearMap.SpectralTraceClass.unitaryConjugate` — canonical closure theorem transporting
  bundled spectral trace-class data through unitary conjugation; it is the stable construction used
  by trace invariance and density-operator evolution.
- `ContinuousLinearMap.SpectralTraceClass.trace_unitaryConjugate` — bundled trace-invariance endpoint
  for spectral trace-class operators. It is the caller-facing theorem corresponding to the unbundled
  spectral-trace identity and remains useful despite being terminal in the compiled theorem graph.
- `Combinatorics.Pairing.pairEndpoint_ne_of_normalizedPair_ne` — canonical indexed endpoint-separation
  theorem: distinct normalized pairs have distinct endpoints for arbitrary `Fin 2` endpoint choices.
  The coordinate four-inequality theorem is a downstream specialization used by crossing arguments.
- `ContinuousLinearMap.finrank_eigenspace_unitaryConjugate` — canonical multiplicity-preservation
  theorem under unitary conjugation. Although its current project consumer is the summability proof,
  equality of eigenspace dimensions is independently useful operator-theory API.
- `Combinatorics.BinaryShuffle.toSlotShuffle_injective` — canonical injectivity property of the public
  forgetful map from recursive binary shuffles to ambient slot shuffles. It participates in both the
  cardinality argument and the final equivalence construction, so it is not merely one-use routing.
- `Combinatorics.permutationSum_eq_momentFromCumulant` — semantic connected-decomposition endpoint
  identifying the project-local permutation sum with the moment transform of the single-cycle
  contribution; the module explicitly reserves public declarations for this moment characterization.
- `LinearPMap.resolventApproximationEvolution_add` — one-parameter-group law for the named bounded
  resolvent-approximation evolution; it is part of the construction API, not just a specialization of
  the generic bounded exponential theorem.
- `LinearPMap.resolventApproximationEvolution_apply_hasDerivAt` — vectorwise bounded-generator
  differential equation for the named resolvent approximation, forming the strong-evolution bridge
  used by the Stone construction.
- `QuantumMechanics.SingleParticle.Continuum.inner_l2MultiplicationOperator1D_eq_integral` —
  continuum-quantum-mechanics expectation-value formula identifying a named multiplication-operator
  matrix element with its pointwise Lebesgue integral.
- `QuantumMechanics.SingleParticle.Continuum.realLInfMultiplier1D_coeFn` — continuum-vocabulary
  normalization theorem exposing the almost-everywhere representative of a bounded real multiplier;
  it is the bridge used by the probability-density layer.
- `QuantumTheory.Transport.bandStateOccupation_zeroTemperature_eq_one_of_isFilledBand` — canonical
  physical endpoint that every state of a filled band has unit zero-temperature occupation, paired
  with the retained empty-band theorem.
- `SecondQuantization.Common.QuarticDiagram.assembleVertexOrder_shuffleOfVertexOrder` — canonical
  reassembly identity for the quartic-diagram-facing component-order API; the module deliberately
  specializes the generic partition-order machinery into this domain vocabulary.
- `SecondQuantization.Common.TwoPointDiagram.legInComponent_iff_vertex_mem` — semantic normalization
  rule for the named flattened-leg component predicate, identifying it with membership of the
  incident vertex in the corresponding component part.
- `SecondQuantization.Common.TwoPointDiagram.prod_mixedComponentWeight_eq_external_mul_prod_vacuum` —
  domain-level factorization of mixed-time component weights into the distinguished external
  component and vacuum components, used by the fixed-external Wick factorization endpoint.
- `SecondQuantization.Common.interactionPicture_zero` — canonical `[simp]` normalization that the named
  interaction-picture operator equals the original operator at zero imaginary time.
- `SecondQuantization.Fermionic.externalFieldOperator_annihilation_eq_smul` — physical evaluation rule
  for an annihilation-labelled external field under free imaginary-time evolution.
- `SecondQuantization.Fermionic.externalFieldOperator_creation_eq_smul` — physical evaluation rule for
  a creation-labelled external field under free imaginary-time evolution.
- `MeasureTheory.integral_orientedIntervalIntegrand` — canonical full-line localization theorem for an
  oriented interval integral: the indicator-difference integrand on `ℝ` integrates to Mathlib's
  oriented `intervalIntegral`. This representation is the reusable bridge that lets downstream
  energy-kernel constructions place transition-localized contributions on one common integration
  domain.
- `Combinatorics.Pairing.partner_partner` — canonical pointwise involution law for a pairing's partner
  map. The theorem is a high-use `[simp]` interface to the structure invariant, not a historical alias.
- `LinearPMap.nonrealResolvent_commute` — canonical `Commute`-packaged form of pairwise nonreal
  resolvent commutation; downstream proofs use the `Commute` combinator API directly.
- `LinearPMap.resolventApproximationEvolution_zero` — standard zero-time normalization of the named
  bounded resolvent-approximation evolution and part of its one-parameter evolution API.
- `QuantumTheory.LinearResponse.isSelfAdjoint_timeDependentInteractionPerturbation_of_isSelfAdjoint` — physical
  self-adjointness endpoint for the named interaction-picture perturbation under pointwise
  self-adjoint input.
- `SecondQuantization.Bosonic.create_basisState_eq` — canonical occupation-basis creation law
  `a†ᵢ|n⟩ = √(nᵢ+1)|n+eᵢ⟩`; its direct proof routing does not make this textbook-level API redundant.
- `SecondQuantization.Fermionic.timedFieldOperator_eq_smul` — canonical normal form expressing a
  time-labelled external field as its scalar imaginary-time factor times the bare field operator.
- `SecondQuantization.Fermionic.twoPointTimeOrderedProduct_of_gt` — canonical later-first branch of
  the named fermionic two-point time-ordering operator, including the statistics convention.
- `SecondQuantization.Fermionic.twoPointTimeOrderedProduct_of_lt` — canonical exchanged branch of the
  named fermionic two-point time-ordering operator, exposing the fermionic minus sign.
- `SecondQuantization.Fermionic.twoPointTimeOrderedProduct_self_time` — canonical equal-time branch of
  the named fermionic two-point time-ordering operator, fixing the project's equal-time convention.
