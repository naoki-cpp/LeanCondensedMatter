# Retained theorem audit declarations

The theorem catalog exposes structural review signals such as low compiled-consumer count,
direct-wrapper status, and terminal status. None of these signals is automatic evidence that a
public theorem should be removed. A declaration remains public when it is the canonical statement
of an independently useful mathematical or physical fact, a deliberate simplification boundary, or
a stable domain-level API.

Declarations listed here have been semantically reviewed and are intentionally retained despite one
or more audit signals. `scripts/TheoremCatalog.lean` records full-name mentions and unambiguous
short-name mentions from this document as the
`retainedMention` attribute. Retained declarations keep their structural attributes in the full
catalog but are omitted from terminal, single-consumer, and direct-wrapper review queues so those
queues represent unresolved audit work.

This list is not a compatibility promise. Reassess an entry if its statement, ownership, attributes,
or consumer structure changes.

## Retained declarations

- `SecondQuantization.Common.heisenbergEvolve_quarticVertexOperator` — canonical vertex-level
  energy-shift eigenoperator law: a quartic vertex assembled from ladder eigenoperators evolves with
  the total signed energy shift of its four legs. It remains independently meaningful even without a
  current compiled consumer.
- `QuantumTheory.Transport.im_inner_resolvent_spectralParameterOfRegulator_apply_self` — canonical
  dimension-independent signed-regulator Herglotz identity for a self-adjoint resolvent. Consumers
  that need the reversed inner-product orientation should reverse it locally rather than expose a
  second public theorem.
- `QuantumTheory.Transport.Models.MassiveDirac.finiteCutoffContinuumBornSelfEnergyOfRegulator_dissipative`
  — model-level dissipativity statement for the finite-cutoff Born self-energy. It is a physical
  property of the model, not merely an intermediate step in the downstream injectivity proof.
- `QuantumMechanics.SingleParticle.symmetrizedVelocityTransport_decomposition` — canonical algebraic
  decomposition of nested symmetrized transport into the symmetrized current term and the
  double-commutator correction.
- `ConservationLaw.localizationCorrectionCurrentFlux_apply` — canonical identification of
  the localization correction with the double commutator; it is also the simplification boundary
  for the corrected-current API.
- `ConservationLaw.localizationCorrectionCurrentFlux_smul_id` — independently useful
  charge-like specialization stating that the localization correction vanishes for a scalar
  multiple of the identity.
- `QuantumMechanics.SingleParticle.correctedChargeCurrentFlux_eq` — physical charge-current
  specialization identifying the corrected current with the local pairing `q v`.
- `QuantumTheory.Transport.tendsto_lorentzianSpectralTailMass_zero` — model-independent analytic
  approximate-identity result for vanishing Lorentzian mass between fixed nested positive windows.
- `SecondQuantization.Fermionic.orderedSimplexContribution_eq_pairingEvaluation` — canonical
  representation theorem identifying one Wick diagram's fixed-order ordered-simplex contribution
  with the flattened pairing evaluator after transport to a chosen vertex order.
- `SecondQuantization.Fermionic.sum_vertexWeight_mul_orderedSimplexContribution_eq_pairingEvaluation`
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
- `QuantumMechanics.SingleParticle.currentEquivalent_nestedSymmetrizedCurrentFlux` — canonical
  corrected-current equivalence theorem: any full current representing the intrinsic transport is
  equivalent on exact differentials to the symmetrized current plus localization correction.
- `QuantumMechanics.SingleParticle.exists_current_eq_symmetrized_add_correction_add_invisible` —
  physics-facing representation theorem `J = J_sym + J_corr + K` with `K` invisible on exact
  differentials; it is the explicit extension-ambiguity endpoint of the corrected-current API.
- `SecondQuantization.Common.dysonTraceCoeff_eq_weightedTrace` — canonical interpretation of the
  named Dyson trace coefficient as the Boltzmann-weighted diagonal functional of the corresponding
  bare Dyson coefficient.
- `SecondQuantization.Fermionic.timeOrderedExternalFields_swap` — canonical fermionic exchange law
  for the named time-ordered external-field construction: swapping both fields and times produces
  the fermionic statistics sign.
- `QuantumMechanics.SingleParticle.linearCommutator_orbitalAngularMomentumZ_continuum_sign` — physics-facing continuum
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
- `SecondQuantization.Common.TwoPointDiagram.legInComponent_iff_vertex_mem` — semantic normalization
  rule for the named flattened-leg component predicate, identifying it with membership of the
  incident vertex in the corresponding component part.
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
- `Combinatorics.PairingOn.partner_partner` — canonical pointwise involution law for a pairing's partner
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
- `SecondQuantization.Fermionic.twoPointTimeOrderedProduct_of_lt` — canonical exchanged branch of
  the named fermionic two-point time-ordering operator, exposing the fermionic minus sign.
- `SecondQuantization.Fermionic.twoPointTimeOrderedProduct_self_time` — canonical equal-time branch of
  the named fermionic two-point time-ordering operator, fixing the project's equal-time convention.
- `LinearPMap.norm_stoneEvolution_sub_resolventApproximationEvolution_le` —
  canonical generator-domain error estimate comparing the limiting Stone evolution with one bounded
  resolvent approximant; it is reusable independently of the downstream slope argument.
- `LinearPMap.resolventApproximationEvolutionAtScale_dist_eq` — canonical isometry property of the
  totalized bounded resolvent approximants, not merely a transport step in the strong-limit proof.
- `QuantumTheory.DensityOperator.hasSum_abs_eigenvalues_eq_one` — spectral normalization law for a
  density operator: the absolute eigenvalue weights sum to one independently of the expectation
  norm estimate that currently consumes it.
- `QuantumTheory.POVM.hasSum_inner_apply` — canonical diagonal weak-operator consequence of strong
  POVM normalization and a reusable bridge from operator normalization to Born probabilities.
- `QuantumTheory.Transport.Models.MassiveDirac.pauliGreenOperatorOfRegulator_eq_closedForm` —
  canonical closed numerator/denominator form of the arbitrary-regulator Massive Dirac Green
  operator.
- `QuantumTheory.Transport.Models.MassiveDirac.sum_bandProjectorOperator_eq_one` — canonical
  completeness relation for the finite family of Massive Dirac band projectors.
- `SecondQuantization.Common.QuarticDiagram.blockVertex_subtypeSubtypeEquivSubtype` — one direction of the
  canonical inverse laws between the public block-vertex embedding and `Equiv.subtypeSubtypeEquivSubtype`, paired
  with `subtypeSubtypeEquivSubtype_blockVertex` rather than one-use proof routing.
- `SecondQuantization.Common.QuarticDiagram.restrictComponentConnected_reassemble` — round-trip law
  for connected component restriction after reassembly; it forms the semantic right-inverse layer
  underlying the public component-decomposition equivalence.
- `SecondQuantization.Common.QuarticDiagram.restrictComponent_vertexGraph_adj_iff` — canonical graph
  transport characterization identifying adjacency in a restricted component with ambient adjacency
  through `blockVertex`.
- `SecondQuantization.Common.TwoPointDiagram.externalVacuumSplit_fst_partner` — canonical partner-map
  characterization for the external split pairing. Source-level public mixed-component theorems also
  use this law even when simplification removes the reference from their compiled proof terms.
- `SecondQuantization.Common.orderedTwoPointTimedEvents_pairwise` — structural invariant that the
  canonical mixed-event list is pairwise ordered by the stable time precedence relation.
- `SecondQuantization.Common.support_dysonCoeff_basisState_subset_reachableSupport` — finite-order
  support/reachability theorem for Dyson coefficients, independently useful beyond the continuity
  proof that currently retains it.
- `SecondQuantization.Fermionic.Validation.twoSiteGappedBenchmark_excited_eigenvector` — explicit
  upper-energy eigenvector theorem for the public two-site gapped validation benchmark.
- `SecondQuantization.Fermionic.Validation.twoSiteGappedBenchmark_ground_eigenvector` — explicit
  lower-energy eigenvector theorem for the public two-site gapped validation benchmark.
- `SecondQuantization.Fermionic.completedModeTruncation_algebraicToCompleted_of_subset` — exactness of
  completed mode truncation once the truncation contains the finite support of an algebraic vector;
  this is the canonical dense-subspace approximation boundary.
- `SecondQuantization.Fermionic.continuous_matrixCoeff_interactionPicture_comp_dysonCoeff` — general
  finite-mode continuity theorem for matrix coefficients of an interaction-picture operator composed
  with a Dyson coefficient, stated for arbitrary interaction `V` rather than the quartic consumer.
- `SecondQuantization.Fermionic.continuous_matrixCoeff_nestedVertexOperatorComp` — joint continuity of
  the public nested vertex-operator product, providing the analytic interface used to lift matrix
  coefficients to Gibbs-expectation continuity.
- `SecondQuantization.Fermionic.dist_completedModeTruncation_le_two_mul_of_fixed` — reusable contraction
  estimate bounding truncation error by twice the distance to any fixed point of the truncation.
- `Combinatorics.Pairing.card_pairs` — canonical cardinality theorem for perfect pairings:
  a pairing of `Fin (2 * n)` has exactly `n` normalized pairs. This is an independently meaningful
  combinatorial endpoint even without a current compiled consumer.
- `Combinatorics.Pairing.sign_pairPerm` — canonical parity endpoint identifying the sign of the
  permutation that lists normalized pairs blockwise with `(-1)` raised to the pairing crossing
  count. It records the intrinsic bridge between crossing parity and permutation sign independently
  of downstream bridge implementations.
- `Combinatorics.Pairing.insertFirstPair_eraseZeroPair` — canonical erase/insert round-trip law:
  erasing the pair containing position zero and reinserting it recovers the original pairing. It is
  the left-inverse law underlying `Pairing.equivSigma`, not merely one-use proof routing.
- `SecondQuantization.Common.ExternalInsertionDiagram.externalSector_card_even` — canonical
  component-parity theorem: every connected external-insertion component carries an even number of
  one-legged external insertions.
- `SecondQuantization.Common.ExternalInsertionDiagram.legInComponent_iff_vertex_mem` — semantic
  normalization rule for the external-insertion flattened-leg component predicate, identifying it
  with membership of the incident vertex in the component part.
- `Combinatorics.FiniteIndex.eq_cast_mul_add_blockEquiv` — canonical reconstruction law for
  flattened finite block coordinates; it is the inverse-direction companion to
  `blockEquiv_cast_mul_add` and is useful independently of its compiled-consumer count.
- `LeanCondensedMatter.Crystal.reciprocalPairing_isSymm` — canonical symmetry property of the
  normalized reciprocal pairing used to construct crystallographic reciprocal bases and lattices.
- `LinearPMap.stoneEvolution_apply_hasDerivAt_zero` — Stone-generator endpoint identifying the
  derivative at zero of the strong Stone evolution with `-iA` on the operator domain.
- `QuantumTheory.Transport.Models.MassiveDirac.finiteCutoffContinuumBornDysonGreenLoopMatrix_apply_eq_radial_integral`
  — model-level T-matrix provenance theorem exposing the finite-cutoff radial Green-loop integral
  and its single physical momentum-measure prefactor.
- `QuantumTheory.Transport.Models.MassiveDirac.radialBastinMassWindowMargin_le_abs_gap_add_offset`
  — model-specific uniform separation bound between the mass-window margin and the shifted
  opposite-band energy denominator.
- `SecondQuantization.Fermionic.CompletedThermalLadder.completedAnticomm_operator_operator` —
  canonical completed-space CAR statement for the unified thermal ladder operator, expressing its
  anticommutator as the scalar CAR coefficient times the identity.
- `Combinatorics.FamilySlotShuffleTo.sum_integral_eq_prod` — canonical finite-family
  ordered-simplex shuffle product identity for measurably locally bounded local integrands; retain
  the general theorem even when its current compiled consumer is private.
- `Combinatorics.Pairing.presentsPairs_of_partner_blockPair` — Criterion for presenting a pairing.
- `Combinatorics.blockPair_apply` — The two positions of a block, written through the block-slot
  presentation.
- `Combinatorics.cycleDefect_eq_sum_orbitFinpartition` — The cycle defect is the sum of `|B| - 1`
  over the canonical orbit blocks.
- `Combinatorics.cycleDefect_mod_two` — The parity of the cycle defect agrees with the parity of
  `cycleType.sum + cycleType.card`.
- `Combinatorics.not_crosses_self` — canonical irreflexivity fact for the pairing-crossing
  relation: a normalized pair never crosses itself.
- `Combinatorics.singleCycleContribution_eq_pow_card_mul_singleCycleKernelSum` — A connected
  permutation on `S` carries the common exchange factor `ζ ^ (|S| - 1)`.
- `Combinatorics.singleCycleKernelSum_univ_eq_sum_isCycleOn` — On the full finite index type, the
  pure connected kernel is the direct sum over permutations that are a single cycle on the whole
  type.
- `Combinatorics.sum_singleCycleContribution_assignments_eq_factorial_mul_trace` — canonical trace
  bridge identifying the assignment sum of connected single-cycle contributions with
  `ζ^(m-1) (m-1)! tr(K^m)` for positive label count.
- `Equiv.Perm.isCycleOn_univ_iff_cycleType_eq_singleton_card` — On a nontrivial finite type, a
  permutation is a single orbit on the whole type exactly when its cycle type is the singleton
  containing the ambient cardinality.
- `List.idxOf_flatMap_lt_of_idxOf_lt` — If one event occurs before another in a duplicate-free event
  list, every element in the first block occurs before every element in the second block of the
  duplicate-free flattened list.
- `QuantumMechanics.SingleParticle.Continuum.minimallyCoupledSchrodingerRhsValue1D_eq_expanded` —
  Explicit physical expansion of the minimally coupled Schrödinger right-hand side.
- `QuantumMechanics.SingleParticle.Continuum.probabilityDensityTimeDerivativeValue_eq_coordinates` —
  Coordinate expansion of the probability-density time derivative.
- `QuantumTheory.LinearResponse.PurePointLehmannData.probability_summable` — structure-level
  invariant recording absolute summability of the normalized pure-point probability weights.
- `QuantumTheory.Transport.FiniteDisorderEnsemble.probability_sum` — structure-level normalization
  invariant stating that the finite disorder probabilities sum to one.
- `QuantumTheory.Transport.FiniteDisorderEnsemble.star_averagedGreenOfRegulator` — Adjointing the
  exact finite disorder-averaged Green operator reverses the signed regulator.
- `QuantumTheory.Transport.Models.MassiveDirac.bandProjectorOperator_ne_zero` — Every band projector
  is a nonzero bounded operator.
- `QuantumTheory.Transport.Models.MassiveDirac.continuumBornDampingScale_eq_selfEnergyPrefactor` —
  The damping scale is exactly the physical-momentum prefactor already extracted from the Born
  self-energy.
- `QuantumTheory.Transport.Models.MassiveDirac.continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq` —
  The radial Cartesian Born denominators multiply to the canonical real weak-Born RA product.
- `QuantumTheory.Transport.Models.MassiveDirac.finiteBroadeningSameSide_integrable_and_integral_eq_endpoint` —
  The finite-broadening bare-source same-side radial integrand is integrable and evaluates to the
  canonical endpoint.
- `QuantumTheory.Transport.Models.MassiveDirac.finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq_denominatorForm` —
  The ordered `xy` radial Hall-surface integrand is the measured-`x`, source-`y` Středa radial
  response in explicit common RA Born-Dyson denominator form.
- `QuantumTheory.Transport.Models.MassiveDirac.finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_x_eq_denominatorForm` —
  The ordered `xx` finite-`η` dressed Středa angular coefficient in explicit denominator form.
- `QuantumTheory.Transport.Models.MassiveDirac.norm_targetCenteredInterbandBastinPairIntegral_radial_le` —
  Uniform norm bound for the complete target-centered interband Bastin pair on the radial axis.
- `QuantumTheory.Transport.Models.MassiveDirac.radius_lt_abs_interbandEnergyGap_of_lt_two_mul_abs_mass` —
  A pole window narrower than the mass gap is valid simultaneously at every momentum.
- `QuantumTheory.Transport.Models.MassiveDirac.star_pauliGreenOperatorOfRegulator` — Adjointing the
  explicit Pauli Green operator reverses the signed regulator.
- `QuantumTheory.Transport.Models.MassiveDirac.tendsto_finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary_disorder_zero` —
  At fixed cutoff beyond the metallic shell, the canonical zero-broadening solved ladder vector
  converges to the longitudinal dressed-current factor `2 (ε² + m²) / (ε² + 3 m²)` with vanishing
  raw transverse component.
- `QuantumTheory.Transport.Models.MassiveDirac.tendsto_finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary_y_div_disorder_zero` —
  The transverse component of the zero-broadening dressed-current vector carries the same first
  nonvanishing weak-disorder coefficient as the transverse ladder action.
- `QuantumTheory.Transport.Models.MassiveDirac.tendsto_targetCenteredInterbandBastinPairIntegral_re_cleanLimitDensity` —
  The pointwise fixed-window theorem expressed through the named clean Bastin-pair limit density.
- `QuantumTheory.Transport.Models.MassiveDirac.zeroTemperatureOccupiedBerryWeightCutoff_eq` — The
  canonical occupation-derived finite-cutoff response keeps the single-cone regulator term explicit,
  including the massless endpoint where both sides vanish.
- `QuantumTheory.Transport.tendsto_integral_radialQuadraticLorentzian_atTop` — For nonzero radial
  scale and positive width, the radial quadratic Lorentzian integral converges as the upper cutoff
  tends to `+∞`.
- `SecondQuantization.Bosonic.QuarticDiagram.orderedThermalAmplitude_eq_prod_components` — The
  coefficientwise bosonic ordered thermal amplitude factors over connected components.
- `SecondQuantization.Bosonic.createOccupation_comm` — Creating particles in two modes commutes.
- `SecondQuantization.Bosonic.removeOccupation_comm` — Removing particles in distinct modes
  commutes.
- `SecondQuantization.Common.QuarticDiagram.fixedOrderComponentPairEmbedding_crosses_iff` — The
  fixed-order component-pair embedding preserves and reflects crossings.
- `SecondQuantization.Common.TwoPointDiagram.dysonSign_eq_external_mul_prod_vacuum` — The Dyson sign
  factors into the external component sign and all vacuum-component signs.
- `SecondQuantization.Common.TwoPointDiagram.mixedComponentCrossingCount_externalComponentPart` —
  The crossing count internal to the ambient external component equals the crossing count of the
  standalone external-piece pairing.
- `SecondQuantization.Common.TwoPointDiagram.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber` —
  Inside one order chamber, canonical transport of a normalized component pair preserves the two
  underlying standard atomic legs in their normalized order.
- `SecondQuantization.Common.TwoPointDiagram.mixedComponentWeight_eq_of_sameOrderChamber` —
  Component exchange-statistics weight is constant on one chamber.
- `SecondQuantization.Common.TwoPointDiagram.prod_slotSplitVacuumComponentSigns_eq` — The product of
  the Dyson signs carried by the ambient vacuum components is the Dyson sign of the whole quartic
  vacuum piece.
- `SecondQuantization.Common.TwoPointDiagram.prod_slotSplitVacuumComponents_eq_vacuumVertexProduct` —
  The product of arbitrary vertex-local weights over all ambient vacuum components is exactly the
  product over all vertices of the standalone quartic vacuum piece.
- `SecondQuantization.Common.TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding_crosses_iff` —
  The vacuum normalized-pair embedding preserves and reflects crossings.
- `SecondQuantization.Common.comp_operatorIntervalIntegral` — Left-composition with a fixed operator
  commutes with `operatorIntervalIntegral`: `L ∘ (∫ F) = ∫ (L ∘ F)`, given interval-integrability of
  every matrix coefficient `F` contributes.
- `SecondQuantization.Common.finiteGibbsExpectation_operatorIntervalIntegral` — The canonical finite
  Gibbs expectation commutes with coefficientwise finite operator integration.
- `SecondQuantization.Common.finiteSupportIntervalIntegral_apply` — If every vector in the family is
  supported in `S`, the finite reconstruction agrees with the coordinatewise interval integral at
  every configuration.
- `SecondQuantization.Common.measurableSet_twoPointOrderSignatureFiber` — canonical measurability
  theorem for a mixed two-point order-signature chamber, used as an analytic boundary for
  chamberwise integration.
- `SecondQuantization.Common.mixedTimeOrderedAtomicLegPosition_lt_uniform` — Legs in one mixed-time
  event block have identical comparison with every leg outside that block.
- `SecondQuantization.Common.orderedTwoPointTimedEventPosition_lt_iff_of_sameOrderChamber` —
  canonical order-chamber invariance theorem for ordered two-point timed-event positions.
- `SecondQuantization.Common.support_finiteSupportIntervalIntegral_subset` — Coordinatewise
  reconstruction cannot create support outside the supplied finite set.
- `SecondQuantization.Common.support_interactionPicture_apply_subset_reachableSupport_succ` —
  Applying an interaction-picture insertion to a vector supported at one reachable order produces
  only configurations reachable at the next order.
- `SecondQuantization.Common.twoPointLegCongr_symm` — The inverse relabeling of legs is the
  relabeling along the inverse.
- `SecondQuantization.Fermionic.AlgebraicFock.create_comp_add_swap` — Two smeared creation operators
  satisfy the creation-creation CAR.
- `SecondQuantization.Fermionic.FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_external_mul_prod_vacuum` —
  External/vacuum factorization of the signed pointwise fixed-time amplitude.
- `SecondQuantization.Fermionic.FixedExternalTwoPointWickDiagram.mixedExternalDysonFixedTimeValue_eq_externalPiece` —
  The Dyson-signed external factor is the standalone external piece's Dyson-signed fixed-time
  amplitude at its inherited interaction times.
- `SecondQuantization.Fermionic.FixedExternalTwoPointWickDiagram.mixedPairContractionValue_eq_orderedTwoPointLegPairContraction` —
  The contraction used by a normalized mixed pair is the density-state contraction of the two fixed
  standard legs represented by its endpoints.
- `SecondQuantization.Fermionic.QuarticWickDiagram.contractionIntegrand_assembleVertexOrder_eq_prod_components` —
  The Wick contraction integrand of an assembled vertex order is the product of the contraction
  integrands of its connected components, evaluated on the corresponding restricted time
  assignments.
- `SecondQuantization.Fermionic.annihilate_comp_self` — `cᵢ cᵢ = 0`: the same-mode consequence of
  `{cᵢ, cᵢ} = 0`.
- `SecondQuantization.Fermionic.completedAnnihilate_comp_algebraicToCompleted` — Completed
  annihilation agrees with algebraic annihilation on every finite-support vector.
- `SecondQuantization.Fermionic.completedCreate_comp_algebraicToCompleted` — Completed creation
  agrees with algebraic creation on every finite-support vector.
- `SecondQuantization.Fermionic.continuous_contractionIntegrand` — The fixed-order contraction
  integrand is continuous.
- `SecondQuantization.Fermionic.fermionSign_toggleOccupation` — Toggling mode `k` flips the
  fermionic sign at `i` exactly when `k` lies before `i`.
- `SecondQuantization.Fermionic.fixedExternalFiberEquiv_symm_externalPieceOfCardEq_eq` — After
  reindexing a fiber, the standalone external piece at any identified slot count is exactly the
  correspondingly standardized connected external diagram, independently of the vacuum piece.
- `SecondQuantization.Fermionic.fixedExternalOfSlotSplit_prod_vacuumDysonFixedTimeValue_eq_quarticIntegrand` —
  For an externally connected left piece and strictly decreasing inherited vacuum times, the
  complete product of ambient vacuum-component Dyson fixed-time values is exactly the standalone
  fixed-order quartic vacuum integrand, including its Dyson sign and vertex-weight prefactor.
- `SecondQuantization.Fermionic.freePartitionFunction_eq_coe_purePointPartitionFunction` — The
  finite complex free-fermion partition function is exactly the canonical pure-point Gibbs partition
  function for `fermionEnergy`, coerced from `ℝ` to `ℂ`.
- `SecondQuantization.Fermionic.interactionPicture_quarticVertexOperator_eq_prod` — A single evolved
  quartic vertex is the composed product of its four individually evolved local legs in the
  canonical local-leg order.
