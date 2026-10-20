# Retained theorem audit declarations

The theorem catalog exposes structural review signals such as low compiled-consumer count,
direct-wrapper status, and terminal status. None of these signals is automatic evidence that a
public theorem should be removed. A declaration remains public when it is the canonical statement
of an independently useful mathematical or physical fact, a deliberate simplification boundary, or
a stable domain-level API.

The theorem entries in the list below have been semantically reviewed and are intentionally retained
when structural audit signals might otherwise suggest removing them. Other structural API contracts are
listed separately at the end of this document and are not retained theorem exceptions.

`scripts/TheoremCatalog.lean` records full-name mentions and unambiguous
short-name mentions from this document as the
`retainedMention` attribute. Retained declarations keep their structural attributes in the full
catalog but are omitted from terminal, single-consumer, and direct-wrapper review queues so those
queues represent unresolved audit work.

This list is not a compatibility promise. Reassess an entry if its statement, ownership, attributes,
or consumer structure changes.

## Retained declarations

- `Dyson.hasSum_intervalIntegral_integrand_of_bound` — generic dominated-convergence result exchanging an interacting Dyson/Volterra series with the Bochner interval integral under explicit continuous bounded-interaction hypotheses; this is an independent analytic endpoint, not a disposable one-consumer proof wrapper.
- `QuantumTheory.Transport.SpectralSide.sign_opposite` — canonical `[simp]` law for the retarded/advanced spectral-side involution; retaining the sign reversal provides a stable normalization rule independently of its current regulator consumer.
- `QuantumTheory.Transport.spectralParameter_im` — canonical `[simp]` evaluation of the imaginary part of a side-indexed complex spectral parameter as its signed regulator; this is the physical-to-analytic boundary even with a single compiled private consumer.
- `Combinatorics.PairingOn.sigmaCongrRight_partner` — retain public `[simp]`: canonical computation rule for the partner map of the dependent-sum pairing constructor.
- `Combinatorics.PairingOn.sumCongr_partner_inl` — retain public `[simp]`: canonical left-summand computation rule for the disjoint-sum pairing constructor.
- `Combinatorics.PairingOn.sumCongr_partner_inr` — retain public `[simp]`: canonical right-summand computation rule for the disjoint-sum pairing constructor.
- `Combinatorics.PairingOn.transport_symm_transport` — retain public `[simp]`: canonical inverse law for transporting a pairing along an equivalence and then back along its inverse.
- `Combinatorics.PairingOn.transport_trans` — retain public: canonical composition law for pairing transport along composed equivalences.
- `Combinatorics.PairingOn.transport_transport_symm` — retain public `[simp]`: canonical inverse law for transporting first along an inverse equivalence and then along the original equivalence.
- `Combinatorics.SumEquiv.leftSubtypeEquiv_val` — retain public `[simp]`: canonical evaluation rule for the equivalence from the left summand to its image subtype.
- `Combinatorics.Pairing.ofSplit_splitLeft_splitRight` — canonical `[simp]` reconstruction law: assembling a split pairing from its induced left and right restrictions recovers the original pairing.
- `Combinatorics.Pairing.pairEndpointEquiv_apply` — canonical `[simp]` evaluation rule exposing the semantic endpoint-selection map of `pairEndpointEquiv`.
- `Combinatorics.Pairing.partner_sideMatching` — canonical `[simp]` characterization of the permutation extracted from a bipartite pairing: its image is exactly the right-side partner of each left position.
- `Combinatorics.Pairing.prod_pairs_eq_firstPair_mul` — general multiplicative decomposition of a product over normalized pairs into the first-pair factor and the erased-pairing product.
- `Combinatorics.Pairing.splitLeft_ofSplit` — canonical `[simp]` left inverse law for assembling then restricting a split pairing.
- `Combinatorics.Pairing.splitRight_ofSplit` — canonical `[simp]` right inverse law for assembling then restricting a split pairing.
- `Combinatorics.Pairing.sum_eq_sum_sum_insertFirstPair` — general additive reindexing theorem decomposing a sum over larger pairings by the partner of zero and the erased smaller pairing.
- `Combinatorics.Pairing.vertexGraph_componentBlockOn_partner` — semantic finite-subtype endpoint stating that paired legs occupy the same ambient connected-component block in the induced vertex graph.
- `Combinatorics.Pairing.eraseZeroPair_insertFirstPair` — canonical inverse law showing that erasing a freshly inserted first pair recovers the original pairing.
- `Combinatorics.Pairing.even_card_of_partner_mem` — general parity theorem stating that any finite partner-closed subset of pairing positions has even cardinality.
- `Combinatorics.Pairing.mem_pairs_map_iff` — canonical membership equivalence for normalized pairs under a partner-intertwining order embedding.
- `Combinatorics.NormalizedSetFunction.moment_apply` — retain public `[simp]`: canonical evaluation rule for the bundled moment transform.
- `Combinatorics.NormalizedSetFunction.moment_cumulant` — retain public: one half of the moment–cumulant inverse laws and the right-inverse theorem used to build `momentCumulantEquiv`.
- `Combinatorics.FamilySlotShuffleTo.blockInversionCount_self` — canonical `[simp]` boundary for the inter-block inversion count, recording that the diagonal block contribution is zero.
- `Combinatorics.FamilySlotShuffleTo.orderedBlockInversionCount_modEq_of_blockInversionCount_modEq` — reusable transport theorem lifting pairwise modular agreement of block inversion counts to the total ordered inversion count.
- `Combinatorics.FamilySlotShuffleTo.timeAssignment_apply` — canonical `[simp]` evaluation rule for restricting an ambient time assignment to one local shuffled block; it is an established simplification boundary used by diagrammatic consumers.
- `Finpartition.partOrdersCompatible_assembleOrder` — canonical compatibility law for a global order assembled from part-local orders and a partition shuffle.
- `Combinatorics.FamilySlotShuffle.cons_slotEquiv_zero` — canonical `[simp]` computation rule for the head-block coordinates of the recursive family-shuffle constructor.
- `Combinatorics.FamilySlotShuffleTo.continuous_ambientIntegrand` — general closure theorem that a finite product of continuous local integrands remains continuous after embedding into an arbitrary ambient total; this is a reusable ordered-simplex analysis API.
- `Combinatorics.FamilySlotShuffle.headTailLocalSlotEquiv_succ` — canonical `[simp]` normalization rule for the tail branch of the dependent head/tail local-slot equivalence.
- `Combinatorics.FamilySlotShuffle.headTailLocalSlotEquiv_symm_inl` — canonical `[simp]` inverse-evaluation rule sending a head local slot back to the zero-index sigma fiber.
- `Combinatorics.FamilySlotShuffle.headTailLocalSlotEquiv_symm_inr` — canonical `[simp]` inverse-evaluation rule sending a tail local slot back to the successor sigma fiber.
- `Combinatorics.FamilySlotShuffle.headTailLocalSlotEquiv_zero` — canonical `[simp]` normalization rule for the head branch of the dependent head/tail local-slot equivalence.
- `Combinatorics.FamilySlotShuffleTo.measurableLocallyBounded_ambientIntegrand` — general closure theorem that measurable locally bounded local integrands remain so after embedding into an arbitrary ambient total; it supplies the regularity input for finite-family shuffle factorization.
- `Combinatorics.FamilySlotShuffle.mem_headSlots_iff` — canonical `[simp]` membership characterization of the ambient head-slot subset in terms of the family-shuffle slot equivalence.
- `Combinatorics.FamilySlotShuffle.mem_tailSlots_iff` — canonical `[simp]` membership characterization of the ambient tail-slot subset in terms of the head/tail local-slot decomposition.
- `Combinatorics.FamilySlotShuffle.orderedSimplexIntegral_cons` — public recursion law identifying the ordered-simplex integral of a constructed family shuffle with the corresponding binary head-versus-tail shuffled integral.
- `intervalIntegral.orderedSimplexIntegral_const` — canonical closed-form evaluation of the ordered-simplex integral on constant integrands, giving the oriented simplex factor `β^n / n!`; retain as a mathematical endpoint even without a current code consumer.
- `intervalIntegral.hasDerivAt_orderedSimplexIntegral_succ` — fundamental-theorem-of-calculus endpoint for ordered-simplex integrals: differentiation in the upper bound exposes the outermost time coordinate; retain as core analytic API even without a current code consumer.
- `Combinatorics.slotShuffleLeftSlotSetEquiv_apply` — canonical `[simp]` evaluation rule for the equivalence between ambient slot shuffles and their left-slot subsets; it exposes the semantic map rather than the equivalence construction.
- `Combinatorics.BinaryShuffle.slot_injective` — core structural property of the public tagged-slot map `slot`; injectivity is independently useful and is the mathematical reason the tagged slots form an ambient-slot equivalence.
- `Combinatorics.BinaryShuffle.sum_succ_succ` — canonical recursion splitting a finite binary-shuffle sum by the side supplying the outermost slot.
- `Combinatorics.BinaryShuffle.sum_zero_left` — canonical boundary evaluation of a shuffle sum when the left family is empty.
- `Combinatorics.BinaryShuffle.sum_zero_right` — canonical boundary evaluation of a shuffle sum when the right family is empty.
- `Combinatorics.FamilySlotShuffle.card_headSlots` — canonical `[simp]` cardinality theorem for the public head-slot subset in the recursive family-shuffle decomposition.
- `Combinatorics.FamilySlotShuffle.cons_injective` — standard injectivity theorem for the public recursive `FamilySlotShuffle.cons` constructor; it is useful independently of the current `consEquiv` construction.
- `Combinatorics.FamilySlotShuffle.cons_outerShuffle_tailShuffle` — canonical reconstruction law showing that extracting the outer and tail shuffles and recombining them recovers the original family shuffle.
- `Combinatorics.FamilySlotShuffle.cons_slotEquiv_succ` — canonical `[simp]` computation rule for tail-block coordinates under the recursive family-shuffle constructor.
- `Combinatorics.BinaryShuffle.eq_allLeft` — canonical uniqueness theorem for the boundary type `BinaryShuffle m 0`; it underlies `zeroRightEquiv` and provides a direct rewrite to the unique all-left shuffle.
- `Combinatorics.BinaryShuffle.eq_allRight` — canonical uniqueness theorem for the boundary type `BinaryShuffle 0 n`; it underlies `zeroLeftEquiv` and provides a direct rewrite to the unique all-right shuffle.
- `Combinatorics.BinaryShuffle.leftSlot_consLeft_succ` — `[simp]` computation rule for recursive left-slot coordinates after a left outer step; it is part of the public recursive slot API used by shuffle-equivalence proofs.
- `Combinatorics.BinaryShuffle.leftSlot_consLeft_zero` — `[simp]` computation rule identifying the newly inserted left outer slot with ambient slot zero.
- `Combinatorics.BinaryShuffle.rightSlot_consLeft` — `[simp]` computation rule for right-slot coordinates after a left outer shuffle step; it is used in the recursive slot-equivalence proofs.
- `Combinatorics.BinaryShuffle.slotEquiv_inl` — canonical `[simp]` evaluation rule exposing the left branch of the noncomputable tagged-slot equivalence.
- `Combinatorics.BinaryShuffle.slotEquiv_inr` — canonical `[simp]` evaluation rule exposing the right branch of the noncomputable tagged-slot equivalence.
- `Combinatorics.BinaryShuffle.slotShuffleEquiv_apply` — canonical `[simp]` evaluation rule for the equivalence between recursive binary shuffles and ambient slot shuffles; it keeps downstream code independent of the `Equiv.ofBijective` implementation.
- `BerryGeometry.PointwiseEigenbasisData.berryConnection_diagonal_im_eq_zero` — canonical gauge-local Berry-connection fact that each diagonal connection element is real; this is a physically meaningful endpoint derived from Hermiticity, not proof routing.
- `BerryGeometry.PointwiseEigenbasisData.berryCurvature_swap` — canonical antisymmetry of pointwise Berry curvature under exchange of parameter directions.
- `BerryGeometry.PointwiseEigenbasisData.bornFock_berryConnection` — canonical Born–Fock off-diagonal Berry-connection formula relating eigenvector derivatives to Hamiltonian-derivative matrix elements and level spacings.
- `BerryGeometry.PointwiseEigenbasisData.hellmannFeynman` — canonical Hellmann–Feynman theorem for the pointwise eigenbasis data.
- `BerryGeometry.PointwiseEigenbasisData.star_berryConnection` — the full band-index Berry-connection matrix is Hermitian by differentiated orthonormality; retain this physically meaningful off-diagonal statement rather than treating its single diagonal-reality consumer as proof-routing evidence.
- `BerryGeometry.PointwiseEigenbasisData.berryCurvature_eq_sum_hamiltonianDerivativeMatrixElements` — canonical pointwise force-matrix representation of Berry curvature for a nondegenerate band, with self-adjoint directional Hamiltonian derivatives explicit; the clean massive-Dirac consumer uses this general spectral identity.
- `Combinatorics.SlotShuffle.leftSlots_orderEmbOfFin` — canonical identification of the increasing enumeration of ambient left slots with the slot-shuffle embedding; it is used source-level by the two-point fiber shuffle integral even though the proof dependency is erased from compiled consumers.
- `Combinatorics.SlotShuffle.card_eq_choose` — canonical binomial-cardinality theorem for ambient order-preserving slot shuffles; it follows from the direct left-slot-set correspondence and supplies the recursive binary-shuffle equivalence.
- `Combinatorics.BinaryShuffle.card_succ_succ` — natural Pascal recurrence for the recursively defined binary-shuffle type and the induction step underlying the closed binomial cardinality formula.
- `Combinatorics.BinaryShuffle.card_zero_left` — canonical `[simp]` boundary stating uniqueness of a binary shuffle with no left slots.
- `Combinatorics.BinaryShuffle.card_zero_right` — canonical `[simp]` boundary stating uniqueness of a binary shuffle with no right slots.
- `LinearPMap.boundedSelfAdjointApproximation_commute` — reusable resolvent-approximation commutation theorem for arbitrary positive scales; its present private error-estimate consumer does not make the operator-theoretic statement implementation-only.
- `LinearPMap.boundedUnitaryEvolution_add_generator_of_commute` — reusable factorization law for bounded evolutions generated by commuting operators; retain the general operator theorem rather than inline it into one private estimate.
- `QuantumTheory.LinearResponse.hasStaticLimit_lehmannTerm` — reusable scalar Lehmann-term continuity result at fixed nonzero switching rate.
- `QuantumTheory.LinearResponse.hasStaticLimit_lehmannTerm_zero_rate` — reusable zero-rate scalar Lehmann-term static-limit result under the explicit nonresonance/zero-weight condition.
- `QuantumTheory.Models.MassiveDirac.continuumAngularGreenIntegralOfRegulator_eq` — model-level angular-reduction identity removing the in-plane Pauli channels and producing the physical `2π` factor.
- `QuantumTheory.Models.RashbaExchange.hamiltonianOperator_mul_bandProjectorOperator` — canonical band-projector eigenoperator identity for the Rashba-exchange Hamiltonian.
- `QuantumTheory.Models.RashbaExchange.spinHamiltonian_mul_self` — canonical spectral identity that the traceless Rashba-exchange spin Hamiltonian squares to `E² I`.
- `QuantumTheory.Models.RashbaExchange.bandProjectorOperator_completeOrthogonalIdempotents` — canonical complete orthogonal idempotent family for the nondegenerate Rashba-exchange band projectors.
- `QuantumTheory.Transport.adiabaticFrequencyDomainSusceptibility_eq_bastinSpectralVertexSum` — physical finite-system endpoint identifying the causal susceptibility with the Kubo–Bastin spectral vertex sum at positive switching rate.
- `SecondQuantization.Common.twoPointOrderSignature_eq_iff` — agreement of strict event-time comparisons is equivalent to equality of finite signatures, including tied-time configurations.
- `QuantumMechanics.SingleParticle.Continuum.realL2MultiplicationOperator1D_symmetric` — deliberate continuum-quantum-mechanics specialization of the measure-space-independent `L2Multiplication.realMultiplicationOperator_symmetric`; the named one-dimensional Lebesgue-space statement is the stable API used by Hamiltonian symmetry and self-adjointness proofs.
- `QuantumTheory.Transport.im_inner_resolvent_spectralParameterOfRegulator_apply_self` — canonical
  dimension-independent signed-regulator Herglotz identity for a self-adjoint resolvent. Consumers
  that need the reversed inner-product orientation should reverse it locally rather than expose a
  second public theorem.
- `QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornSelfEnergyOfRegulator_dissipative`
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
- `Lorentzian.tendsto_spectralTailMass_zero` — model-independent analytic
  approximate-identity result for the vanishing difference of Lorentzian masses
  on any two fixed positive symmetric windows, without a nesting assumption.
- `SecondQuantization.Fermionic.orderedSimplexContribution_eq_pairingEvaluation` — canonical
  representation theorem identifying one Wick diagram's fixed-order ordered-simplex contribution
  with the flattened pairing evaluator after transport to a chosen vertex order.
- `SecondQuantization.Fermionic.sum_vertexWeight_mul_orderedSimplexContribution_eq_pairingEvaluation`
  — canonical reindexing theorem converting the full fixed-order Wick-diagram sum into the
  vertex-label/pairing double sum used by the Dyson-to-Wick expansion.
- `Combinatorics.smul_permutationConnectedCycleSeries_eq_neg_traceLog` — canonical
  division-free statistics-independent trace-log identity for a finite kernel at arbitrary exchange
  weight, including `ζ = 0`; the nonzero diagonal endpoint is derived from this reusable
  formal-series boundary by scalar cancellation.
- `Finset.card_filter_product_eq_sum_card_filter` — canonical generic double-counting identity for a
  filtered finite self-product. Its remaining crossing-count consumer is a domain specialization,
  while the theorem itself is independent of pairing or crossing structure.
- `QuantumMechanics.SingleParticle.Continuum.l2MultiplicationOperator1D_apply` — deliberate `[simp]`
  boundary for the continuum-domain multiplication-operator vocabulary. The proof delegates to the
  analysis-level operator theorem, but the specialization is the normalization rule for this API.
- `SecondQuantization.Bosonic.numberOperator_basisState` — canonical number-operator eigenvalue
  equation `N_i |n⟩ = n_i |n⟩`; this is a physical statement about the named number operator rather
  than proof-routing around `create_annihilate_basisState_same`.
- `QuantumTheory.Transport.TracedStredaAnalyticData.staticChannelConductivity_eq_surface_add_sea`
  — named physical endpoint identifying the normalized finite static channel response with the
  regularized Středa surface-plus-sea split under the stated traced-kernel and response-identity assumptions.
- `QuantumTheory.Transport.regularizedBastinOperatorIntegrand_neg_neg` — canonical
  bilinearity/sign symmetry of the generic finite-broadening Bastin operator kernel under
  simultaneous reversal of both current vertices.
- `SecondQuantization.Fermionic.Validation.twoLevel_zeroCurrent_streda_sum_zero` — concrete
  two-level zero-current validation endpoint for the pointwise Bastin/Středa decomposition; it is
  intentionally retained as a symbolic sanity check rather than proof infrastructure.
- `QuantumTheory.Transport.FiniteDisorderEnsemble.retardedAdvancedLadderCLM_apply` — canonical
  evaluation rule identifying the bundled retarded-advanced ladder action with the physical
  covariance insertion `C₂(Gᴿ Γ Gᴬ)`; it is the stable simplification boundary for the ladder API.
- `QuantumMechanics.SingleParticle.currentEquivalent_nestedSymmetrizedCurrentFlux` — canonical
  corrected-current equivalence theorem: any full current representing the intrinsic transport is
  equivalent on exact differentials to the canonical nested current flux.
- `QuantumMechanics.SingleParticle.exists_current_eq_symmetrized_add_correction_add_invisible` —
  physics-facing representation theorem `J = J_sym + J_corr + K` with `K` invisible on exact
  differentials; it is the explicit extension-ambiguity endpoint of the corrected-current API.
- `SecondQuantization.Fermionic.timeOrderedExternalFields_swap` — canonical fermionic exchange law
  for the named time-ordered external-field construction: swapping both fields and times produces
  the fermionic statistics sign.
- `QuantumMechanics.SingleParticle.lie_orbitalAngularMomentumZ_continuum_sign` — physics-facing continuum
  specialization fixing the derivative-localizer coefficient to `iℏ`; it records the expected
  orbital-angular-momentum localization commutator rather than a proof-routing alias.
- `QuantumMechanics.SingleParticle.Continuum.continuumRealPotentialSchrodingerHamiltonian1D_isClosed`
  — physical real-scalar-potential closedness theorem for the named continuum Hamiltonian; the
  generic complex-multiplier proof does not make the real-potential endpoint redundant.
- `SecondQuantization.Bosonic.annihilate_fockVacuum` — canonical `[simp]` vacuum identity stating that
  every bosonic annihilation operator kills the Fock vacuum.
- `SecondQuantization.Bosonic.particleNumber_vacuum` — canonical `[simp]` statement that the bosonic
  vacuum has zero total occupation number.
- `SecondQuantization.Common.finiteGibbsExpectation_comp_eq_div_of_exchangeCommutator` — deliberate
  `Statistics`-indexed Gibbs two-point API for callers that already work with `exchangeCommutator`,
  rather than the lower-level raw-`ζ` presentation.
- `SecondQuantization.Fermionic.annihilate_fockVacuum` — canonical `[simp]` CAR vacuum identity that
  every fermionic annihilation operator kills the Fock vacuum.
- `ContinuousLinearMap.adjointConjugate_rankOne` — canonical rank-one covariance identity under
  bounded adjoint conjugation. The current single consumer is a density-operator specialization,
  while the statement itself is general operator infrastructure.
- `ContinuousLinearMap.eigenspace_adjointConjugate` — canonical eigenspace transport theorem under
  unitary conjugation. It identifies the full eigenspace submodule, not merely the finite-dimensional
  rank consequence used downstream.
- `ContinuousLinearMap.IsTraceClass.adjointConjugate` — canonical closure of general
  trace-class membership under bounded adjoint conjugation `T ↦ U T U†`.
- `ContinuousLinearMap.IsTraceClass.trace_adjointConjugate` — canonical complex-trace invariance
  endpoint `Tr(U T U†) = Tr(T)` under `U†U = 1`, derived directly from general trace cyclicity.
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
- `QuantumTheory.bandStateOccupation_zeroTemperature_eq_one_of_isFilledBand` — canonical
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
- `QuantumTheory.DensityOperator.hasSum_abs_eigenvalues_eq_one` — spectral normalization law for a
  density operator: the absolute eigenvalue weights sum to one as an independent statement about
  the density state's spectral probability weights.
- `QuantumTheory.POVM.hasSum_inner_apply` — canonical diagonal weak-operator consequence of strong
  POVM normalization and a reusable bridge from operator normalization to Born probabilities.
- `QuantumTheory.Models.MassiveDirac.pauliGreenOperatorOfRegulator_eq_closedForm` —
  canonical closed numerator/denominator form of the arbitrary-regulator Massive Dirac Green
  operator.
- `QuantumTheory.Models.MassiveDirac.bandProjectorOperator_completeOrthogonalIdempotents` — canonical
  complete orthogonal idempotent family for nondegenerate Massive Dirac band projectors.
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
- `SecondQuantization.Fermionic.continuous_matrixCoeff_quarticVertexSequenceInteractionPicture` — joint continuity of
  matrix coefficients of the quartic vertex sequence for arbitrary mode types; this follows from
  the Common scalar-time-factor decomposition without finite intermediate-state sums.
- `SecondQuantization.Fermionic.dist_completedModeTruncation_le_two_mul_of_fixed` — reusable contraction
  estimate bounding truncation error by twice the distance to any fixed point of the truncation.
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
- `LeanCondensedMatter.Crystal.reciprocalPairing_isSymm` — canonical symmetry property of the
  normalized reciprocal pairing used to construct crystallographic reciprocal bases and lattices.
- `LinearPMap.stoneEvolution_apply_hasDerivAt_zero` — Stone-generator endpoint identifying the
  derivative at zero of the strong Stone evolution with `-iA` on the operator domain.
- `QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonGreenLoopMatrix_apply_eq_radial_integral`
  — model-level T-matrix provenance theorem exposing the finite-cutoff radial Green-loop integral
  and its single physical momentum-measure prefactor.
- `QuantumTheory.Models.MassiveDirac.radialBastinMassWindowMargin_le_abs_gap_add_offset`
  — model-specific uniform separation bound between the mass-window margin and the shifted
  opposite-band energy denominator.
- `SecondQuantization.Fermionic.CompletedThermalLadder.completedAnticomm_operator_operator` —
  canonical completed-space CAR statement for the unified thermal ladder operator, expressing its
  anticommutator as the scalar CAR coefficient times the identity.
- `Combinatorics.Pairing.presentsPairs_of_partner_blockPair` — Criterion for presenting a pairing.
- `Combinatorics.blockPair_apply` — The two positions of a block, written through the block-slot
  presentation.
- `Combinatorics.cycleDefect_eq_sum_orbitFinpartition` — The cycle defect is the sum of `|B| - 1`
  over the canonical orbit blocks.
- `Combinatorics.cycleDefect_mod_two` — The parity of the cycle defect agrees with the parity of
  `cycleType.sum + cycleType.card`.
- `Combinatorics.not_crosses_self` — canonical irreflexivity fact for the pairing-crossing
  relation: a normalized pair never crosses itself.
- `Combinatorics.singleCycleContribution_factor_exchangeWeight` — A connected
  permutation on `S` carries the common exchange factor `ζ ^ (|S| - 1)`, factored from the
  exchange-weight-one connected contribution.
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
- `QuantumTheory.finiteDimensional_of_gibbsOp_isCompact` — bounded-Gibbs obstruction theorem:
  compactness of the invertible Gibbs exponential forces finite dimensionality, documenting why the
  bounded Gibbs API is explicitly finite-dimensional.
- `QuantumTheory.Transport.FiniteDisorderEnsemble.star_averagedGreenOfRegulator` — Adjointing the
  exact finite disorder-averaged Green operator reverses the signed regulator.
- `QuantumTheory.Models.MassiveDirac.bandProjectorOperator_ne_zero` — Every band projector
  is a nonzero bounded operator.
- `QuantumTheory.Models.MassiveDirac.continuumBornDampingScale_eq_selfEnergyPrefactor` —
  The damping scale is exactly the physical-momentum prefactor already extracted from the Born
  self-energy.
- `QuantumTheory.Models.MassiveDirac.continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq` —
  The radial Cartesian Born denominators multiply to the canonical real weak-Born RA product.
- `QuantumTheory.Models.MassiveDirac.finiteBroadeningSameSide_integrable_and_integral_eq_endpoint` —
  The finite-broadening bare-source same-side radial integrand is integrable and evaluates to the
  canonical endpoint.
- `QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq_denominatorForm` —
  The ordered `xy` radial Hall-surface integrand is the measured-`x`, source-`y` Středa radial
  response in explicit common RA Born-Dyson denominator form.
- `QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_x_eq_denominatorForm` —
  The ordered `xx` finite-`η` dressed Středa angular coefficient in explicit denominator form.
- `QuantumTheory.Models.MassiveDirac.norm_targetCenteredInterbandBastinPairIntegral_radial_le` —
  Uniform norm bound for the complete target-centered interband Bastin pair on the radial axis.
- `QuantumTheory.Models.MassiveDirac.radius_lt_abs_interbandEnergyGap_of_lt_two_mul_abs_mass` —
  A pole window narrower than the mass gap is valid simultaneously at every momentum.
- `QuantumTheory.Models.MassiveDirac.star_pauliGreenOperatorOfRegulator` — Adjointing the
  explicit Pauli Green operator reverses the signed regulator.
- `QuantumTheory.Models.MassiveDirac.tendsto_finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary_disorder_zero` —
  At fixed cutoff beyond the metallic shell, the canonical zero-broadening solved ladder vector
  converges to the longitudinal dressed-current factor `2 (ε² + m²) / (ε² + 3 m²)` with vanishing
  raw transverse component.
- `QuantumTheory.Models.MassiveDirac.tendsto_finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary_y_div_disorder_zero` —
  The transverse component of the zero-broadening dressed-current vector carries the same first
  nonvanishing weak-disorder coefficient as the transverse ladder action.
- `QuantumTheory.Models.MassiveDirac.zeroTemperatureOccupiedBerryWeightCutoff_eq` — The
  canonical occupation-derived finite-cutoff response keeps the single-cone regulator term explicit,
  including the massless endpoint where both sides vanish.
- `Real.tendsto_integral_radialQuadraticLorentzian_atTop` — For nonzero radial
  scale and positive width, the radial quadratic Lorentzian integral converges as the upper cutoff
  tends to `+∞`.
- `SecondQuantization.Bosonic.QuarticDiagram.orderedThermalAmplitude_eq_prod_components` — The
  coefficientwise bosonic ordered thermal amplitude factors over connected components.
- `SecondQuantization.Bosonic.createOccupation_comm` — Creating particles in two modes commutes.
- `SecondQuantization.Bosonic.removeOccupation_comm` — Removing particles in distinct modes
  commutes.
- `SecondQuantization.Common.QuarticDiagram.fixedOrderComponentPairEmbedding_crosses_iff` — The
  fixed-order component-pair embedding preserves and reflects crossings.
- `SecondQuantization.Common.TwoPointDiagram.mixedComponentCrossingCount_externalComponentPart` —
  The crossing count internal to the ambient external component equals the crossing count of the
  standalone external-piece pairing.
- `SecondQuantization.Common.TwoPointDiagram.mixedComponentPairTimeEquiv_endpointLegs_eq_of_comparisons` —
  When all strict time-event comparisons agree, canonical transport of a normalized component
  pair preserves the underlying standard atomic legs in normalized order.
- `SecondQuantization.Common.TwoPointDiagram.mixedComponentWeight_eq_of_comparisons` —
  Component exchange-statistics weight is unchanged when every strict time-event comparison agrees.
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
- `LocallyFiniteHopping.operator_latticeKet` — canonical
  `[simp]` evaluation of the hopping operator on a localized site ket.
- `LocallyFiniteHopping.amplitude_eq` — canonical `[simp]`
  normalization of the named hopping matrix element to the corresponding column coefficient.
  Source-level validation proofs use this rule even when simplification erases the compiled
  dependency edge.
- `LocallyFiniteHopping.amplitude_eq_zero_of_not_mem` —
  canonical incoming-locality consequence: hopping amplitudes vanish outside the finite incident
  neighborhood.
- `LocallyFiniteHopping.amplitude_swap_eq_zero_of_not_mem` —
  canonical outgoing-locality companion to `amplitude_eq_zero_of_not_mem`.
- `LocallyFiniteHopping.bondOperator_swap` — canonical
  orientation-reversal law for the one-particle bond-current operator.
- `LocallyFiniteHopping.lie_siteProjector` —
  one-particle local continuity identity expressing the hopping/projector commutator as the finite
  outgoing bond-operator sum.
- `SecondQuantization.Fermionic.Lattice.bondCurrent_swap` — physical orientation-reversal law for
  the many-particle bond current; the bounded finite-lattice current transports this algebraic fact.
- `SecondQuantization.Fermionic.Lattice.discrete_continuity` — canonical algebraic local continuity
  equation on an arbitrary locally finite lattice and the source theorem for the bounded
  finite-lattice continuity equation.
- `SecondQuantization.Fermionic.freePartitionFunction_eq_coe_eigenbasisPartitionFunction` — The
  finite complex free-fermion partition function is exactly the canonical pure-point Gibbs partition
  function for `fermionEnergy`, coerced from `ℝ` to `ℂ`.
- `SecondQuantization.Fermionic.sum_freeGibbsConfigurationProbability_filter_mem` — canonical
  finite-mode marginal-probability identity: the total Gibbs probability of configurations
  containing mode `i` is exactly its Fermi–Dirac occupation.
- `SecondQuantization.Fermionic.eigenbasisGibbsEnergyExpectation_fermionEnergy_eq_sum_fermiDirac` — canonical
  finite free-fermion mean-energy identity `⟨E⟩ = ∑ᵢ εᵢ fᵢ`; its current single consumer is the
  entropy endpoint, but the thermodynamic statement is independently meaningful.
- `SecondQuantization.Fermionic.vonNeumannEntropy_freeGibbsDensityOperator_toReal_eq_sum_fermiDirac`
  — canonical finite free-fermion entropy endpoint expressing the Gibbs-state von Neumann entropy
  as the sum of binary Fermi–Dirac mode entropies.
- `ContinuousLinearMap.IsTraceClass.traceNorm_nonneg` — Canonical nonnegativity of the trace norm of a general trace-class operator. Although its proof reuses Hilbert–Schmidt norm-square, the trace-norm invariant deserves its own operator-facing API.
- `ContinuousLinearMap.IsTraceClass.traceNorm_proof_irrel` — Trace norm depends on the operator rather than the witness of trace-class membership. Retain the trace-class-facing statement used by adjoint and norm-congruence arguments.
- `ContinuousLinearMap.IsTraceClass.trace_add` — General additivity of the canonical complex trace on trace-class operators. Its present private density-expectation consumer does not make the operator theorem proof plumbing.
- `ContinuousLinearMap.innerHS_eq_of_isHilbertSchmidt` — Hilbert-basis independence of the Hilbert–Schmidt inner product, independently meaningful even when its current consumer is the private basis-independence proof for trace.
- `LinearPMap.mem_compOnDomain_domain_iff` — Canonical operator-product domain-membership statement. The reduction to `mem_naturalCompDomain_iff` is intentional: it exposes the condition through the public `compOnDomain` construction.
- `SecondQuantization.Common.ExternalInsertionDiagram.componentMixedPositionShuffle_slotEquiv_apply` — Canonical `[simp]` evaluation of the component mixed-position shuffle. Its proof connects the family shuffle to the component-position API and fixes the normal form used by crossing parity.
- `SecondQuantization.Bosonic.removeOccupation_createOccupation_of_ne` — General commutation of occupation creation and removal in distinct bosonic modes, a reusable occupation-algebra fact rather than a private CCR proof step.
- `ContinuousLinearMap.IsTraceClass.norm_trace_le_traceNorm` — Fundamental trace-ideal inequality `‖Tr T‖ ≤ ‖T‖₁`, valid for general trace-class bounded operators; retain as an independently useful analytic bound.
- `ContinuousLinearMap.IsTraceClass.traceNorm_comp_right_le` — The trace norm is bounded under composition with an arbitrary bounded right factor; this is the trace-ideal inequality rather than a consumer-specific estimate.
- `LinearPMap.boundedUnitaryEvolution_eq_exp` — Canonical explicit Schrödinger-exponential formula for the bounded evolution API; the definitional proof provides a stable operator-facing statement.
- `LinearPMap.compOnDomain_apply` — Canonical evaluation rule for partial-map composition on its natural domain. The equation expresses the public composition API even when its proof is definitional.
- `SecondQuantization.Bosonic.completedAnnihilate_comp_algebraicCore` — Compatibility of completed bosonic annihilation with the finite-support algebraic core, an independent domain-and-operator bridge.
- `SecondQuantization.Bosonic.completedCreate_comp_algebraicCore` — Compatibility of completed bosonic creation with the finite-support algebraic core; keep separate from annihilation because its weighted domain differs.
- `SecondQuantization.Common.ExternalInsertionDiagram.hasNoVacuumComponent_externalBearingDiagram` — External-bearing restriction removes purely vacuum components without requiring different external insertions to be connected; it is the structural guarantee of the slot-split API.
- `SecondQuantization.Common.QuarticDiagram.pairingInOrder_partner_componentOrderedLeg` — The global pairing partner agrees with the embedded component-local partner after assembling ordered vertices; retain this reusable pairing compatibility law.
- `SecondQuantization.Common.continuousInteractionPicture_eq_conj` — Canonical conjugation formula connecting the interaction picture to transported continuous free evolution; it states the operator-level semantics of the construction.
- `SecondQuantization.Common.continuousOperatorIntervalIntegral_eq` — Identifies the coefficientwise algebraic interval integral with the Bochner interval integral of its continuous-operator realization; this is a reusable analytic bridge.
- `SecondQuantization.Common.hasFPowerSeriesAt_analyticDysonPartitionFunction` — The actual finite-configuration interacting Dyson partition function has the prescribed Taylor expansion at zero coupling, serving as a stable analytic endpoint for logarithmic derivatives.
- `SecondQuantization.Common.measurableSet_externalInsertionOrderSignatureFiber` — Borel measurability of each external-insertion order chamber, an independently meaningful regularity statement for chamberwise integration.
- `SecondQuantization.Common.mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff` — Preservation of the flattened leg order under changes of event times that preserve the supporting-event comparison; a reusable statistics-independent ordering bridge.
- `SecondQuantization.Fermionic.matrixCoeff_annihilate` — Occupation-basis matrix-element formula, including the fermionic sign and the removal-support condition; the matrix-coefficient presentation is a physical operator API.
- `SecondQuantization.Fermionic.matrixCoeff_create` — Occupation-basis matrix-element formula for fermionic creation, including its Pauli-exclusion branch and sign; retain alongside the annihilation formula.
- `QuantumTheory.Transport.continuous_resolvent_spectralParameterOfRegulator_energy` — Continuity of the self-adjoint resolvent along the real-energy axis at fixed nonzero signed regulator, a reusable spectral regularity result.
- `SecondQuantization.Fermionic.ExternalInsertionWickDiagram.relativeComponentShuffleSign_mul_mixedPairingValue_eq_componentExternalOrderSign_mul_prod_components` — Fermionic pairing-level factorization of the relative shuffle sign and mixed contraction values into the external-component sign and component products, without conflating it with the full amplitude.
- `SecondQuantization.Common.ExternalInsertionDiagram.relativeComponentShuffle_sign_eq_mixedAtomic_mul_prod_components` — Permutation-sign factorization relating the relative shuffle, global mixed-time order, and component-local orders; retain as the independent sign bridge.
- `ConservationLaw.symmetrizedProductBilinear_apply` — Deliberate explicit bridge from the canonical bilinear symmetrized-product owner to its evaluated two-operator form. Keep it out of global `[simp]` to avoid competing normal forms.
- `PowerSeries.coeff_one_logOf` — The first coefficient of the formal logarithm of a normalized complex power series equals its first original coefficient; retain as a general power-series identity.
- `Combinatorics.BinaryShuffle.card_eq_choose` — canonical binomial-cardinality formula for recursively constructed binary shuffles. It is used source-level to prove the bijectivity of `BinaryShuffle.slotShuffleEquiv`, even though this proof-only dependency is absent from the compiled-consumer count.
- `Combinatorics.NormalizedSetFunction.cumulant_apply` — canonical `[simp]` evaluation rule for the normalized cumulant transform; it complements the retained `moment_apply` rule and exposes the underlying finite-set cumulant without unfolding the bundled function.
- `Combinatorics.MultiplicativeWeight.normalizedObjectMoment_apply` — canonical `[simp]` evaluation rule connecting the normalized object-moment bundle to the original weighted object sum; it is the stable boundary between the connected-decomposition construction and the normalized finite-set function interface.
- `Combinatorics.Pairing.prod_pairs_ofSplit` — general factorization theorem for contraction products on pairings assembled from two independent parts. Its comparison hypotheses explicitly account for possible endpoint reversal when the position splitting is not order preserving.
- `Combinatorics.Pairing.isSplit_inr` — intrinsic closure of the right part of a split pairing, derived from the left-closure definition and the involutive partner map; retain this symmetric mathematical consequence as an independently usable split-pairing fact.
- `Combinatorics.Pairing.cast_partner` — general transport law for the pairing partner permutation across an equality of pair counts. Its present private consumer lies in fermionic external-insertion diagrammatics, but the theorem belongs to the reusable combinatorial pairing layer.
- `Combinatorics.singleCycleContribution_univ_eq_sum_isCycleOn` — intrinsic finite-permutation formula identifying the connected contribution on the full index set with the sum over full cycles. Retain the combinatorial identity independently of its current private assignment-to-trace bridge.
- `QuantumTheory.Transport.Topology.PeriodicBlochProjector.berryCurvatureComplex_isSelfAdjoint` — geometric realness statement for the gauge-invariant complex projector-curvature trace, using self-adjointness and finite trace cyclicity. Its private scalar-wrapper consumer does not make the mathematically meaningful reality theorem proof-only plumbing.
- `SecondQuantization.Common.TwoPointDiagram.slotCongr_partner` — canonical transport compatibility for a two-point diagram's paired legs under interaction-slot relabeling. Retain as a reusable geometric law rather than restricting it to the private external-piece compatibility proof.
- `SecondQuantization.Common.QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg` — canonical reconstruction identity for flattened quartic legs from vertex and local-leg coordinates. The simple proof delegates to the quartic-leg equivalence, but the named equation exposes the coordinate reconstruction law used by component restriction and reassembly.
- `SecondQuantization.Common.interactionSector_externalComponent_ofSlotSplit` — physical/combinatorial reconstruction theorem identifying the external connected component's interaction sector after assembling an externally connected two-point piece and a vacuum piece. It is the inverse-fiber condition underlying the public external-fiber equivalence, despite its private compiled consumer.
- `QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary_ne_zero` — reusable fixed-cutoff RA boundary nonvanishing criterion under explicit metallic, disorder, cutoff, and renormalization assumptions. Its current private limit-proof consumer needs precisely this denominator condition.
- `QuantumTheory.Models.MassiveDirac.star_finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary` — canonical complex-conjugation symmetry exchanging retarded and advanced Born–Dyson denominator boundaries; this model-level spectral-side identity is meaningful independently of its single private algebraic consumer.
- `QuantumTheory.Models.MassiveDirac.tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_denominator_nonzero` — general fixed-cutoff current-rung integral convergence theorem assuming only boundary denominator nonvanishing along the radial interval, without the stronger model-specific renormalization bound. Retain the reusable weaker-hypothesis limit boundary.
- `QuantumTheory.Models.MassiveDirac.tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand_broadening_zero` — pointwise positive-broadening limit of the radial current-rung integrand, with denominator nonvanishing supplied explicitly; it is a meaningful analytic premise for dominated-convergence arguments rather than a private proof alias.
- `Finpartition.bind_restrict_eq_of_le` — canonical reconstruction law for a refinement: restricting it to each block of a coarser partition and binding those restrictions recovers the original refinement. This is the left-inverse proof underlying `refinementsEquivFiberPartitions`, even when compiled consumers report zero.
- `Finpartition.replicaPolynomial_eval_nat_eq_sum_labelings` — combinatorial interpretation of replica-polynomial evaluation at a natural replica count as independently labelled partition blocks. It connects the formal replica variable to actual finite labelings, not just a proof transformation.
- `Finpartition.partitionProduct_eq_mul_of_isIndependentAcross` — general factorization of partition-product weights across independent disjoint regions. It is an independent multiplicative identity useful before taking cumulants.
- `Finpartition.cumulantFromMoment_eq_zero_of_isIndependentAcross` — canonical vanishing of mixed connected cumulants for a union of two nonempty independent regions; the physically meaningful independence endpoint specializes the more general straddling-set result.
- `Combinatorics.pairingSum_eq_permutationSum_of_inl_vanishing` — the central exchange-statistics bridge from crossing-weighted perfect pairings to a cycle-weighted permutation sum under the left-pair selection rule and `ζ² = 1`. The module explicitly identifies this as its canonical public theorem.
- `ConservationLaw.FluxBalanceLaw.evolution_eq_zero_of_differential_eq_zero_of_source_eq_zero` — physical conservation criterion: a test configuration annihilated by the differential and source has zero localized evolution. The compact proof uses intrinsic transport factorization without choosing an extension current.
- `ConservationLaw.FluxBalanceLaw.sourceFreeFlux_unique` — uniqueness of test-space transport for a source-free balance law with fixed evolution and localized quantity; independently expresses the no-source uniqueness boundary even when no compiled consumer invokes it.
- `Fredholm.diagonalDet_reindex` — canonical invariance of the diagonal Fredholm determinant under an arbitrary equivalence of coefficient indices, expressing independence of enumeration in the infinite-product definition.
- `Fredholm.diagonalDet_eq_finsetProd` — finite-support reduction of the diagonal Fredholm determinant even when the ambient index type is infinite; this is distinct from the finite-index-type formula.
- `Fredholm.diagonalDet_eq_det_one_add_diagonalOp` — canonical finite-dimensional consistency theorem identifying the diagonal Fredholm determinant with the ordinary determinant of `1 + diagonalOp`.
- `HilbertBasis.one_add_diagonalOp_has_nonzero_kernel_vector_of_diagonalDet_eq_zero` — spectral consequence of determinant vanishing: for an absolutely summable diagonal perturbation, `1 + diagonalOp` has a nonzero kernel vector. Retain as the Fredholm criterion endpoint.
- `PowerSeries.replicaCoeffPolynomial_eval_nat` — finite-replica interpretation of the fixed-order replica polynomial as the factorial-normalized coefficient of `Z ^ n`; this bridges the formal replica variable with actual integer powers.
- `QuantumTheory.LinearResponse.expValue_hamiltonian_evolveState` — complex pure-state energy-conservation endpoint for bounded free evolution, specializing the general commutation conservation theorem to the physical Hamiltonian.
- `QuantumTheory.LinearResponse.observableExpValue_hamiltonian_evolveState` — real-valued pure-state energy-conservation endpoint, preserving the lossless observable expectation API rather than extracting the real part of a complex expression.
- `QuantumTheory.LinearResponse.expectation_hamiltonian_evolveDensityOperator` — complex density-state Hamiltonian expectation conservation; the density-state presentation is an independently useful endpoint of the general commutation law.
- `QuantumTheory.LinearResponse.observableExpectation_hamiltonian_evolveDensityOperator` — real-valued density-state energy-conservation endpoint for the named Hamiltonian observable, distinct from the pure-state and complex-expectation interfaces.
- `Models.Heisenberg.excitationHamiltonian_isPositive` — physical positivity of the exchange excitation Hamiltonian at nonnegative coupling; retain the order-theoretic stability endpoint even without a compiled consumer.
- `Models.Heisenberg.hamiltonian_eq_spinSum` — equivalence between the exchange representation and the dimensionful spin-product Hamiltonian under nonzero ℏ; retain the modeling bridge even without a compiled consumer.
- `Models.Heisenberg.hamiltonian_isSelfAdjoint` — self-adjointness of the finite spin-ring Hamiltonian; this is the canonical operator statement, with its one-use symmetry proof inlined rather than published separately.
- `Models.Heisenberg.hamiltonian_polarized` — the fully polarized state is an eigenvector of the exchange Hamiltonian with the specified ground-state energy; retain the physical benchmark.
- `Models.Heisenberg.hamiltonian_eq_excitation_add_ground` — the exact decomposition into excitation Hamiltonian and polarized ground-state energy; this is an independent normalization identity, not merely a proof helper.
- `Models.Heisenberg.excitationHamiltonian_oneMagnonKet` — the concrete nearest-neighbor one-magnon action of the excitation Hamiltonian; retain this lattice dynamics statement independently of its embedding consumer.
- `Models.Heisenberg.excitationHamiltonian_comp_oneMagnonEmbedding` — the exact intertwining of the excitation Hamiltonian with the one-magnon discrete Laplacian; retain the invariant-subspace statement despite a single Fourier-mode consumer.
- `QuantumTheory.Models.MassiveDirac.energySq_neg_momentum` — canonical `[simp]` invariance of the quadratic Dirac dispersion under simultaneous momentum reversal, reused by propagator calculations.
- `QuantumTheory.Models.MassiveDirac.bandSign_lower` — canonical `[simp]` constructor evaluation of the lower-band energy sign; terminal status reflects the normal-form role, not dead API.
- `QuantumTheory.Models.MassiveDirac.bandSign_upper` — canonical `[simp]` constructor evaluation of the upper-band energy sign; terminal status reflects the normal-form role, not dead API.
- `QuantumTheory.Models.MassiveDirac.oppositeBand_lower` — canonical `[simp]` evaluation of band interchange on the lower band, providing the model's public two-band normalization.
- `QuantumTheory.Models.MassiveDirac.oppositeBand_upper` — canonical `[simp]` evaluation of band interchange on the upper band, providing the model's public two-band normalization.
- `QuantumTheory.Models.RashbaExchange.spinOrbitEnergy_sq` — canonical identity relating the positive spin-orbit/exchange splitting to its nonnegative defining quadratic polynomial; its simple nonnegativity proof is inlined.
- `QuantumTheory.Models.RashbaExchange.sum_bandProjector_eq_one` — two-band completeness of the gauge-independent projectors, including the totalized zero-splitting boundary where idempotency is not assumed.
- `QuantumTheory.Models.RashbaExchange.trace_bandProjector` — canonical `[simp]` trace-one rule for each Pauli-form band projector, independently useful even when no compiled consumer remains.
- `QuantumTheory.Models.RashbaExchange.bandEnergy_injective` — nondegeneracy of the two Rashba-exchange bands when the spin-orbit energy is nonzero; this physical spectral endpoint is meaningful without an in-repository consumer.
- `QuantumTheory.Models.RashbaExchange.hamiltonian_mul_bandProjector` — the band projector is an eigenspace projector for the model Hamiltonian away from degeneracy; keep this matrix-level spectral relation.
- `QuantumTheory.Models.RashbaExchange.bandProjector_completeOrthogonalIdempotents` — completeness and orthogonal idempotency of the two band projectors under nonzero splitting; retain the model's algebraic spectral decomposition.

- `Combinatorics.even_card_of_fixedPointFreeInvolution` — reusable finite-type cardinality parity theorem for a fixed-point-free involution; the matching-graph proof is an implementation choice, while the public statement avoids forcing pairing-specific callers to construct graph objects.
- `Combinatorics.PairingOn.even_card` — canonical cardinality property of the public perfect-pairing abstraction. Inline expansion at its current consumer would expose the underlying involutive permutation and fixed-point-freeness assumptions instead of stating the result at the pairing boundary.
- `Combinatorics.SumEquiv.rightImage_eq_sdiff_leftImage` — finite-set complement identity for the two images of a sum equivalence. Although it currently serves a slot-shuffle cardinality argument, the result is independent of slot shuffles and is the natural set-level companion of `mem_rightImage_iff_not_mem_leftImage`.
- `Combinatorics.finset_sum_offDiag_modEq_of_pair_add_modEq_of_order` — generic oriented-pair modular-congruence theorem over arbitrary finite sets and injective order keys; its geometric-crossing consumer is a specialization, not a reason to inline the order-selection argument into pairing geometry.
- `Combinatorics.fintype_sum_sum_modEq_diag_of_pair_add_modEq_zero` — finite-type diagonal-reduction theorem for cancellation of complementary off-diagonal contributions. Retain the independently usable sum statement; its private finset-level proof helper is not a competing public API.

- `Combinatorics.FiniteIndex.card_deletedPositions` — canonical `[simp]` cardinality rule for the public deleted-position finset, accounting for distinct removed indices; keep the normal form alongside `deletedPositionsOrderIso` rather than hiding its precondition in the order-isomorphism constructor.
- `List.eraseIdx_ofFn_eq_ofFn_succAbove` — general list/finite-index identity equating erasure from `List.ofFn` with restriction through `Fin.succAbove`. Its induction proof supports the later sum-reindexing theorem without making that theorem's interface list-implementation-specific.
- `Finpartition.partitionProduct_top` — canonical `[simp]` evaluation of block products on the nonempty top partition; the nonempty precondition matters and the rule is a stable boundary for the named `partitionProduct` construction.
- `Finpartition.pow_card_eq_prod_parts` — general cardinality-exponent factorization across finite-partition blocks in a commutative monoid. Keep it independent of the current diagram vertex-product specialization.
- `Combinatorics.SumEquiv.rightSubtypeEquiv_val` — canonical `[simp]` evaluation of the right image-subtype equivalence, symmetric to the already reviewed left-side rule and independent of the present pairing-split consumer.
- `Equiv.Perm.sign_sigmaCongrRight` — general sign formula for permutations on a finite dependent sum; the arbitrary dependent fibers are a genuine extension of the homogeneous product law, not diagram-specific sign routing.
- `Combinatorics.Pairing.exists_normalizedPairEmbedding_eq_of_firstEndpoint` — image characterization of the canonical normalized-pair embedding under partner-preserving order embeddings. Keep the useful existence law at the generic pairing boundary rather than inline its reconstruction into a two-point diagram proof.
- `Combinatorics.FiniteIndex.blockCoordinate_lt` — well-formedness bound for row-major block coordinates, used to construct elements of the canonical flattened finite-index type. Its condition and result are independent of the current imaginary-time consumer.
- `Combinatorics.FiniteIndex.blockEquiv_blockMap` — canonical `[simp]` computation rule for transporting a block-index map through `blockEquiv`, expressing precisely that only the block coordinate changes.
- `Combinatorics.FiniteIndex.blockMap_strictMono` — strict monotonicity of a flat block map induced by a strictly increasing block-index map. Retain the generic order theorem independently of its current slot-order consumer.
- `Combinatorics.FiniteIndex.blockEquiv_symm_lt_symm_iff_snd_lt_of_fst_eq` — canonical same-block order characterization under the flattened block equivalence; exposing the local-index order directly avoids reopening the general lexicographic proof at the sole consumer.
- `Combinatorics.sign_relative_binarySplittings_eq_inversionCounts` — explicit binary-splitting sign formula specialized from the general family-shuffle sign theorem; retain the mathematical two-sector inversion-count interface without publishing its private Bool-indexed construction.
- `List.idxOf_flatMap_block_lt_uniform` — generic uniformity of comparisons with an outside element across one block of a duplicate-free flattened list. The inductive ordering argument is reusable outside the present mixed-event proof.
- `Finpartition.card_parts_eq_stirlingSecond` — canonical enumerative endpoint counting finite set partitions with exactly `k` blocks by the second-kind Stirling number; its lack of additional external consumers does not make the enumeration a proof helper.
- `Finpartition.card_coarsenings_parts_eq_stirlingSecond` — count of `k`-block coarsenings of an existing finite partition, obtained by transporting to a partition of its block set; retain this distinct relative-enumeration theorem.
- `SimpleGraph.componentBlock_eq_iff_reachable` — canonical equivalence between equality of graph component blocks and reachability of their base vertices; it is the set-valued component API's characteristic theorem.
- `Combinatorics.Pairing.vertexGraph_reachable_partner` — basic connectivity property of the graph induced by a perfect pairing: a paired leg's incident vertices are reachable, including the same-vertex case. Retain independently of the two block-corollary proofs.
- `SimpleGraph.reachable_sum_inr_iff` — general reflection and preservation of reachability in the right summand of a graph disjoint union. The no-cross-summand walk proof is substantive generic graph infrastructure, not diagram-specific.

- `Finpartition.card_parts_coarseningsEquivBlockPartitions` — cardinality preservation under the equivalence from coarsenings to partitions of the original block set; it is the reusable enumeration boundary used by the Stirling count of coarsenings.
- `Finpartition.mu_to_top_eq_mu_bot_top_parts` — partition-lattice Möbius value from a partition to the top expressed as the bottom-to-top Möbius value on its blocks. Retain this canonical reduction, independently of the explicit factorial formula that consumes it.
- `Finpartition.sum_partitionProduct_momentFromCumulant_partsCard_eq` — reindexing theorem for products of moments across partitions with exactly `k` outer blocks, with the coarsening multiplicity given by Stirling numbers; it links finite-set cumulants to replica coefficients.
- `Finpartition.replicaPolynomial_eq_sum_descPochhammer_stirling` — canonical falling-factorial expansion of the replica polynomial grouped by block count. Retain the final coefficient identity consumed by the formal power-series replica bridge, without committing to public status for its internal intermediate expansion.
- `Finpartition.partitionProduct_restrict_eq_prod_inf` — general product-restriction identity with explicit empty-block normalization `m ⊥ = 1`; it is a finite-partition algebra law that does not depend on the separate independence predicate.
- `Finpartition.cumulantFromMoment_eq_splitCumulant_of_le` — uniqueness/inversion identification of the cumulant with the region-supported split cumulant on nonempty subsets of independent regions. This structural theorem is stronger than the vanishing corollary.
- `Finpartition.cumulantFromMoment_eq_zero_of_straddles` — general independence endpoint: mixed cumulants vanish for any subset straddling both regions, not only their total union; retain the stronger domain theorem despite its current single special-case consumer.

- `Finpartition.mu_eq_prod_restrict` — canonical Möbius-function factorization over blocks of the coarser partition, formulated over arbitrary commutative coefficient rings; the factorial Möbius formulas reuse this general incidence-algebra theorem.
- `Finpartition.weightedMomentFromCumulant_one` — specialization of the weighted moment transform at unit partition weight; it marks the semantic boundary from arbitrary partition coefficients to the ordinary moment transform used by multiplicative connected decompositions.
- `Finpartition.partitionProduct_distinguishedBlockEquiv_symm` — block-product factorization through the distinguished-block decomposition. The formula is a reusable reindexing identity independent of the formal power-series replica consumer.
- `Finpartition.restrict_bind_eq` — reconstruction law showing that restricting a blockwise refinement to an original block recovers its chosen partition; a core inverse property of the finite-partition bind/restrict interface.
- `Finpartition.restrict_self_part_eq_top` — canonical identity that restricting a partition to one of its own blocks yields the indiscrete partition of that block; retain the general refinement and Möbius boundary rather than duplicate the restriction proof downstream.
- `Finpartition.replicaPolynomial_coeff_one` — canonical replica-method coefficient theorem: on nonempty support, the coefficient linear in the replica count is exactly the one-block weight. It is independently used by formal-series and diagrammatic replica endpoints.
- `Combinatorics.Pairing.crossingCount_eraseZeroPair` — structural recurrence splitting the crossing count into residual-pairing crossings and crossings involving the first pair, independent of any chosen exchange scalar.
- `Combinatorics.Pairing.crossingsWithFirstPair_mod_two` — parity identity equating first-pair crossing count to intervening position count modulo two; the generic sign-recursion and Bloch–de Dominicis uses depend on this combinatorial theorem.
- `Combinatorics.Pairing.normalizedPairOfEndpointEquiv_pair_eq_of_lt` — oriented endpoint transport rule: when transported endpoints remain increasing, normalized-pair construction preserves their order rather than silently reversing an asymmetric contraction kernel.
- `Combinatorics.Pairing.normalizedPair_endpoints_ne_of_ne` — four-way endpoint disjointness for distinct normalized pairs, derived from the global pair-endpoint equivalence; retain this general fact instead of reopening endpoint injectivity in crossing-count proofs.
- `Combinatorics.Pairing.ofSplitNormalizedPairEquiv_pair_eq_or_swap` — exact characterization of endpoints under pairing-split reassembly up to orientation reversal; this is necessary when contractions are not symmetric in their endpoint arguments.
- `Combinatorics.Pairing.ofSplitNormalizedPairEquiv_pair_eq_of_lt` — order-preserving specialization of the pairing-split normalized-endpoint transport theorem, giving the unswapped coordinate formula used by geometric crossing proofs.
- `SimpleGraph.reachable_sum_inl_iff` — reflection and preservation of reachability inside the left summand of a disjoint graph union, dual to the retained right-summand result and independent of diagrammatic connectivity.
- `List.idxOf_flatMap_block_lt_iff` — local-to-global equivalence for the relative order of two elements of one block in a duplicate-free flattened list. Generic list-order infrastructure reused by event-order and leg-embedding proofs.
- `Combinatorics.FiniteIndex.blockEquiv_symm_lt_symm_iff_fst_lt_of_ne` — comparison of flattened coordinates from distinct fixed-width blocks by their block indices; the hypothesis of distinct blocks is essential, and the rule is independent of the physical leg embedding.
- `Finpartition.momentFromCumulant_eq_sum_blockContaining` — canonical distinguished-block recursion for finite-set moments, used by both Möbius-style formulas and the formal-log moment recurrence.
- `Finpartition.sum_Iic_partitionProduct_eq` — factorization of the partition-product sum over a refinement interval into blockwise moments; the generic finite-partition identity underlies cumulant inversion and replica reindexing.
- `Combinatorics.Pairing.card_normalizedPair` — cardinality of the normalized pair family, exactly half of the ambient positions; this is a core structural theorem of perfect pairings, not merely a counting step for current consumers.

- `IncidenceAlgebra.mu_orderIso_apply` — Möbius invariance under order isomorphism for locally finite posets; this is the generic incidence-algebra transport theorem used by partition-lattice reductions.
- `IncidenceAlgebra.map_mu_apply` — naturality of the Möbius function under a ring homomorphism, independent of any specific coefficient ring or combinatorial lattice.
- `IncidenceAlgebra.mu_subtype_le_apply` — restriction of the Möbius function to a principal lower interval, a generic interval-closure property used in partition refinements.
- `IncidenceAlgebra.mu_subtype_ge_apply` — restriction of the Möbius function to a principal upper interval, complementary to the lower-interval result and used by partition coarsenings.
- `IncidenceAlgebra.mu_pi_finset_apply` — finite dependent-product factorization of the Möbius function, providing the reusable product decomposition behind partition-lattice Möbius factorization.
- `Finpartition.mu_bot_top_eq_factorial` — explicit nonempty-partition-lattice Möbius value as a signed factorial; a standalone enumerative identity rather than proof routing.
- `Finpartition.mu_bot_top_eq_factorial_ite` — total signed-factorial Möbius formula including the exceptional empty finite set, avoiding an implicit nonemptiness side condition.
- `Finpartition.mu_to_top_eq_factorial` — explicit signed-factorial formula from an arbitrary finite partition to top, indexed by its block count.
- `Finpartition.mu_eq_prod_factorial` — closed integer-valued Möbius formula for any interval of the finite-partition lattice, as a product over coarser blocks.
- `Finpartition.cumulantFromMoment_empty` — canonical empty-set evaluation of the Möbius-defined cumulant transform; it supplies normalization for the bundled moment–cumulant interface.
- `Finpartition.cumulantFromMoment_momentFromCumulant` — one direction of finite-set moment–cumulant inversion on nonempty sets, independent of normalized-function packaging.
- `Finpartition.sum_Iic_mu_partitionProduct_eq` — incidence-algebra convolution identity over a refinement interval, factoring its Möbius-weighted sum into blockwise cumulants.
- `Finpartition.momentFromCumulant_cumulantFromMoment` — converse finite-set moment–cumulant inversion on nonempty sets; both inverse identities define the generic transform equivalence.
- `Combinatorics.Pairing.componentGeometricCrossingCount_eq_oriented_add` — decomposition of geometric inter-component crossings into the two oriented crossing counts; makes the asymmetry of oriented crossings explicit.
- `Combinatorics.Pairing.componentGeometricCrossingCount_comm` — symmetry of geometric crossing count under exchange of components, unlike its oriented counterpart.
- `Combinatorics.Pairing.componentGeometricCrossingCount_mod_two_eq_endpointInversionCount` — parity bridge between pairwise geometric crossings and endpoint-order inversions for distinct components.
- `Combinatorics.Pairing.componentGeometricCrossingCount_mod_two_eq_zero_of_even_fiber` — general even-fiber cancellation criterion for geometric crossing parity, independent of particular diagram component types.
- `Combinatorics.Pairing.componentCrossingCount_self_eq` — identifies diagonal component crossing count with a local pairing's crossing count under monotone endpoint transport.
- `Combinatorics.Pairing.crossingCount_eq_sum_componentCrossingCount` — exact decomposition of the global crossing count as a double sum over oriented component crossings.
- `Combinatorics.Pairing.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount` — parity identification of inter-component crossings with ordered family-shuffle block inversions, retaining explicit block order.
- `Combinatorics.Pairing.crossingCount_eq_sum_localCrossingCount_add_inter` — additive crossing decomposition into local pairing counts and an inter-component residual, under strict local position monotonicity.
- `Combinatorics.Pairing.crossingCount_mod_two_eq_sum_componentCrossingCount_of_geometric_even` — global crossing parity reduction to diagonal contributions when all off-diagonal geometric crossing counts are even.
- `Combinatorics.Pairing.normalizedPairSigmaEquiv_apply_of_strictMono` — endpoint computation of the dependent-sum normalized-pair equivalence under strictly increasing component position maps, preserving orientation.
- `Combinatorics.Pairing.prod_pairs_eq_prod_components` — generic product factorization over normalized pairing components, assuming kernel compatibility; independent of scalar evaluation weights.
- `Combinatorics.Pairing.evaluation_eq_mul_prod_components` — semantic scalar evaluation factorization into a residual and component evaluations when both weights and pair kernels factor.
- `Combinatorics.familyOrdersOfOrder_strictMono` — strict monotonicity of local orders extracted from a global order on dependent family fibers; a core property of order decomposition.
- `Finpartition.assembleOrder_shuffleOfOrder` — reconstruction equation for a global order from its compatible local block orders and induced shuffle.
- `Finpartition.partOrdersCompatible_partOrdersOfOrder` — compatibility of local orders extracted from a global ordering with the partition's original parts.
- `Finpartition.sum_order_eq_mul_prod_sum_partOrders` — general finite-order sum factorization into a scalar, shuffle contribution, and block-local order sums under weight factorization.
- `Combinatorics.Pairing.ofSplitInterSectorCrossingCount_mod_two_eq_positionInversions` — terminal binary pairing-split parity formula reducing inter-sector crossing parity to position inversions; used by thermal pairing weights.
- `Combinatorics.Pairing.ofSplit_crossingCount_eq_left_add_right_add_inter` — terminal exact crossing-count decomposition for an order-preserving binary pairing split, retaining local counts and the residual.
- `Combinatorics.FamilySlotShuffleTo.relativePerm_sign_eq_orderedBlockInversionCount_add` — sign identity for relative order-preserving family shuffles, expressed through both ordered block-inversion counts with explicit component order.

- `Combinatorics.BinaryShuffle.leftSlot_strictMono` — strict order-preservation of left recursive slots; it supplies the canonical left component of the order-preserving binary-shuffle representation.
- `Combinatorics.BinaryShuffle.rightSlot_strictMono` — strict order-preservation of right recursive slots, dual to the left identity and needed to construct the ambient slot shuffle.
- `Combinatorics.BinaryShuffle.leftSlot_ne_rightSlot` — separation of left and right ambient positions in the recursive shuffle; it is the disjointness invariant behind the tagged-slot injection.
- `Combinatorics.BinaryShuffle.slotEquiv_injective` — injectivity of the recursive shuffle representation as an ambient slot equivalence; distinct recursive insertion histories cannot describe the same ordered interleaving.
- `Combinatorics.BinaryShuffle.sum_slotShuffle` — canonical equivalence-based finite-sum reindexing between recursive binary shuffles and order-preserving ambient slot shuffles, used across ordered-simplex and diagrammatic integrations.
- `Combinatorics.SlotShuffle.mem_rightSlots_iff_not_mem_leftSlots` — complement characterization of right ambient slots, a structural partition invariant rather than a caller-specific simplification.
- `Combinatorics.SlotShuffle.card_sdiff_leftSlots` — cardinality of the complement of the left slot set, supplying the right-side cardinality witness for `Finset.orderIsoOfFin`.
- `Combinatorics.SlotShuffle.sdiffLeftSlots_orderEmbOfFin` — the increasing enumeration of the complement of left slots agrees pointwise with the right shuffle slot map; this is the canonical order interface used in shuffle geometry.
- `Combinatorics.SlotShuffle.eq_of_leftSlots_eq` — uniqueness of an order-preserving slot shuffle from the set of its left positions; a substantial reconstruction principle reused by the family-shuffle decomposition.
- `Combinatorics.FamilySlotShuffle.mem_tailSlots_iff_not_mem_headSlots` — generic head-versus-tail complement identity for multi-component shuffles; avoids imposing arbitrary component order on tail slots.
- `Combinatorics.FamilySlotShuffle.tailSlotSubtypeEquiv_val` — simp-style evaluation law for the tail-slot subtype equivalence, fixing its concrete embedding into ambient positions.
- `Combinatorics.FamilySlotShuffle.tailSlots_set_eq_compl_headSlots` — set-level equality of tail positions with the complement of the head positions, needed as a typed bridge to `Equiv.Set.sumCompl`.
- `Combinatorics.FamilySlotShuffle.outerSlotEquiv_apply_inl` — simp evaluation of the binary head/tail outer equivalence on the head component, connecting the extracted and original shuffle coordinates.
- `Combinatorics.FamilySlotShuffle.outerSlotEquiv_apply_inr` — simp evaluation of the same outer equivalence on the tail component through its increasing finite-set enumeration.
- `Combinatorics.FamilySlotShuffle.card_tailSlots` — tail position cardinality needed to build the canonical ordered tail permutation and reconstruct the family shuffle.
- `Combinatorics.FamilySlotShuffleTo.blockInversionCount_of_ne` — the explicit cross-block inversion sum on distinct component indices; retaining the non-diagonal simplification keeps the invariant usable without unfolding its conditional definition.
- `Combinatorics.FamilySlotShuffleTo.blockInversionCount_add_swap` — pairwise inversion-complement identity: the two block orientations together count every cross-block slot pair exactly once.
- `Combinatorics.FamilySlotShuffleTo.orderedBlockInversionCount_modEq_of_even_sizes` — parity independence of arbitrary component ordering when every component has even size, derived from the orientation-complement identity; used in fermionic component signs.
- `Combinatorics.pow_eq_of_mod_two_eq` — generic monoid law for powers of an involutive exchange scalar depending only on parity, used in multiple bosonic/fermionic and pairing-sign modules.
- `Combinatorics.subsetSumSdiffEquiv_inl_apply` — simp evaluation of the left branch of the finite-set subset/complement equivalence, preserving the explicit proof of subset inclusion in the ambient type.
- `Combinatorics.subsetSumSdiffEquiv_inr_apply` — simp evaluation of the relative-complement branch of the same equivalence, used by leg and connectivity splittings.

- `SimpleGraph.mem_componentBlock` — identifies graph-component block membership with reachability; the canonical bridge from graph connectivity to finite partition membership.
- `SimpleGraph.self_mem_componentBlock` — simp-friendly fact that each vertex belongs to its own connected component, used to connect reflexive reachability with block reasoning.
- `SimpleGraph.componentBlock_mem_componentPartition` — connects a chosen vertex's component block to the parts of the canonical component partition, used when indexing over partition blocks.
- `SimpleGraph.componentBlock_eq_of_reachable` — reachable vertices yield equal connected-component blocks, an order-free uniqueness property useful for graph decompositions.
- `SimpleGraph.componentBlock_eq_iff_mem` — a vertex lies in a component partition part exactly when its component block equals that part; used in interaction-sector and diagrammatic component APIs.
- `SimpleGraph.mem_componentBlockOn` — characterizes ambient finite-set graph-component membership by subtype membership and reachability, enabling component reasoning without changing vertex type.
- `SimpleGraph.componentBlockOn_eq_of_reachable` — transports reachability to equality of ambient component blocks for graphs whose vertices are finite-set subtypes; reused by pairing graphs and quartic components.
- `Finpartition.bind_le` — independently refining every block always yields a refinement of the starting partition; this defines the inverse of the refinement-fiber equivalence.
- `Finpartition.mem_restrict_iff` — explicit formula for membership in a partition restricted to a subset; supports bind/restrict inversion and downstream cumulant independence proofs.
- `Finpartition.eq_of_inf_ne_bot` — uniqueness of a partition block containing the same nonempty subset, the disjointness argument that makes local refinement reconstruction well-defined.
- `Finpartition.partitionProduct_bind` — multiplicativity of block products under partition bind, the algebraic backbone of blockwise moment-cumulant factorization.
- `Combinatorics.Pairing.pairEndpoint_zero` — simp evaluation of the first endpoint of a normalized pair, exposing the endpoint indexing convention of the pairing equivalence.
- `Combinatorics.Pairing.pairEndpoint_one` — simp evaluation of the second endpoint of a normalized pair, paired with the zero-endpoint rule for finite endpoint reindexing.
- `Combinatorics.Pairing.normalizedPairOfEndpointEquiv_pair_eq_or_swap` — the abstract endpoint transport chooses either original orientation or its swap; the general transport theorem must not assume order preservation.
- `Combinatorics.Pairing.normalizedPairSubtypeEndpointEquiv_apply_val` — simp projection formula for the endpoint equivalence restricted to partner-invariant position subsets; used by mixed diagram components.

- `Combinatorics.MultiplicativeWeight.normalizedObjectMoment_cumulant_eq_connectedContribution` — generic connected-object Möbius-inversion identity under commutative-ring coefficients. The power-series cumulant bridge specializes this endpoint; inlining it into that analytic consumer would lose the statistics-independent combinatorial statement.
- `Combinatorics.Pairing.eraseZeroOrderIso_partner` — intertwining of the surviving positions' partner involution with the original one under the increasing deletion order-isomorphism; reused by insertion and erasure proofs.
- `Combinatorics.Pairing.pairs_erase_firstPair_eq_image` — exact characterization of the remaining normalized pairs as the embedded pairs of the smaller pairing after deleting the distinguished pair; used in products and crossing decomposition.
- `Combinatorics.Pairing.insertFirstPair_partner_zero` — computational rule for the partner of zero after inserting a distinguished first pair, used in the inverse recursive decomposition and pairing recursion.

## Other retained API contracts (outside theorem audit)

These structural interfaces are worth retaining, but they are not independent proof declarations
for theorem-audit suppression. Lean compiles proof-valued structure-field projections as
`kind = theorem`; `TheoremCatalog.lean` deliberately excludes those projections from its theorem
audit. The definition listed here also lies outside that audit.

- **`QuantumTheory.Transport.FiniteDisorderEnsemble.probability_sum`** — structure-field normalization of the finite disorder ensemble: all configuration probability weights sum to one.
- **`LocallyFiniteHopping.self_mem`** — structure-field locality invariant: each site belongs to its own finite incident neighborhood.
- **`Combinatorics.SlotShuffle.sdiffLeftSlotsOrderEquiv`** — public finite-set order equivalence used by two independent diagram-standardization modules.
- **`Finpartition.blockContainingEquivPowerset`** — canonical equivalence between subsets of a finite set containing a distinguished element and subsets of its complement. Its current counting consumer uses the equivalence internally, but the bijection is a standalone combinatorial fact, not a proof-stage forwarding wrapper.
- **`Combinatorics.Pairing.eraseZeroPairEmbedding`** — canonical embedding of the smaller pairing's ordered pair positions into the ambient pairing; unlike a caller-specific cast it preserves the pair index abstraction.
- **`Combinatorics.Pairing.eraseZeroOrderIso`** — canonical strictly increasing equivalence between surviving positions and the smaller finite index type after removing zero and its partner.
- **`Combinatorics.Pairing.eraseZeroPair`** — canonical pairing obtained from restricting a fixed-point-free involution away from position zero and its partner, the recursive datum of the first-pair decomposition.
- **`Combinatorics.Pairing.insertFirstPair`** — canonical inverse construction to deleting the distinguished first pair, reconstituting a larger pairing from a smaller pairing and a chosen nonzero partner.
- **`Combinatorics.Pairing.equivSigma`** — bijective recursion identifying a pairing on 2(n+1) positions with the partner of zero and a pairing on 2n positions; underlies pairing-sum decompositions.
- **`Combinatorics.Pairing.interveningPositionCount`** — geometric count of ambient positions strictly between zero and its partner, the invariant appearing in the crossing-parity recursion.
- **`Finpartition.coarseningsEquivBlockPartitions`** — structural equivalence identifying coarsenings of a finite partition with partitions of its block set; used to reduce coarsening counts to Stirling numbers.
- **`Finpartition.coarseningsOrderIsoBlockPartitions`** — order-isomorphism strengthening the coarsening/block-partition equivalence, enabling transport of incidence-algebra Möbius functions across the upper interval.
- **`Finpartition.refinementsEquivFiberPartitions`** — structural equivalence between refinements and independent partitions of each original block, supplying the block-factorized combinatorics of moments and cumulants.
- **`Finpartition.refinementsOrderIsoFiberPartitions`** — order-preserving refinement equivalence, needed to transport interval structures and multiplicative Möbius coefficients to the product of block lattices.
