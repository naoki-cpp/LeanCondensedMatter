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
- `Combinatorics.SlotShuffle.leftSlots_orderEmbOfFin` — canonical identification of the increasing enumeration of ambient left slots with the slot-shuffle embedding; it is used source-level by the two-point fiber shuffle integral even though the proof dependency is erased from compiled consumers.
- `Combinatorics.SlotShuffle.card_eq_choose` — canonical binomial-cardinality theorem for ambient order-preserving slot shuffles; it follows from the direct left-slot-set correspondence and supplies the recursive binary-shuffle equivalence.
- `Combinatorics.BinaryShuffle.card_succ_succ` — natural Pascal recurrence for the recursively defined binary-shuffle type and the induction step underlying the closed binomial cardinality formula.
- `Combinatorics.BinaryShuffle.card_zero_left` — canonical `[simp]` boundary stating uniqueness of a binary shuffle with no left slots.
- `Combinatorics.BinaryShuffle.card_zero_right` — canonical `[simp]` boundary stating uniqueness of a binary shuffle with no right slots.
- `LinearPMap.boundedSelfAdjointApproximation_commute` — reusable resolvent-approximation commutation theorem for arbitrary positive scales; its present private error-estimate consumer does not make the operator-theoretic statement implementation-only.
- `LinearPMap.boundedUnitaryEvolution_add_generator_of_commute` — reusable factorization law for bounded evolutions generated by commuting operators; retain the general operator theorem rather than inline it into one private estimate.
- `QuantumTheory.LinearResponse.HasAdiabaticRemovalLimit.finsetSum` — generic finite-sum closure property for adiabatic-removal limits, independent of the Lehmann consumer that currently uses it.
- `QuantumTheory.LinearResponse.HasStaticLimit.finsetSum` — generic finite-sum closure property for static limits, independent of the Lehmann consumer that currently uses it.
- `QuantumTheory.LinearResponse.finite_purePointLehmann_has_both_local_iterated_limits` — canonical finite pure-point Lehmann limit-order theorem giving both local iterated limits under the static nonresonance condition.
- `QuantumTheory.LinearResponse.hasStaticLimit_lehmannTerm` — reusable scalar Lehmann-term continuity result at fixed nonzero switching rate.
- `QuantumTheory.LinearResponse.hasStaticLimit_unswitchedLehmannTerm` — reusable zero-rate scalar Lehmann-term static-limit result under the explicit nonresonance/zero-weight condition.
- `QuantumTheory.Transport.Models.MassiveDirac.continuumAngularGreenIntegralOfRegulator_eq` — model-level angular-reduction identity removing the in-plane Pauli channels and producing the physical `2π` factor.
- `QuantumTheory.Models.RashbaExchange.hamiltonianOperator_mul_bandProjectorOperator` — canonical band-projector eigenoperator identity for the Rashba-exchange Hamiltonian.
- `QuantumTheory.Models.RashbaExchange.spinHamiltonian_mul_self` — canonical spectral identity that the traceless Rashba-exchange spin Hamiltonian squares to `E² I`.
- `QuantumTheory.Models.RashbaExchange.sum_bandProjectorOperator_eq_one` — canonical resolution-of-identity theorem for the Rashba-exchange band projectors.
- `QuantumTheory.Transport.adiabaticFrequencyDomainSusceptibility_eq_bastinSpectralVertexSum` — physical finite-system endpoint identifying the causal susceptibility with the Kubo–Bastin spectral vertex sum at positive switching rate.
- `SecondQuantization.Common.sameTwoPointOrderChamber_iff_orderSignature_eq` — canonical equivalence between the geometric mixed-order chamber relation and the finite signature used for measurable chamber decomposition.
- `SecondQuantization.Fermionic.ExternalInsertionWickDiagram.orderedExternalInsertionLegField_componentOrderedLeg` — canonical compatibility of component-local and ambient timed fields under the component leg embedding.
- `QuantumMechanics.SingleParticle.Continuum.realL2MultiplicationOperator1D_symmetric` — deliberate continuum-quantum-mechanics specialization of the measure-space-independent `L2Multiplication.realMultiplicationOperator_symmetric`; the named one-dimensional Lebesgue-space statement is the stable API used by Hamiltonian symmetry and self-adjointness proofs.
- `QuantumTheory.Transport.im_inner_resolvent_spectralParameterOfRegulator_apply_self` — canonical
  dimension-independent signed-regulator Herglotz identity for a self-adjoint resolvent. Consumers
  that need the reversed inner-product orientation should reverse it locally rather than expose a
  second public theorem.
- `QuantumTheory.Transport.Models.MassiveDirac.finiteCutoffContinuumBornSelfEnergyOfRegulator_dissipative`
  — model-level dissipativity statement for the finite-cutoff Born self-energy. It is a physical
  property of the model, not merely an intermediate step in the downstream injectivity proof.
- `ConservationLaw.DependsOnlyOnDifferential.iff_ker_le_ker` — canonical linear-algebra
  characterization of intrinsic differential dependence as `ker d ≤ ker Φ` over modules with
  subtraction; it records the representation-independent content of the current condition without
  choosing a current extension.
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
- `SecondQuantization.Bosonic.exchangeCommutator_annihilate_create_self` — canonical bosonic CCR
  statement at the bosonic algebra layer. Its generic exchange-algebra proof does not make the
  named bosonic commutator identity redundant as a physical API result.
- `SecondQuantization.Bosonic.numberOperator_basisState` — canonical number-operator eigenvalue
  equation `N_i |n⟩ = n_i |n⟩`; this is a physical statement about the named number operator rather
  than proof-routing around `create_annihilate_basisState_same`.
- `SecondQuantization.Fermionic.Transport.TracedStredaAnalyticData.staticKuboBastinConductivity_eq_surface_add_sea`
  — named physical endpoint identifying the finite static Kubo–Bastin conductivity with the Středa
  surface-plus-sea split under the explicit analytic and Ward assumptions.
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
- `QuantumTheory.DensityOperator.hasSum_abs_eigenvalues_eq_one` — spectral normalization law for a
  density operator: the absolute eigenvalue weights sum to one as an independent statement about
  the density state's spectral probability weights.
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
- `SecondQuantization.Fermionic.continuous_matrixCoeff_quarticVertexSequenceInteractionPicture` — joint continuity of
  the public nested vertex-operator product, providing the analytic interface used to lift matrix
  coefficients to Gibbs-expectation continuity.
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
- `QuantumTheory.Transport.Models.MassiveDirac.finiteCutoffContinuumBornDysonGreenLoopMatrix_apply_eq_radial_integral`
  — model-level T-matrix provenance theorem exposing the finite-cutoff radial Green-loop integral
  and its single physical momentum-measure prefactor.
- `QuantumTheory.Transport.Models.MassiveDirac.radialBastinMassWindowMargin_le_abs_gap_add_offset`
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
- `SecondQuantization.Common.TwoPointDiagram.mixedComponentCrossingCount_externalComponentPart` —
  The crossing count internal to the ambient external component equals the crossing count of the
  standalone external-piece pairing.
- `SecondQuantization.Common.TwoPointDiagram.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber` —
  Inside one order chamber, canonical transport of a normalized component pair preserves the two
  underlying standard atomic legs in their normalized order.
- `SecondQuantization.Common.TwoPointDiagram.mixedComponentWeight_eq_of_sameOrderChamber` —
  Component exchange-statistics weight is constant on one chamber.
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
- `SecondQuantization.Fermionic.Lattice.LocallyFiniteHopping.self_mem` — defining locality
  invariant of `LocallyFiniteHopping`: every site lies in its finite incident neighborhood. The
  generated projection is part of the model contract even when it has no compiled theorem consumer.
- `SecondQuantization.Fermionic.Lattice.LocallyFiniteHopping.operator_latticeKet` — canonical
  `[simp]` evaluation of the hopping operator on a localized site ket.
- `SecondQuantization.Fermionic.Lattice.LocallyFiniteHopping.amplitude_eq` — canonical `[simp]`
  normalization of the named hopping matrix element to the corresponding column coefficient.
  Source-level validation proofs use this rule even when simplification erases the compiled
  dependency edge.
- `SecondQuantization.Fermionic.Lattice.LocallyFiniteHopping.amplitude_eq_zero_of_not_mem` —
  canonical incoming-locality consequence: hopping amplitudes vanish outside the finite incident
  neighborhood.
- `SecondQuantization.Fermionic.Lattice.LocallyFiniteHopping.amplitude_swap_eq_zero_of_not_mem` —
  canonical outgoing-locality companion to `amplitude_eq_zero_of_not_mem`.
- `SecondQuantization.Fermionic.Lattice.LocallyFiniteHopping.bondOperator_swap` — canonical
  orientation-reversal law for the one-particle bond-current operator.
- `SecondQuantization.Fermionic.Lattice.LocallyFiniteHopping.lie_siteProjector` —
  one-particle local continuity identity expressing the hopping/projector commutator as the finite
  outgoing bond-operator sum.
- `SecondQuantization.Fermionic.Lattice.bondCurrent_swap` — physical orientation-reversal law for
  the many-particle bond current; the bounded finite-lattice current transports this algebraic fact.
- `SecondQuantization.Fermionic.Lattice.discrete_continuity` — canonical algebraic local continuity
  equation on an arbitrary locally finite lattice and the source theorem for the bounded
  finite-lattice continuity equation.
- `SecondQuantization.Fermionic.freePartitionFunction_eq_coe_purePointPartitionFunction` — The
  finite complex free-fermion partition function is exactly the canonical pure-point Gibbs partition
  function for `fermionEnergy`, coerced from `ℝ` to `ℂ`.
- `SecondQuantization.Fermionic.sum_freeGibbsConfigurationProbability_filter_mem` — canonical
  finite-mode marginal-probability identity: the total Gibbs probability of configurations
  containing mode `i` is exactly its Fermi–Dirac occupation.
- `SecondQuantization.Fermionic.purePointGibbsEnergyExpectation_fermionEnergy_eq_sum_fermiDirac` — canonical
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
- `SecondQuantization.Common.TwoPointDiagram.prod_vertexLabel_eq_prod_componentInteractionParts` — Two-point diagram specialization of the general interaction-sector product factorization; it exposes vertex-local weights in the component decomposition used by Dyson signs and fermionic amplitudes.
- `SecondQuantization.Fermionic.ExternalInsertionWickDiagram.componentMixedPositionShuffle_slotEquiv_apply` — Canonical `[simp]` evaluation of the component mixed-position shuffle. Its forwarding proof connects the concrete family shuffle to the component-position API and fixes the normal form used by crossing parity.
- `SecondQuantization.Bosonic.removeOccupation_createOccupation_of_ne` — General commutation of occupation creation and removal in distinct bosonic modes, a reusable occupation-algebra fact rather than a private CCR proof step.
- `ContinuousLinearMap.IsTraceClass.norm_trace_le_traceNorm` — Fundamental trace-ideal inequality `‖Tr T‖ ≤ ‖T‖₁`, valid for general trace-class bounded operators; retain as an independently useful analytic bound.
- `ContinuousLinearMap.IsTraceClass.traceNorm_comp_right_le` — The trace norm is bounded under composition with an arbitrary bounded right factor; this is the trace-ideal inequality rather than a consumer-specific estimate.
- `LinearPMap.boundedUnitaryEvolution_eq_exp` — Canonical explicit Schrödinger-exponential formula for the bounded evolution API; the definitional proof provides a stable operator-facing statement.
- `LinearPMap.compOnDomain_apply` — Canonical evaluation rule for partial-map composition on its natural domain. The equation expresses the public composition API even when its proof is definitional.
- `SecondQuantization.Bosonic.completedAnnihilate_comp_algebraicCore` — Compatibility of completed bosonic annihilation with the finite-support algebraic core, an independent domain-and-operator bridge.
- `SecondQuantization.Bosonic.completedCreate_comp_algebraicCore` — Compatibility of completed bosonic creation with the finite-support algebraic core; keep separate from annihilation because its weighted domain differs.
- `SecondQuantization.Common.ExternalInsertionDiagram.hasNoVacuumComponent_externalSupportDiagram` — External-support restriction removes purely vacuum components without requiring different external insertions to be connected; it is the structural guarantee of the slot-split API.
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
- `SecondQuantization.Fermionic.ExternalInsertionWickDiagram.relativeComponentShuffle_sign_eq_mixedAtomic_mul_prod_components` — Permutation-sign factorization relating the relative shuffle, global mixed-time order, and component-local orders; retain as the independent sign bridge.
- `ConservationLaw.symmetrizedProductBilinear_apply` — Deliberate explicit bridge from the canonical bilinear symmetrized-product owner to its evaluated two-operator form. Keep it out of global `[simp]` to avoid competing normal forms.
- `PowerSeries.coeff_one_logOf` — The first coefficient of the formal logarithm of a normalized complex power series equals its first original coefficient; retain as a general power-series identity.
