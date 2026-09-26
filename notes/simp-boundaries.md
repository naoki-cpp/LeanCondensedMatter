# Reviewed simp boundaries

This note records the current semantic review of the project's global `simp` API.

The governing rule is in `conventions.md`: `@[simp]` declares a canonical normal form, not merely a
useful theorem. This file is intentionally asymmetric:

- **Green** entries below are reviewed and intentionally retained in the global simp set.
- Any current `@[simp]` declaration not listed below is **Yellow by default**: it remains available
  while its normal-form role is reviewed, but is not yet endorsed as a permanent global simp rule.
- The **explicit-only** entries at the end are reviewed declarations that must not be global simp
  rules. They remain ordinary theorems for `rw`, `simp only [...]`, or targeted `simp [...]`.

The registry describes the current API rather than a migration history. Update it whenever a
reviewed simp boundary is added, removed, or reclassified. After the Yellow audit completed on
2026-09-26, every then-current global simp declaration was either covered by a Green entry below or
moved to the explicit-only set; future unlisted declarations are Yellow by default.

## Green: Analysis

The following declarations are deliberate computation, projection, coercion, zero/identity, or
homomorphic normalization rules:

- `Dyson.coeff_zero`
- `Dyson.coeff_at_zero`
- `Dyson.term_zero`
- `Dyson.term_at_zero`
- `Dyson.evolution_zero`
- `Dyson.evolution_zero_coupling`
- `Dyson.majorant_zero`
- `ScalarExchange.peelSum_nil`
- `InternalSpace.pauliCombination_add`
- `InternalSpace.pauliCombination_smul`
- `InternalSpace.trace_pauliBasis`
- `InternalSpace.trace_pauliCombination`
- `InternalSpace.pauliScalarCoefficient_pauliZ_conjugate`
- `InternalSpace.pauliVectorCoefficient_pauliZ_conjugate`
- `InternalSpace.pauliScalarCoefficient_neg`
- `InternalSpace.pauliVectorCoefficient_neg`
- `linearCommutator_apply`
- `commutatorEvolution_apply`
- `linearCommutator_smul_id_right`
- `PowerSeries.coeff_normalizeByConstantCoeff`
- `ConservationLaw.shiftCurrentSource_current`
- `ConservationLaw.shiftCurrentSource_source`
- `ConservationLaw.toDifferentialCurrentRepresentationOfSourceFactors_current`
- `symmetrizedProduct_apply`
- `symmetrizedProduct_zero_left`
- `symmetrizedProduct_zero_right`
- `symmetrizedProduct_smul_id`
- `coe_diagonalExpectationValue_right`
- `coe_diagonalExpectationNNReal`
- `diagonalExpectationValue_add`
- `SchwartzSpinor1D.spatialLift_apply`
- `SchwartzSpinor1D.internalOperator_apply`
- `SchwartzSpinor1D.multiplicationOperator_apply`
- `SchwartzSpinor1D.multiplicationLinear_apply`
- `nonrealShiftLinearEquiv_apply`
- `nonrealShiftInverseDomain_apply`
- `nonrealResolvent_apply`
- `ConservationLaw.nestedSymmetrizedCurrentFlux_apply`
- `ConservationLaw.conventionalSymmetrizedCurrentFlux_apply`
- `ConservationLaw.localizationCorrectionCurrentFlux_apply`
- `ConservationLaw.localizationCorrectionCurrentFlux_smul_id`
- `diagonalDet_zero`
- `SchwartzKinetic1D.derivative_apply`
- `SchwartzKinetic1D.multiplicationOperator_apply`
- `ConservationLaw.symmetrizedProductRightLinear_apply`
- `ConservationLaw.localizedQuantityFunctional_apply`
- `ConservationLaw.localizedQuantity_smul_id`
- `ConservationLaw.localizationCommutatorFunctional_apply`
- `ConservationLaw.transportFunctional_apply`
- `ConservationLaw.sourceFunctional_apply`
- `ConservationLaw.sourceCommutator_eq_zero_of_commutes`
- `ConservationLaw.transportCommutator_smul_id`
- `zetaCommutator_apply`
- `orderedSimplexIntegral_zero`
- `orderedSimplexIntegral_zero_fun`
- `finiteDimensionalOperatorTrace_apply`
- `L2MultiplicationRealLine.multiplicationOperator_apply`
- `L2MultiplicationRealLine.multiplicationLinear_apply`
- `PowerSeries.logOf_one`
- `FamilySlotShuffleTo.timeAssignment_apply`
- `SpectralTraceClass.trace_eq_spectralTrace`
- `boundedUnitaryEvolution_zero`
- `resolventApproximationEvolution_zero`
- `stoneEvolution_apply`
- `resolventApproximationEvolutionAtScale_zero`
- `stoneEvolution_zero`
- `shiftDomainMap_apply`
- `Fredholm.diagonalDet_fintype`
- `LinearPMap.resolventRegularizer_apply`
- `LinearPMap.boundedSelfAdjointApproximation_apply`
- `LinearPMap.cayleyTransform_apply`

## Green: Combinatorics

All current `@[simp]` declarations under `LeanCondensedMatter/Combinatorics/` are Green. They are
constructor equations, equivalence round trips, partner involutions, canonical membership/cardinality
rules, or empty/zero cases. In particular this covers the current simp API in:

- `SubsetSplit`
- `SumEquivPartition`
- `BinaryShuffle`
- `BinaryShuffleSlots`
- `BinaryShuffleSlotEquiv`
- `FamilySlotShuffle`
- `FamilySlotShuffleDecomposition`
- `FamilyOrderShuffle`
- `FinpartitionOrderShuffle`
- `FiniteIndex/DeletedPositions`
- `SimpleGraphComponentPartition`
- `Cumulant/Normalized`
- `Cumulant/Moment`
- `Cumulant/Inversion`
- `Cumulant/ConnectedDecompositionInversion`
- `PerfectPairing/Core`
- `PerfectPairing/Transport`
- `PerfectPairing/Restriction`
- `PerfectPairing/Split`
- `PerfectPairing/Bipartite`
- `PerfectPairing/EraseZero`
- `PerfectPairing/PairEndpoints`
- `PerfectPairing/NormalizedPairRestriction`
- `PerfectPairing/InsertFirstPair`
- `PerfectPairing/Examples/Four`

## Green: Crystal

All current `@[simp]` declarations in `Crystal/Symmetry`, `Crystal/Lattice`, and
`Crystal/Translation` are Green. They expose canonical membership, coercion, action, reciprocal
basis, and involution rules.

## Green: Permutation

- `constantCoeff_formalTraceLogOneSubSeries`
- `constantCoeff_permutationConnectedCycleSeries`
- `coeff_formalTraceLogOneSubSeries`

## Green: QuantumMechanics

All current `@[simp]` declarations in the following modules are Green:

- `SingleParticle/LocalizedTransport`
- `SingleParticle/ConventionalCurrent`
- `SingleParticle/CorrectedCurrent`
- `SingleParticle/SymmetrizedVelocityCurrent`
- `SingleParticle/ChargeLikeCurrent`
- `SingleParticle/Continuum/Hamiltonian/Basic1D`
- `SingleParticle/Continuum/Hamiltonian/MaximalLaplacian1D`
- `SingleParticle/Continuum/Hamiltonian/Closed1D`
- `SingleParticle/Continuum/L2/Multiplication1D`
- `SingleParticle/Continuum/L2/Probability1D`
- `SingleParticle/Continuum/Continuity/CurrentRepresentation1D`
- `SingleParticle/Continuum/Continuity/OperatorCurrentBridge1D`
- `SingleParticle/Continuum/Continuity/SchwartzCurrent1D`
- `SingleParticle/Continuum/Continuity/Schwartz1D`
- `SingleParticle/Continuum/Continuity/FiniteDimensional`
- `SingleParticle/Continuum/Continuity/SchwartzSpinCurrent1D`

The remaining reviewed declarations are also Green:

- `ContinuumSchrodingerEvolution1D.norm_propagator_apply`
- `electromagneticChargeCurrentValue1D_eq_charge_mul_probabilityCurrent`
- `gaugeCovariantDerivativeValue1D_re`
- `gaugeCovariantDerivativeValue1D_im`

## Green: QuantumTheory

The following declaration families are deliberate API normalization boundaries:

- `DensityOperator.isPureDensity_pure`
- `PureState.val_ofStateVector`
- `PureState.ofStateVector_smul_of_norm_eq_one`
- all current simp rules in `LinearResponse/FreeDynamics`
- `DensityOperator.normalizePositive_op`
- all current simp rules in `LinearResponse/HarmonicSource`
- all current simp rules in `LinearResponse/FrequencyDomain`
- all current simp rules in `POVM/Born`
- `NormalizedExpectation.pullback_apply`
- all current simp rules in `LinearResponse/FiniteLehmannTable`
- all current simp rules in `LinearResponse/PictureEquivalence`
- all current simp rules in `DensityOperator/ObservableExpectation`
- all current simp rules in `LinearResponse/RetardedSusceptibility`
- `coe_observableExpValue`
- `gibbsState_op`
- `ConservationLaw.heisenbergEvolution_apply`
- all current simp rules in `LinearResponse/KuboFormula`
- `DensityOperator.spectralTrace_op_eq_one`
- `ResponseChannel.fixed_contactExpectation`
- `DensityOperator.expectation_op`
- `purePointDensityOperator_apply_basis`
- `DensityOperator.ofFiniteDimensional_op`
- `DensityOperator.expectation_id`
- `perturbedDensityOperator_zero_coupling`
- `constantCoeff_freeExchangeGrandPartitionSeries`
- `timeDependentInteractionPerturbation_sourceCoupledPerturbation`
- `timeDependentInteractionPropagator_zero_coupling`
- `timeDependentInteractionPropagator_zero_time`
- `purePointGibbsCompetitor_probability`
- `finiteTimeAdiabaticTransform_zero_time`
- `purePointGibbsDensityOperator_apply_basis`
- `finitePurePointGibbsDensityOperator_apply_basis`
- all current simp rules in `LinearResponse/AdiabaticSwitching` except
  `not_adiabaticIntegrable_zero_rate`
- `orderedLehmannEnergyGap`
- `orderedLehmannTransitionWeight`
- `orderedLehmannTransitionData_energyGap`
- `orderedLehmannTransitionData_weight`
- `lehmannModeExponent_re`
- `lehmannDenominator_re`
- `norm_timeTerm`
- `purePointTransitionData_energyGap`
- `purePointTransitionWeight_diag`
- `norm_freePropagator_apply`
- `phaseState_val`
- `evolveState_val`
- `evolveState_zero`
- `evolveState_neg_after`
- `evolveState_after_neg`
- `evolveState_phaseState`
- `DensityOperator.toNormalizedExpectation_apply`
- `norm_purePointSchrodingerPhase`
- `norm_purePointTransitionPhase`
- `timeDependentPerturbedNormalizedExpectation_apply`
- `norm_heisenbergEvolution`

## Green: SecondQuantization

All current `@[simp]` declarations under `LeanCondensedMatter/SecondQuantization/` are Green.
The reviewed set consists of basis-state and occupation evaluation rules, vacuum/zero cases,
creation/annihilation actions, CAR-related involutions, equivalence and reindexing round trips,
imaginary-time event/leg constructors, diagram component projections, finite compatibility bridges,
Dyson order-zero rules, and thermal normalization rules.

This broad approval is intentional: the reviewed rules normalize domain-specific constructors to
their canonical basis, slot, component, or zero/identity forms. It does not authorize future
representation-expansion theorems merely because they live under `SecondQuantization`; new simp
rules must still satisfy the general policy.

## Green: Transport

The following current simp boundaries are Green:

- all current simp rules in `Resolvent/Basic`
- `ConductivityTensor.hallComponent_self`
- `StaticStredaResponseMatrix.fermiSea_self`
- `energySq_neg_momentum`
- `oppositeBand_lower`
- `oppositeBand_upper`
- `oppositeBand_oppositeBand`
- `bandSign_oppositeBand`
- `bandSign_lower`
- `bandSign_upper`
- `bandEnergy_lower`
- `bandEnergy_upper`
- `retardedAdvancedLadderCLM_apply`
- `resummedLadderVertex_smul`
- all current simp rules in `Analysis/ZeroTemperatureOccupation`
- all current simp rules in `Analysis/ZeroTemperatureBandFilling`
- all current simp rules in `Models/MassiveDirac/Propagator/Symmetry`
- all current simp rules in `Models/MassiveDirac/Vertex/InPlaneLadder`
- `energySq_polar`
- `energy_polar_eq_radial`
- `finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_zero_disorder`
- `finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_im`
- `finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral_psi_im`
- `finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral_psi_im`
- `finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral_zero_disorder`
- all current simp parity rules in `Analysis/PolarFourier`
- `pauliGreenDenominatorOfRegulator_polar`
- `pauliGreenScalarCoefficientOfRegulator_polar`
- `trace_bandProjector`
- `bandSign_sq`
- `inPlanePauliVertexCLM_apply`
- `interbandEnergyGap_oppositeBand`
- `gaussianCrossedTraceKernel_psi_im`
- `finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_zero_disorder`
- `finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge_zero_disorder`
- `finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_zero_disorder`
- `finiteCutoffContinuumBornDysonLadderRegular_zero_disorder`
- `finiteCutoffContinuumBornDysonLadderSolvedVector_zero_disorder`
- `pointwiseEigenbasisData_energy`
- `pointwiseEigenbasisData_hamiltonianDerivative`
- `finiteCutoffContinuumBornSelfEnergyCoefficient_zero_disorder`
- `continuumBornRetardedAdvancedPauliXRadialIntegrand_y_massless`
- `finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient_y_massless`
- `finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor_zero_disorder`
- `finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_neg_radius`
- `finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel_psi_im`
- `finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_xy`
- `finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_im`
- `finiteCutoffContinuumBornDysonDenominator_zero_disorder`
- `finiteCutoffContinuumBornDysonGreenOperator_zero_disorder`
- `finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_neg_radius`
- `hamiltonian_eq_pauliCombination`
- `AheScalingParameters.finiteBroadeningPair_sxx`
- `AheScalingParameters.zeroBroadeningPairAtDisorder_sxx`
- `AheScalingParameters.zeroBroadeningPair_sxx`
- `zeroTemperatureLorentzianPoleWeight_of_occupied`
- `zeroTemperatureLorentzianPoleWeight_of_unoccupied`
- `zeroTemperatureLorentzianPoleWeight_at_fermi_surface`
- `currentOperator_eq_charge_smul_velocityOperator`
- `pauliGreenDenominator_radial_re`
- `pauliGreenDenominator_radial_im`

## Explicit-only reviewed boundaries

These declarations are intentionally ordinary theorems rather than global simp rules. Their use is
a substantive proof step, a coordinate/representation expansion, or a nontrivial analytic fact.

- `InternalSpace.dotProduct_pauliAxis` — explicit x/y/z coordinate expansion.
- `purePointBoltzmannWeight_pos` — positivity fact, not normalization.
- `purePointBoltzmannWeight_nonneg` — positivity fact, not normalization.
- `purePointGibbsProbability_nonneg` — positivity fact, not normalization.
- `LinearResponse.not_adiabaticIntegrable_zero_rate` — analytic side-condition theorem.
- `ResponseChannel.finiteTimeAdiabaticResponse_fixed` — expands a named response to an interval integral.
- `finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_re` — explicit logarithmic boundary formula.
- `finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_im` — explicit boundary-value formula.
- `PowerSeries.coeff_one_logOf` — derived order-one logarithm identity on the generic Mathlib power-series API.
- `AheScalingParameters.finiteBroadeningPair_sxy` — uses rotational closure to identify the Hall projection with ordered `xy`.
- `AheScalingParameters.zeroBroadeningPairAtDisorder_sxy` — uses the proved Hall-projection identity at the zero-broadening boundary.
- `AheScalingParameters.zeroBroadeningPair_sxy` — stored-disorder specialization of that Hall-coordinate identification.
