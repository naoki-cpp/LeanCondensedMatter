import LeanCondensedMatter.Transport.Resolvent.EnergyDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option linter.style.header false

/-!
# Regularized Středa operator kernels

This module records the dimension-independent operator algebra needed before taking an ordinary
finite-dimensional trace. At fixed positive broadening it defines:

* the retarded-minus-advanced Green operator;
* the standard Smrčka–Středa surface factor;
* a scaled surface primitive compatible with the sign convention used by the integration-by-parts
  layer;
* its exact real-energy derivative;
* the canonical static Kubo–Bastin operator integrand; and
* the residual sea kernel required to make the finite-broadening pointwise identity exact.

The residual sea kernel is defined before any identification with the conventional Smrčka–Středa
`II` formula. Such an identification can require additional trace cyclicity and limiting
hypotheses, and is deliberately kept as a later theorem rather than built into the definition.
No trace, occupation integral, zero-broadening, DC-limit, disorder, or thermodynamic statement is
made here.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Difference between retarded and advanced resolvents at the same real energy and broadening. -/
noncomputable def retardedAdvancedResolventDifference
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  retardedResolvent hamiltonian energy broadening -
    advancedResolvent hamiltonian energy broadening

/-- Real-energy derivative of the retarded-minus-advanced resolvent difference. -/
noncomputable def retardedAdvancedResolventDifferenceDerivative
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  -(retardedResolvent hamiltonian energy broadening) ^ 2 -
    (-(advancedResolvent hamiltonian energy broadening) ^ 2)

/-- The operator factor multiplying the occupation derivative in the traditional
Smrčka–Středa `I` contribution, before its overall scalar normalization. -/
noncomputable def smrckaStredaSurfaceFactor
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  (current₁ * retardedResolvent hamiltonian energy broadening * current₂ -
      current₂ * advancedResolvent hamiltonian energy broadening * current₁) *
    retardedAdvancedResolventDifference hamiltonian energy broadening

/-- Exact real-energy derivative of `smrckaStredaSurfaceFactor`. -/
noncomputable def smrckaStredaSurfaceFactorDerivative
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  (current₁ * (-(retardedResolvent hamiltonian energy broadening) ^ 2) * current₂ -
      current₂ * (-(advancedResolvent hamiltonian energy broadening) ^ 2) * current₁) *
      retardedAdvancedResolventDifference hamiltonian energy broadening +
    (current₁ * retardedResolvent hamiltonian energy broadening * current₂ -
      current₂ * advancedResolvent hamiltonian energy broadening * current₁) *
      retardedAdvancedResolventDifferenceDerivative hamiltonian energy broadening

/-- Surface primitive with the `-1/2` scaling required by the repository's convention
`surface = -∫ f' P`. -/
noncomputable def regularizedStredaSurfacePrimitiveOperator
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  (-(1 / 2 : ℂ)) •
    smrckaStredaSurfaceFactor hamiltonian current₁ current₂ energy broadening

/-- Exact derivative assigned to `regularizedStredaSurfacePrimitiveOperator`. -/
noncomputable def regularizedStredaSurfacePrimitiveOperatorDerivative
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  (-(1 / 2 : ℂ)) •
    smrckaStredaSurfaceFactorDerivative
      hamiltonian current₁ current₂ energy broadening

/-- The retarded-minus-advanced resolvent difference has the expected real-energy derivative. -/
private theorem hasDerivAt_retardedAdvancedResolventDifference
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt
      (fun x : ℝ => retardedAdvancedResolventDifference hamiltonian x broadening)
      (retardedAdvancedResolventDifferenceDerivative hamiltonian energy broadening)
      energy := by
  change HasDerivAt
    ((fun x : ℝ => retardedResolvent hamiltonian x broadening) -
      fun x : ℝ => advancedResolvent hamiltonian x broadening)
    (-(retardedResolvent hamiltonian energy broadening) ^ 2 -
      (-(advancedResolvent hamiltonian energy broadening) ^ 2))
    energy
  have hretarded :
      HasDerivAt (fun x : ℝ => retardedResolvent hamiltonian x broadening)
        (-(retardedResolvent hamiltonian energy broadening) ^ 2) energy := by
    simpa [retardedResolvent, retardedSpectralParameter] using
      hasDerivAt_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself energy broadening (ne_of_gt hbroadening)
  have hadvanced :
      HasDerivAt (fun x : ℝ => advancedResolvent hamiltonian x broadening)
        (-(advancedResolvent hamiltonian energy broadening) ^ 2) energy := by
    simpa [advancedResolvent, advancedSpectralParameter] using
      hasDerivAt_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself energy (-broadening) (neg_ne_zero.mpr (ne_of_gt hbroadening))
  exact hretarded.sub hadvanced

/-- Product differentiation of the standard Smrčka–Středa surface factor. -/
private theorem hasDerivAt_smrckaStredaSurfaceFactor
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt
      (fun x : ℝ =>
        smrckaStredaSurfaceFactor hamiltonian current₁ current₂ x broadening)
      (smrckaStredaSurfaceFactorDerivative
        hamiltonian current₁ current₂ energy broadening)
      energy := by
  have hretarded :
      HasDerivAt (fun x : ℝ => retardedResolvent hamiltonian x broadening)
        (-(retardedResolvent hamiltonian energy broadening) ^ 2) energy := by
    simpa [retardedResolvent, retardedSpectralParameter] using
      hasDerivAt_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself energy broadening (ne_of_gt hbroadening)
  have hadvanced :
      HasDerivAt (fun x : ℝ => advancedResolvent hamiltonian x broadening)
        (-(advancedResolvent hamiltonian energy broadening) ^ 2) energy := by
    simpa [advancedResolvent, advancedSpectralParameter] using
      hasDerivAt_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself energy (-broadening) (neg_ne_zero.mpr (ne_of_gt hbroadening))
  have hleftRetarded := (hretarded.const_mul current₁).mul_const current₂
  have hleftAdvanced := (hadvanced.const_mul current₂).mul_const current₁
  have hleft := hleftRetarded.sub hleftAdvanced
  have hdifference := hasDerivAt_retardedAdvancedResolventDifference
    hamiltonian hself energy broadening hbroadening
  change HasDerivAt
    (((fun x : ℝ =>
        current₁ * retardedResolvent hamiltonian x broadening * current₂) -
      fun x : ℝ =>
        current₂ * advancedResolvent hamiltonian x broadening * current₁) *
      fun x : ℝ => retardedAdvancedResolventDifference hamiltonian x broadening)
    ((current₁ * (-(retardedResolvent hamiltonian energy broadening) ^ 2) * current₂ -
        current₂ * (-(advancedResolvent hamiltonian energy broadening) ^ 2) * current₁) *
        retardedAdvancedResolventDifference hamiltonian energy broadening +
      (current₁ * retardedResolvent hamiltonian energy broadening * current₂ -
        current₂ * advancedResolvent hamiltonian energy broadening * current₁) *
        retardedAdvancedResolventDifferenceDerivative hamiltonian energy broadening)
    energy
  exact hleft.mul hdifference

/-- The scaled surface primitive has the explicitly stored derivative. -/
theorem hasDerivAt_regularizedStredaSurfacePrimitiveOperator
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt
      (fun x : ℝ => regularizedStredaSurfacePrimitiveOperator
        hamiltonian current₁ current₂ x broadening)
      (regularizedStredaSurfacePrimitiveOperatorDerivative
        hamiltonian current₁ current₂ energy broadening)
      energy := by
  change HasDerivAt
    ((-(1 / 2 : ℂ)) • fun x : ℝ =>
      smrckaStredaSurfaceFactor hamiltonian current₁ current₂ x broadening)
    ((-(1 / 2 : ℂ)) •
      smrckaStredaSurfaceFactorDerivative
        hamiltonian current₁ current₂ energy broadening)
    energy
  exact
    (hasDerivAt_smrckaStredaSurfaceFactor
      hamiltonian hself current₁ current₂ energy broadening hbroadening).const_smul
      (-(1 / 2 : ℂ))

private theorem continuous_retardedAdvancedResolventDifference_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ =>
      retardedAdvancedResolventDifference hamiltonian energy broadening) := by
  unfold retardedAdvancedResolventDifference
  change Continuous
    ((fun energy : ℝ => retardedResolvent hamiltonian energy broadening) -
      fun energy : ℝ => advancedResolvent hamiltonian energy broadening)
  have hretarded : Continuous (fun energy : ℝ =>
      retardedResolvent hamiltonian energy broadening) := by
    simpa [retardedResolvent, retardedSpectralParameter] using
      continuous_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself broadening (ne_of_gt hbroadening)
  have hadvanced : Continuous (fun energy : ℝ =>
      advancedResolvent hamiltonian energy broadening) := by
    simpa [advancedResolvent, advancedSpectralParameter] using
      continuous_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself (-broadening) (neg_ne_zero.mpr (ne_of_gt hbroadening))
  exact hretarded.sub hadvanced

private theorem continuous_retardedAdvancedResolventDifferenceDerivative_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ =>
      retardedAdvancedResolventDifferenceDerivative hamiltonian energy broadening) := by
  unfold retardedAdvancedResolventDifferenceDerivative
  have hretarded : Continuous (fun energy : ℝ =>
      retardedResolvent hamiltonian energy broadening) := by
    simpa [retardedResolvent, retardedSpectralParameter] using
      continuous_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself broadening (ne_of_gt hbroadening)
  have hadvanced : Continuous (fun energy : ℝ =>
      advancedResolvent hamiltonian energy broadening) := by
    simpa [advancedResolvent, advancedSpectralParameter] using
      continuous_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself (-broadening) (neg_ne_zero.mpr (ne_of_gt hbroadening))
  exact (hretarded.pow 2).neg.sub ((hadvanced.pow 2).neg)

private theorem continuous_smrckaStredaSurfaceFactorDerivative_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ =>
      smrckaStredaSurfaceFactorDerivative
        hamiltonian current₁ current₂ energy broadening) := by
  have hretarded : Continuous (fun energy : ℝ =>
      retardedResolvent hamiltonian energy broadening) := by
    simpa [retardedResolvent, retardedSpectralParameter] using
      continuous_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself broadening (ne_of_gt hbroadening)
  have hadvanced : Continuous (fun energy : ℝ =>
      advancedResolvent hamiltonian energy broadening) := by
    simpa [advancedResolvent, advancedSpectralParameter] using
      continuous_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself (-broadening) (neg_ne_zero.mpr (ne_of_gt hbroadening))
  have hdifference :=
    continuous_retardedAdvancedResolventDifference_energy
      hamiltonian hself broadening hbroadening
  have hdifferenceDerivative :=
    continuous_retardedAdvancedResolventDifferenceDerivative_energy
      hamiltonian hself broadening hbroadening
  have hleftDerivative :
      Continuous (fun energy : ℝ =>
        current₁ * (-(retardedResolvent hamiltonian energy broadening) ^ 2) * current₂ -
          current₂ * (-(advancedResolvent hamiltonian energy broadening) ^ 2) * current₁) := by
    exact
      ((continuous_const.mul (hretarded.pow 2).neg).mul continuous_const).sub
        ((continuous_const.mul (hadvanced.pow 2).neg).mul continuous_const)
  have hleft :
      Continuous (fun energy : ℝ =>
        current₁ * retardedResolvent hamiltonian energy broadening * current₂ -
          current₂ * advancedResolvent hamiltonian energy broadening * current₁) := by
    exact
      ((continuous_const.mul hretarded).mul continuous_const).sub
        ((continuous_const.mul hadvanced).mul continuous_const)
  unfold smrckaStredaSurfaceFactorDerivative
  exact (hleftDerivative.mul hdifference).add (hleft.mul hdifferenceDerivative)

/-- At fixed positive broadening, the exact surface-primitive derivative is continuous in energy. -/
theorem continuous_regularizedStredaSurfacePrimitiveOperatorDerivative_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ =>
      regularizedStredaSurfacePrimitiveOperatorDerivative
        hamiltonian current₁ current₂ energy broadening) := by
  unfold regularizedStredaSurfacePrimitiveOperatorDerivative
  exact
    (continuous_smrckaStredaSurfaceFactorDerivative_energy
      hamiltonian hself current₁ current₂ broadening hbroadening).const_smul
      (-(1 / 2 : ℂ))

/-- Canonical static Kubo–Bastin operator integrand at fixed finite broadening, with the overall
physical prefactor omitted. -/
noncomputable def regularizedBastinOperatorIntegrand
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  -((current₁ * (-(retardedResolvent hamiltonian energy broadening) ^ 2) * current₂ -
      current₂ * (-(advancedResolvent hamiltonian energy broadening) ^ 2) * current₁) *
    retardedAdvancedResolventDifference hamiltonian energy broadening)

/-- Finite-broadening residual after removing the derivative of the chosen surface primitive from
the canonical Bastin operator integrand. -/
noncomputable def regularizedStredaResidualSeaOperatorKernel
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  regularizedBastinOperatorIntegrand
      hamiltonian current₁ current₂ energy broadening -
    regularizedStredaSurfacePrimitiveOperatorDerivative
      hamiltonian current₁ current₂ energy broadening

/-- At fixed positive broadening, the canonical static Bastin operator integrand is continuous in
real energy. -/
theorem continuous_regularizedBastinOperatorIntegrand_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ =>
      regularizedBastinOperatorIntegrand
        hamiltonian current₁ current₂ energy broadening) := by
  have hretarded : Continuous (fun energy : ℝ =>
      retardedResolvent hamiltonian energy broadening) := by
    simpa [retardedResolvent, retardedSpectralParameter] using
      continuous_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself broadening (ne_of_gt hbroadening)
  have hadvanced : Continuous (fun energy : ℝ =>
      advancedResolvent hamiltonian energy broadening) := by
    simpa [advancedResolvent, advancedSpectralParameter] using
      continuous_resolvent_spectralParameterOfRegulator_energy
        hamiltonian hself (-broadening) (neg_ne_zero.mpr (ne_of_gt hbroadening))
  have hdifference :=
    continuous_retardedAdvancedResolventDifference_energy
      hamiltonian hself broadening hbroadening
  have hleftDerivative :
      Continuous (fun energy : ℝ =>
        current₁ * (-(retardedResolvent hamiltonian energy broadening) ^ 2) * current₂ -
          current₂ * (-(advancedResolvent hamiltonian energy broadening) ^ 2) * current₁) := by
    exact
      ((continuous_const.mul (hretarded.pow 2).neg).mul continuous_const).sub
        ((continuous_const.mul (hadvanced.pow 2).neg).mul continuous_const)
  unfold regularizedBastinOperatorIntegrand
  exact (hleftDerivative.mul hdifference).neg

/-- At fixed positive broadening, the residual sea operator kernel is continuous in real energy. -/
theorem continuous_regularizedStredaResidualSeaOperatorKernel_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ =>
      regularizedStredaResidualSeaOperatorKernel
        hamiltonian current₁ current₂ energy broadening) := by
  unfold regularizedStredaResidualSeaOperatorKernel
  exact
    (continuous_regularizedBastinOperatorIntegrand_energy
      hamiltonian hself current₁ current₂ broadening hbroadening).sub
      (continuous_regularizedStredaSurfacePrimitiveOperatorDerivative_energy
        hamiltonian hself current₁ current₂ broadening hbroadening)

/-- Pointwise finite-broadening decomposition into the surface-primitive derivative and the
residual sea kernel. -/
theorem regularizedBastinOperatorIntegrand_eq_surfaceDerivative_add_residualSea
    {KSpace : Type*} [NormedAddCommGroup KSpace] [InnerProductSpace ℂ KSpace]
    (hamiltonian current₁ current₂ : KSpace →L[ℂ] KSpace)
    (energy broadening : ℝ) :
    regularizedBastinOperatorIntegrand
        hamiltonian current₁ current₂ energy broadening =
      regularizedStredaSurfacePrimitiveOperatorDerivative
          hamiltonian current₁ current₂ energy broadening +
        regularizedStredaResidualSeaOperatorKernel
          hamiltonian current₁ current₂ energy broadening := by
  unfold regularizedStredaResidualSeaOperatorKernel
  abel

end

end QuantumTheory.Transport
