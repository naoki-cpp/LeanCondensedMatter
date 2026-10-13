import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.FiniteDisorderConductivity

set_option linter.style.header false

/-!
# Quenched connected current correlations in a finite disorder ensemble

The current correlator is normalized separately in each disorder configuration,
using the canonical pure-point density-state expectation of that configuration.
Only then is the finite disorder ensemble average performed.

The connected correlator refers to two composite current insertions:
`⟨Jₓ Jᵧ⟩ω - ⟨Jₓ⟩ω ⟨Jᵧ⟩ω`. This differs from subtracting the
product of the **disorder-averaged** one-current expectations by the
covariance of those one-current expectations over disorder configurations.

These statements are exact for finite ensembles with supplied normalized
pure-point states. No assumption of Gaussian disorder, fermionic Wick
factorization, a linked-cluster theorem, or an analytic continuation is made.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open scoped BigOperators
open SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site Ω ι : Type*}
variable [LinearOrder Site] [Fintype Site] [Fintype Ω]

/-- Connected product of two supplied bounded current insertions in the
normalized pure-point state of one exact disorder configuration. -/
noncomputable def finiteDisorderConfigurationConnectedCurrentCorrelation
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) →
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (Jx Jy : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (ω : Ω) : ℂ :=
  purePointNormalizedExpectation
      (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) (Jx * Jy) -
    purePointNormalizedExpectation
        (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jx *
      purePointNormalizedExpectation
        (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jy

/-- Quenched averaging is performed *after* normalizing and taking the
connected current correlator in each disorder configuration. -/
noncomputable def finiteDisorderAveragedConnectedCurrentCorrelation
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) →
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (Jx Jy : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :
    ℂ :=
  ensemble.average (fun ω =>
    finiteDisorderConfigurationConnectedCurrentCorrelation
      ensemble hbar hbar_pos spectralData Jx Jy ω)

/-- Expanding the quenched connected correlation subtracts the
*average of configuration-wise one-current products*, not the product
of two separately disorder-averaged one-current expectations. -/
theorem finiteDisorderAveragedConnectedCurrentCorrelation_eq_average_sub
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) →
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (Jx Jy : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :
    finiteDisorderAveragedConnectedCurrentCorrelation
        ensemble hbar hbar_pos spectralData Jx Jy =
      ensemble.average (fun ω =>
        purePointNormalizedExpectation
          (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) (Jx * Jy)) -
      ensemble.average (fun ω =>
        purePointNormalizedExpectation
            (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jx *
          purePointNormalizedExpectation
            (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jy) := by
  unfold finiteDisorderAveragedConnectedCurrentCorrelation
    finiteDisorderConfigurationConnectedCurrentCorrelation
    FiniteDisorderEnsemble.average
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- Disorder-averaging a *connected* current response is different in
general from taking the connected response of the two disorder-averaged
one-point functions. The missing term is the disorder covariance of the
one-point currents. -/
theorem finiteDisorderAveragedConnectedCurrentCorrelation_eq_annealed_sub_covariance
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) →
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (Jx Jy : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :
    finiteDisorderAveragedConnectedCurrentCorrelation
        ensemble hbar hbar_pos spectralData Jx Jy =
      (ensemble.average (fun ω =>
          purePointNormalizedExpectation
            (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) (Jx * Jy)) -
        ensemble.average (fun ω =>
          purePointNormalizedExpectation
            (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jx) *
        ensemble.average (fun ω =>
          purePointNormalizedExpectation
            (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jy)) -
      (ensemble.average (fun ω =>
          purePointNormalizedExpectation
              (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jx *
            purePointNormalizedExpectation
              (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jy) -
        ensemble.average (fun ω =>
          purePointNormalizedExpectation
            (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jx) *
        ensemble.average (fun ω =>
          purePointNormalizedExpectation
            (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jy)) := by
  rw [finiteDisorderAveragedConnectedCurrentCorrelation_eq_average_sub]
  ring

/-- Once a genuine configuration-wise four-leg expansion has been proved,
its **finite** diagram sum can be interchanged with the quenched average,
while the configuration-wise disconnected current product stays inside
the average. This statement does not postulate Wick/Gaussian factorization
or identify a formal Dyson coefficient with a physical response. -/
theorem finiteDisorderAveragedConnectedCurrentCorrelation_eq_fourLegAverage
    {α : Type*} [Fintype α]
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) →
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (Jx Jy : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (coefficient : α → ℂ) (fourLeg : Ω → α → ℂ)
    (hfourLeg : ∀ ω,
      purePointNormalizedExpectation
          (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) (Jx * Jy) =
        ∑ a : α, coefficient a * fourLeg ω a) :
    finiteDisorderAveragedConnectedCurrentCorrelation
        ensemble hbar hbar_pos spectralData Jx Jy =
      (∑ a : α, coefficient a * ensemble.average (fun ω => fourLeg ω a)) -
        ensemble.average (fun ω =>
          purePointNormalizedExpectation
              (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jx *
            purePointNormalizedExpectation
              (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) Jy) := by
  rw [finiteDisorderAveragedConnectedCurrentCorrelation_eq_average_sub]
  congr 1
  unfold FiniteDisorderEnsemble.average
  calc
    (∑ ω, (ensemble.probability ω : ℂ) *
      purePointNormalizedExpectation
        (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω) (Jx * Jy)) =
        ∑ ω, (ensemble.probability ω : ℂ) *
          ∑ a : α, coefficient a * fourLeg ω a := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [hfourLeg ω]
    _ = ∑ a : α, coefficient a *
          ∑ ω, (ensemble.probability ω : ℂ) * fourLeg ω a := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω _
            ring

end
end Transport
end Fermionic
end SecondQuantization
