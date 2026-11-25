import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.AdiabaticSwitching
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.LimitOrder
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Symmetry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.EquationsOfMotion
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Intertwining

set_option linter.style.header false

/-!
# Finite-time scalar adiabatic response

This module owns the representation-independent finite-observation-time transform used by the
frequency-domain response stack. For a scalar causal kernel `K` and the canonical adiabatic phase

```text
exp ((i ω - η) τ),
```

the finite-time transform is

```text
∫₀ᵀ dτ exp ((i ω - η) τ) K(τ).
```

The module also applies the same finite-time phase directly to a neutral `ResponseChannel`, keeping
its retarded measured/source kernel and explicit observable-variation contact expectation together.
It names convergence in the observation-time variable `T → +∞` and remains independent of particle
statistics, Fock-space realizations, current operators, lattice geometry, and conductivity
normalization. Microscopic symmetry extends to the integrated response by finite-sum interchange
under explicit interval-integrability hypotheses, including the contact term. Zero-switching and static-limit orderings are owned by `Frequency.LimitOrder`.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

/-- Finite-observation-time adiabatic transform of a scalar causal kernel. No limit is taken. -/
noncomputable def finiteTimeAdiabaticTransform
    (kernel : ℝ → ℂ) (ω η T : ℝ) : ℂ :=
  ∫ τ in (0 : ℝ)..T, adiabaticFrequencyPhase ω η τ * kernel τ

@[simp]
theorem finiteTimeAdiabaticTransform_zero_time
    (kernel : ℝ → ℂ) (ω η : ℝ) :
    finiteTimeAdiabaticTransform kernel ω η 0 = 0 := by
  simp [finiteTimeAdiabaticTransform]

/-- Integration by parts for a continuously differentiable lag kernel. The
equal-time term cancels the lower endpoint, leaving the finite-time boundary
and the phase derivative. No infinite observation-time limit is taken. -/
theorem finiteTimeAdiabaticTransform_derivative_add_initial
    (K K' : ℝ → ℂ) (ω η T : ℝ)
    (hK : ∀ t, HasDerivAt K (K' t) t) (hK' : Continuous K') :
    finiteTimeAdiabaticTransform K' ω η T + K 0 =
      adiabaticFrequencyPhase ω η T * K T -
        (Complex.I * (ω : ℂ) - (η : ℂ)) *
          finiteTimeAdiabaticTransform K ω η T := by
  let z := Complex.I * (ω : ℂ) - (η : ℂ)
  let P := adiabaticFrequencyPhase ω η
  have hP (t : ℝ) : HasDerivAt P (z * P t) t := by
    have hz : HasDerivAt (fun s : ℝ => z * (s : ℂ)) z t := by
      have hcast : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t :=
        (hasDerivAt_id (x := t)).ofReal_comp
      simpa only [mul_one] using hcast.const_mul z
    change HasDerivAt (fun s : ℝ => Complex.exp (z * (s : ℂ)))
      (z * Complex.exp (z * (t : ℂ))) t
    rw [mul_comm z (Complex.exp (z * (t : ℂ)))]
    exact hz.cexp
  have hPc : Continuous P := continuous_iff_continuousAt.mpr
    fun t => (hP t).continuousAt
  have hKc : Continuous K := continuous_iff_continuousAt.mpr
    fun t => (hK t).continuousAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := T) hPc.continuousOn hKc.continuousOn
    (fun t _ => hP t) (fun t _ => hK t)
    ((continuous_const.mul hPc).intervalIntegrable 0 T)
    (hK'.intervalIntegrable 0 T)
  change (∫ t in (0 : ℝ)..T, P t * K' t) =
    P T * K T - P 0 * K 0 -
      ∫ t in (0 : ℝ)..T, (z * P t) * K t at hparts
  simp only [mul_assoc, intervalIntegral.integral_const_mul] at hparts
  have hzero : P 0 = 1 := adiabaticFrequencyPhase_zero_time ω η
  rw [hzero, one_mul] at hparts
  change (∫ t in (0 : ℝ)..T, P t * K' t) + K 0 =
    P T * K T - z * ∫ t in (0 : ℝ)..T, P t * K t
  rw [hparts]
  abel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The lag susceptibility of a displacement differentiates to the lag
susceptibility of its Hamiltonian time derivative. This uses bounded free
dynamics, not a stationarity or spectral-basis hypothesis. -/
theorem hasDerivAt_commutatorSusceptibility_lag
    (system : BoundedFreeSystem H) (expectation : NormalizedExpectation H)
    (D B : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt
      (fun s => commutatorSusceptibility (freePropagatorGroup system)
        system.hbar expectation D B s 0)
      (commutatorSusceptibility (freePropagatorGroup system) system.hbar expectation
        ((Complex.I / (system.hbar : ℂ)) • ⁅system.hamiltonian.1, D⁆) B t 0) t := by
  have h := heisenbergEquation_initial system D t
  have hcomm := (h.mul_const B).sub (h.const_mul B)
  have hexpect :=
    (expectation.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hcomm
  simp only [commutatorSusceptibility, heisenbergEvolution_zero,
    LieRing.of_associative_ring_bracket]
  exact hexpect.const_mul (Complex.I / (system.hbar : ℂ))

namespace ResponseChannel

/-- Finite-observation-time adiabatic response of a neutral response channel.

The source value at the observation time has been factored out, so the retarded kernel carries the
lag phase `exp ((i ω - η) (T - s))` while the explicit observable variation contributes its
contact expectation at `T`. No stationarity or infinite-time limit is assumed. -/
noncomputable def finiteTimeAdiabaticResponse
    (channel : ResponseChannel H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ) (expectation : NormalizedExpectation H)
    (ω η T : ℝ) : ℂ :=
  (∫ s in (0 : ℝ)..T,
      adiabaticFrequencyPhase ω η (T - s) *
        channel.retardedKernel U hbar expectation T s) +
    channel.contactExpectation U expectation T

/-- A fixed-observable channel has no contact contribution, so its finite-time adiabatic response is
exactly the retarded measured/source transform. -/
theorem finiteTimeAdiabaticResponse_fixed
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ) (expectation : NormalizedExpectation H)
    (measured source : H →L[ℂ] H) (ω η T : ℝ) :
    (fixed measured source).finiteTimeAdiabaticResponse U hbar expectation ω η T =
      ∫ s in (0 : ℝ)..T,
        adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility U hbar
            expectation measured source T s := by
  rw [finiteTimeAdiabaticResponse, fixed_contactExpectation]
  simp [retardedKernel, fixed]

/-- In a stationary state, a nonnegative observation interval is a lag transform plus the
stationary observable-variation expectation. The source value at observation time is factored out. -/
theorem finiteTimeAdiabaticResponse_eq_stationaryLag
    (channel : ResponseChannel H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ) (expectation : NormalizedExpectation H)
    (hstationary : IsStationary U expectation)
    (ω η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    channel.finiteTimeAdiabaticResponse U hbar expectation ω η T =
      finiteTimeAdiabaticTransform
          (fun τ => commutatorSusceptibility U hbar expectation
            channel.measured channel.source τ 0) ω η T +
        expectation channel.observableVariation := by
  rw [finiteTimeAdiabaticResponse, contactExpectation,
    hstationary T channel.observableVariation]
  congr 1
  let g : ℝ → ℂ := fun τ => adiabaticFrequencyPhase ω η τ *
    commutatorSusceptibility U hbar
      expectation channel.measured channel.source τ 0
  change (∫ s in (0 : ℝ)..T, adiabaticFrequencyPhase ω η (T - s) *
      retardedSusceptibility U hbar
        expectation channel.measured channel.source T s) =
    ∫ τ in (0 : ℝ)..T, g τ
  calc
    _ = ∫ s in (0 : ℝ)..T, g (T - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsIcc : s ∈ Set.Icc (0 : ℝ) T := by
        simpa [Set.uIcc_of_le hT] using hs
      change adiabaticFrequencyPhase ω η (T - s) *
        retardedSusceptibility U hbar
          expectation channel.measured channel.source T s =
          g (T - s)
      rw [retardedSusceptibility_eq_timeDifference_of_stationary
        U hbar
        expectation hstationary channel.measured channel.source T s]
      simp [g, sub_nonneg.mpr hsIcc.2]
    _ = ∫ τ in (0 : ℝ)..T, g τ := by
      simpa using intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ)) (b := T) g T

/-- For a fixed displacement D, the channel measuring its time derivative
has an explicit source variation (i/ℏ)[-B,D]. In a stationary state, its
source-normalized finite-time response is the upper boundary minus the
phase derivative times the displacement transform. The equal-time contact
cancels the lower integration-by-parts boundary exactly. -/
theorem finiteTimeAdiabaticResponse_of_displacement
    (channel : ResponseChannel H) (system : BoundedFreeSystem H)
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary (freePropagatorGroup system) expectation)
    (D : H →L[ℂ] H)
    (hJ : channel.measured =
      (Complex.I / (system.hbar : ℂ)) • ⁅system.hamiltonian.1, D⁆)
    (hC : channel.observableVariation =
      (Complex.I / (system.hbar : ℂ)) • ⁅-channel.source, D⁆)
    (ω η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    let K := fun τ => commutatorSusceptibility (freePropagatorGroup system)
      system.hbar expectation D channel.source τ 0
    channel.finiteTimeAdiabaticResponse (freePropagatorGroup system)
      system.hbar expectation ω η T =
      adiabaticFrequencyPhase ω η T * K T -
        (Complex.I * (ω : ℂ) - (η : ℂ)) *
          finiteTimeAdiabaticTransform K ω η T := by
  let U := freePropagatorGroup system
  let K := fun τ => commutatorSusceptibility U system.hbar expectation D channel.source τ 0
  let K' := fun τ => commutatorSusceptibility U system.hbar expectation
    channel.measured channel.source τ 0
  have hK (t : ℝ) : HasDerivAt K (K' t) t := by
    dsimp only [K, K']
    rw [hJ]
    exact hasDerivAt_commutatorSusceptibility_lag system expectation D channel.source t
  have hK' : Continuous K' :=
    continuous_commutatorSusceptibility_timeDifference U system.hbar expectation
      channel.measured channel.source (continuous_heisenbergEvolution system channel.measured)
  have hcontact : expectation channel.observableVariation = K 0 := by
    have heq := retardedSusceptibility_sameTime_eq_commutatorVariation U system.hbar
      expectation D channel.source 1 0
    rw [one_smul, one_mul, heisenbergEvolution_zero,
      retardedSusceptibility_eq_commutatorSusceptibility_of_le U system.hbar
        expectation D channel.source (le_refl (0 : ℝ))] at heq
    rw [hC]
    exact heq
  rw [channel.finiteTimeAdiabaticResponse_eq_stationaryLag U system.hbar
    expectation hstationary ω η hT, hcontact]
  exact finiteTimeAdiabaticTransform_derivative_add_initial K K' ω η T hK hK'

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
variable (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))

/-- After explicitly assuming integrability of every weighted retarded
component, the full *finite-time* response (including the contact term)
has the same separate measured/source matrix transformation law as the
two-time Kubo kernel. Neither continuity nor integrability is inferred
from an arbitrary algebraic unitary time-evolution group. -/
theorem finiteTimeAdiabaticResponse_linearMixing
    {I J : Type*} [Fintype I] [Fintype J]
    (measured : I → (H →L[ℂ] H))
    (source : J → (H →L[ℂ] H))
    (variation : I → J → (H →L[ℂ] H))
    (R : I → I → ℂ) (S : J → J → ℂ)
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (hbar : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ A : H →L[ℂ] H, expectation (Φ A) = expectation A)
    (hMeasured : ∀ i, Φ (measured i) = ∑ k, R i k • measured k)
    (hSource : ∀ j, Φ (source j) = ∑ l, S j l • source l)
    (hVariation : ∀ i j,
      Φ (variation i j) = ∑ k, ∑ l, (R i k * S j l) • variation k l)
    (ω η T : ℝ)
    (hIntegrable : ∀ k l,
      IntervalIntegrable
        (fun s : ℝ => adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility U hbar expectation (measured k) (source l) T s)
        MeasureTheory.volume 0 T)
    (i : I) (j : J) :
    (∑ k, ∑ l, (R i k * S j l) *
      (({ measured := measured k, source := source l,
          observableVariation := variation k l } : ResponseChannel H).finiteTimeAdiabaticResponse
        U hbar expectation ω η T)) =
      (({ measured := measured i, source := source j,
          observableVariation := variation i j } : ResponseChannel H).finiteTimeAdiabaticResponse
        U hbar expectation ω η T) := by
  classical
  let K : I → J → ℝ → ℂ := fun k l s =>
    adiabaticFrequencyPhase ω η (T - s) *
      retardedSusceptibility U hbar expectation (measured k) (source l) T s
  let C : I → J → ℂ := fun k l =>
    expectation (heisenbergEvolution U T (variation k l))
  have hIntegral :
      (∫ s in (0 : ℝ)..T, ∑ k : I, ∑ l : J,
        (R i k * S j l) * K k l s) =
        ∑ k : I, ∑ l : J,
          (R i k * S j l) * (∫ s in (0 : ℝ)..T, K k l s) := by
    have hProd :
        (∫ s in (0 : ℝ)..T, ∑ p : I × J,
          (R i p.1 * S j p.2) * K p.1 p.2 s) =
          ∑ p : I × J,
            (R i p.1 * S j p.2) * (∫ s in (0 : ℝ)..T, K p.1 p.2 s) := by
      rw [intervalIntegral.integral_finsetSum
        (by intro p hp; exact (hIntegrable p.1 p.2).const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
    simpa only [Fintype.sum_prod_type] using hProd
  have hPointwise (s : ℝ) :
      (∑ k : I, ∑ l : J, (R i k * S j l) * K k l s) = K i j s := by
    dsimp [K]
    calc
      (∑ k : I, ∑ l : J, (R i k * S j l) *
          (adiabaticFrequencyPhase ω η (T - s) *
            retardedSusceptibility U hbar expectation (measured k) (source l) T s)) =
        (∑ k : I, ∑ l : J, (R i k * S j l) *
          retardedSusceptibility U hbar expectation (measured k) (source l) T s) *
          adiabaticFrequencyPhase ω η (T - s) := by
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro l hl
            ring
      _ = retardedSusceptibility U hbar expectation (measured i) (source j) T s *
          adiabaticFrequencyPhase ω η (T - s) := by
            rw [retardedSusceptibility_linearMixing U Φ measured source R S
              hU hbar expectation hω hMeasured hSource i j T s]
      _ = _ := mul_comm _ _
  have hIntegralEq :
      (∑ k : I, ∑ l : J,
        (R i k * S j l) * (∫ s in (0 : ℝ)..T, K k l s)) =
        ∫ s in (0 : ℝ)..T, K i j s := by
    rw [← hIntegral]
    apply intervalIntegral.integral_congr
    intro s hs
    exact hPointwise s
  have hContact :
      (∑ k : I, ∑ l : J, (R i k * S j l) * C k l) = C i j := by
    exact expectation_heisenbergEvolution_linearMixing U Φ
      variation R S hU expectation hω hVariation i j T
  change
    (∑ k : I, ∑ l : J, (R i k * S j l) *
      ((∫ s in (0 : ℝ)..T, K k l s) + C k l)) =
      (∫ s in (0 : ℝ)..T, K i j s) + C i j
  calc
    _ = (∑ k : I, ∑ l : J,
          (R i k * S j l) * (∫ s in (0 : ℝ)..T, K k l s)) +
        (∑ k : I, ∑ l : J, (R i k * S j l) * C k l) := by
          simp_rw [mul_add]
          simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hIntegralEq, hContact]

/-- The complete finite-time Kubo response is an intertwiner between independent
input-field and output-coordinate representations, with no restriction to
orthogonal or identical representations.

For each group element the supplied microscopic symmetry must transform the
measured family with the rows of the output matrix and the source family with
the rows of the *inverse transpose* input matrix. The latter is the dual action
required by the source-field pairing, not an identification of the source
operator representation with the input-field representation. The explicit
contact operators transform with the corresponding two factors. The microscopic
symmetries are supplied pointwise (for instance by inverse conjugation of a
unitary group action); no claim of a group action on observables is inferred
from these pointwise hypotheses.

The existing integrated response covariance gives `R X S = X`, where
`S` is the matrix of the inverse input action. The representation law then
gives `R X = X P`. The resulting map is Mathlib's intertwining map, not a
new response or representation structure. -/
theorem finiteTimeAdiabaticResponse_exists_intertwiningMap
    {G I J : Type*} [Group G] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (ρin : Representation ℂ G (J → ℂ))
    (ρout : Representation ℂ G (I → ℂ))
    (symmetry : G → ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)))
    (measured : I → (H →L[ℂ] H))
    (source : J → (H →L[ℂ] H))
    (variation : I → J → (H →L[ℂ] H))
    (hU : ∀ g t, symmetry g (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (hbar : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ g A, expectation (symmetry g A) = expectation A)
    (hMeasured : ∀ g i, symmetry g (measured i) =
      ∑ k, LinearMap.toMatrix' (ρout g) i k • measured k)
    (hSource : ∀ g j, symmetry g (source j) =
      ∑ l, LinearMap.toMatrix' (ρin g⁻¹) l j • source l)
    (hVariation : ∀ g i j, symmetry g (variation i j) =
      ∑ k, ∑ l, (LinearMap.toMatrix' (ρout g) i k *
        LinearMap.toMatrix' (ρin g⁻¹) l j) • variation k l)
    (ω η T : ℝ)
    (hIntegrable : ∀ k l,
      IntervalIntegrable
        (fun s : ℝ => adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility U hbar expectation (measured k) (source l) T s)
        MeasureTheory.volume 0 T) :
    ∃ F : Representation.IntertwiningMap ρin ρout,
      F.toLinearMap = Matrix.toLin' (fun i j =>
        ({ measured := measured i, source := source j,
           observableVariation := variation i j } : ResponseChannel H).finiteTimeAdiabaticResponse
          U hbar expectation ω η T) := by
  let X : Matrix I J ℂ := fun i j =>
    ({ measured := measured i, source := source j,
       observableVariation := variation i j } : ResponseChannel H).finiteTimeAdiabaticResponse
      U hbar expectation ω η T
  change ∃ F : Representation.IntertwiningMap ρin ρout, F.toLinearMap = Matrix.toLin' X
  refine ⟨⟨Matrix.toLin' X, ?_⟩, rfl⟩
  intro g
  let R := LinearMap.toMatrix' (ρout g)
  let P := LinearMap.toMatrix' (ρin g)
  let S := LinearMap.toMatrix' (ρin g⁻¹)
  have hCov : R * X * S = X := by
    rw [Matrix.mul_assoc]
    ext i j
    have h := finiteTimeAdiabaticResponse_linearMixing U (symmetry g)
      measured source variation R (fun j l => S l j) (hU g) hbar expectation
      (hω g) (hMeasured g) (hSource g) (hVariation g) ω η T hIntegrable i j
    change (∑ k, ∑ l, (R i k * S l j) * X k l) = X i j at h
    rw [← h]
    simp only [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hInv : S * P = 1 := by
    dsimp only [S, P]
    rw [← LinearMap.toMatrix'_mul, ← ρin.map_mul, inv_mul_cancel, ρin.map_one,
      LinearMap.toMatrix'_one]
  have hComm : R * X = X * P := by
    have h := congrArg (fun A : Matrix I J ℂ => A * P) hCov
    change (R * X * S) * P = X * P at h
    rw [Matrix.mul_assoc (R * X) S P, hInv, Matrix.mul_one] at h
    exact h
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  exact hComm.symm

end ResponseChannel

end
end LinearResponse
end QuantumTheory
