import LeanCondensedMatter.Crystal.PointGroup
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.FiniteTime
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

open scoped Matrix

/-!
# Finite-time Kubo conductivity under unitary spatial symmetry

The representation-independent finite-time response covariance is proved in
`QuantumTheory.LinearResponse.Frequency.FiniteTime`. This module only applies
the existing positive-volume normalization for a total-current response to
a vector-potential source, retaining the contact contribution.

The normalized tensor is a physical conductivity when the supplied operators
realize the physical current, vector-potential coupling and contact variation,
the observation time is nonnegative, and the driving frequency and switching
rate are not both zero. The algebraic definition remains total; no zero-rate,
DC or thermodynamic limit is asserted. The planar corollary uses an actual
configuration point-group element with explicit microscopic realization
hypotheses.
-/

namespace QuantumTheory.Transport

open QuantumTheory.LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
variable (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))

/-- A finite-observation-time conductivity tensor using the shared
positive-volume vector-potential-to-electric-field normalization.
The operator families must be supplied by a physical current and
vector-potential coupling model for the components to be conductivities.
For physical electric-field conversion require `0 ≤ T` and
`ω ≠ 0 ∨ η ≠ 0`; the latter guarantees a nonzero denominator by
`finiteVolumeConductivityDenominator_ne_zero`. At `ω = η = 0` the totalized
inverse returns zero, not a physical DC conductivity.
There is no new tensor representation or normalization convention. -/
noncomputable def finiteTimeVectorPotentialConductivityTensor
    {I : Type*}
    (measured source : I → (H →L[ℂ] H))
    (variation : I → I → (H →L[ℂ] H))
    (volume : PositiveVolume)
    (hbar ω η T : ℝ) (expectation : NormalizedExpectation H) :
    ConductivityTensor I where
  component i j := finiteVolumeConductivityFromVectorPotential volume ω η
    (({ measured := measured i, source := source j,
        observableVariation := variation i j } : ResponseChannel H).finiteTimeAdiabaticResponse
      U hbar expectation ω η T)

/-- Microscopic unitary covariance and interval integrability imply
the two-sided matrix constraint on the *normalized* finite-volume tensor.
Only the already-defined scalar normalization is used. The equality is algebraic
also at zero rates; its physical interpretation requires the nonzero-rate
condition documented on the tensor definition. -/
theorem finiteTimeVectorPotentialConductivityTensor_linearMixing
    {I : Type*} [Fintype I]
    (measured source : I → (H →L[ℂ] H))
    (variation : I → I → (H →L[ℂ] H))
    (R S : I → I → ℂ)
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (volume : PositiveVolume)
    (hbar ω η T : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ A : H →L[ℂ] H, expectation (Φ A) = expectation A)
    (hMeasured : ∀ i, Φ (measured i) = ∑ k, R i k • measured k)
    (hSource : ∀ j, Φ (source j) = ∑ l, S j l • source l)
    (hVariation : ∀ i j,
      Φ (variation i j) = ∑ k, ∑ l, (R i k * S j l) • variation k l)
    (hIntegrable : ∀ k l,
      IntervalIntegrable
        (fun s : ℝ => adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility U hbar expectation (measured k) (source l) T s)
        MeasureTheory.volume 0 T)
    (i j : I) :
    (∑ k, ∑ l, (R i k * S j l) *
      (finiteTimeVectorPotentialConductivityTensor U measured source variation
        volume hbar ω η T expectation).component k l) =
      (finiteTimeVectorPotentialConductivityTensor U measured source variation
        volume hbar ω η T expectation).component i j := by
  classical
  let X : I → I → ℂ := fun k l =>
    (({ measured := measured k, source := source l,
        observableVariation := variation k l } : ResponseChannel H).finiteTimeAdiabaticResponse
      U hbar expectation ω η T)
  let n := finiteVolumeConductivityNormalization volume ω η
  have hX :
      (∑ k : I, ∑ l : I, (R i k * S j l) * X k l) = X i j :=
    ResponseChannel.finiteTimeAdiabaticResponse_linearMixing U Φ measured source variation R S
      hU hbar expectation hω hMeasured hSource hVariation ω η T hIntegrable i j
  change (∑ k : I, ∑ l : I, (R i k * S j l) * (X k l * n)) = X i j * n
  calc
    _ = (∑ k : I, ∑ l : I, (R i k * S j l) * X k l) * n := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := by rw [hX]

/-- The physically normalized finite-time conductivity inherits the general
input/output intertwiner of the complete response, including its contact term.
Normalization by a common complex scalar preserves equivariance, even for
distinct or nonorthogonal representations on the coordinate space.

The underlying map is exactly the existing conductivity tensor interpreted as
a matrix acting on input fields. The physical domain and operator realization
requirements are those of `finiteTimeVectorPotentialConductivityTensor`;
in particular, this is not a zero-regulator or DC limit. -/
theorem finiteTimeVectorPotentialConductivityTensor_exists_intertwiningMap
    {G I : Type*} [Group G] [Fintype I] [DecidableEq I]
    (ρin ρout : Representation ℂ G (I → ℂ))
    (symmetry : G → ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)))
    (measured source : I → (H →L[ℂ] H))
    (variation : I → I → (H →L[ℂ] H))
    (hU : ∀ g t, symmetry g (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (volume : PositiveVolume)
    (hbar ω η T : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ g A, expectation (symmetry g A) = expectation A)
    (hMeasured : ∀ g i, symmetry g (measured i) =
      ∑ k, LinearMap.toMatrix' (ρout g) i k • measured k)
    (hSource : ∀ g j, symmetry g (source j) =
      ∑ l, LinearMap.toMatrix' (ρin g⁻¹) l j • source l)
    (hVariation : ∀ g i j, symmetry g (variation i j) =
      ∑ k, ∑ l, (LinearMap.toMatrix' (ρout g) i k *
        LinearMap.toMatrix' (ρin g⁻¹) l j) • variation k l)
    (hIntegrable : ∀ k l,
      IntervalIntegrable
        (fun s : ℝ => adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility U hbar expectation (measured k) (source l) T s)
        MeasureTheory.volume 0 T) :
    ∃ F : Representation.IntertwiningMap ρin ρout,
      F.toLinearMap = Matrix.toLin'
        (finiteTimeVectorPotentialConductivityTensor U measured source variation
          volume hbar ω η T expectation).component := by
  obtain ⟨F, hF⟩ := ResponseChannel.finiteTimeAdiabaticResponse_exists_intertwiningMap
    U ρin ρout symmetry measured source variation hU hbar expectation
    hω hMeasured hSource hVariation ω η T hIntegrable
  let n := finiteVolumeConductivityNormalization volume ω η
  refine ⟨n • F, ?_⟩
  rw [Representation.IntertwiningMap.toLinearMap_smul, hF, ← map_smul]
  apply congrArg (fun M : Matrix I I ℂ => Matrix.toLin' M)
  ext i j
  change n * (({ measured := measured i, source := source j,
    observableVariation := variation i j } : ResponseChannel H).finiteTimeAdiabaticResponse
      U hbar expectation ω η T) =
    (({ measured := measured i, source := source j,
      observableVariation := variation i j } : ResponseChannel H).finiteTimeAdiabaticResponse
        U hbar expectation ω η T) * n
  exact mul_comm _ _

/-- A quarter-turn in the point group of the actual species-labeled configuration
forces planar isotropy of the finite-time, normalized conductivity if that
geometric symmetry is realized on the microscopic dynamics, state, both polar
current/source families, and contact variation.

The matrix is read from the supplied point-group element in an orthonormal
spatial basis, not from the potentially larger intrinsic lattice point group.
The operator symmetry `Φ` must realize the indicated transformation laws;
membership of the geometric point group alone does not imply that the
Hamiltonian or a magnetic state preserves it. No Hall-vanishing constraint,
space-group splitting, or DC limit follows from this proper rotation. -/
theorem finiteTimeVectorPotentialConductivityTensor_isPlanarIsotropic_of_pointGroup_quarterTurn
    {V E Species : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace E] [NormedAddTorsor V E]
    (X : LeanCondensedMatter.Crystal.AtomicConfiguration E Species)
    (g : X.pointGroup (V := V))
    (b : OrthonormalBasis (Fin 2) ℝ V)
    (measured source : Fin 2 → (H →L[ℂ] H))
    (variation : Fin 2 → Fin 2 → (H →L[ℂ] H))
    (hU : ∀ t : ℝ, Φ (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
    (volume : PositiveVolume)
    (hbar ω η T : ℝ) (expectation : NormalizedExpectation H)
    (hω : ∀ A : H →L[ℂ] H, expectation (Φ A) = expectation A)
    (hIntegrable : ∀ k l,
      IntervalIntegrable
        (fun s : ℝ => adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility U hbar expectation (measured k) (source l) T s)
        MeasureTheory.volume 0 T) :
    let R : Matrix (Fin 2) (Fin 2) ℂ := fun i k =>
      ((b.repr ((g : V ≃ₗᵢ[ℝ] V) (b k)) i : ℝ) : ℂ)
    R = !![0, -1; 1, 0] →
    (∀ i, Φ (measured i) = ∑ k, R i k • measured k) →
    (∀ j, Φ (source j) = ∑ l, R j l • source l) →
    (∀ i j, Φ (variation i j) = ∑ k, ∑ l, (R i k * R j l) • variation k l) →
    (finiteTimeVectorPotentialConductivityTensor U measured source variation
      volume hbar ω η T expectation).IsPlanarIsotropic := by
  classical
  intro R hQuarter hMeasured hSource hVariation
  apply (ConductivityTensor.isQuarterTurnInvariant_iff_isPlanarIsotropic _).mp
  dsimp only [ConductivityTensor.IsQuarterTurnInvariant]
  intro i j
  have h := finiteTimeVectorPotentialConductivityTensor_linearMixing U Φ
    measured source variation R R hU volume hbar ω η T expectation hω
    hMeasured hSource hVariation hIntegrable i j
  rw [hQuarter] at h
  simpa only [mul_right_comm] using h

end
end QuantumTheory.Transport
