import LeanCondensedMatter.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.MatrixBilinear
import LeanCondensedMatter.QuantumTheory.Gibbs.State
import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation.Density
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.ObservableVariation
import Mathlib.Order.Prod.Lex.Basic

set_option linter.style.header false

/-! # Massive Dirac fermions with finitely many momentum modes

Each sampled physical momentum has two internal modes. The Hilbert space includes every
occupation sector, and the Hamiltonian is `∑ p a b, h(p) a b c†(p,a)c(p,b)`.
The model uses the clean Hamiltonian and electron charge `-e` of `Model.Basic`.
Minimal coupling shifts physical momentum by `+e A`; its current is `-∂H/∂A`.
The finite set of modes is held fixed under that shift. No continuum limit or reduction of
many-body thermal response to a one-particle trace is asserted here.
-/

namespace QuantumTheory.Models.MassiveDirac.FiniteFock

open SecondQuantization.Fermionic.Lattice LinearResponse
open scoped BigOperators

noncomputable section

variable {Momentum : Type*} [Fintype Momentum] [LinearOrder Momentum]

/-- Full fermionic Fock space over momentum and the two internal components. -/
abbrev Hilbert (Momentum : Type*) := FiniteLatticeHilbertFock (Momentum ×ₗ Fin 2)

private def liftMatrix (p : Momentum) :=
  matrixBilinear (fun a : Fin 2 => toLex (p, a))

/-- Clean many-body Hamiltonian at the specified finite set of physical momenta. -/
def hamiltonian (momentum : Momentum → ℝ × ℝ) (v m : ℝ) :
    Hilbert Momentum →L[ℂ] Hilbert Momentum :=
  ∑ p, liftMatrix p (MassiveDirac.hamiltonian v m (momentum p).1 (momentum p).2)

/-- Total current, with electron charge `-e`, in either Cartesian direction. -/
def current (direction : Fin 2) (e v : ℝ) :
    Hilbert Momentum →L[ℂ] Hilbert Momentum :=
  ∑ p : Momentum, liftMatrix p (MassiveDirac.current direction e v)

theorem hamiltonian_isSelfAdjoint (momentum : Momentum → ℝ × ℝ) (v m : ℝ) :
    IsSelfAdjoint (hamiltonian momentum v m) := by
  rw [isSelfAdjoint_iff]
  simp only [hamiltonian, star_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [liftMatrix, star_matrixBilinear,
    (hamiltonian_isHermitian v m (momentum p).1 (momentum p).2).isSelfAdjoint.star_eq]

theorem current_isSelfAdjoint (direction : Fin 2) (e v : ℝ) :
    IsSelfAdjoint (current (Momentum := Momentum) direction e v) := by
  rw [isSelfAdjoint_iff]
  simp only [current, star_sum, liftMatrix, star_matrixBilinear,
    (current_isHermitian direction e v).isSelfAdjoint.star_eq]

/-- Uniform vector potential in one Cartesian direction, with the mode set held fixed. -/
def shiftedMomentum (momentum : Momentum → ℝ × ℝ) (direction : Fin 2) (e a : ℝ) :
    Momentum → ℝ × ℝ :=
  fun p => if direction = 0 then ((momentum p).1 + e * a, (momentum p).2)
    else ((momentum p).1, (momentum p).2 + e * a)

/-- Minimal coupling is exactly affine in the vector potential for this linear Dirac model. -/
theorem hamiltonian_shiftedMomentum (momentum : Momentum → ℝ × ℝ)
    (direction : Fin 2) (e v m a : ℝ) :
    hamiltonian (shiftedMomentum momentum direction e a) v m =
      hamiltonian momentum v m - (a : ℂ) • current direction e v := by
  have hmatrix (px py : ℝ) :
      MassiveDirac.hamiltonian v m
          (if direction = 0 then px + e * a else px)
          (if direction = 0 then py else py + e * a) =
        MassiveDirac.hamiltonian v m px py -
          (a : ℂ) • MassiveDirac.current direction e v := by
    fin_cases direction <;>
      simp [MassiveDirac.hamiltonian, MassiveDirac.current, velocity,
        directionPauli, inPlanePauliAxis, InternalSpace.pauliBasis] <;> module
  unfold hamiltonian current
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hp := hmatrix (momentum p).1 (momentum p).2
  fin_cases direction <;>
    simpa [shiftedMomentum, liftMatrix, map_sub, map_smul] using
      congrArg (liftMatrix p) hp

/-- The negative vector-potential derivative is the total creation-annihilation current. -/
theorem hasDerivAt_hamiltonian_shiftedMomentum (momentum : Momentum → ℝ × ℝ)
    (direction : Fin 2) (e v m a : ℝ) :
    HasDerivAt (fun field : ℝ =>
      hamiltonian (shiftedMomentum momentum direction e field) v m)
      (-current (Momentum := Momentum) direction e v) a := by
  simp only [hamiltonian_shiftedMomentum]
  have hscalar (r : ℝ) :
      (r : ℂ) • current (Momentum := Momentum) direction e v =
        r • current (Momentum := Momentum) direction e v :=
    algebraMap_smul ℂ r _
  simp only [hscalar]
  rw [hasDerivAt_iff_tendsto]
  have hzero (field : ℝ) :
      hamiltonian momentum v m - field • current (Momentum := Momentum) direction e v -
          (hamiltonian momentum v m - a • current direction e v) -
          (field - a) • (-current direction e v) = 0 := by
    module
  simpa only [hzero, norm_zero, mul_zero] using
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) (nhds a) (nhds 0))

/-- A time-profiled minimal coupling is the source perturbation used by bounded response. -/
theorem hamiltonian_sourceCoupledPerturbation (momentum : Momentum → ℝ × ℝ)
    (direction : Fin 2) (e v m : ℝ) (f : ℝ → ℝ) (lam t : ℝ) :
    hamiltonian (shiftedMomentum momentum direction e (lam * f t)) v m =
      hamiltonian momentum v m + (lam : ℂ) •
        sourceCoupledPerturbation f (current direction e v) t := by
  rw [hamiltonian_shiftedMomentum]
  simp only [sourceCoupledPerturbation, Complex.ofReal_mul,
    neg_smul, smul_neg, smul_smul, sub_eq_add_neg]

/-- Unperturbed bounded dynamics; the Hamiltonian acts on the full Fock space. -/
def system (momentum : Momentum → ℝ × ℝ) (v m hbar : ℝ) (hbar_pos : 0 < hbar) :
    BoundedFreeSystem (Hilbert Momentum) where
  hamiltonian := ⟨hamiltonian momentum v m, hamiltonian_isSelfAdjoint momentum v m⟩
  hbar := hbar
  hbar_pos := hbar_pos

/-- Current response to a uniform vector potential. Since the Dirac Hamiltonian is affine,
the current has zero explicit variation, hence zero contact contribution for this finite model. -/
def channel (measuredDirection sourceDirection : Fin 2) (e v : ℝ) :
    ResponseChannel (Hilbert Momentum) :=
  ResponseChannel.fixed (current measuredDirection e v) (current sourceDirection e v)

/-- The actual finite-Fock Gibbs state at chemical potential zero supplies the expectation
in the general Kubo theorem.
`horizon` is a time interval endpoint, distinct from the inverse temperature. Analytic bounds
and interval integrability of the applied source remain explicit hypotheses. -/
theorem hasDerivAt_gibbsCurrentResponse
    (momentum : Momentum → ℝ × ℝ) (measuredDirection sourceDirection : Fin 2)
    (e v m hbar inverseTemperature : ℝ) (hbar_pos : 0 < hbar)
    (f : ℝ → ℝ) {horizon M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) horizon,
      ‖timeDependentInteractionPerturbation (system momentum v m hbar hbar_pos)
        (sourceCoupledPerturbation f (current sourceDirection e v)) s‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) horizon)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation (system momentum v m hbar hbar_pos)
        (sourceCoupledPerturbation f (current sourceDirection e v)))
      MeasureTheory.volume 0 t) :
    let S := system momentum v m hbar hbar_pos
    let expectation := (gibbsState S.hamiltonian inverseTemperature).toNormalizedExpectation
    let C := channel (Momentum := Momentum) measuredDirection sourceDirection e v
    HasDerivAt
      (fun lam : ℝ => affinePerturbedExpectation S expectation
        (sourceCoupledPerturbation f C.source) C.measured C.observableVariation lam t)
      (C.causalResponse S expectation f t) 0 := by
  exact ResponseChannel.hasDerivAt_affineSourceCoupledExpectation_zero_of_bound_retarded
      (channel measuredDirection sourceDirection e v)
      (system momentum v m hbar hbar_pos) _ f
      (current_isSelfAdjoint sourceDirection e v) hM hV ht hInt

end
end QuantumTheory.Models.MassiveDirac.FiniteFock
