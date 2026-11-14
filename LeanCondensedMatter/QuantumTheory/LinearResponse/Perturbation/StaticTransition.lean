import LeanCondensedMatter.Analysis.OscillatoryIntegral
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Eigenstate
import LeanCondensedMatter.QuantumTheory.LinearResponse.Perturbation.TransitionProbability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Static perturbations between energy eigenvectors

The actual operator Dyson variation reduces to the oscillatory phase integral using two
free eigenvector equations. Its squared weight is the finite-time sine kernel off resonance
and grows as t² at resonance. All statements are at fixed finite time; no golden-rule
long-time limit or continuum density of states is asserted.
-/
namespace QuantumTheory.LinearResponse
open Filter Set
open scoped Topology
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- A static perturbation's first Dyson matrix element is its bare matrix element times
the finite-time phase integral. No complete basis or state probabilities are needed. -/
theorem staticTransitionFirstVariation_eq_timeIntegral
    (initial final : H) (energyInitial energyFinal : ℝ)
    (hinitial : system.hamiltonian.1 initial = (energyInitial : ℂ) • initial)
    (hfinal : system.hamiltonian.1 final = (energyFinal : ℂ) • final)
    (V : H →L[ℂ] H) (time : ℝ) :
    inner ℂ final
        (timeDependentPropagatorFirstVariation (freePropagatorGroup system) system.hbar
          (fun _ => V) time initial) =
      (-(Complex.I / (system.hbar : ℂ))) *
        OscillatoryIntegral.timeIntegral ((energyFinal - energyInitial) / system.hbar) time *
          inner ℂ final (V initial) := by
  let matrixElement : (H →L[ℂ] H) →L[ℂ] ℂ :=
    (innerSL ℂ final).comp (ContinuousLinearMap.apply ℂ H initial)
  have hint := matrixElement.intervalIntegral_comp_comm
    ((continuous_heisenbergEvolution system V).intervalIntegrable
      (μ := MeasureTheory.volume) (a := 0) (b := time))
  change inner ℂ final ((-(Complex.I / (system.hbar : ℂ))) •
    ((∫ s in (0 : ℝ)..time,
      heisenbergEvolution (freePropagatorGroup system) s V) initial)) = _
  rw [inner_smul_right]
  change (-(Complex.I / (system.hbar : ℂ))) *
    matrixElement (∫ s in (0 : ℝ)..time,
      heisenbergEvolution (freePropagatorGroup system) s V) = _
  calc
    _ = (-(Complex.I / (system.hbar : ℂ))) *
        (∫ s in (0 : ℝ)..time,
          matrixElement (heisenbergEvolution (freePropagatorGroup system) s V)) :=
      congrArg (fun z : ℂ => (-(Complex.I / (system.hbar : ℂ))) * z) hint.symm
    _ = _ := by
      change (-(Complex.I / (system.hbar : ℂ))) *
        (∫ s in (0 : ℝ)..time,
          inner ℂ final (heisenbergEvolution (freePropagatorGroup system) s V initial)) = _
      simp_rw [inner_heisenbergEvolution_of_eigenvectors system initial final
        energyInitial energyFinal hinitial hfinal V]
      have hphase (s : ℝ) :
          Complex.exp (Complex.I * ((((energyFinal - energyInitial) * s) /
            system.hbar : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((((energyFinal - energyInitial) / system.hbar * s) : ℝ) : ℂ)) := by
        congr 1
        push_cast
        ring
      simp_rw [hphase]
      rw [intervalIntegral.integral_mul_const]
      rfl

/-- Off resonance the squared first-order transition amplitude has the finite-time sine form. -/
theorem norm_staticTransitionFirstVariation_sq_of_ne
    (initial final : H) (energyInitial energyFinal : ℝ)
    (hinitial : system.hamiltonian.1 initial = (energyInitial : ℂ) • initial)
    (hfinal : system.hamiltonian.1 final = (energyFinal : ℂ) • final)
    (hgap : energyFinal - energyInitial ≠ 0) (V : H →L[ℂ] H) (time : ℝ) :
    ‖inner ℂ final
        (timeDependentPropagatorFirstVariation (freePropagatorGroup system) system.hbar
          (fun _ => V) time initial)‖ ^ 2 =
      4 * ‖inner ℂ final (V initial)‖ ^ 2 *
        Real.sin (((energyFinal - energyInitial) / system.hbar) * time / 2) ^ 2 /
          (energyFinal - energyInitial) ^ 2 := by
  have hhbar : system.hbar ≠ 0 := ne_of_gt system.hbar_pos
  have hfrequency := div_ne_zero hgap hhbar
  rw [staticTransitionFirstVariation_eq_timeIntegral system initial final
    energyInitial energyFinal hinitial hfinal V time]
  simp only [norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, div_pow, one_pow, sq_abs]
  rw [OscillatoryIntegral.norm_timeIntegral_sq _ _ hfrequency]
  field_simp [hhbar, hgap] <;> ring

/-- At resonance the squared first-order transition amplitude grows quadratically in time. -/
theorem norm_staticTransitionFirstVariation_sq_resonant
    (initial final : H) (energy : ℝ)
    (hinitial : system.hamiltonian.1 initial = (energy : ℂ) • initial)
    (hfinal : system.hamiltonian.1 final = (energy : ℂ) • final)
    (V : H →L[ℂ] H) (time : ℝ) :
    ‖inner ℂ final
        (timeDependentPropagatorFirstVariation (freePropagatorGroup system) system.hbar
          (fun _ => V) time initial)‖ ^ 2 =
      ‖inner ℂ final (V initial)‖ ^ 2 * time ^ 2 / system.hbar ^ 2 := by
  rw [staticTransitionFirstVariation_eq_timeIntegral system initial final
    energy energy hinitial hfinal V time]
  simp only [sub_self, zero_div, OscillatoryIntegral.timeIntegral_zero, norm_mul,
    norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, div_pow, one_pow, sq_abs]
  ring

/-- The finite-time kernel controls the leading squared amplitude of the exact Dyson
propagator, not merely a postulated first-order ansatz. Orthogonality removes the constant term. -/
theorem tendsto_staticTransitionWeight_div_sq_zero_of_eigenvectors
    (initial final : H) (energyInitial energyFinal : ℝ)
    (hinitial : system.hamiltonian.1 initial = (energyInitial : ℂ) • initial)
    (hfinal : system.hamiltonian.1 final = (energyFinal : ℂ) • final)
    (horthogonal : inner ℂ final initial = 0) (V : H →L[ℂ] H)
    (time : ℝ) (htime : 0 ≤ time) :
    Tendsto
      (fun lam : ℝ =>
        ‖inner ℂ final (timeDependentInteractionPropagator (freePropagatorGroup system)
          system.hbar (fun _ => V) lam time initial)‖ ^ 2 / lam ^ 2)
      (𝓝[≠] 0)
      (𝓝 ((‖inner ℂ final (V initial)‖ ^ 2 / system.hbar ^ 2) *
        ‖OscillatoryIntegral.timeIntegral ((energyFinal - energyInitial) / system.hbar) time‖ ^ 2)) := by
  have hbound : ∀ s ∈ Icc (0 : ℝ) time,
      ‖timeDependentInteractionPerturbation (freePropagatorGroup system) (fun _ => V) s‖ ≤ ‖V‖ := by
    intro s _
    exact (norm_heisenbergEvolution (freePropagatorGroup system) V s).le
  have hlimit := tendsto_timeDependentTransitionWeight_div_sq_zero_of_bound
    (freePropagatorGroup system) system.hbar initial final horthogonal
    (norm_nonneg V) hbound ⟨htime, le_rfl⟩
  rw [staticTransitionFirstVariation_eq_timeIntegral system initial final
    energyInitial energyFinal hinitial hfinal V time] at hlimit
  have hvalue :
      (‖inner ℂ final (V initial)‖ ^ 2 / system.hbar ^ 2) *
          ‖OscillatoryIntegral.timeIntegral
            ((energyFinal - energyInitial) / system.hbar) time‖ ^ 2 =
        ‖(-(Complex.I / (system.hbar : ℂ))) *
          OscillatoryIntegral.timeIntegral ((energyFinal - energyInitial) / system.hbar) time *
            inner ℂ final (V initial)‖ ^ 2 := by
    simp only [norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, div_pow, one_pow, sq_abs]
    ring
  rw [hvalue]
  exact hlimit

end
end QuantumTheory.LinearResponse
