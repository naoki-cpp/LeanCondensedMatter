import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Spinful
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedOneBodyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CorrectedCurrentResponse
import LeanCondensedMatter.QuantumTheory.LinearResponse.ResponseChannel

set_option linter.style.header false

/-!
# Finite polarized spin-current / electric-source cross response

This module gives a concrete generalized-current response on the finite spinful lattice
`Site × Fin 2`. For a chosen spatial flow direction represented by a supplied one-particle velocity
`v_d`, and an arbitrary real spin polarization `p`, the measured conventional spin current is

```text
J_d^(S_p) = dΓ( 1/2 {v_d, S_p} ),
S_p = (s/2) p · σ.
```

The electric source is an oriented bond current, so the response kernel is genuinely mixed:

```text
χᴿ_{J_d^(S_p), J^charge_{u→v}}.
```

The flow direction is intentionally encoded by the supplied velocity operator rather than by a
repository-wide geometric direction type: finite lattices need not carry Euclidean coordinates.
Likewise, the oriented source bond `u → v` remains explicit. A concrete Rashba or Dirac model can
therefore supply any directional velocity or linear combination of directional velocities without
changing this response API.

The current density above is the existing general symmetrized-velocity current with transported
quantity `m = S_p`, not an independent definition. The general current theory therefore gives

```text
intrinsic current = conventional current + localization correction,
J_corr(α) = 1/4 [v_d, [N α, S_p]].
```

Thus the conventional spin current represents the intrinsic transport whenever the chosen localizer
evolution is represented by `v_d` and `[N α, S_p] = 0` for every localizer one-form `α`. No
condition `[v_d, S_p] = 0` is required.

No equality between spin current and charge current is assumed. Conductivity normalization and
source-dependent contact terms remain separate from this causal cross-response kernel. The
conventional-current/proper-current distinction is motivated by Shi, Zhang, Xiao, and Niu,
*Phys. Rev. Lett.* **96**, 076604 (2006),
[doi:10.1103/PhysRevLett.96.076604](https://doi.org/10.1103/PhysRevLett.96.076604); this module does
not identify the conventional operator with their torque-dipole-completed current. The finite Rashba,
disorder-vertex, and inverse-response follow-ups are tracked in `notes/roadmaps/spin-hall.md`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- One-body conventional spin-current density for an arbitrary polarization and supplied
flow-direction velocity.

This is not a separate spin-current axiom: it is the generic conservation-law symmetrized current
specialized to the transported quantity `S_p`. The corrected-current response layer can therefore
consume it without introducing a second spin-specific current theory. -/
noncomputable def spinCurrentOneBody
    (velocity : LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site))
    (spinScale : ℝ) (polarization : InternalSpace.PauliAxis → ℝ) :
    LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site) :=
  _root_.ConservationLaw.symmetrizedProduct
    velocity
    (spinPolarizationOneBody spinScale polarization)

/-- Bounded second-quantized realization of `spinCurrentOneBody`. -/
noncomputable def boundedSpinCurrent
    (velocity : LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site))
    (spinScale : ℝ) (polarization : InternalSpace.PauliAxis → ℝ) :
    FiniteLatticeHilbertFock (SpinfulSite Site) →L[ℂ]
      FiniteLatticeHilbertFock (SpinfulSite Site) :=
  boundedOneBodyOperator (spinCurrentOneBody velocity spinScale polarization)


/-- Intrinsic exact-flux spin response reduces to the conventional spin-current flux whenever the
chosen localizers commute with the transported spin polarization.

This is the spin specialization of the generic corrected-current theorem. It deliberately keeps the
two hypotheses that carry physical content: `hΦ` identifies the intrinsic transport with the nested
current functional, while `hcomm` states that localization acts independently of the internal spin
observable. No commutation of `velocity` with spin is assumed. -/
theorem boundedIntrinsicSpinFluxRetardedResponse_eq_conventional_of_commutes
    {Test OneForm : Type*}
    [AddCommGroup Test] [Module ℂ Test]
    [AddCommGroup OneForm] [Module ℂ OneForm]
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (source : FiniteLatticeHilbertFock (SpinfulSite Site) →L[ℂ]
      FiniteLatticeHilbertFock (SpinfulSite Site))
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ]
      (LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site)))
    (velocity : LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site))
    (spinScale : ℝ) (polarization : InternalSpace.PauliAxis → ℝ)
    (N : OneForm →ₗ[ℂ]
      (LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site)))
    (hΦ : _root_.ConservationLaw.FactorsThroughDifferential d Φ
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        (LatticeState (SpinfulSite Site))
        velocity (spinPolarizationOneBody spinScale polarization) N))
    (hcomm : ∀ α, _root_.ConservationLaw.linearCommutator
      (N α) (spinPolarizationOneBody spinScale polarization) = 0)
    (t s : ℝ) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s =
      (boundedConventionalCurrentFluxRetardedResponse
        system expectation source velocity
        (spinPolarizationOneBody spinScale polarization) N t s).comp d :=
  boundedIntrinsicFluxRetardedResponse_eq_conventional_of_commutes
    system expectation source d Φ velocity
    (spinPolarizationOneBody spinScale polarization) N hΦ hcomm t s

/-- Neutral fixed-observable response channel for an arbitrarily polarized finite spin current
driven by an oriented electric bond-current source.

The measured-current direction is encoded by `velocity`; the spin polarization is encoded by
`polarization`; and the source direction is the oriented bond `u → v`. -/
noncomputable def boundedSpinCurrentBondSourceResponseChannel
    (velocity : LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site))
    (spinScale : ℝ) (polarization : InternalSpace.PauliAxis → ℝ)
    (ℏ q : ℂ)
    (K : LocallyFiniteHopping (SpinfulSite Site))
    (u v : SpinfulSite Site) :
    ResponseChannel (FiniteLatticeHilbertFock (SpinfulSite Site)) :=
  ResponseChannel.fixed
    (boundedSpinCurrent velocity spinScale polarization)
    (boundedBondCurrent ℏ q K u v)

/-- Retarded response of an arbitrarily polarized finite spin current to an oriented electric
bond-current source. -/
noncomputable def boundedSpinCurrentBondSourceRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (velocity : LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site))
    (spinScale : ℝ) (polarization : InternalSpace.PauliAxis → ℝ)
    (ℏ q : ℂ)
    (K : LocallyFiniteHopping (SpinfulSite Site))
    (u v : SpinfulSite Site) (t s : ℝ) : ℂ :=
  (boundedSpinCurrentBondSourceResponseChannel
      velocity spinScale polarization ℏ q K u v).retardedKernel
    system expectation t s

end
end Transport
end Fermionic
end SecondQuantization
