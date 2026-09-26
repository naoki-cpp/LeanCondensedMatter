import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Spinful
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.ConventionalCurrentResponse
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

/-- Bounded conventional spin current for an arbitrary polarization and supplied flow-direction
velocity on the finite spinful lattice. -/
noncomputable def boundedSpinCurrent
    (velocity : LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site))
    (spinScale : ℝ) (polarization : InternalSpace.PauliAxis → ℝ) :
    FiniteLatticeHilbertFock (SpinfulSite Site) →L[ℂ]
      FiniteLatticeHilbertFock (SpinfulSite Site) :=
  boundedConventionalCurrent velocity (spinPolarizationOneBody spinScale polarization)

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
