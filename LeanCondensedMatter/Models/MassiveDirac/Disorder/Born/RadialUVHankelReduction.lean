import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVBesselJ
import LeanCondensedMatter.Transport.Analysis.BesselYAnalyticWronskian
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.RCLike.Sqrt

set_option linter.style.header false

/-!
# Fixed-center Fourier UV boundary: causal Hankel branch reduction

This file records the correctly normalized proposed outgoing two-dimensional
Helmholtz resolvent and rigorously reduces its identification with the
existing fixed-center Fourier UV value to **one upper-half-plane, positive-
radius Fourier–Hankel transform identity**.

For an upper-half-plane quadratic center `s` the proposed result is

  ∫₀∞ 2π p J₀(pc)/(s-v²p²) dp
    = -(i π²/v²) (J₀(k r) + i Y₀(k r)),

where `r=|c|` and `k=√s/|v|`, with the *principal* complex square root
and the concrete DLMF Y₀ series. Here the integral denotes the already
constructed oscillatory UV limit, not an absolutely convergent raw integral.
The outgoing identity itself requires a contour/resolvent transform theorem
that is not in Mathlib, and **is not asserted or assumed unconditionally**.

The existing evenness and Schwarz reflection of the Fourier UV value
show that it suffices to prove the upper-half-plane identity at r>0.
The lower-half-plane incoming candidate is defined as the reflection of
the upper-half-plane outgoing candidate, avoiding an unjustified
choice of analytic continuation across the negative-real Bessel cut.

This module does not change Born self-energy, take its running UV cutoff,
exchange real-space limits, or evaluate physical crossed X/Psi diagrams.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open scoped ComplexConjugate

/-- Dimensionless Bessel argument `√s |c| / |v|` for a fixed quadratic
spectral center. The absolute values are essential: the radial UV Fourier
kernel depends only on `v²` and `|c|`. -/
noncomputable def massiveDiracRadialHankelArgument
    (v c : ℝ) (center : ℂ) : ℂ :=
  Complex.sqrt center * (((|c| / |v| : ℝ) : ℂ))

/-- The outgoing first-kind, order-zero Hankel *candidate* for the
unrenormalized fixed-center UV radial Fourier transform, in the
Fourier convention with full angular factor `2π J₀`.
The formula uses the concrete entire-plus-logarithm Y₀ series.
This definition alone does not establish equality with the Fourier UV integral. -/
noncomputable def massiveDiracRadialOutgoingHankelCandidate
    (v c : ℝ) (center : ℂ) : ℂ :=
  (-(Complex.I * (((Real.pi : ℝ) : ℂ) ^ 2 / (v : ℂ) ^ 2))) *
    (Complex.besselJ 0 (massiveDiracRadialHankelArgument v c center) +
      Complex.I * besselY0Series (massiveDiracRadialHankelArgument v c center))

/-- Advanced/incoming candidate obtained by *causal reflection* from
the upper-half-plane outgoing expression. This definition preserves the
square-root and logarithmic branches and does not silently equate
`conj (Y₀ z)` with `Y₀ (conj z)` on the branch cut. -/
noncomputable def massiveDiracRadialIncomingHankelCandidate
    (v c : ℝ) (center : ℂ) : ℂ :=
  conj (massiveDiracRadialOutgoingHankelCandidate v c (conj center))

/-- Outgoing Bessel/Hankel reference depends on radius only through
`|c|`, just like the exact finite-cutoff Fourier transform. -/
theorem massiveDiracRadialOutgoingHankelCandidate_neg
    (v c : ℝ) (center : ℂ) :
    massiveDiracRadialOutgoingHankelCandidate v (-c) center =
      massiveDiracRadialOutgoingHankelCandidate v c center := by
  simp [massiveDiracRadialOutgoingHankelCandidate,
    massiveDiracRadialHankelArgument, abs_neg]

/-- The advanced candidate inherits the same radial parity. -/
theorem massiveDiracRadialIncomingHankelCandidate_neg
    (v c : ℝ) (center : ℂ) :
    massiveDiracRadialIncomingHankelCandidate v (-c) center =
      massiveDiracRadialIncomingHankelCandidate v c center := by
  simp only [massiveDiracRadialIncomingHankelCandidate,
    massiveDiracRadialOutgoingHankelCandidate_neg]

/-- The *only genuinely new* Fourier–Hankel integral identity needed
for a fixed velocity is the upper-half-plane identity at positive radius.
This is an explicit proposition, not an axiom and not proved here. -/
def MassiveDiracUpperHalfPlaneHankelTransform (v : ℝ) : Prop :=
  ∀ (radius : ℝ) (center : ℂ), 0 < radius → 0 < center.im →
    massiveDiracRadialFourierUVCenter v radius center =
      massiveDiracRadialOutgoingHankelCandidate v radius center

/-- If the upper-half-plane Fourier–Hankel identity is established at
positive radius, the result extends to *both signs* of every nonzero
real radius by the already-proved Fourier parity. -/
theorem massiveDiracRadialFourierUVCenter_eq_outgoing_of_upper
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hupperCenter : 0 < center.im)
    (hupper : MassiveDiracUpperHalfPlaneHankelTransform v) :
    massiveDiracRadialFourierUVCenter v c center =
      massiveDiracRadialOutgoingHankelCandidate v c center := by
  by_cases hcpos : 0 ≤ c
  · have hcstrict : 0 < c := lt_of_le_of_ne hcpos (Ne.symm hc)
    exact hupper c center hcstrict hupperCenter
  · have hcneg : c < 0 := lt_of_not_ge hcpos
    have hpositive : 0 < -c := neg_pos.mpr hcneg
    have hreference := hupper (-c) center hpositive hupperCenter
    calc
      massiveDiracRadialFourierUVCenter v c center =
          massiveDiracRadialFourierUVCenter v (-c) center := by
        exact (massiveDiracRadialFourierUVCenter_neg
          v c center hv hc (ne_of_gt hupperCenter)).symm
      _ = massiveDiracRadialOutgoingHankelCandidate v (-c) center :=
        hreference
      _ = massiveDiracRadialOutgoingHankelCandidate v c center :=
        massiveDiracRadialOutgoingHankelCandidate_neg v c center

/-- The advanced/lower-half-plane fixed-center transform follows
*without another contour integral*: Schwarz reflection of the exact
Fourier UV boundary turns the upper outgoing expression into the
lower incoming expression. -/
theorem massiveDiracRadialFourierUVCenter_eq_incoming_of_upper
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hlowerCenter : center.im < 0)
    (hupper : MassiveDiracUpperHalfPlaneHankelTransform v) :
    massiveDiracRadialFourierUVCenter v c center =
      massiveDiracRadialIncomingHankelCandidate v c center := by
  have hconjIm : 0 < (conj center).im := by
    rw [Complex.conj_im]
    exact neg_pos.mpr hlowerCenter
  have hupperReflected :=
    massiveDiracRadialFourierUVCenter_eq_outgoing_of_upper
      v c (conj center) hv hc hconjIm hupper
  have hreflection :=
    massiveDiracRadialFourierUVCenter_conj
      v c (conj center) hv hc (ne_of_gt hconjIm)
  calc
    massiveDiracRadialFourierUVCenter v c center =
        conj (massiveDiracRadialFourierUVCenter v c (conj center)) := by
      simpa using hreflection.symm
    _ = conj (massiveDiracRadialOutgoingHankelCandidate v c (conj center)) :=
      congrArg conj hupperReflected
    _ = massiveDiracRadialIncomingHankelCandidate v c center := rfl

/-- Fixed-center causal Fourier–Hankel formula for nonreal quadratic
spectral center, *conditional only on the single upper branch identity*.
Both the lower branch and negative radius are reduced to already
proved symmetries. -/
theorem massiveDiracRadialFourierUVCenter_eq_causalHankel_of_upper
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hcenter : center.im ≠ 0)
    (hupper : MassiveDiracUpperHalfPlaneHankelTransform v) :
    massiveDiracRadialFourierUVCenter v c center =
      if 0 < center.im then
        massiveDiracRadialOutgoingHankelCandidate v c center
      else massiveDiracRadialIncomingHankelCandidate v c center := by
  by_cases him : 0 < center.im
  · simpa [him] using
      (massiveDiracRadialFourierUVCenter_eq_outgoing_of_upper
        v c center hv hc him hupper)
  · have hlower : center.im < 0 := by
      have hle : center.im ≤ 0 := le_of_not_gt him
      exact lt_of_le_of_ne hle hcenter
    simpa [him] using
      (massiveDiracRadialFourierUVCenter_eq_incoming_of_upper
        v c center hv hc hlower hupper)

/-- **Exact logical reduction:** the Fourier UV limit equals the causal
Hankel expression for all nonreal centers and nonzero radii if and only
if the positive-radius upper-half-plane transform holds.
The forward implication specializes; the reverse uses parity and
Schwarz reflection. No Fourier–Hankel integral is assumed proved. -/
theorem massiveDiracRadialFourierUVCenter_causalHankel_iff_upper
    (v : ℝ) (hv : v ≠ 0) :
    (∀ (c : ℝ) (center : ℂ), c ≠ 0 → center.im ≠ 0 →
      massiveDiracRadialFourierUVCenter v c center =
        if 0 < center.im then
          massiveDiracRadialOutgoingHankelCandidate v c center
        else massiveDiracRadialIncomingHankelCandidate v c center) ↔
      MassiveDiracUpperHalfPlaneHankelTransform v := by
  constructor
  · intro h c center hc him
    have hresult := h c center (ne_of_gt hc) (ne_of_gt him)
    simpa [him] using hresult
  · intro h c center hc him
    exact massiveDiracRadialFourierUVCenter_eq_causalHankel_of_upper
      v c center hv hc him h

end

end QuantumTheory.Models.MassiveDirac
