#!/usr/bin/env python3
"""Finite-grid reference evaluation of the regulated massive-Dirac radial Green kernel.

The angular kernel is the *original* K0(x) = integral_0^(2 pi) exp(i*x*cos(theta)) dtheta,
not a different Bessel/Hankel propagator. Both the radial Born self-energy
and the final real-space radial Fourier integral are approximated by
midpoint sums at the same *finite* momentum cutoff.

Physical conventions (matching the Lean model):
    z_s = energy + i * side * broadening
    J = integral_0^cutoff p / (z_s**2 - mass**2 - velocity**2*p**2) dp
    Sigma_0 = W * [2 pi / (2 pi hbar)**2] * z_s * J
    Sigma_z = W * [2 pi / (2 pi hbar)**2] * mass * J
    E_eff = z_s - Sigma_0; M_eff = mass + Sigma_z
    F_s(r) = [1/(2 pi hbar)**2] * integral_0^cutoff
             p * K0(p*r/hbar) / (E_eff**2-M_eff**2-v**2*p**2) dp

This is a numerical *reference* for the finite-grid implementation, not
a theorem about quadrature convergence, zero broadening, infinite cutoff,
or the crossed X/Psi Hall conductivity. No third-party packages required.
"""

from __future__ import annotations

import argparse
import cmath
from dataclasses import dataclass
import math


@dataclass(frozen=True)
class Parameters:
    velocity: float = 1.0
    mass: float = 0.45
    energy: float = 1.6
    broadening: float = 0.12
    disorder_strength: float = 0.05
    hbar: float = 1.0
    cutoff: float = 3.5
    radius: float = 1.2

    def validate(self) -> None:
        if self.velocity == 0 or self.hbar == 0:
            raise ValueError("velocity and hbar must be nonzero")
        if self.broadening <= 0 or self.cutoff < 0 or self.disorder_strength < 0:
            raise ValueError("require positive broadening and nonnegative cutoff/disorder")


def midpoint_grid(cutoff: float, count: int) -> tuple[float, list[float]]:
    if count < 1 or cutoff < 0:
        raise ValueError("require a positive cell count and nonnegative cutoff")
    step = cutoff / count
    return step, [step * (index + 0.5) for index in range(count)]


def angular_kernel_k0(argument: float, angular_count: int) -> complex:
    if angular_count < 4:
        raise ValueError("angular grid needs at least four points")
    step = 2 * math.pi / angular_count
    return step * sum(
        cmath.exp(1j * argument * math.cos(step * index))
        for index in range(angular_count)
    )


def regulated_radial_scalar_grid(
    params: Parameters, count: int, angular_count: int = 64, side: int = 1
) -> tuple[complex, complex, complex]:
    """Return (radial Green generator, scalar Born shift, z Born shift).

    side=+1: retarded; side=-1: advanced.
    All grids share the same finite momentum cutoff; neither limit is taken.
    """
    params.validate()
    if side not in (-1, 1):
        raise ValueError("side must be +1 (retarded) or -1 (advanced)")
    dp, momenta = midpoint_grid(params.cutoff, count)
    v, m, hbar = params.velocity, params.mass, params.hbar
    z = complex(params.energy, side * params.broadening)
    momentum_measure = 1 / (2 * math.pi * hbar) ** 2
    full_angle_measure = 2 * math.pi * momentum_measure

    # Same bare Dirac denominator and Born radial Jacobian as the Lean model.
    born_integral = dp * sum(
        p / (z * z - m * m - v * v * p * p) for p in momenta
    )
    scalar_shift = params.disorder_strength * full_angle_measure * z * born_integral
    z_shift = params.disorder_strength * full_angle_measure * m * born_integral

    effective_energy = z - scalar_shift
    effective_mass = m + z_shift
    generator = momentum_measure * dp * sum(
        p * angular_kernel_k0(p * params.radius / hbar, angular_count)
        / (effective_energy**2 - effective_mass**2 - v * v * p * p)
        for p in momenta
    )
    return generator, scalar_shift, z_shift


def self_check() -> None:
    params = Parameters()
    _, points = midpoint_grid(params.cutoff, 64)
    assert all(0 < p < params.cutoff for p in points)

    for x in (0.0, 0.3, 1.4):
        assert abs(angular_kernel_k0(x, 64) - angular_kernel_k0(-x, 64)) < 1e-12
    assert abs(angular_kernel_k0(0, 64) - 2 * math.pi) < 1e-12

    retarded = regulated_radial_scalar_grid(params, 128, side=1)
    advanced = regulated_radial_scalar_grid(params, 128, side=-1)
    assert all(abs(a.conjugate() - b) < 1e-12 for a, b in zip(retarded, advanced))

    clean = Parameters(disorder_strength=0)
    _, scalar_zero, mass_zero = regulated_radial_scalar_grid(clean, 128)
    assert scalar_zero == 0 and mass_zero == 0

    g64 = regulated_radial_scalar_grid(params, 64)[0]
    g128 = retarded[0]
    g256 = regulated_radial_scalar_grid(params, 256)[0]
    assert abs(g256 - g128) < abs(g128 - g64)
    assert abs(g256 - g128) < 2e-5

    # The numerical tests concern a fixed nonzero broadening and cutoff only.
    print("finite-grid checks passed (midpoints, angular parity, causal conjugation, clean limit, refinement)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="run deterministic numerical checks")
    parser.add_argument("--points", type=int, default=128)
    parser.add_argument("--angles", type=int, default=64)
    args = parser.parse_args()
    if args.check:
        self_check()
        return
    params = Parameters()
    value, sigma_scalar, sigma_z = regulated_radial_scalar_grid(
        params, args.points, args.angles
    )
    print(f"cutoff={params.cutoff:g}, eta={params.broadening:g}, W={params.disorder_strength:g}")
    print(f"grid={args.points} radial x {args.angles} angular")
    print(f"F_R({params.radius:g}) = {value}")
    print(f"Sigma_0 = {sigma_scalar}; Sigma_z = {sigma_z}")


if __name__ == "__main__":
    main()
