#!/usr/bin/env python3
"""Numerical reference for the finite Rashba proper-spin response (NumPy).

One electron in the lowest energy orbital of a 2 x 3 open rectangle.
All operators are number-conserving one-body lifts; the singleton occupation
sector therefore suffices. This is not a Lean-certified numerical evaluation.
"""
from __future__ import annotations

import numpy as np


def comm(a, b):
    return a @ b - b @ a


def sym(a, b):
    return (a @ b + b @ a) / 2


def benchmark(soc: float = 0.5):
    sites = np.array([(x, y) for x in range(2) for y in range(3)])
    identity = np.eye(2, dtype=complex)
    sx = np.array([[0, 1], [1, 0]], dtype=complex)
    sy = np.array([[0, -1j], [1j, 0]])
    sz = np.diag([1, -1]).astype(complex)
    # hbar = q = spacing = t = 1, spinScale = 1/2, exchange = 1/2.
    # Same target-minus-source orientation as realSpaceRashbaHopping.
    h = np.kron(np.eye(len(sites)), 4 * identity + 0.5 * sz)
    for u, ru in enumerate(sites):
        for v, rv in enumerate(sites):
            dx, dy = ru - rv
            if (dx, dy) in ((1, 0), (0, 1)):
                block = -identity + 1j * soc * (dy * sx - dx * sy)
                h[2*u:2*u+2, 2*v:2*v+2] = block
                h[2*v:2*v+2, 2*u:2*u+2] = block.conj().T
    x = np.kron(np.diag(sites[:, 0] - 0.5), identity)
    y = np.kron(np.diag(sites[:, 1] - 1), identity)
    s = np.kron(np.eye(len(sites)), sz / 2)
    omega, eta, volume = 0.7, 0.2, 6.0
    z = 1j * omega - eta
    np.testing.assert_allclose(h, h.conj().T, atol=1e-12)
    energy, basis = np.linalg.eigh(h)
    assert energy[1] - energy[0] > 1e-8
    p = np.zeros(len(energy))
    p[0] = 1
    gap = energy[:, None] - energy[None, :]
    weight = 1j * (p[:, None] - p[None, :]) / (eta - 1j * (omega + gap))

    def in_energy(a):
        return basis.conj().T @ a @ basis

    def response(measured, source):
        return np.sum(weight * in_energy(measured) * in_energy(source).T)

    result = {}
    for label, measured, source in (("yx", y, x), ("xy", x, y)):
        d = sym(measured, s)
        b = 1j * comm(h, source)
        j = 1j * comm(h, d)
        contact = 1j * comm(-b, d)
        conventional = sym(1j * comm(h, measured), s)
        torque = sym(measured, 1j * comm(h, s))
        np.testing.assert_allclose(j, conventional + torque, atol=1e-12)
        for operator in (d, b, j, contact, conventional, torque):
            np.testing.assert_allclose(operator, operator.conj().T, atol=1e-12)
        c = in_energy(contact)[0, 0]
        # Check the derivative of the actual Peierls family independently.
        coord = np.diag(source).real
        diff = coord[:, None] - coord[None, :]
        eps = 1e-5
        hp = h * np.exp(1j * eps * diff)
        hm = h * np.exp(-1j * eps * diff)
        np.testing.assert_allclose((hp - hm) / (2 * eps), -b, atol=1e-9)
        np.testing.assert_allclose(1j * comm((hp - hm) / (2 * eps), d), contact, atol=1e-9)
        direct = (response(j, b) + c) / (volume * z)
        displacement = -response(d, b) / volume
        np.testing.assert_allclose(direct, displacement, atol=1e-12, rtol=1e-10)
        result[label] = (displacement, response(conventional, b) / (volume * z),
                         response(torque, b) / (volume * z), c)
    return result


def main():
    result = benchmark()
    for label, (proper, conventional, torque, contact) in result.items():
        print(f"sigma_{label}^z = {proper:.12g}; conventional retarded = {conventional:.12g}; "
              f"torque retarded = {torque:.12g}; contact expectation = {contact:.3g}")
    assert abs(result["yx"][0]) > 1e-4
    assert abs(result["yx"][2]) > 1e-4
    assert abs((result["yx"][0] - result["xy"][0]) / 2) > 1e-4
    for proper, _, torque, _ in benchmark(soc=0).values():
        assert abs(proper) < 1e-10
        assert abs(torque) < 1e-10
    print("All numerical checks passed.")


if __name__ == "__main__":
    main()
