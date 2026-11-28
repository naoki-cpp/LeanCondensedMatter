#!/usr/bin/env python3
"""Exact modular certificate for the centered 2 x 3 Rashba reference (SymPy).

This checks the explicit Gaussian-rational matrix, not the equality between
that matrix and the Lean hopping operator. No floating-point arithmetic,
numerical eigensolver, or eigenvector approximation is used.
"""
from itertools import product

from sympy import Matrix, Poly, Symbol, eye, gcd, trace, zeros

P = 101
I = 10  # image of the Gaussian unit: I**2 = -1 mod P
N = 12


def mod(matrix):
    return matrix.applyfunc(lambda x: int(x) % P)


def benchmark_matrices():
    """Reduce M = 2H, centered X, D = Y sigma_z/2, B = i[H,X]."""
    sites = list(product(range(2), range(3)))
    m, x, d = zeros(N), zeros(N), zeros(N)
    half = pow(2, -1, P)
    for u, (ux, uy) in enumerate(sites):
        for a in range(2):
            spin = 1 if a == 0 else -1
            m[2*u+a, 2*u+a] = 8 + spin
            x[2*u+a, 2*u+a] = ux - half
            d[2*u+a, 2*u+a] = (uy - 1) * spin * half
        for v, (vx, vy) in enumerate(sites):
            dx, dy = ux-vx, uy-vy
            if (dx, dy) in ((1, 0), (0, 1)):
                block = Matrix([[-2, I*dy-dx], [I*dy+dx, -2]])
                # Take the adjoint before reduction (i maps to -i under conjugation).
                reverse = Matrix([[-2, -I*dy+dx], [-I*dy-dx, -2]])
                m[2*u:2*u+2, 2*v:2*v+2] = block
                m[2*v:2*v+2, 2*u:2*u+2] = reverse
    m = mod(m)
    return m, mod(d), mod(I * half * (m*x-x*m))


def certificate():
    """Prove coprimality after reduction from Z[i, 1/10] to F_101.

    Let f(t) = det(t I - M), C(t) = adj(t I - M), s = 2(omega+i eta).
    A simple root lambda = 2E has eigenprojector C(lambda)/f'(lambda).
    The displacement formula gives sigma_yx = 2/(V f'(lambda)) times
      tr(C(lambda) D C(lambda+s) B)/f(lambda+s)
      + tr(C(lambda) B C(lambda-s) D)/f(lambda-s).
    Thus the numerator tested here is the common-denominator numerator
    of those two fractions. Its gcd with the monic f being 1 modulo P
    proves the corresponding resultant is nonzero over Q(i).
    The same argument with f' proves simplicity of the entire spectrum.
    For real lambda the shifted denominators are nonzero by Hermiticity
    and eta > 0; their modular gcd is also checked independently.
    """
    assert I**2 % P == P-1
    m, d, b = benchmark_matrices()
    t = Symbol("t")
    f = Poly(m.charpoly(t).as_expr(), t, modulus=P)
    assert gcd(f, f.diff()).is_one
    # C(t) = sum_k t**(N-1-k) C_k, by the characteristic polynomial.
    coeff = [eye(N)]
    for c in f.all_coeffs()[1:-1]:
        coeff.append(mod(m*coeff[-1] + c*eye(N)))
    shift = (7+2*I) * pow(5, -1, P) % P
    power = [Poly(t**(N-1-k), t, modulus=P) for k in range(N)]
    plus = [Poly((t+shift)**(N-1-k), t, modulus=P) for k in range(N)]
    minus = [Poly((t-shift)**(N-1-k), t, modulus=P) for k in range(N)]
    r1 = r2 = Poly(0, t, modulus=P)
    for k, j in product(range(N), repeat=2):
        a = int(trace(coeff[k]*d*coeff[j]*b)) % P
        c = int(trace(coeff[k]*b*coeff[j]*d)) % P
        r1 = (r1 + a*power[k]*plus[j]) % f
        r2 = (r2 + c*power[k]*minus[j]) % f
    fp = Poly(f.as_expr().subs(t, t+shift), t, modulus=P)
    fm = Poly(f.as_expr().subs(t, t-shift), t, modulus=P)
    numerator = (r1*fm + r2*fp) % f
    assert gcd(f, fp*fm).is_one
    assert gcd(f, numerator).is_one
    print("f mod 101:", f.as_expr())
    print("response numerator mod 101:", numerator.as_expr())
    print("All three gcds equal 1; exact matrix spectrum simple and response nonzero.")


if __name__ == "__main__":
    certificate()
