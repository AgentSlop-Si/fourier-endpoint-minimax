#!/usr/bin/env python3
"""
Standalone exact verification script (Python 3 standard library only) for:
  "Fourier Endpoint Minimax and Autocorrelation-Deficit Rank Bounds
   for Finite Abelian Character Tables"

All matrix ranks are computed in exact cyclotomic fields Q[x]/(Phi_N(x))
using exact integer/rational polynomial arithmetic (zero floating point).
"""

from __future__ import annotations

import itertools
import math
from fractions import Fraction


# ---- Exact polynomial & cyclotomic-field arithmetic over Q ----

def poly_trim(a: list[Fraction]) -> list[Fraction]:
    res = list(a)
    while len(res) > 1 and res[-1] == 0:
        res.pop()
    return res


def poly_add(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    n = max(len(a), len(b))
    out = [Fraction(0)] * n
    for i in range(len(a)):
        out[i] += a[i]
    for i in range(len(b)):
        out[i] += b[i]
    return poly_trim(out)


def poly_sub(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    n = max(len(a), len(b))
    out = [Fraction(0)] * n
    for i in range(len(a)):
        out[i] += a[i]
    for i in range(len(b)):
        out[i] -= b[i]
    return poly_trim(out)


def poly_mul(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca:
            for j, cb in enumerate(b):
                if cb:
                    out[i + j] += ca * cb
    return poly_trim(out)


def poly_divmod(a: list[Fraction], b: list[Fraction]) -> tuple[list[Fraction], list[Fraction]]:
    a = poly_trim(a)
    b = poly_trim(b)
    db = len(b) - 1
    if len(a) - 1 < db:
        return [Fraction(0)], a
    q = [Fraction(0)] * (len(a) - db)
    rem = list(a)
    lcb = b[-1]
    for i in range(len(a) - 1, db - 1, -1):
        c = rem[i] / lcb
        q[i - db] = c
        if c:
            for j in range(db + 1):
                rem[i - db + j] -= c * b[j]
    return poly_trim(q), poly_trim(rem)


def poly_mod(a: list[Fraction], m: list[Fraction]) -> list[Fraction]:
    _, r = poly_divmod(a, m)
    return r


def poly_inv_mod(a: list[Fraction], m: list[Fraction]) -> list[Fraction]:
    """Extended Euclidean inverse of nonzero a modulo irreducible m over Q."""
    r0, r1 = poly_trim(m), poly_mod(a, m)
    t0, t1 = [Fraction(0)], [Fraction(1)]
    while not (len(r1) == 1 and r1[0] == 0):
        q, r2 = poly_divmod(r0, r1)
        r0, r1 = r1, r2
        t0, t1 = t1, poly_sub(t0, poly_mul(q, t1))
    assert len(r0) == 1 and r0[0] != 0, "Element not invertible modulo Phi_N"
    inv_c = Fraction(1) / r0[0]
    return poly_mod([c * inv_c for c in t0], m)


def cyclotomic_poly(n: int) -> list[Fraction]:
    """Exact n-th cyclotomic polynomial Phi_n(x) over Q."""
    # x^n - 1 divided by Phi_d for proper divisors d | n
    num = [Fraction(0)] * (n + 1)
    num[0] = Fraction(-1)
    num[n] = Fraction(1)
    for d in range(1, n):
        if n % d == 0:
            num, rem = poly_divmod(num, cyclotomic_poly(d))
            assert rem == [Fraction(0)]
    return num


class CyclotomicField:
    def __init__(self, n: int) -> None:
        self.n = n
        self.phi = cyclotomic_poly(n)
        self.deg = len(self.phi) - 1
        self.zero = [Fraction(0)]
        self.one = [Fraction(1)]
        # Precompute zeta^e mod Phi_n for 0 <= e < n
        self.pows: list[list[Fraction]] = []
        for e in range(n):
            mon = [Fraction(0)] * (e + 1)
            mon[e] = Fraction(1)
            self.pows.append(poly_mod(mon, self.phi))

    def is_zero(self, a: list[Fraction]) -> bool:
        return len(a) == 1 and a[0] == 0

    def add(self, a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
        return poly_add(a, b)

    def sub(self, a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
        return poly_sub(a, b)

    def mul(self, a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
        return poly_mod(poly_mul(a, b), self.phi)

    def inv(self, a: list[Fraction]) -> list[Fraction]:
        return poly_inv_mod(a, self.phi)

    def rank(self, mat: list[list[list[Fraction]]]) -> int:
        if not mat or not mat[0]:
            return 0
        m = len(mat)
        n = len(mat[0])
        A = [[list(x) for x in row] for row in mat]
        r = 0
        for col in range(n):
            piv = None
            for i in range(r, m):
                if not self.is_zero(A[i][col]):
                    piv = i
                    break
            if piv is None:
                continue
            A[r], A[piv] = A[piv], A[r]
            inv_p = self.inv(A[r][col])
            for j in range(col, n):
                A[r][j] = self.mul(A[r][j], inv_p)
            for i in range(r + 1, m):
                if not self.is_zero(A[i][col]):
                    fac = A[i][col]
                    for j in range(col, n):
                        A[i][j] = self.sub(A[i][j], self.mul(fac, A[r][j]))
            r += 1
            if r == m:
                break
        return r


def bitrev(j: int, m: int) -> int:
    out = 0
    for _ in range(m):
        out = (out << 1) | (j & 1)
        j >>= 1
    return out


def r_rec(m: int, k: int) -> int:
    N = 1 << m
    if k == 0 or k == N:
        return 0
    if m == 1:
        return 1
    if k > N // 2:
        return r_rec(m, N - k)
    return (k + 1) // 2 + r_rec(m - 2, k // 2)


# ---- 1. Verify exact bit-reversal cut profiles & half-squares at N = 1, 2, 4, 8, 16 ----
def verify_bitrev_and_half_squares() -> None:
    expected_q = {1: 0, 2: 1, 4: 1, 8: 3, 16: 5}
    expected_s = {1: 0, 2: 1, 4: 3, 8: 14, 16: 48}
    for m in range(5):
        N = 1 << m
        K = CyclotomicField(N)
        perm = [bitrev(i, m) for i in range(N)]
        Q = [[K.pows[(perm[i] * perm[j]) % N] for j in range(N)] for i in range(N)]
        prof = []
        for k in range(1, N):
            sub_u = [Q[i][k:N] for i in range(k)]
            sub_l = [Q[i][0:k] for i in range(k, N)]
            ru = K.rank(sub_u)
            rl = K.rank(sub_l)
            assert ru == rl == r_rec(m, k), (N, k, ru, rl, r_rec(m, k))
            prof.append(ru)
        q_val = max(prof) if prof else 0
        s_val = sum(prof)
        assert q_val == expected_q[N] and s_val == expected_s[N], (N, q_val, s_val)
        # Verify reflection
        for k in range(1, N):
            assert prof[k - 1] == prof[N - 1 - k]
        # Verify even-even half-square has exact rank N/4 for N >= 4
        if N >= 4:
            evens = list(range(0, N, 2))
            F_ee = [[K.pows[(a * b) % N] for b in evens] for a in evens]
            assert K.rank(F_ee) == N // 4
    print("  [PASS] Exact cyclotomic-field bit-reversal cuts & half-squares verified for N in {1,2,4,8,16}")


# ---- 2. Exhaustive F_8 critical 3x5 blocks (3,136) and 4x4 half-squares (4,900) ----
def verify_F8_exhaustive() -> None:
    N = 8
    K = CyclotomicField(N)
    # Precompute full F_8 over Q[x]/(x^4 + 1)
    F = [[K.pows[(a * b) % N] for b in range(N)] for a in range(N)]

    # Fast integer row-reduction in Z[x]/(x^4 + 1) via Q-fractions:
    # 3x5 blocks: 56 * 56 = 3136 blocks
    cnt_3x5 = 0
    for R in itertools.combinations(range(N), 3):
        for H in itertools.combinations(range(N), 5):
            sub = [[F[r][c] for c in H] for r in R]
            rk = K.rank(sub)
            assert rk == 3, (R, H, rk)
            cnt_3x5 += 1
    assert cnt_3x5 == 3136

    # 4x4 blocks: 70 * 70 = 4900 blocks
    dist = {2: 0, 3: 0, 4: 0}
    for R in itertools.combinations(range(N), 4):
        for H in itertools.combinations(range(N), 4):
            sub = [[F[r][c] for c in H] for r in R]
            rk = K.rank(sub)
            assert rk in dist, (R, H, rk)
            dist[rk] += 1
    assert dist == {2: 20, 3: 576, 4: 4304}, dist
    print("  [PASS] F_8 exhaustive: all 3,136 critical 3x5 blocks have rank 3; 4,900 4x4 blocks -> {2:20, 3:576, 4:4304}")


# ---- 3. Exhaustive finite abelian autocorrelation-deficit checks on C2xC2, C3, C4, C6 ----
def verify_small_abelian_groups() -> None:
    # Represent group elements as tuples; exponent e is LCM of orders
    groups = [
        ("C2xC2", [(0, 0), (0, 1), (1, 0), (1, 1)], (2, 2), 2),
        ("C3", [(0,), (1,), (2,)], (3,), 3),
        ("C4", [(0,), (1,), (2,), (3,)], (4,), 4),
        ("C6", [(0,), (1,), (2,), (3,), (4,), (5,)], (6,), 6),
    ]
    total_rects = 0
    strict_imps = {}
    for name, elems, mods, exp in groups:
        N = len(elems)
        K = CyclotomicField(exp)

        def g_add(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
            return tuple((xi + yi) % mi for xi, yi, mi in zip(x, y, mods))

        def g_sub(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
            return tuple((xi - yi) % mi for xi, yi, mi in zip(x, y, mods))

        def pairing(chi: tuple[int, ...], x: tuple[int, ...]) -> int:
            acc = 0
            for ci, xi, mi in zip(chi, x, mods):
                acc += (ci * xi) * (exp // mi)
            return acc % exp

        F = [[K.pows[pairing(chi, x)] for x in elems] for chi in elems]
        zero_el = tuple(0 for _ in mods)

        # All nonempty subsets of [N]
        subsets = [
            list(comb)
            for sz in range(1, N + 1)
            for comb in itertools.combinations(range(N), sz)
        ]
        # Precompute c_H(s) and d_H for every nonempty subset
        d_map: dict[tuple[int, ...], int] = {}
        c_map: dict[tuple[int, ...], dict[tuple[int, ...], int]] = {}
        for H in subsets:
            H_set = {elems[i] for i in H}
            cs = {}
            max_nz = 0
            for s in elems:
                ov = sum(1 for x in H_set if g_add(x, s) in H_set)
                cs[s] = ov
                if s != zero_el and ov > max_nz:
                    max_nz = ov
            key = tuple(H)
            c_map[key] = cs
            d_map[key] = len(H) - max_nz

        # Precompute |f_I(s)|^2 in Q for every subset I (including empty)
        fI_sq: dict[tuple[int, ...], dict[tuple[int, ...], Fraction]] = {}
        for sz in range(0, N + 1):
            for I in itertools.combinations(range(N), sz):
                sq_s = {}
                for s in elems:
                    # f_I(s) = sum_{chi in I} zeta^{<chi, s>}
                    val = K.zero
                    conj = K.zero
                    for i in I:
                        e = pairing(elems[i], s)
                        val = K.add(val, K.pows[e])
                        conj = K.add(conj, K.pows[(-e) % exp])
                    prod = K.mul(val, conj)
                    assert len(prod) == 1, f"|f_I(s)|^2 not rational: {prod}"
                    sq_s[s] = prod[0]
                fI_sq[I] = sq_s

        imp_cnt = 0
        for R in subsets:
            r = len(R)
            I = tuple(i for i in range(N) if i not in R)
            for H in subsets:
                h = len(H)
                total_rects += 1
                dH = d_map[tuple(H)]
                BH = Fraction(h * (N - r), N) - Fraction(dH * r * (N - r), N * N)
                # Direct exact tr(A^2) from A_xy = (1/N) f_I(y - x)
                cs = c_map[tuple(H)]
                tr_moment = sum(cs[s] * fI_sq[I][s] for s in elems) / (N * N)
                assert tr_moment <= BH, (name, R, H, tr_moment, BH)

                # Verify directly from A = (1/N) F[I,H]^* F[I,H] (tr(A^2) = sum_{x,y} |A_xy|^2)
                tr_direct = Fraction(0)
                for x in H:
                    for y in H:
                        diff = g_sub(elems[y], elems[x])
                        tr_direct += fI_sq[I][diff]
                tr_direct /= (N * N)
                assert tr_direct == tr_moment

                # Exact cyclotomic-field rank check
                sub = [[F[i][j] for j in H] for i in R]
                rk = K.rank(sub)
                lb = math.ceil(Fraction(r * h, N) + Fraction(dH * r * (N - r), N * N))
                base_lb = math.ceil(Fraction(r * h, N))
                assert rk >= lb, (name, R, H, rk, lb)
                if lb > base_lb:
                    imp_cnt += 1
        strict_imps[name] = imp_cnt
    assert total_rects == 225 + 49 + 225 + 3969 == 4468
    assert strict_imps == {"C2xC2": 0, "C3": 0, "C4": 24, "C6": 1020}, strict_imps
    print(f"  [PASS] All {total_rects:,} nonempty rectangles over C2xC2, C3, C4, C6 passed; strict improvements: {strict_imps}")


# ---- 4. Exact rational B_L, cut-rank sums S_N, N=64/s=21 example, and N=32 gap ----
def verify_rational_identities() -> None:
    # N=64, s=21 example
    val = Fraction(21 * 21, 64) + Fraction(21 * (64 - 21), 64 * 64)
    assert val == Fraction(29127, 4096) and math.ceil(val) == 8 and math.ceil(Fraction(441, 64)) == 7

    # Exact B_L < L + 1 and S_N closed form for m = 0..12 (N up to 4096)
    S_prev = {0: 0, 1: 1}
    for m in range(0, 13):
        N = 1 << m
        if m >= 3:
            L = N // 4
            h = 2 * L + 1
            BL = Fraction(h**3 + (h - 1) * (N * h - h**2), N * N)
            BL_form = Fraction(L) + Fraction(3, 4) + Fraction(1, 4 * L) + Fraction(1, 16 * L * L)
            assert BL == BL_form and BL < L + 1
        if m >= 2:
            S_prev[m] = (N * N) // 8 + N // 4 + 4 * S_prev[m - 2]
        if m % 2 == 0:
            S_closed = Fraction(N * N, 6) + N * (Fraction(m, 8) - Fraction(1, 6))
        else:
            S_closed = Fraction(N * N, 6) + N * (Fraction(m, 8) + Fraction(1, 24))
        assert S_closed.denominator == 1 and int(S_closed) == S_prev[m]
        # Compare against direct sum of r_rec(m, k)
        s_direct = sum(r_rec(m, k) for k in range(1, N))
        assert s_direct == S_prev[m]
        # Pointwise lower sum
        lb_sum = 0
        for k in range(1, N):
            if k % 2 == 1:
                lb_sum += math.ceil(Fraction(k * (N - k) * (N + 1), N * N))
            else:
                lb_sum += math.ceil(Fraction(k * (N - k), N))
        assert lb_sum <= S_prev[m]
        if N in (1, 2, 4, 8, 16):
            assert lb_sum == S_prev[m]
        if N == 32:
            assert lb_sum == 182 and S_prev[m] == 192
    print("  [PASS] Exact rational B_L < L+1, closed-form S_N, N=64/s=21 (29127/4096 -> 8), and N=32 (182 vs 192) verified through N=4096")


def main() -> None:
    print("Running exact verification for Paper 4 (Fourier Endpoint Minimax & Deficit Rank Bounds)...")
    verify_bitrev_and_half_squares()
    verify_F8_exhaustive()
    verify_small_abelian_groups()
    verify_rational_identities()
    print("ALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
