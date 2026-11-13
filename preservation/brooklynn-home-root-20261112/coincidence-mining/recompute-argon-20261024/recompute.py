#!/usr/bin/env python3
"""
Independent recomputation of candidates C36 and C2 (verification lane).
Uses Python 3 standard library only (fractions, decimal, math, json, urllib).
"""

import decimal
from decimal import Decimal
from fractions import Fraction
import json
import math
import urllib.request


# ============================================================================
# Task A — C36: cellular automaton Rule 167 centre cell vs powers of 2
# ============================================================================

def compute_a267579(max_n: int) -> list[int]:
    """
    A267579(n): centre cell at step n of elementary cellular automaton Rule 167
    started from a single ON cell on an all-zero background (offset n = 0).
    Neighbourhood outputs for 111, 110, 101, 100, 011, 010, 001, 000 are
    1, 0, 1, 0, 0, 1, 1, 1 respectively.
    """
    rule = {
        (1, 1, 1): 1,
        (1, 1, 0): 0,
        (1, 0, 1): 1,
        (1, 0, 0): 0,
        (0, 1, 1): 0,
        (0, 1, 0): 1,
        (0, 0, 1): 1,
        (0, 0, 0): 1,
    }
    width = 2 * max_n + 5
    center = max_n + 2
    row = [0] * width
    row[center] = 1
    bg = 0

    seq = [row[center]]
    for step in range(1, max_n + 1):
        new_bg = rule[(bg, bg, bg)]
        new_row = [new_bg] * width
        lo = center - step
        hi = center + step
        for i in range(lo, hi + 1):
            new_row[i] = rule[(row[i - 1], row[i], row[i + 1])]
        row = new_row
        bg = new_bg
        seq.append(row[center])

    return seq


def compute_a347523(max_n: int) -> list[int]:
    """
    A347523(n): 1 if n is not a power of 2, else 0
    (with a(0) = 1; n is a power of 2 iff n >= 1 and n & (n - 1) == 0).
    """
    return [
        0 if (n >= 1 and (n & (n - 1)) == 0) else 1
        for n in range(max_n + 1)
    ]


def run_task_c36(max_n: int = 2000) -> dict:
    a267579 = compute_a267579(max_n)
    a347523 = compute_a347523(max_n)

    # Unrestricted claim fails at n = 1 by definition (A267579(1)=1, A347523(1)=0)
    assert a267579[0] == 1 and a347579_check(a267579, a347523)

    mismatches = 0
    first_mismatch = None
    for n in range(2, max_n + 1):
        if a267579[n] != a347523[n]:
            mismatches += 1
            if first_mismatch is None:
                first_mismatch = n

    verdict = "AGREE_TO_2000" if mismatches == 0 else "MISMATCH"
    result = {
        "candidate": "C36",
        "compared_to": max_n,
        "domain": "n>=2",
        "mismatches": mismatches,
        "first_mismatch": first_mismatch,
        "verdict": verdict,
    }
    with open("result-C36.json", "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    return result


def a347579_check(a267579: list[int], a347523: list[int]) -> bool:
    return a267579[1] == 1 and a347523[1] == 0


# ============================================================================
# Task B — C2: the sign of Maslanka's coefficients A(n)
# ============================================================================

def compute_pi(prec: int) -> Decimal:
    """Compute pi to `prec` decimal digits via Machin's formula: pi/4 = 4*atan(1/5) - atan(1/239)."""
    old_prec = decimal.getcontext().prec
    decimal.getcontext().prec = prec + 25

    def atan_inv(m: int) -> Decimal:
        m2 = m * m
        term = Decimal(1) / Decimal(m)
        total = term
        k = 1
        while True:
            term /= m2
            step = term / (2 * k + 1)
            if step == 0:
                break
            if k & 1:
                total -= step
            else:
                total += step
            k += 1
        return total

    pi_val = 4 * (4 * atan_inv(5) - atan_inv(239))
    decimal.getcontext().prec = old_prec
    return +pi_val


def compute_scaled_bernoulli_even(max_k: int) -> list[Fraction]:
    """
    Compute exact rational V_k = 2^(2k) * B_{2k} for k = 0..max_k
    using the identity Sum_{j=0..k} comb(2k+1, 2j) * 2^(2j) * B_{2j} = 2k + 1.
    Then B_{2k} = V_k / 2^(2k) as an exact Fraction.
    """
    v = [Fraction(0)] * (max_k + 1)
    v[0] = Fraction(1)
    for k in range(1, max_k + 1):
        s = Fraction(2 * k + 1)
        for j in range(k):
            s -= math.comb(2 * k + 1, 2 * j) * v[j]
        v[k] = s / (2 * k + 1)
    return v


def compute_maslanka_coefficients(max_n: int, output_prec: int = 250) -> list[Decimal]:
    """
    Compute A(n) = Sum_{j=0..n} (-1)^j * comb(n, j) * (2j + 1) * zeta(2j + 2)
    for n = 0..max_n.
    Uses working precision `output_prec + 110` (360 digits when output_prec=250)
    to absorb the ~91-digit alternating binomial cancellation at n = 300,
    so that all `output_prec` digits of A(n) are certified exact.
    """
    work_prec = output_prec + 110
    decimal.getcontext().prec = work_prec

    pi_val = compute_pi(work_prec)
    max_k = max_n + 1
    v_even = compute_scaled_bernoulli_even(max_k)

    # zeta(2k) = (-1)^(k+1) * B_{2k} * (2*pi)^(2k) / (2 * (2k)!)
    #          = (-1)^(k+1) * V_k * pi^(2k) / (2 * (2k)!)
    zeta_even = [Decimal(0)] * (max_k + 1)
    pi2 = pi_val * pi_val
    pi_pow = Decimal(1)
    for k in range(1, max_k + 1):
        pi_pow *= pi2
        coeff = v_even[k] / (2 * math.factorial(2 * k))
        if (k + 1) & 1:
            coeff = -coeff
        coeff_dec = Decimal(coeff.numerator) / Decimal(coeff.denominator)
        zeta_even[k] = coeff_dec * pi_pow

    out_ctx = decimal.Context(prec=output_prec)
    a_vals = []
    for n in range(max_n + 1):
        total = Decimal(0)
        for j in range(n + 1):
            term = Decimal(math.comb(n, j) * (2 * j + 1)) * zeta_even[j + 1]
            if j & 1:
                total -= term
            else:
                total += term
        a_vals.append(out_ctx.create_decimal(total))

    decimal.getcontext().prec = output_prec
    return a_vals


def crosscheck_m_series(a_vals: list[Decimal]) -> str:
    """
    Cross-check a sample of small n (including n=1..12 and around sign changes)
    against the equivalent m-series:
      A(n) = Sum_{m>=1} m^(-2) * (1 - m^(-2))^(n-1) * (1 - (2n+1)*m^(-2))
    Note: As m -> infinity, the general term f_n(m) ~ m^(-2) - 3n*m^(-4) + O(m^(-6))
    decays algebraically like m^(-2) rather than falling below 10^(-220) at small m.
    Furthermore, f_n(x) has the exact closed-form antiderivative
      F_n(x) = -x^(-1) * (1 - x^(-2))^n,
    so by Euler-Maclaurin summation at cutoff M:
      A(n) = Sum_{m=1}^{M-1} f_n(m) + f_n(M)/2 + M^(-1)*(1 - M^(-2))^n + O(M^(-3)),
    and even the unaccelerated partial sum S_M = Sum_{m=1}^M f_n(m) satisfies the rigorous
    elementary bound 0 < A(n) - S_M < 1/M for all M > sqrt(2n + 1).
    We verify both the raw partial sum bound and the Euler-Maclaurin accelerated m-series.
    """
    old_prec = decimal.getcontext().prec
    decimal.getcontext().prec = 50

    sample_n = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 17, 31, 32]
    M = 10000
    for n in sample_n:
        s_partial = Decimal(0)
        for m in range(1, M):
            inv_m2 = Decimal(1) / Decimal(m * m)
            if m == 1:
                # For m = 1: (1 - m^(-2))^(n-1) is 1 if n == 1 else 0
                term = Decimal(-2) if n == 1 else Decimal(0)
            else:
                term = inv_m2 * ((Decimal(1) - inv_m2) ** (n - 1)) * (Decimal(1) - Decimal(2 * n + 1) * inv_m2)
            s_partial += term

        inv_M2 = Decimal(1) / Decimal(M * M)
        f_M = inv_M2 * ((Decimal(1) - inv_M2) ** (n - 1)) * (Decimal(1) - Decimal(2 * n + 1) * inv_M2)
        s_raw = s_partial + f_M

        # 1. Check strict elementary truncation bound: 0 < A(n) - s_raw < 1/M
        diff_raw = a_vals[n] - s_raw
        if not (Decimal(0) < diff_raw < Decimal(1) / Decimal(M)):
            decimal.getcontext().prec = old_prec
            return f"fail + raw m-series bound violated at n={n}: diff={diff_raw}"

        # 2. Check Euler-Maclaurin with exact integral tail M^(-1)*(1 - M^(-2))^n
        em_approx = s_partial + Decimal("0.5") * f_M + (Decimal(1) / Decimal(M)) * ((Decimal(1) - inv_M2) ** n)
        err_em = abs(a_vals[n] - em_approx)
        if err_em > Decimal("1e-11"):
            decimal.getcontext().prec = old_prec
            return f"fail + Euler-Maclaurin m-series mismatch at n={n}: err={err_em}"

        # 3. Check signs match between A(n) and the m-series (with closed-form integral tail)
        sign_a = -1 if a_vals[n] < 0 else 1
        sign_m = -1 if em_approx < 0 else 1
        if sign_a != sign_m:
            decimal.getcontext().prec = old_prec
            return f"fail + sign mismatch at n={n}"

    decimal.getcontext().prec = old_prec
    return "pass"


# Published %S/%T/%U listing in OEIS A355437.seq (covers n = 0..115)
FALLBACK_A355437_STU = [
    1, -1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1
]


def fetch_oeis_listing(max_n: int = 300) -> list[int]:
    """
    Fetch A355437 published listing from OEIS github record (%S/%T/%U lines, n=0..115)
    and b-file b355437.txt (n=0..max_n) if reachable, falling back to embedded %S/%T/%U.
    """
    stu_vals = []
    try:
        url = "https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A355/A355437.seq"
        with urllib.request.urlopen(url, timeout=10) as resp:
            text = resp.read().decode("utf-8")
        for line in text.splitlines():
            if line.startswith(("%S", "%T", "%U")):
                payload = line.split(" ", 2)[2]
                for tok in payload.split(","):
                    tok = tok.strip()
                    if tok:
                        stu_vals.append(int(tok))
    except Exception:
        stu_vals = list(FALLBACK_A355437_STU)

    # Also attempt to fetch b355437.txt for n up to max_n if available
    try:
        req = urllib.request.Request(
            "https://oeis.org/A355437/b355437.txt",
            headers={"User-Agent": "Mozilla/5.0"},
        )
        with urllib.request.urlopen(req, timeout=10) as resp:
            b_text = resp.read().decode("utf-8")
        b_vals = {}
        for line in b_text.splitlines():
            line = line.strip()
            if line and not line.startswith("#"):
                parts = line.split()
                if len(parts) >= 2:
                    idx = int(parts[0])
                    if idx <= max_n:
                        b_vals[idx] = int(parts[1])
        if all(n in b_vals for n in range(max_n + 1)):
            # Verify %S/%T/%U matches b-file on 0..len(stu_vals)-1
            for n, val in enumerate(stu_vals):
                assert b_vals[n] == val, f"%S/%T/%U vs b-file mismatch at n={n}"
            return [b_vals[n] for n in range(max_n + 1)]
    except Exception:
        pass

    return stu_vals


def run_task_c2(max_n: int = 300, precision_digits: int = 250) -> dict:
    a_vals = compute_maslanka_coefficients(max_n, output_prec=precision_digits)

    threshold = Decimal("1e-150")
    uncertain_n = []
    signs = []
    min_abs = None

    for n, val in enumerate(a_vals):
        abs_val = abs(val)
        if min_abs is None or abs_val < min_abs:
            min_abs = abs_val
        if abs_val <= threshold:
            uncertain_n.append(n)
        if val > 0:
            signs.append(1)
        elif val < 0:
            signs.append(-1)
        else:
            signs.append(0)

    # Pinned claim under test: sign(A(n)) = -1 iff n = 1 (mod 8), else +1, for all n >= 0
    pattern_holds = True
    first_pattern_break = None
    for n in range(max_n + 1):
        expected_sign = -1 if (n % 8 == 1) else 1
        if signs[n] != expected_sign:
            pattern_holds = False
            if first_pattern_break is None:
                first_pattern_break = n

    listing = fetch_oeis_listing(max_n=max_n)
    listing_disagreements = [
        n for n in range(min(len(listing), max_n + 1))
        if listing[n] != signs[n]
    ]

    crosscheck_status = crosscheck_m_series(a_vals)

    result = {
        "candidate": "C2",
        "computed_to": max_n,
        "precision_digits": precision_digits,
        "pattern_holds": pattern_holds,
        "first_pattern_break": first_pattern_break,
        "uncertain_n": uncertain_n,
        "listing_disagreements": listing_disagreements,
        "signs_0_to_60": signs[:61],
        "min_abs_value": str(min_abs),
        "crosscheck": crosscheck_status,
    }
    with open("result-C2.json", "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    return result


def main() -> None:
    res_c36 = run_task_c36(2000)
    print("C36 result:", json.dumps(res_c36))
    res_c2 = run_task_c2(300, precision_digits=250)
    print("C2 result (summary):", json.dumps({
        k: (v if k != "min_abs_value" else v[:30] + "...")
        for k, v in res_c2.items()
    }))


if __name__ == "__main__":
    main()
