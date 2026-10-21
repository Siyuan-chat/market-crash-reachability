#!/usr/bin/env python3
"""Reconstruct two idealized ten-asset witnesses from the analytical appendices.

These are double-precision evaluations of analytic-primitive constructions,
NOT interval certificates. The constrained B-series is independently
certified in verification/loss_breadth/ and is not regenerated here.

Run from the repository root:
    python verification/twin_ten_asset_benchmarks.py --check
    python verification/twin_ten_asset_benchmarks.py --json
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "data" / "twin_ten_asset_benchmarks.json"
N = 10


def root_bisection(f, left: float, right: float) -> float:
    """Bracketed root of a continuous scalar function."""
    fl, fr = f(left), f(right)
    if not (math.isfinite(fl) and math.isfinite(fr) and fl * fr < 0):
        raise ValueError(f"Unbracketed root: f({left})={fl}, f({right})={fr}")
    for _ in range(100):
        mid = (left + right) / 2
        if mid == left or mid == right:
            break
        fm = f(mid)
        if not math.isfinite(fm):
            raise ValueError("Nonfinite mismatch during bisection")
        if fm * fl > 0:
            left, fl = mid, fm
        else:
            right, fr = mid, fm
    return (left + right) / 2


class PathLedger:
    """Track paired dollar pulses and constant-direction continuous stages.

    F=eta=1 throughout; pulse dollar increments are (S_new^2-S_old^2)/2.
    Interpolating squared prices preserves strict positivity at each pulse.
    """

    def __init__(self, n: int, rho: float):
        self.prices = [1.0] * n
        self.dollars = [0.0] * n
        self.gross_sales = [0.0] * n
        self.turnover = 0.0
        self.rho = rho
        self.min_price = 1.0
        self.max_pairing_residual = 0.0

    def apply(self, prices: list[float], dollars: list[float], shares: list[float]):
        if not all(math.isfinite(x) and x > 0 for x in prices):
            raise AssertionError("Price positivity failed")
        net = abs(sum(dollars))
        self.max_pairing_residual = max(self.max_pairing_residual, net)
        if net > 1e-9:
            raise AssertionError(f"Unpaired dollar flow: {net}")
        for i, (dx, dtheta) in enumerate(zip(dollars, shares)):
            self.dollars[i] += dx
            self.gross_sales[i] += max(-dtheta, 0.0)
        self.turnover += sum(max(x, 0.0) for x in dollars)
        self.prices = prices[:]
        self.min_price = min(self.min_price, *prices)

    def pulse(self, prices: list[float]):
        if len(prices) != len(self.prices):
            raise AssertionError("Invalid pulse length")
        dx = [(new * new - old * old) / 2
              for old, new in zip(self.prices, prices)]
        dtheta = [new - old for old, new in zip(self.prices, prices)]
        self.apply(prices, dx, dtheta)

    def stage(self, direction: list[float], H: float, t0: float, t1: float, R, IR):
        if any(abs(p - R(t0) * u) > 2e-9
               for p, u in zip(self.prices, direction)):
            raise AssertionError("Stage discontinuity not represented as a pulse")
        if not t1 > t0 or R(t0) <= 0 or R(t1) <= 0:
            raise AssertionError("Nonpositive radius or invalid stage")
        area = IR(t1) - IR(t0)
        dollars = [self.rho * u * (u * H - 1) * area for u in direction]
        shares = [self.rho * (u * H - 1) * (t1 - t0) for u in direction]
        self.apply([u * R(t1) for u in direction], dollars, shares)

    def report(self):
        return {
            "turnover": self.turnover,
            "max_cumulative_sales": max(self.gross_sales),
            "terminal_dollar_residual": max(abs(x) for x in self.dollars),
            "max_instant_pairing_residual": self.max_pairing_residual,
            "minimum_visited_price": self.min_price,
        }


def radial_data(n: int, rho: float, a: float, b: float,
                low_count: int, low: float):
    H = a + b + low_count * low
    d = math.sqrt(n) - H

    def R(t):
        return H + d * math.exp(-rho * t)

    def IR(t):
        return H * t + d * (-math.expm1(-rho * t)) / rho

    def IR2(t):
        return (H * H * t + 2 * H * d * (-math.expm1(-rho * t)) / rho
                + d * d * (-math.expm1(-2 * rho * t)) / (2 * rho))

    return H, R, IR, IR2


def balanced_cuts(n: int, T: float, weight_integral):
    total = weight_integral(T)
    if total <= 0:
        raise AssertionError("Stage-order weight must be positive")
    cuts = [0.0]
    for j in range(1, n):
        cuts.append(root_bisection(
            lambda t: weight_integral(t) - total * j / n, 0.0, T))
    cuts.append(T)
    if not all(t0 < t1 for t0, t1 in zip(cuts, cuts[1:])):
        raise AssertionError("Stage cuts not increasing")
    return cuts


def full_coverage_50pct():
    """Appendix D, N=10, F=eta=1, rho=0.4, T=40."""
    rho, T, target_price = 0.4, 40.0, 0.5

    def family(b):
        a = math.sqrt(1 - (N - 1) * b * b)
        H, R, IR, IR2 = radial_data(N, rho, a, b, N - 2, b)
        return a, H, R, IR, IR2

    b = root_bisection(
        lambda x: family(x)[2](T) / math.sqrt(N) - target_price,
        0.0, 1 / math.sqrt(N))
    a, H, R, IR, IR2 = family(b)

    def IW(t):
        return (a - b) * ((a + b) * IR2(t) - IR(t))

    cuts = balanced_cuts(N, T, IW)
    path = PathLedger(N, rho)
    for j in range(N):
        direction = [b] * N
        direction[j] = a
        path.pulse([u * R(cuts[j]) for u in direction])
        path.stage(direction, H, cuts[j], cuts[j + 1], R, IR)
    path.pulse([target_price] * N)
    if any(abs(s - target_price) > 1e-12 for s in path.prices):
        raise AssertionError("Full-coverage terminal target missed")
    if max(abs(x) for x in path.dollars) >= 2e-10:
        raise AssertionError("Full-coverage executed-dollar closure failed")
    critical = math.log(
        math.sqrt(N) / (1 + (math.sqrt(N) - 1) * math.exp(-rho * T)))
    if math.log(2) >= critical:
        raise AssertionError("Target outside strict reachability region")
    return {
        "N": N, "k": N, "F": 1, "eta": 1, "rho": rho, "T": T,
        "ordinary_target_drop": 1 - target_price,
        "terminal_price_each": target_price,
        "terminal_C1": math.log(2),
        "critical_log_loss_unattained": critical,
        "critical_ordinary_drop_unattained": 1 - math.exp(-critical),
        "direction_low_b": b, "direction_high_a": a,
        "stage_cut_times": cuts, **path.report(),
    }


def severe_partial_coverage(target_log_loss: int):
    """Appendix C/F, N=10, k=9, F=eta=rho=1, T=4."""
    rho, T, low, k = 1.0, 4.0, 0.001, N - 1
    eps = math.exp(-target_log_loss)

    def family(b):
        a = math.sqrt(1 - b * b - (k - 1) * low * low)
        H, R, IR, IR2 = radial_data(N, rho, a, b, k - 1, low)
        return a, H, R, IR, IR2

    def compensator_mismatch(b):
        a, H, R, IR, IR2 = family(b)
        return (R(T)**2 - k * eps**2 - 1
                + 2 * rho * (b * b * IR2(T) - b * IR(T)))

    b = root_bisection(compensator_mismatch, 0.0, 0.25)
    a, H, R, IR, IR2 = family(b)

    def IW(t):
        return (a * a - low * low) * IR2(t) - (a - low) * IR(t)

    cuts = balanced_cuts(k, T, IW)
    base = low * low * IR2(T) - low * IR(T)
    weight_required_by_ledger = (1 - eps * eps) / 2 - rho * base
    if abs(rho * IW(T) / k - weight_required_by_ledger) > 3e-9:
        raise AssertionError("Target recovery weights do not close")

    path = PathLedger(N, rho)
    for j in range(k):
        direction = [low] * k + [b]
        direction[j] = a
        path.pulse([u * R(cuts[j]) for u in direction])
        path.stage(direction, H, cuts[j], cuts[j + 1], R, IR)
    compensator = math.sqrt(R(T)**2 - k * eps**2)
    path.pulse([eps] * k + [compensator])
    losses = [math.log(1 / x) for x in path.prices]
    avg = sum(losses) / N
    q = sorted(losses, reverse=True)[k - 1]
    if max(abs(x) for x in path.dollars) > 2e-10:
        raise AssertionError("Partial-coverage executed-dollar closure failed")
    if not (0 < eps < 1 and all(s > 0 for s in path.prices)):
        raise AssertionError("Nonpositive endpoint")
    # Explicit severity-independent, nonoptimal bounds from Appendix C.
    M0 = N**3 / 4 + rho * N * T
    H0 = N * math.sqrt(N) + rho * T * (math.sqrt(N) + 1)
    if path.turnover > M0 or max(path.gross_sales) > H0:
        raise AssertionError("Known uniform resource bound violated")
    return {
        "N": N, "k": k, "F": 1, "eta": 1, "rho": rho, "T": T,
        "low_coordinate_c": low, "target_log_loss": target_log_loss,
        "target_terminal_price_each": eps,
        "compensator_terminal_price": compensator,
        "C_0.9": min(avg, q), "mean_log_loss": avg, "Q_0.9": q,
        "direction_compensator_b": b, **path.report(),
    }


def compute():
    return {
        "evidence_class": "ordinary double-precision reconstruction; NOT interval-certified",
        "model": "paired marginal-dollar p=0 flow-completed pulses with price-level resilience",
        "full_coverage": full_coverage_50pct(),
        "partial_coverage": [severe_partial_coverage(L) for L in (3, 5, 10, 20)],
        "constrained_B_series_evidence": "verification/loss_breadth/verified_results_manifest.json",
    }


def check(result):
    """Regress key numerical values against independently recorded benchmarks."""
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    full = result["full_coverage"]
    for field, expected in fixture["full_coverage"].items():
        actual = full[field]
        if not math.isclose(actual, expected, rel_tol=5e-10, abs_tol=3e-10):
            raise AssertionError(f"A1 {field}: {actual} != {expected}")
    for item, expected_row in zip(
            result["partial_coverage"], fixture["partial_coverage"], strict=True):
        for field, expected in expected_row.items():
            actual = item[field]
            if not math.isclose(actual, expected, rel_tol=5e-10, abs_tol=3e-10):
                raise AssertionError(
                    f"A2 L={item['target_log_loss']} {field}: {actual} != {expected}")
    if not (abs(full["turnover"] - 34.3736804823) < 5e-7 and
            abs(full["max_cumulative_sales"] - 16.5884822581) < 5e-7):
        raise AssertionError("A1 author-side reference values changed")
    for item in [full, *result["partial_coverage"]]:
        if (item["terminal_dollar_residual"] > 3e-10 or
                item["max_instant_pairing_residual"] > 3e-10 or
                item["minimum_visited_price"] <= 0):
            raise AssertionError("Closure, matching or price positivity failed")
    print("PASS: both idealized ten-asset witness families match checked numerical fixture")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check committed numerical fixture")
    parser.add_argument("--json", action="store_true", help="print machine-readable result")
    args = parser.parse_args()
    result = compute()
    if args.check:
        check(result)
    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=False))
    elif not args.check:
        full = result["full_coverage"]
        print(f'A1: N=10, 50% each, M={full["turnover"]:.8f}, max sales={full["max_cumulative_sales"]:.8f}, residual={full["terminal_dollar_residual"]:.3g}')
        for row in result["partial_coverage"]:
            print(f'A2: L={row["target_log_loss"]:2d}, C_0.9={row["C_0.9"]:.8f}, M={row["turnover"]:.8f}, max sales={row["max_cumulative_sales"]:.8f}, residual={row["terminal_dollar_residual"]:.3g}')


if __name__ == "__main__":
    main()
