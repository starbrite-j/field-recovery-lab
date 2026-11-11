"""Independent numerical checks for the source-derived recovery calibration.

Run with Python 3; no third-party packages or network access are needed.
The forward angular samples integrate the actual OutgoingSchedule slope.
The inverses use observed axial levels / angular ratios, or angular data alone,
not hidden parameter inputs. Observation-window assumptions are explicit.

These check the initial-drop / clean-hold / reserved-patch identities only.
They DO NOT instantiate a ResetWitness, CompensationWitness, or PDE solution,
and DO NOT validate recovery from arbitrary finite/noisy data or execute Lean.
"""

from __future__ import annotations

import json
import math
from collections.abc import Callable


def sigma(x: float) -> float:
    """OutgoingSchedule.sigma with FlatCutoff.edge(1,x)=exp(-1/x**2)."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    logit = -1.0 / x**2 + 1.0 / (1.0 - x) ** 2
    if logit >= 0:
        return 1.0 / (1.0 + math.exp(-logit))
    weight = math.exp(logit)
    return weight / (1.0 + weight)


def bisect_increasing(
    f: Callable[[float], float], target: float, low: float, high: float
) -> float:
    if not f(low) <= target <= f(high):
        raise ValueError("The observation bracket does not contain the target.")
    for _ in range(100):
        mid = (low + high) / 2
        if mid == low or mid == high:
            break
        if f(mid) < target:
            low = mid
        else:
            high = mid
    return (low + high) / 2


def integral(f: Callable[[float], float], low: float, high: float) -> float:
    """Adaptive Simpson quadrature, independent of the inverse power formula."""
    if low == high:
        return 0.0
    if high < low:
        return -integral(f, high, low)
    mid = (low + high) / 2
    fl, fm, fh = f(low), f(mid), f(high)
    whole = (high - low) * (fl + 4 * fm + fh) / 6

    def refine(a, b, fa, fc, fb, estimate, tol, depth):
        c = (a + b) / 2
        d, e = (a + c) / 2, (c + b) / 2
        fd, fe = f(d), f(e)
        left = (c - a) * (fa + 4 * fd + fc) / 6
        right = (b - c) * (fc + 4 * fe + fb) / 6
        delta = left + right - estimate
        if abs(delta) <= 15 * tol:
            return left + right + delta / 15
        if depth == 0:
            raise ArithmeticError("Quadrature did not reach its tolerance.")
        return refine(a, c, fa, fd, fc, left, tol / 2, depth - 1) + refine(
            c, b, fc, fe, fb, right, tol / 2, depth - 1
        )

    return refine(low, high, fl, fm, fh, whole, 2e-13, 24)


def source_log_angular(P: float, m: float, rate: float, y: float) -> float:
    """log(angular(P,dropLength,rate)(y,0)), via the source slope integral."""
    length = math.exp(m) + 10

    def slope_minus_half(t):
        return 0.6 * (1 - sigma(t)) - rate * sigma(t - (length + 1)) - 0.5

    # Splitting at every source transition prevents missing a short ramp
    # inside a long interval on which the rest of the integrand is constant.
    if y < 0:
        cuts = [y, 0.0]
        sign = -1
    else:
        cuts = sorted({0.0, y, *(p for p in [1.0, length + 1, length + 2] if p < y)})
        sign = 1
    value = sum(integral(slope_minus_half, a, b) for a, b in zip(cuts, cuts[1:]))
    return math.log(P) + sign * value


def recover_early(
    axial: Callable[[float], float], log_angular: Callable[[float], float]
) -> dict[str, float]:
    """Recover from log-radius observations in a valid initial-drop bracket.

    The fixed bracket below covers the test cases' INITIAL drop and ends
    before their later pulse. It is an observation-coverage condition, not
    an automatic certified locator for an arbitrary field.
    """
    alpha = bisect_increasing(sigma, 0.25, 0.0, 0.5)
    z3 = bisect_increasing(lambda z: -axial(z), -3.0, -20.0, 50.0)
    z2 = bisect_increasing(lambda z: -axial(z), -2.0, -20.0, 50.0)
    gap = z2 - z3
    m = bisect_increasing(
        lambda value: math.exp(value / 2) - math.exp(alpha * value),
        gap,
        0.0,
        40.0,
    )
    log_scale = z2 - math.exp(m / 2)
    hold = math.exp(m) + 12
    rate = -(log_angular(log_scale + hold + 2) - log_angular(log_scale + hold + 1)) - 0.5
    if not 0 < rate < 0.1:
        raise ValueError("Recovered rate is outside the source parameter range.")
    return {
        "m": m,
        "log_scale": log_scale,
        "rate": rate,
        "log_P": log_angular(log_scale),
        "log_patch": log_scale + hold + 60 * math.log(1 / rate) - 20,
    }


def recover_angular_only(
    log_angular: Callable[[float], float],
) -> dict[str, float]:
    """Conditional E-only calibration from a covered, unedited early window.

    The test observations cover z in [-21, 81]. The first ramp is in
    [-20, 50]; after it is located, [r+49,r+50] is a KNOWN clean hold and
    [r+1,r+45] brackets the second ramp. These coverage promises hold for
    the cases below, not every source parameter choice. This numerical
    alternative avoids exact equality at the second ramp's flat boundary.
    """
    def observed_slope(z):
        step = 1e-4
        return (log_angular(z + step) - log_angular(z - step)) / (2 * step)

    marker = bisect_increasing(lambda z: -observed_slope(z), 0.2, -20.0, 50.0)
    log_scale = marker - 0.5
    rate = -(log_angular(log_scale + 50) - log_angular(log_scale + 49)) - 0.5
    if not 0 < rate < 0.1:
        raise ValueError("Recovered angular-only rate is outside the source range.")
    # On the second ramp g'=-1/2-rate*sigma(y-(exp(m)+11));
    # its half-height is at y=exp(m)+11.5.
    second_center = bisect_increasing(
        lambda z: -observed_slope(z), 0.5 + rate / 2,
        log_scale + 1, log_scale + 45,
    )
    m = math.log(second_center - log_scale - 11.5)
    hold = math.exp(m) + 12
    return {
        "m": m,
        "log_scale": log_scale,
        "rate": rate,
        "log_P": log_angular(log_scale),
        "log_patch": log_scale + hold + 60 * math.log(1 / rate) - 20,
    }


def run_checks() -> dict:
    cases = []
    maximum = {key: 0.0 for key in ["m", "log_scale", "rate", "log_P", "log_patch", "patch_curve"]}
    angular_only_maximum = {key: 0.0 for key in ["m", "log_scale", "rate", "log_P", "log_patch"]}
    for m, scale, P in [(0.05, 0.001, 2.0), (1.0, 3.0, 7.0), (3.0, 1e10, 100.0)]:
        for rate in [1 / 120, 1 / 150, 1 / 300]:
            log_scale = math.log(scale)

            def axial(z):
                y = z - log_scale
                return 4.0 if y <= 1 else 4.0 * (1 - sigma(math.log(y) / m))

            def observed_log_angular(z):
                return source_log_angular(P, m, rate, z - log_scale)

            got = recover_early(axial, observed_log_angular)
            hold = math.exp(m) + 12
            patch_clock = hold + 60 * math.log(1 / rate) - 20
            expected = {
                "m": m,
                "log_scale": log_scale,
                "rate": rate,
                "log_P": math.log(P),
                "log_patch": log_scale + patch_clock,
            }
            errors = {key: abs(got[key] - value) for key, value in expected.items()}
            log_amplitude = source_log_angular(P, m, rate, patch_clock)
            # Verify the ENTIRE patch model at several interior/boundary
            # positions against independent integration of the source slope.
            patch_error = max(
                abs(source_log_angular(P, m, rate, patch_clock + s)
                    - (log_amplitude - (0.5 + rate) * s))
                for s in [0.0, 0.1, 1.0, 2.5, 4.9, 5.0]
            )
            errors["patch_curve"] = patch_error
            for key, error in errors.items():
                maximum[key] = max(maximum[key], error)
            if any(error > 2e-8 for error in errors.values()):
                raise AssertionError({"parameters": expected, "recovered": got, "errors": errors})
            angular_got = recover_angular_only(observed_log_angular)
            angular_errors = {key: abs(angular_got[key] - value) for key, value in expected.items()}
            for key, error in angular_errors.items():
                angular_only_maximum[key] = max(angular_only_maximum[key], error)
            if any(error > 2e-6 for error in angular_errors.values()):
                raise AssertionError({"parameters": expected, "angular_only": angular_got,
                                      "errors": angular_errors})
            cases.append({"m": m, "scale": scale, "rate": rate, "errors": errors,
                          "angular_only_errors": angular_errors})
    return {
        "status": "passed",
        "cases": len(cases),
        "scope": "source initial-drop, clean-hold, and reserved-patch calibration",
        "certified_profile_or_PDE_witness": False,
        "tested_tail_or_last_equality_identification": False,
        "maximum_absolute_errors": maximum,
        "angular_only_cases": len(cases),
        "angular_only_scope": "early calibration with a known clean-hold observation window",
        "angular_only_maximum_absolute_errors": angular_only_maximum,
        "tested_missing_U_regeneration": False,
        "case_results": cases,
    }


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2))
