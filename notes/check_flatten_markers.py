"""Audit finite-precision endpoint markers in the source flattening law.

The exact Lean endpoint reader uses the last E(X,0)=2*E(X,1) equality.
These controlled fixtures test what happens when that predicate is rounded.
The optional estimator uses interior log-ratio levels instead and estimates
both flattenLength and the log endpoint, without supplying either value.

This is a conditional numerical estimate of the flattening transition ONLY.
It does not certify a Profile, source membership, full calibration, E/U
reconstruction, arbitrary noise tolerance, or terminal observation coverage.

Run the fixture audit:
    python3 notes/check_flatten_markers.py --output notes/flatten_marker_audit.json

Estimate from a JSON file of points with natural-log fields:
    python3 notes/check_flatten_markers.py --input samples.json --max-gap 0.1
Input: {"points": [{"z": 1.0, "log_e0": -2.0, "log_e1": -2.5}, ...]}
Here z=log(X). The observations must include the flattening transition and
enough later data for its selected last crossings to be the source markers.
The max-gap limit is a supplied coverage constraint, not a coverage proof.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import math
import platform
import sys
from pathlib import Path

from check_recovery_calibration import bisect_increasing, sigma


LOG2 = math.log(2.0)


class ObservationError(ValueError):
    pass


def positive_fields_to_logs(z: float, e0: float, e1: float) -> dict[str, float]:
    """Reject already-lost amplitudes; log(0) cannot recover underflowed data."""
    if not all(math.isfinite(v) for v in (z, e0, e1)) or e0 <= 0 or e1 <= 0:
        raise ObservationError("Positive finite amplitudes are required; underflowed zeros have lost information.")
    return {"z": z, "log_e0": math.log(e0), "log_e1": math.log(e1)}


def validate_points(points: list[dict], max_gap: float) -> list[tuple[float, float]]:
    if not math.isfinite(max_gap) or max_gap <= 0:
        raise ObservationError("max_gap must be positive and finite.")
    if len(points) < 4:
        raise ObservationError("At least four observations are required.")
    values = []
    for point in points:
        try:
            z, e0, e1 = (float(point[key]) for key in ("z", "log_e0", "log_e1"))
        except (KeyError, TypeError, ValueError) as error:
            raise ObservationError("Each point requires z, log_e0, and log_e1 numbers.") from error
        if not all(math.isfinite(v) for v in (z, e0, e1)):
            raise ObservationError("Observations must be finite.")
        if values and not 0 < z - values[-1][0] <= max_gap:
            raise ObservationError("Radii must increase strictly and respect the supplied max_gap.")
        values.append((z, e0 - e1))
    return values


def last_downcrossing(values: list[tuple[float, float]], level: float) -> float:
    candidates = []
    for (left, a), (right, b) in zip(values, values[1:]):
        if a >= level >= b and a > b:
            candidates.append(left + (right - left) * (a - level) / (a - b))
    if not candidates:
        raise ObservationError("A required interior ratio level is not bracketed by the observations.")
    return candidates[-1]


def interpolate(values: list[tuple[float, float]], z: float) -> float:
    index = bisect.bisect_right(values, (z, math.inf)) - 1
    if index < 0 or index + 1 >= len(values):
        raise ObservationError("A predicted transition point is outside the observation coverage.")
    a, b = values[index], values[index + 1]
    return a[1] + (b[1] - a[1]) * (z - a[0]) / (b[0] - a[0])


def estimate_flatten_endpoint(points: list[dict], *, max_gap: float,
                              max_fit_residual: float = 1e-4) -> dict:
    if not math.isfinite(max_fit_residual) or max_fit_residual <= 0:
        raise ObservationError("max_fit_residual must be positive and finite.")
    values = validate_points(points, max_gap)
    # On the actual flattening law log(E0/E1)=(1-sigma(u))*log(2).
    # Levels sigma=1/4 and 1/2 give ratios above sqrt(2) or equal to it.
    # The reset bound |relative|<=lam<1/10 limits its ratio to <11/9,
    # which cannot recreate these levels in the exact source family.
    alpha = bisect_increasing(sigma, 0.25, 0.0, 0.5)
    first = last_downcrossing(values, 0.75 * LOG2)
    center = last_downcrossing(values, 0.5 * LOG2)
    length = (center - first) / (0.5 - alpha)
    if not math.isfinite(length) or length <= 0:
        raise ObservationError("The ordered interior markers imply no positive flattening length.")
    endpoint = center - length / 2
    # These levels did not determine the fitted endpoint/length. Their
    # discrepancies can reject a poor fit but cannot certify source membership.
    residuals = []
    for step_level in (0.30, 0.35, 0.40, 0.45):
        u = bisect_increasing(sigma, step_level, 0.0, 0.5)
        z = endpoint + length * u
        residuals.append(abs(interpolate(values, z) - (1 - step_level) * LOG2))
    if max(residuals) > max_fit_residual:
        raise ObservationError("Interior markers fail the held-out flattening-law fit tolerance.")
    return {
        "status": "conditional_estimate",
        "endpoint_log_radius": endpoint,
        "flatten_length": length,
        "quarter_step_log_radius": first,
        "half_step_log_radius": center,
        "maximum_held_out_log_ratio_residual": max(residuals),
        "source_membership_certified": False,
        "finite_noise_error_bound_proved": False,
        "full_field_recovery_tested": False,
        "coverage_certified": False,
        "supplied_max_gap": max_gap,
        "supplied_max_fit_residual": max_fit_residual,
        "observation_count": len(values),
    }


def forward_step(u: float) -> float:
    """Independent literal edge formula, rather than the inverse's logit form."""
    if u <= 0:
        return 0.0
    if u >= 1:
        return 1.0
    a = math.exp(-1 / u**2)
    b = math.exp(-1 / (1 - u) ** 2)
    return a / (a + b)


def fixture(endpoint: float, length: float, noise: float = 0.0) -> list[dict]:
    result = []
    for index in range(20001):
        offset = -3 + index / 4000
        z = endpoint + length * offset
        log_ratio = (1 - forward_step(offset)) * LOG2
        if offset < -2:
            # An unrelated earlier prefix can cross the same interior levels.
            log_ratio = 0.45 + 0.35 * math.sin(18 * offset)
        if offset > 1:
            # Later compact reset-like contrasts stay below the interior levels.
            log_ratio = math.log(1 + 0.18 * math.exp(-((offset - 1.3) / 0.09) ** 2))
            log_ratio -= max(0, offset - 1.7) * 0.1
        common = 3.0 - 0.507 * z
        result.append({"z": z,
                       "log_e0": common + log_ratio + noise * math.sin(index * 0.73),
                       "log_e1": common + noise * math.cos(index * 0.41)})
    return result


def run_checks() -> dict:
    cases = []
    for endpoint, length in [(10.0, 80.0), (500.0, 160.0), (100000.0, 800.0)]:
        # Even the exact forward ratio rounds to 2 after the true endpoint.
        rounded_last = max(endpoint + length * (index / 20000)
                           for index in range(20001)
                           if 2 * math.exp(-forward_step(index / 20000) * LOG2) == 2.0)
        assert rounded_last > endpoint + 0.1 * length
        for noise in (0.0, 1e-8, 1e-6):
            points = fixture(endpoint, length, noise)
            estimate = estimate_flatten_endpoint(points, max_gap=length / 3999)
            endpoint_error = abs(estimate["endpoint_log_radius"] - endpoint)
            length_error = abs(estimate["flatten_length"] - length)
            assert endpoint_error / length < 1e-4, (endpoint, length, noise, estimate)
            assert length_error / length < 2e-4, (endpoint, length, noise, estimate)
            assert estimate["maximum_held_out_log_ratio_residual"] < 1e-4
            cases.append({"endpoint": endpoint, "length": length, "noise_amplitude": noise,
                          "interior_endpoint_absolute_error": endpoint_error,
                          "interior_length_absolute_error": length_error,
                          "rounded_equality_endpoint_error": rounded_last - endpoint,
                          "held_out_log_ratio_residual": estimate["maximum_held_out_log_ratio_residual"]})
    rejected = []
    clean = fixture(10.0, 80.0)
    invalid = {
        "missing_transition": clean[:1000],
        "large_gap": clean[::1000],
        "duplicate_radius": [clean[0], clean[0], *clean[1:5]],
        "nonfinite_amplitude": [{**clean[0], "log_e0": float("nan")}, *clean[1:5]],
        "excessive_fit_error": fixture(10.0, 80.0, 0.01),
    }
    for label, points in invalid.items():
        try:
            estimate_flatten_endpoint(points, max_gap=0.021)
        except ObservationError:
            rejected.append(label)
        else:
            raise AssertionError("Invalid observations accepted: " + label)
    try:
        positive_fields_to_logs(100000, math.exp(-100000), math.exp(-100001))
    except ObservationError:
        rejected.append("underflowed_raw_fields")
    else:
        raise AssertionError("Underflowed amplitudes were not rejected.")
    return {
        "status": "passed",
        "scope": "Controlled source flattening-law fixtures and conditional interior-marker estimator",
        "cases": len(cases), "rejected_inputs": rejected, "case_results": cases,
        "certified_Profile_or_PDE_witness": False,
        "actual_observed_dataset_recovered": False,
        "full_calibration_or_EU_pipeline_tested": False,
        "universal_noise_or_coverage_guarantee": False,
        "finding": "Rounded exact equality shifts the endpoint by more than a tenth of the flattening length in these fixtures. Interior ratio markers avoid that boundary predicate, subject to the stated sampling and source-family assumptions.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--max-gap", type=float)
    parser.add_argument("--max-fit-residual", type=float, default=1e-4)
    args = parser.parse_args()
    try:
        if args.input:
            if args.max_gap is None:
                parser.error("--input requires an explicit --max-gap coverage constraint")
            data = json.loads(args.input.read_text())
            result = estimate_flatten_endpoint(data["points"], max_gap=args.max_gap,
                                              max_fit_residual=args.max_fit_residual)
        else:
            result = run_checks()
    except (ObservationError, KeyError, TypeError, ValueError, OSError) as error:
        parser.exit(2, str(error) + "\n")
    result.update({"python_version": platform.python_version(),
                   "float_mantissa_bits": sys.float_info.mant_dig,
                   "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()})
    encoded = json.dumps(result, indent=2, allow_nan=False) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
