"""Independent quadrature audit of the direct angular-to-axial energy inverse.

Run with the existing local SciPy environment:
    /Users/jj/.venvs/dedalus-test/bin/python notes/check_axial_from_angular.py

The exact source-instantiation argument is in AxialFromAngular.lean. This
script tests its functional algebra with controlled Gaussian fields, whose
weighted integrals are independently available in closed form. The trial
axial field is affine in amplitude, as OutgoingSchedule.axial is; its mixed
coefficient is nonzero and its pulse includes a negative correction.

These are NOT numerical instances of the repository's Profile/ResetWitness,
Mathlib's bump, the terminal heat edit, or a PDE solution. No complete observed
angular dataset has been supplied. Passing this audit does not fill that gap
or compile Lean. The separate calibration script tests the early source ramps.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path

from scipy.integrate import quad

from check_recovery_calibration import sigma


@dataclass(frozen=True)
class Gaussian:
    coefficient: float
    center: float
    width: float

    def weighted(self, y: float) -> float:
        """exp(y/2)*signal(y), without evaluating exp(y) separately."""
        return self.coefficient * math.exp(
            -0.5 * ((y - self.center) / self.width) ** 2 + y / 2
        )

    def value(self, y: float) -> float:
        return self.coefficient * math.exp(-0.5 * ((y - self.center) / self.width) ** 2)


class CoverageError(ValueError):
    """An integral asked for field observations outside their known coverage."""


def signal(terms: tuple[Gaussian, ...], y: float, *, weighted=False) -> float:
    return math.fsum(term.weighted(y) if weighted else term.value(y) for term in terms)


def exact_inner(left: tuple[Gaussian, ...], right: tuple[Gaussian, ...]) -> float:
    """Independent closed form of integral exp(y)*left(y)*right(y) dy."""
    pieces = []
    for f in left:
        for g in right:
            a = 0.5 / f.width**2 + 0.5 / g.width**2
            b = f.center / f.width**2 + g.center / g.width**2 + 1
            c = -0.5 * (f.center / f.width) ** 2 - 0.5 * (g.center / g.width) ** 2
            pieces.append(f.coefficient * g.coefficient * math.sqrt(math.pi / a)
                          * math.exp(c + b * b / (4 * a)))
    return math.fsum(pieces)


def negative_clamp(c: float) -> float:
    """The actual PulseAmplitude.negativeClamp, including its transition."""
    switch = sigma(10 * (c + 0.2))
    return (1 - switch) * c - switch / 10


def stable_reference_root(q: float, linear: float, c: float) -> float:
    """Independent stable solution of q*A^2+linear*A+clamp(c)=0."""
    clamped = negative_clamp(c)
    discriminant_root = math.hypot(linear, 2 * math.sqrt(-q * clamped))
    if linear >= 0:
        return -2 * clamped / (linear + discriminant_root)
    return (discriminant_root - linear) / (2 * q)


def integrate(f, high=math.inf) -> tuple[float, float]:
    return quad(f, -math.inf, high, epsabs=2e-11, epsrel=2e-12, limit=250)


def reconstruct(
    observed_weighted_e,
    known_weighted_u0,
    known_weighted_direction,
    normalization: float,
) -> dict[str, float]:
    """Consumes angular observations and a known affine axial schedule only.

    No original axial observations or reset/heat coefficients are inputs.
    Integrating the weighted functions avoids exp(y)*tiny_signal**2.
    """
    q, q_error = integrate(lambda y: known_weighted_direction(y) ** 2)
    linear, l_error = integrate(
        lambda y: 2 * known_weighted_u0(y) * known_weighted_direction(y)
    )
    constant, c_error = integrate(
        lambda y: known_weighted_u0(y) ** 2 - observed_weighted_e(y) ** 2 / 2
    )
    q *= normalization
    linear *= normalization
    constant *= normalization
    if not (math.isfinite(q) and q > 0 and math.isfinite(linear) and math.isfinite(constant)):
        raise ValueError("Invalid energy coefficients; recovery is not defined.")
    discriminant = linear**2 - 4 * q * negative_clamp(constant)
    amplitude = (-linear + math.sqrt(discriminant)) / (2 * q)
    return {
        "quadratic": q,
        "linear": linear,
        "constant": constant,
        "amplitude": amplitude,
        "estimated_quadrature_error": normalization * max(q_error, l_error, c_error),
    }


def run_checks() -> dict:
    u0 = (Gaussian(0.4, -1, 0.8), Gaussian(-0.12, 4, 0.6))
    direction = (Gaussian(0.8, 1.5, 0.7), Gaussian(-0.15, 5, 0.5))
    normalization = 0.005
    angular_template = (Gaussian(1, 0.5, 0.9), Gaussian(0.6, 6, 0.8))
    exact_q = normalization * exact_inner(direction, direction)
    exact_linear = 2 * normalization * exact_inner(u0, direction)
    axial_energy = exact_inner(u0, u0)
    template_energy = exact_inner(angular_template, angular_template)
    results = []
    maxima = {key: 0.0 for key in ["quadratic", "linear", "constant", "amplitude", "U", "later_U"]}

    # Covers inactive clamp, the interior clamp transition, and active clamp.
    for target_constant in [-0.8, -0.23, -0.15, 0.005]:
        scale = math.sqrt(2 * (axial_energy - target_constant / normalization) / template_energy)
        angular = tuple(Gaussian(scale * f.coefficient, f.center, f.width) for f in angular_template)
        exact_c = normalization * (axial_energy - exact_inner(angular, angular) / 2)
        expected_a = stable_reference_root(exact_q, exact_linear, exact_c)

        # Reconstruction sees callables only, not Gaussian parameters, analytic
        # integrals, target_constant, or the original amplitude / U outputs.
        recovered = reconstruct(
            lambda y: signal(angular, y, weighted=True),
            lambda y: signal(u0, y, weighted=True),
            lambda y: signal(direction, y, weighted=True),
            normalization,
        )
        errors = {
            "quadratic": abs(recovered["quadratic"] - exact_q),
            "linear": abs(recovered["linear"] - exact_linear),
            "constant": abs(recovered["constant"] - exact_c),
            "amplitude": abs(recovered["amplitude"] - expected_a),
        }

        def reference_u(y):
            return signal(u0, y) + expected_a * signal(direction, y)

        def recovered_u(y):
            return signal(u0, y) + recovered["amplitude"] * signal(direction, y)

        sample_clocks = [-20, -4, -1, 0, 1.5, 3, 4, 5, 6, 9, 20]
        errors["U"] = max(abs(reference_u(y) - recovered_u(y)) for y in sample_clocks)
        # Include scales whose physical coordinates underflow/overflow float64.
        errors["later_U"] = max(
            abs(reference_u(y) - recovered_u((y + r) - r))
            for r in [-2000, -0.7, 2.3, 2000] for y in sample_clocks
        )
        residual = recovered["quadratic"] * recovered["amplitude"]**2 + recovered["linear"] * recovered["amplitude"] + negative_clamp(recovered["constant"])
        if abs(residual) > 1e-11 or any(value > 2e-10 for value in errors.values()):
            raise AssertionError({"constant": exact_c, "errors": errors, "residual": residual})
        for key, value in errors.items():
            maxima[key] = max(maxima[key], value)

        # Negative control: falsely call the missing angular tail zero.
        truncated = reconstruct(
            lambda y: signal(angular, y, weighted=True) if y <= 4 else 0,
            lambda y: signal(u0, y, weighted=True),
            lambda y: signal(direction, y, weighted=True),
            normalization,
        )
        tail_omission_changes = abs(truncated["amplitude"] - expected_a)
        # Active clamping can erase the change in A, despite a wrong C.
        # Always inspect the reconstructed coefficient too.
        tail_constant_error = abs(truncated["constant"] - exact_c)
        lost_angular_energy_fraction = tail_constant_error / (
            normalization * exact_inner(angular, angular) / 2
        )
        if lost_angular_energy_fraction < 0.9:
            raise AssertionError("The omitted-tail control was not consequential.")

        # Check the actual, unclamped energy independently. It is not generally
        # zero when the source clamp changes the constant term.
        true_energy = exact_q * expected_a**2 + exact_linear * expected_a + exact_c
        assert abs(true_energy - (exact_c - negative_clamp(exact_c))) < 1e-11
        if exact_c > -0.2:
            assert abs(true_energy) > 1e-3

        results.append({
            "true_constant": exact_c,
            "clamp_active": exact_c > -0.2,
            "errors": errors,
            "clamped_polynomial_residual": abs(residual),
            "actual_unclamped_energy": true_energy,
            "omitted_tail_constant_error": tail_constant_error,
            "omitted_tail_amplitude_error": tail_omission_changes,
            "omitted_angular_energy_fraction": lost_angular_energy_fraction,
            "estimated_quadrature_error": recovered["estimated_quadrature_error"],
        })

    # An honest finite observation provider must reject an integral query
    # beyond its coverage, rather than silently completing the field with zero.
    def finite_observations(y):
        if not -8 <= y <= 8:
            raise CoverageError("Angular data are absent outside [-8,8].")
        return signal(angular_template, y, weighted=True)

    try:
        reconstruct(finite_observations,
                    lambda y: signal(u0, y, weighted=True),
                    lambda y: signal(direction, y, weighted=True), normalization)
    except CoverageError:
        missing_coverage_rejected = True
    else:
        raise AssertionError("Incomplete observations were accepted as complete.")

    return {
        "status": "passed",
        "scope": "direct energy inverse and later coordinate rescaling on controlled analytic fixtures",
        "cases": len(results),
        "maximum_absolute_errors": maxima,
        "checks_clamp_transition_and_nonzero_unclamped_energy": True,
        "checks_consequential_omitted_angular_tail": True,
        "incomplete_observation_coverage_rejected": missing_coverage_rejected,
        "uses_log_radius_and_weighted_fields": True,
        "float64_source_schedule_limit_example": {
            "rate": 1 / 120,
            "log_radial_pulse_length": 13 / (1 / 120),
            "log_largest_finite_float64": math.log(float.fromhex('0x1.fffffffffffffp+1023')),
            "rate_to_power_28": (1 / 120) ** 28,
            "one_plus_rate_to_power_28_equals_one": 1 + (1 / 120) ** 28 == 1,
        },
        "actual_source_Profile_instantiated": False,
        "actual_observed_E_dataset_recovered": False,
        "early_calibration_integrated_into_same_fixture": False,
        "terminal_heat_edit_tested": False,
        "Lean_compiled": False,
        "case_results": results,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Also save the exact JSON result locally.")
    args = parser.parse_args()
    result = run_checks()
    encoded = json.dumps(result, indent=2, allow_nan=False) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")
