import NavierStokes.OutgoingProfile

/-!
# Axial recovery directly from the restored angular field

Local source-derived investigation for Jess, 2026-11-11.
Source revision: f9e8bc5b38b6e212696e8a30e3e91517af887bbd.

STATUS: Compiled successfully with the pinned Lean 4.34.0-rc2 toolchain on
2026-11-11. The source identity and slice-congruence proofs below are checked.
The axiom audit reports only propext, Classical.choice, and Quot.sound for
the audited recovery theorems, with no unfinished-proof axiom. See
notes/verification/proof_verification.json and RecoveryAxiomAudit.log.
These proofs use the repository's actual energy identity, not a substituted
numerical bump or a guessed heat coefficient. They assume the stated original
angular field and schedule, and do not prove E-only calibration identification.

This removes an unnecessary intermediate dependency in FullFieldRecovery:
once the original angular field E and its core schedule have been recovered,
there is no need to recover either the earlier two reset coefficients or the
later three heat coefficients in order to reconstruct U.

For a trial amplitude A=0 the normalized total-energy polynomial is exactly
its constant coefficient C. Compute that energy from the supplied E and the
known zero-amplitude axial schedule. The remaining quadratic and linear
coefficients depend only on the core schedule. Insert C into the SAME clamped
positive-root formula that Profile.amp actually uses, then evaluate axial.

The clamp matters: a bare Profile record does not by itself assert zero total
energy. Using the source's negativeClamp makes the identity valid for every
Profile, without quietly adding an energy-zero or small-error hypothesis.

Sources: CorrectedPulseAmplitude.totalEnergy_normalized (59-66),
energyPolynomial (55-57), amplitude (85-87); OutgoingProfile.Profile.amp,
logE, logU, E, U (31-41). The field integral is over the entire log radius.
Unknown or omitted angular tails therefore invalidate an exact recovery claim.
This is an exact-real inverse, not a certified finite-sample quadrature routine.

Local check commands, only after the matching toolchain, dependencies and
imported library modules are already available (no network setup implied):
    mkdir -p .lake/build/lib/lean/notes
    lake env lean -o .lake/build/lib/lean/notes/AxialFromAngular.olean notes/AxialFromAngular.lean
    lake env lean notes/FullFieldRecovery.lean
-/

noncomputable section

open Set Filter MeasureTheory

namespace NavierStokes.AxialFromAngular

abbrev Field := (ℝ × ℝ) → ℝ

/-- Read the normalized energy polynomial at trial amplitude zero. -/
def constantFromField (core : OutgoingSchedule.Parameters) (E : Field) (eta : ℝ) : ℝ :=
  core.lam *
    (∫ y : ℝ, Real.exp y *
      (OutgoingSchedule.axial core (fun _ => 0) (y, eta) ^ 2 -
        E (Real.exp y, eta) ^ 2 / 2)) /
    (PulseAmplitude.normalization core * OutgoingSchedule.shape eta ^ 2)

/-- The root convention is the one in CorrectedPulseAmplitude.amplitude. -/
def amplitudeFromField (core : OutgoingSchedule.Parameters) (E : Field) (eta : ℝ) : ℝ :=
  (-PulseAmplitude.linearTerm core eta + Real.sqrt
    (PulseAmplitude.linearTerm core eta ^ 2 -
      4 * PulseAmplitude.quadraticCoefficient core *
        PulseAmplitude.negativeClamp (constantFromField core E eta))) /
    (2 * PulseAmplitude.quadraticCoefficient core)

def UFromField (core : OutgoingSchedule.Parameters) (E : Field) (p : ℝ × ℝ) : ℝ :=
  OutgoingSchedule.axial core (amplitudeFromField core E) (Real.log p.1, p.2)

/-- Source-instantiation proof: the observed angular field supplies
the exact constant term, including the earlier reset's energy contribution. -/
theorem constantFromField_source (F : OutgoingProfile.Profile) (eta : ℝ) :
    constantFromField F.data.core F.E eta =
      CorrectedPulseAmplitude.constantTerm F.data F.reset.coefficients eta := by
  have h := CorrectedPulseAmplitude.totalEnergy_normalized
    F.data F.reset.coefficients 0 eta
  simpa only [constantFromField, CorrectedPulseAmplitude.totalEnergy,
    CorrectedPulseAmplitude.energyIntegrand, OutgoingProfile.Profile.E,
    OutgoingProfile.Profile.logE, Real.log_exp,
    CorrectedPulseAmplitude.energyPolynomial, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add] using h

theorem amplitudeFromField_source (F : OutgoingProfile.Profile) :
    amplitudeFromField F.data.core F.E = F.amp := by
  funext eta
  rw [amplitudeFromField, constantFromField_source]
  rfl

/-- Exact mathematical statement of the missing-U reconstruction. The proof
does not take a reset witness separately, original U samples, or heat c. -/
theorem UFromField_source (F : OutgoingProfile.Profile) :
    UFromField F.data.core F.E = F.U := by
  funext p
  rw [UFromField, amplitudeFromField_source]
  rfl

/-- For a fixed core, the original angular field determines the axial field. -/
theorem same_core_and_E_same_U (F G : OutgoingProfile.Profile)
    (hcore : F.data.core = G.data.core) (hE : F.E = G.E) : F.U = G.U := by
  rw [← UFromField_source F, ← UFromField_source G, hcore, hE]

/-- Recovery at one eta needs that angular slice on positive radii only.
Arbitrary angular extensions outside the physical eta band are not inputs. -/
theorem UFromField_congr_slice (core : OutgoingSchedule.Parameters)
    (E G : Field) (eta x : ℝ)
    (hE : ∀ X : ℝ, 0 < X → E (X, eta) = G (X, eta)) :
    UFromField core E (x, eta) = UFromField core G (x, eta) := by
  have hi : (∫ y : ℝ, Real.exp y *
      (OutgoingSchedule.axial core (fun _ => 0) (y, eta) ^ 2 -
        E (Real.exp y, eta) ^ 2 / 2)) =
      ∫ y : ℝ, Real.exp y *
      (OutgoingSchedule.axial core (fun _ => 0) (y, eta) ^ 2 -
        G (Real.exp y, eta) ^ 2 / 2) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by
      dsimp only
      rw [hE (Real.exp y) (Real.exp_pos y)])
  have hc : constantFromField core E eta = constantFromField core G eta := by
    unfold constantFromField
    rw [hi]
  have ha : amplitudeFromField core E eta = amplitudeFromField core G eta := by
    simp only [amplitudeFromField, hc]
  exact PulseAmplitude.axial_eq_of_amplitude_eq core
    (amplitudeFromField core E) (amplitudeFromField core G) eta (Real.log x) ha

end NavierStokes.AxialFromAngular
