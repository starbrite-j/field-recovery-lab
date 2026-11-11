import notes.CoreFieldRecovery

/-!
# A symbolic reproduction of the named original and its exact initial region

This instantiates the inverse with a fixed matching observation constructed
from PreparedOutgoing.prepared.profile. The observation itself is selected by
an existence proof; it is not an independently supplied numerical dataset.

The complete reproduced fields are noncomputable. No numerical P, m, lam, h,
or reset coefficients for the selected original are assigned by this file.
The initial region does give exact U and exact E/P values without those choices.
-/

noncomputable section
open Set

namespace NavierStokes.OriginalFieldReproduction

abbrev original := SourceFieldRecovery.originalProfile

def observedWitness : NominalProfile.Witness original :=
  Classical.choose (PreparedOutgoing.prepared.large_nominal 0 0 le_rfl)

def observedE : FullFieldRecovery.Field := observedWitness.E

def reproducedE : FullFieldRecovery.Field :=
  CoreFieldRecovery.recoveredE observedE (CoreFieldRecovery.assembled_admissible observedWitness)

def reproducedU : FullFieldRecovery.Field :=
  CoreFieldRecovery.recoveredU observedE (CoreFieldRecovery.assembled_admissible observedWitness)

theorem reproducedE_eq_original (x eta : ℝ) (hx : 0 < x)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    reproducedE (x, eta) = original.E (x, eta) :=
  CoreFieldRecovery.recoveredE_source observedWitness _ x eta hx heta

theorem reproducedU_eq_original (x eta : ℝ)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    reproducedU (x, eta) = original.U (x, eta) :=
  CoreFieldRecovery.recoveredU_source observedWitness _ x eta heta

/-- Taking x=t^10 makes normalized angular prefix values rational when t and
eta are rational. The unknown original amplitude P is retained explicitly. -/
theorem reproducedE_prefix (t eta : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    reproducedE (t ^ (10 : ℕ), eta) =
      original.data.core.P * OutgoingSchedule.shape eta * t := by
  rw [reproducedE_eq_original _ eta (pow_pos ht 10) heta,
    original.E_ideal eta (pow_pos ht 10) (pow_le_one₀ ht.le ht1)]
  have hr : (t ^ (10 : ℕ)) ^ (1 / 10 : ℝ) = t := by
    simpa only [Nat.cast_ofNat, one_div] using
      Real.pow_rpow_inv_natCast ht.le (show (10 : ℕ) ≠ 0 by norm_num)
  rw [hr]

theorem reproducedE_prefix_normalized (t eta : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    reproducedE (t ^ (10 : ℕ), eta) / original.data.core.P =
      OutgoingSchedule.shape eta * t := by
  have hP : original.data.core.P ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) PreparedOutgoing.prepared.amplitude_lower)
  rw [reproducedE_prefix t eta ht ht1 heta]
  field_simp [hP]

theorem reproducedU_prefix (t eta : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    reproducedU (t ^ (10 : ℕ), eta) = 4 * eta := by
  rw [reproducedU_eq_original _ eta heta]
  exact original.U_ideal eta (pow_pos ht 10) (pow_le_one₀ ht.le ht1)

end NavierStokes.OriginalFieldReproduction
