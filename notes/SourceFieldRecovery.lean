import NavierStokes.PreparedOutgoing
import notes.FullFieldRecovery

/-!
# Return to the starting field through the actual source construction

Local investigation for Jess, 2026-11-11.
Source revision: f9e8bc5b38b6e212696e8a30e3e91517af887bbd.

The source names a fixed pre-heat outgoing profile:
    PreparedOutgoing.prepared.profile.
ScheduledProfileChoice first builds core, TailData, and a reset witness r,
then F := <d,K,r>. PreparedOutgoing stores this F. NominalProfile.Witness F
uses the same F for its axis and outgoing heat stages.

An important distinction: the final assembled W.E includes an axis section.
It agrees with HeatedOutgoing.E only AFTER W.controls.heatJoin. Feeding W.E
unchanged into an inverse for the whole heated outgoing field would use the
wrong early history. The source supplies the missing outgoing prefix exactly:
P*shape(eta)*(X/XR)^(1/10), because heatJoin<XR and XR<patchRadius.

The reader below takes assembled E, core, and calibration. It fills only
that known ideal prefix, then applies the checked heat/patch inverse and
direct energy reconstruction. No original F, U observations, reset coefficients,
or heat coefficients are reader arguments. The statements identify the
result with the actual source F on X>0, |eta|<=1, after supplied calibration.
The reconstructed later U agrees with W.U on the outgoing side of the join;
the source's separately built axis U is not asserted to be that same field.

The final existence statement instantiates this route for the source's fixed
prepared profile and an actual matching witness. Its choices remain
noncomputable; it does not produce numerical field samples or prove automatic
E-only calibration identification. This file is checked by verify_recovery.py.
-/

noncomputable section

open Set

namespace NavierStokes.SourceFieldRecovery

abbrev Field := FullFieldRecovery.Field
abbrev Calibration := FullFieldRecovery.Calibration
abbrev originalProfile := PreparedOutgoing.prepared.profile

def originalE : Field := originalProfile.E
def originalU : Field := originalProfile.U

/-- The still-earlier angular schedule, before flattening, release, and the
two-bump reset. Its first coordinate is log radius y, not physical radius X. -/
def scheduledLogE : Field :=
  OutgoingSchedule.angular originalProfile.data.core.P originalProfile.data.core.dropLength
    originalProfile.data.core.lam

/-- Complete the outgoing observation using the source's known ideal prefix.
The join is a public source constant times the retained matching radius. -/
def completeOutgoing (observed : Field) (core : OutgoingSchedule.Parameters)
    (XR : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 ≤ XR * NominalProfile.matchFraction then
    core.P * OutgoingSchedule.shape p.2 * (p.1 / XR) ^ (1 / 10 : ℝ)
  else observed p

theorem completeOutgoing_source {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (X eta : ℝ) (hX : 0 < X)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    completeOutgoing W.E F.data.core W.controls.radius (X, eta) =
      HeatedOutgoing.E F W.controls.radius W.heat.coefficients (X, eta) := by
  change (if X ≤ W.controls.heatJoin then
    F.data.core.P * OutgoingSchedule.shape eta * (X / W.controls.radius) ^ (1 / 10 : ℝ)
    else W.E (X, eta)) = _
  by_cases hp : X ≤ W.controls.heatJoin
  · rw [ite_eq_left hp]
    have hXR : X ≤ W.controls.radius := hp.trans W.controls.heatJoin_lt_radius.le
    rw [HeatedOutgoing.E_before_patch F W.controls.radius W.heat.coefficients eta X
      W.controls.radius_pos hX
      (hXR.trans (HeatedOutgoing.entrance_before_patch F W.controls.radius W.controls.radius_pos).le)]
    exact (OutgoingDilation.ideal_prefix F W.controls.radius eta X W.controls.radius_pos hX hXR).1.symm
  · rw [ite_eq_right hp]
    exact (W.heat_agreement (lt_of_not_ge hp) heta).2.1

private theorem restoreE_congr_slice (E G : Field) (k : Calibration)
    (x eta : ℝ) (hx : 0 < x) (hscale : 0 < k.scale) (hpatch : 0 < k.patch)
    (heq : ∀ X : ℝ, 0 < X → E (X, eta) = G (X, eta)) :
    FullFieldRecovery.restoreE E k (x, eta) = FullFieldRecovery.restoreE G k (x, eta) := by
  unfold FullFieldRecovery.restoreE FullFieldRecovery.restoreDilatedE
  dsimp only
  by_cases hp : k.patch ≤ k.scale * x ∧ k.scale * x ≤ k.patch * Real.exp 5
  · rw [ite_eq_left hp, ite_eq_left hp, heq k.patch hpatch]
  · rw [ite_eq_right hp, ite_eq_right hp, heq (k.scale * x) (mul_pos hscale hx)]

def recoverOriginalE (observed : Field) (core : OutgoingSchedule.Parameters)
    (k : Calibration) : Field :=
  FullFieldRecovery.restoreE (completeOutgoing observed core k.scale) k

def recoverOriginalU (observed : Field) (core : OutgoingSchedule.Parameters)
    (k : Calibration) : Field :=
  AxialFromAngular.UFromField core (recoverOriginalE observed core k)

def recoverLaterU (observed : Field) (core : OutgoingSchedule.Parameters)
    (k : Calibration) (p : ℝ × ℝ) : ℝ :=
  recoverOriginalU observed core k (p.1 / k.scale, p.2)

theorem recoverOriginalE_source {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (x eta : ℝ) (hx : 0 < x)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    recoverOriginalE W.E F.data.core (FullFieldRecovery.sourceCalibration F W.controls.radius)
      (x, eta) = F.E (x, eta) := by
  have heq := fun X hX => completeOutgoing_source W X eta hX heta
  have hpatch := OutgoingDilation.patchRadius_pos F W.controls.radius W.controls.radius_pos
  exact (restoreE_congr_slice
    (completeOutgoing W.E F.data.core W.controls.radius)
    (HeatedOutgoing.E F W.controls.radius W.heat.coefficients)
    (FullFieldRecovery.sourceCalibration F W.controls.radius)
    x eta hx W.controls.radius_pos hpatch heq).trans
    (FullFieldRecovery.restoreE_roundtrip F W.controls.radius W.heat.coefficients
      x eta W.controls.radius_pos hx heta)

theorem recoverOriginalU_source {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (x eta : ℝ)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    recoverOriginalU W.E F.data.core (FullFieldRecovery.sourceCalibration F W.controls.radius)
      (x, eta) = F.U (x, eta) := by
  have heq := fun X hX => recoverOriginalE_source W X eta hX heta
  exact (AxialFromAngular.UFromField_congr_slice F.data.core
    (recoverOriginalE W.E F.data.core (FullFieldRecovery.sourceCalibration F W.controls.radius))
    F.E eta x heq).trans (congrFun (AxialFromAngular.UFromField_source F) (x, eta))

theorem recoverLaterU_source {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (X eta : ℝ)
    (hX : W.controls.heatJoin < X) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    recoverLaterU W.E F.data.core (FullFieldRecovery.sourceCalibration F W.controls.radius)
      (X, eta) = W.U (X, eta) := by
  change recoverOriginalU W.E F.data.core
    (FullFieldRecovery.sourceCalibration F W.controls.radius)
    (X / W.controls.radius, eta) = _
  rw [recoverOriginalU_source W (X / W.controls.radius) eta heta]
  exact (W.heat_agreement (p := (X, eta)) hX heta).1.symm

/-- An actual source-selected starting profile has matching assembled fields
whose outgoing E and U reconstruct this same profile after calibration. -/
theorem exists_matched_recovery (floor : ℝ) :
    ∃ W : NominalProfile.Witness originalProfile,
      floor < W.controls.radius ∧
      ∀ x eta : ℝ, 0 < x → eta ∈ HeatedOutgoing.parameterDomain →
        recoverOriginalE W.E originalProfile.data.core
          (FullFieldRecovery.sourceCalibration originalProfile W.controls.radius) (x, eta) =
            originalE (x, eta) ∧
        recoverOriginalU W.E originalProfile.data.core
          (FullFieldRecovery.sourceCalibration originalProfile W.controls.radius) (x, eta) =
            originalU (x, eta) := by
  obtain ⟨W, hR, _⟩ := PreparedOutgoing.prepared.large_nominal floor 0 le_rfl
  refine ⟨W, hR, ?_⟩
  intro x eta hx heta
  exact ⟨recoverOriginalE_source W x eta hx heta, recoverOriginalU_source W x eta heta⟩

end NavierStokes.SourceFieldRecovery
