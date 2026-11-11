import notes.ObservedFieldRecovery

/-!
# Observable markers for the core of an assembled field

No core parameters, scale, calibration, reset coefficients, heat coefficients,
or U observations are supplied to the readers. Scalar admissibility is proved
for the actual source family; its inequalities alone do not certify membership
for an arbitrary field. Correctness is stated for NominalProfile.Witness.

The endpoint marker uses the LAST physical radius with E(X,0)=2 E(X,1),
so arbitrary earlier axis behavior cannot move it. Later reset bumps cannot
recreate this ratio: their derivative bound and compact support give a
stronger value bound than their standalone positivity bound. Heating can
only decrease the eta=0 slice and leaves eta=1 unchanged.

All readers here use the complete exact angular field. They are not finite
sample locators or noise-tolerant numerical algorithms.

The marker chain is: last 2:1 ratio -> endpoint -> clean late-core rate ->
physical patch boundary -> last initial-slope marker before that patch ->
radial scale -> second ramp -> m. The entrance amplitude gives P; the endpoint
time minus pulse length and hold start gives wait. The boundary tail supplies h
through ObservedFieldRecovery, which completes calibration and E/U recovery.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace NavierStokes.CoreFieldRecovery

abbrev Field := FullFieldRecovery.Field

theorem reset_relative_bound (F : OutgoingProfile.Profile) (eta u : ℝ) :
    |AngularMomentReset.relative (F.reset.coefficients eta) u| ≤ F.data.core.lam := by
  let f := AngularMomentReset.relative (F.reset.coefficients eta)
  by_cases hzero : f u = 0
  · change |f u| ≤ _
    simpa only [hzero, abs_zero] using F.data.core.lam_pos.le
  have hu := AngularMomentReset.relative_support (F.reset.coefficients eta) hzero
  have hleft : f (-1) = 0 := by
    by_contra hn
    have hs := AngularMomentReset.relative_support (F.reset.coefficients eta) hn
    norm_num at hs
  have hd : Differentiable ℝ f :=
    (AngularMomentReset.relative_contDiff (F.reset.coefficients eta)).differentiable (by simp)
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (-1 : ℝ)) (b := u) (C := F.data.core.lam / 4)
    (fun x _ => (hd x).hasDerivAt.hasDerivWithinAt)
    (fun x _ => by simpa only [Real.norm_eq_abs] using (F.reset.small_jets eta x).2)
    u ⟨by linarith [hu.1], le_rfl⟩
  rw [hleft, sub_zero, Real.norm_eq_abs] at hm
  exact hm.trans (by nlinarith [hu.2, F.data.core.lam_pos])

theorem logE_ratio_after_core (F : OutgoingProfile.Profile) {y : ℝ}
    (hy : F.data.core.endpoint < y) : F.logE (y, 0) < 2 * F.logE (y, 1) := by
  by_cases hf : F.data.flattenEnd ≤ y
  · have he := OutgoingTail.finalAngular_eta_independent F.data 0 1 hf
    have hp := OutgoingTail.finalAngular_pos F.data (y, 1)
    have h0 := abs_le.mp (reset_relative_bound F 0
      (y - UniformAngularReset.correctionCenter F.data))
    have h1 := abs_le.mp (reset_relative_bound F 1
      (y - UniformAngularReset.correctionCenter F.data))
    have hb : 1 + AngularMomentReset.relative (F.reset.coefficients 0)
        (y - UniformAngularReset.correctionCenter F.data) <
        2 * (1 + AngularMomentReset.relative (F.reset.coefficients 1)
          (y - UniformAngularReset.correctionCenter F.data)) := by
      linarith [F.data.core.lam_lt]
    unfold OutgoingProfile.Profile.logE UniformAngularReset.correctedAngular
    rw [he]
    nlinarith [mul_pos hp (sub_pos.mpr hb)]
  · have hno : y ∉ Ioo (F.data.releaseStart - 4) F.data.releaseStart := by
      intro hs
      linarith [UniformAngularReset.last_four_after_flatten F.data, hs.1]
    rw [OutgoingProfile.Profile.logE, UniformAngularReset.correctedAngular_unchanged
      F.data F.reset.coefficients 0 hno,
      UniformAngularReset.correctedAngular_unchanged F.data F.reset.coefficients 1 hno]
    have hs : 0 < OutgoingSchedule.sigma ((y - F.data.core.endpoint) / OutgoingTail.flattenLength) := by
      exact div_pos (FlatCutoff.edge_pos 1 (div_pos (sub_pos.mpr hy) OutgoingTail.flattenLength_pos))
        (OutgoingSchedule.sigma_denom_pos _)
    have he : Real.exp (OutgoingSchedule.sigma
        ((y - F.data.core.endpoint) / OutgoingTail.flattenLength) * (-Real.log 2)) < 1 :=
      Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hs
        (neg_neg_of_pos (Real.log_pos (by norm_num))))
    have hA : 0 < OutgoingSchedule.radialAmplitude F.data.core.P F.data.core.dropLength
        F.data.core.lam y := mul_pos F.data.core.P_pos (Real.exp_pos _)
    have hflat : OutgoingTail.flattened F.data (y, 0) <
        2 * OutgoingTail.flattened F.data (y, 1) := by
      norm_num [OutgoingTail.flattened, OutgoingSchedule.angular, OutgoingSchedule.shape,
        OutgoingTail.flattenFactor, OutgoingTail.logShape]
      have he' : Real.exp (-(OutgoingSchedule.sigma
          ((y - F.data.core.endpoint) / OutgoingTail.flattenLength) * Real.log 2)) < 1 := by
        simpa only [mul_neg] using he
      nlinarith [mul_pos hA (sub_pos.mpr he')]
    have hB := Real.exp_pos (OutgoingTail.releaseAdjustment F.data (y - F.data.releaseStart))
    have hC : 0 < OutgoingTail.tailShape F.data (y - OutgoingTail.tailStart F.data) /
        (1 - F.data.rho) := div_pos (OutgoingTail.tailShape_pos F.data _)
      (by linarith [F.data.rho_lt_half])
    have hm := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hflat hB) hC
    simpa only [OutgoingTail.finalAngular, mul_assoc] using hm

theorem pulseLength_gt_two (core : OutgoingSchedule.Parameters) : 2 < core.pulseLength := by
  apply (lt_div_iff₀ core.lam_pos).mpr
  linarith [core.lam_lt]

theorem endpoint_window_after_patch (F : OutgoingProfile.Profile) :
    OutgoingDilation.patchClock F + 5 < F.data.core.endpoint - 2 := by
  dsimp only [OutgoingDilation.patchClock, OutgoingSchedule.Parameters.endpoint]
  linarith [pulseLength_gt_two F.data.core]

theorem endpoint_window_pos (core : OutgoingSchedule.Parameters) : 0 < core.endpoint - 2 := by
  dsimp only [OutgoingSchedule.Parameters.endpoint]
  linarith [pulseLength_gt_two core, core.pulseStart_pos]

theorem endpoint_before_switch (F : OutgoingProfile.Profile) :
    F.data.core.endpoint < HeatTailEdit.switchStart F.data := by
  have h1 := OutgoingTail.flattenEnd_gt_core F.data
  have h2 := OutgoingTail.releaseStart_gt_flattenEnd F.data
  have h3 := OutgoingTail.tailStart_gt_release F.data
  dsimp only [HeatTailEdit.switchStart]
  linarith

theorem assembled_core_window {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (y eta : ℝ)
    (hlo : F.data.core.endpoint - 2 ≤ y) (hhi : y ≤ F.data.core.endpoint)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    W.E (W.controls.radius * Real.exp y, eta) =
      OutgoingSchedule.angular F.data.core.P F.data.core.dropLength F.data.core.lam (y, eta) := by
  have hy : 0 < y := (endpoint_window_pos F.data.core).trans_le hlo
  have hR : W.controls.radius ≤ W.controls.radius * Real.exp y := by
    nlinarith [Real.one_le_exp_iff.mpr hy.le, W.controls.radius_pos]
  have hpatch : OutgoingDilation.patchRadius F W.controls.radius *
      OutgoingDilation.compensationPatch.right ≤ W.controls.radius * Real.exp y := by
    change W.controls.radius * Real.exp (OutgoingDilation.patchClock F) * Real.exp 5 ≤ _
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      ((endpoint_window_after_patch F).le.trans hlo)) W.controls.radius_pos.le
  have hswitch : W.controls.radius * Real.exp y ≤ OutgoingDilation.switchRadius F W.controls.radius :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (hhi.trans (endpoint_before_switch F).le)) W.controls.radius_pos.le
  rw [(W.heat_agreement (p := (W.controls.radius * Real.exp y, eta))
    (W.controls.heatJoin_lt_radius.trans_le hR) heta).2.1]
  change HeatedOutgoing.E F W.controls.radius W.heat.coefficients
    (W.controls.radius * Real.exp y, eta) = _
  rw [HeatedOutgoing.E_between_patch_and_switch F W.controls.radius W.heat.coefficients eta _
    W.controls.radius_pos (W.controls.radius_pos.trans_le hR) hpatch hswitch]
  change F.logE (Real.log ((W.controls.radius * Real.exp y) / W.controls.radius), eta) = _
  rw [mul_div_cancel_left₀ _ W.controls.radius_pos.ne', Real.log_exp]
  exact F.logE_before eta hhi

theorem assembled_ratio_after_core {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) {X : ℝ}
    (hX : W.controls.radius * Real.exp F.data.core.endpoint < X) :
    W.E (X, 0) < 2 * W.E (X, 1) := by
  have hXp : 0 < X := (mul_pos W.controls.radius_pos (Real.exp_pos _)).trans hX
  have hy : F.data.core.endpoint < Real.log (X / W.controls.radius) :=
    (OutgoingDilation.radius_lt_iff W.controls.radius X F.data.core.endpoint
      W.controls.radius_pos hXp).mp hX
  have hR : W.controls.radius < X := by
    have he := Real.one_le_exp_iff.mpr ((endpoint_window_pos F.data.core).le.trans (by linarith :
      F.data.core.endpoint - 2 ≤ F.data.core.endpoint))
    nlinarith [W.controls.radius_pos]
  have hpatch : OutgoingDilation.patchRadius F W.controls.radius *
      OutgoingDilation.compensationPatch.right < X := by
    calc
      _ = W.controls.radius * Real.exp (OutgoingDilation.patchClock F + 5) := by
        change W.controls.radius * Real.exp (OutgoingDilation.patchClock F) * Real.exp 5 = _
        rw [Real.exp_add]
        ring
      _ < W.controls.radius * Real.exp F.data.core.endpoint :=
        mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith [endpoint_window_after_patch F]))
          W.controls.radius_pos
      _ < X := hX
  have hc (eta : ℝ) : TerminalCompensation.correction OutgoingDilation.compensationPatch
      (W.heat.coefficients eta) (X / OutgoingDilation.patchRadius F W.controls.radius) = 0 := by
    apply HeatedOutgoing.correction_zero_outside
    intro ht
    have hr := (div_le_iff₀ (OutgoingDilation.patchRadius_pos F W.controls.radius
      W.controls.radius_pos)).mp ht.2
    exact (not_le_of_gt hpatch) (by simpa only [mul_comm] using hr)
  have hmul1 : HeatTailEdit.multiplier F.data.h (ParametricHeatTail.diffusion 1)
      (OutgoingDilation.switchRadius F W.controls.radius) X = 1 := by
    have hp := RadialHeatProfile.profile_zero (a := 1 + F.data.h) (by linarith [F.data.h_pos])
    norm_num [HeatTailEdit.multiplier, ParametricHeatTail.diffusion, hp]
  have hm0 := (HeatTailEdit.multiplier_bounds (K := OutgoingDilation.switchRadius F W.controls.radius)
    F.data.h_pos (show 0 ≤ ParametricHeatTail.diffusion 0 by norm_num [ParametricHeatTail.diffusion]) hXp).2
  rw [(W.heat_agreement (p := (X, 0)) (W.controls.heatJoin_lt_radius.trans hR)
    (by norm_num [HeatedOutgoing.parameterDomain])).2.1,
    (W.heat_agreement (p := (X, 1)) (W.controls.heatJoin_lt_radius.trans hR)
    (by norm_num [HeatedOutgoing.parameterDomain])).2.1]
  change HeatedOutgoing.E F W.controls.radius W.heat.coefficients (X, 0) <
    2 * HeatedOutgoing.E F W.controls.radius W.heat.coefficients (X, 1)
  simp only [HeatedOutgoing.E, HeatedOutgoing.heatE, HeatedOutgoing.patchIncrement,
    hc, mul_zero, add_zero, hmul1, mul_one]
  have he := logE_ratio_after_core F hy
  have hp := OutgoingDilation.positive F W.controls.radius (X, 0)
  change OutgoingDilation.E F W.controls.radius (X, 0) * _ < _
  exact (mul_le_of_le_one_right hp.le hm0).trans_lt he

def endpointRadius (observed : Field) : ℝ :=
  sSup {X : ℝ | 0 < X ∧ observed (X, 0) = 2 * observed (X, 1)}

theorem endpointRadius_source {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) :
    endpointRadius W.E = W.controls.radius * Real.exp F.data.core.endpoint := by
  let R := W.controls.radius * Real.exp F.data.core.endpoint
  have hmem : R ∈ {X : ℝ | 0 < X ∧ W.E (X, 0) = 2 * W.E (X, 1)} := by
    refine ⟨mul_pos W.controls.radius_pos (Real.exp_pos _), ?_⟩
    rw [assembled_core_window W _ 0 (by linarith) le_rfl
      (by norm_num [HeatedOutgoing.parameterDomain]),
      assembled_core_window W _ 1 (by linarith) le_rfl
      (by norm_num [HeatedOutgoing.parameterDomain])]
    norm_num [OutgoingSchedule.angular, OutgoingSchedule.shape]
    ring
  have hbound : ∀ X ∈ {X : ℝ | 0 < X ∧ W.E (X, 0) = 2 * W.E (X, 1)}, X ≤ R := by
    intro X hX
    by_contra hn
    have hs := assembled_ratio_after_core W (lt_of_not_ge hn)
    linarith [hX.2]
  exact le_antisymm (csSup_le ⟨R, hmem⟩ hbound) (le_csSup ⟨R, hbound⟩ hmem)

def readRate (observed : Field) : ℝ :=
  -(Real.log (observed (Real.exp (Real.log (endpointRadius observed) - 1), 0)) -
    Real.log (observed (Real.exp (Real.log (endpointRadius observed) - 2), 0))) - 1 / 2

theorem readRate_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    readRate W.E = F.data.core.lam := by
  unfold readRate
  rw [endpointRadius_source W, Real.log_mul W.controls.radius_pos.ne' (Real.exp_ne_zero _), Real.log_exp]
  have hexp (s : ℝ) : Real.exp (Real.log W.controls.radius + F.data.core.endpoint - s) =
      W.controls.radius * Real.exp (F.data.core.endpoint - s) := by
    rw [show Real.log W.controls.radius + F.data.core.endpoint - s =
      Real.log W.controls.radius + (F.data.core.endpoint - s) by ring, Real.exp_add,
      Real.exp_log W.controls.radius_pos]
  rw [hexp 1, hexp 2,
    assembled_core_window W _ 0 (by linarith) (by linarith)
      (by norm_num [HeatedOutgoing.parameterDomain]),
    assembled_core_window W _ 0 le_rfl (by linarith)
      (by norm_num [HeatedOutgoing.parameterDomain])]
  norm_num only [OutgoingSchedule.angular, OutgoingSchedule.shape, zero_pow, add_zero,
    inv_one, mul_one]
  have hh : F.data.core.dropLength + 2 ≤ F.data.core.endpoint - 2 := by
    change F.data.core.holdStart ≤ _
    dsimp only [OutgoingSchedule.Parameters.endpoint, OutgoingSchedule.Parameters.pulseStart]
    linarith [F.data.core.wait_gt, pulseLength_gt_two F.data.core]
  rw [OutgoingSchedule.radialAmplitude_hold F.data.core.dropLength_pos.le hh
    (show F.data.core.endpoint - 2 ≤ F.data.core.endpoint - 1 by linarith)]
  have hp : 0 < OutgoingSchedule.radialAmplitude F.data.core.P F.data.core.dropLength
      F.data.core.lam (F.data.core.endpoint - 2) := mul_pos F.data.core.P_pos (Real.exp_pos _)
  rw [Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

def readPatchRadius (observed : Field) : ℝ :=
  endpointRadius observed * Real.exp (-(13 / readRate observed) - 20)

theorem readPatchRadius_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    readPatchRadius W.E = OutgoingDilation.patchRadius F W.controls.radius := by
  unfold readPatchRadius
  rw [endpointRadius_source W, readRate_source W]
  change W.controls.radius * Real.exp F.data.core.endpoint *
    Real.exp (-(13 / F.data.core.lam) - 20) =
    W.controls.radius * Real.exp (F.data.core.pulseStart - 20)
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  dsimp only [OutgoingSchedule.Parameters.endpoint, OutgoingSchedule.Parameters.pulseLength]
  ring

theorem sigma_half : OutgoingSchedule.sigma (1 / 2) = 1 / 2 := by
  have hp := FlatCutoff.edge_pos 1 (show (0 : ℝ) < 1 / 2 by norm_num)
  norm_num only [OutgoingSchedule.sigma, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  field_simp
  ring

theorem sigma_gt_half {y : ℝ} (hy : 1 / 2 < y) : 1 / 2 < OutgoingSchedule.sigma y := by
  have hleft : 0 < FlatCutoff.edge 1 y := FlatCutoff.edge_pos 1 (by linarith)
  have hcross : FlatCutoff.edge 1 (1 - y) < FlatCutoff.edge 1 y := by
    by_cases hlate : 1 ≤ y
    · rw [FlatCutoff.edge_of_nonpos 1 (by linarith)]
      exact hleft
    · have hy1 : 0 < 1 - y := by linarith
      have hyp : 0 < y := by linarith
      rw [FlatCutoff.edge_of_pos 1 hy1, FlatCutoff.edge_of_pos 1 hyp]
      apply Real.exp_lt_exp.mpr
      apply (div_lt_div_iff₀ (sq_pos_of_pos hy1) (sq_pos_of_pos hyp)).mpr
      nlinarith
  exact (lt_div_iff₀ (OutgoingSchedule.sigma_denom_pos y)).mpr (by linarith)

theorem patchClock_gt_two (F : OutgoingProfile.Profile) : 2 < OutgoingDilation.patchClock F := by
  dsimp only [OutgoingDilation.patchClock, OutgoingSchedule.Parameters.pulseStart,
    OutgoingSchedule.Parameters.holdStart, OutgoingSchedule.Parameters.dropLength]
  linarith [F.data.core.wait_gt, Real.exp_pos F.data.core.m]

theorem assembled_early {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (y eta : ℝ) (hlo : -5 < y) (hhi : y ≤ OutgoingDilation.patchClock F)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    W.E (W.controls.radius * Real.exp y, eta) =
      OutgoingSchedule.angular F.data.core.P F.data.core.dropLength F.data.core.lam (y, eta) := by
  have hjoin : W.controls.heatJoin < W.controls.radius * Real.exp y :=
    mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hlo) W.controls.radius_pos
  have hpatch : W.controls.radius * Real.exp y ≤ OutgoingDilation.patchRadius F W.controls.radius :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hhi) W.controls.radius_pos.le
  rw [(W.heat_agreement (p := (W.controls.radius * Real.exp y, eta)) hjoin heta).2.1]
  change HeatedOutgoing.E F W.controls.radius W.heat.coefficients
    (W.controls.radius * Real.exp y, eta) = _
  rw [HeatedOutgoing.E_before_patch F W.controls.radius W.heat.coefficients eta _
    W.controls.radius_pos (mul_pos W.controls.radius_pos (Real.exp_pos y)) hpatch]
  change F.logE (Real.log ((W.controls.radius * Real.exp y) / W.controls.radius), eta) = _
  rw [mul_div_cancel_left₀ _ W.controls.radius_pos.ne', Real.log_exp]
  exact F.logE_before eta (by linarith [endpoint_window_after_patch F])

private theorem core_log_hasDerivAt (core : OutgoingSchedule.Parameters) (y : ℝ) :
    HasDerivAt (fun t => Real.log (OutgoingSchedule.radialAmplitude core.P core.dropLength core.lam t))
      (OutgoingSchedule.slope core.dropLength core.lam y - 1 / 2) y := by
  have hp : 0 < OutgoingSchedule.radialAmplitude core.P core.dropLength core.lam y :=
    mul_pos core.P_pos (Real.exp_pos _)
  convert (OutgoingSchedule.radialAmplitude_hasDerivAt core.P core.dropLength core.lam y).log hp.ne'
    using 1
  field_simp

theorem assembled_logSlope_early {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (y : ℝ) (hlo : -5 < y) (hhi : y < OutgoingDilation.patchClock F) :
    FullFieldRecovery.EOnly.logSlope W.E (Real.log W.controls.radius + y) =
      OutgoingSchedule.slope F.data.core.dropLength F.data.core.lam y - 1 / 2 := by
  let r := Real.log W.controls.radius
  have heq : FullFieldRecovery.EOnly.logAngular W.E =ᶠ[𝓝 (r + y)]
      (fun z => Real.log (OutgoingSchedule.radialAmplitude F.data.core.P F.data.core.dropLength
        F.data.core.lam (z - r))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show r + y ∈ Ioo (r - 5)
      (r + OutgoingDilation.patchClock F) by constructor <;> linarith)] with z hz
    have hexp : Real.exp z = W.controls.radius * Real.exp (z - r) := by
      calc
        _ = Real.exp (r + (z - r)) := by congr 1; ring
        _ = _ := by rw [Real.exp_add, Real.exp_log W.controls.radius_pos]
    unfold FullFieldRecovery.EOnly.logAngular
    rw [hexp, assembled_early W _ 0 (by linarith [hz.1]) (by linarith [hz.2])
      (by norm_num [HeatedOutgoing.parameterDomain])]
    norm_num [OutgoingSchedule.angular, OutgoingSchedule.shape]
  unfold FullFieldRecovery.EOnly.logSlope
  rw [heq.deriv_eq]
  have hd := (core_log_hasDerivAt F.data.core (r + y - r)).comp (r + y)
    ((hasDerivAt_id (r + y)).sub_const r)
  simpa only [Function.comp_def, id_eq, add_sub_cancel_left, mul_one] using hd.deriv

def readLogScale (observed : Field) : ℝ :=
  sSup {z : ℝ | z < Real.log (readPatchRadius observed) ∧
    FullFieldRecovery.EOnly.logSlope observed z = -(1 / 5 : ℝ)} - 1 / 2

theorem readLogScale_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    readLogScale W.E = Real.log W.controls.radius := by
  let r := Real.log W.controls.radius
  let S := {z : ℝ | z < Real.log (readPatchRadius W.E) ∧
    FullFieldRecovery.EOnly.logSlope W.E z = -(1 / 5 : ℝ)}
  have hpatch : Real.log (readPatchRadius W.E) = r + OutgoingDilation.patchClock F := by
    rw [readPatchRadius_source W]
    exact Real.log_mul W.controls.radius_pos.ne' (Real.exp_ne_zero _)
      |>.trans (by rw [Real.log_exp])
  have hmem : r + 1 / 2 ∈ S := by
    constructor
    · rw [hpatch]
      linarith [patchClock_gt_two F]
    · rw [assembled_logSlope_early W (1 / 2) (by norm_num) (by linarith [patchClock_gt_two F])]
      rw [OutgoingSchedule.slope, sigma_half,
        OutgoingSchedule.sigma_zero (show (1 / 2 : ℝ) - (F.data.core.dropLength + 1) ≤ 0 by
          linarith [F.data.core.dropLength_pos])]
      norm_num
  have hbound : ∀ z ∈ S, z ≤ r + 1 / 2 := by
    intro z hz
    by_contra hn
    have hy : 1 / 2 < z - r := by linarith
    have hhi : z - r < OutgoingDilation.patchClock F := by
      have := hz.1
      rw [hpatch] at this
      linarith
    have hd := assembled_logSlope_early W (z - r) (by linarith) hhi
    have hd' : FullFieldRecovery.EOnly.logSlope W.E z =
        OutgoingSchedule.slope F.data.core.dropLength F.data.core.lam (z - r) - 1 / 2 := by
      have hclock : Real.log W.controls.radius + (z - r) = z := by dsimp [r]; ring
      simpa only [hclock] using hd
    rw [hz.2] at hd'
    unfold OutgoingSchedule.slope at hd'
    have hs := sigma_gt_half hy
    have hn := mul_nonneg F.data.core.lam_pos.le
      (OutgoingSchedule.sigma_nonneg ((z - r) - (F.data.core.dropLength + 1)))
    nlinarith
  have hsup : sSup S = r + 1 / 2 :=
    le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)
  change sSup S - 1 / 2 = r
  rw [hsup]
  ring

def secondRampStart (observed : Field) : ℝ :=
  sInf {y : ℝ | 1 < y ∧
    FullFieldRecovery.EOnly.logSlope observed (readLogScale observed + y) ≠ -(1 / 2 : ℝ)}

theorem secondRampStart_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    secondRampStart W.E = F.data.core.dropLength + 1 := by
  let T := F.data.core.dropLength + 1
  let S := {y : ℝ | 1 < y ∧
    FullFieldRecovery.EOnly.logSlope W.E (readLogScale W.E + y) ≠ -(1 / 2 : ℝ)}
  have hTp : 1 < T := by dsimp [T]; linarith [F.data.core.dropLength_pos]
  have hTpatch : T + 1 < OutgoingDilation.patchClock F := by
    have h := OutgoingDilation.patchClock_after_hold F
    dsimp only [OutgoingSchedule.Parameters.holdStart] at h
    dsimp [T]
    linarith
  have hmem (delta : ℝ) (hdp : 0 < delta) (hdl : delta < 1) : T + delta ∈ S := by
    refine ⟨by linarith, ?_⟩
    rw [readLogScale_source W,
      assembled_logSlope_early W (T + delta) (by linarith) (by linarith)]
    intro hh
    rw [OutgoingSchedule.slope, OutgoingSchedule.sigma_one (show 1 ≤ T + delta by linarith)] at hh
    have hs : 0 < OutgoingSchedule.sigma (T + delta - (F.data.core.dropLength + 1)) := by
      have he : T + delta - (F.data.core.dropLength + 1) = delta := by dsimp [T]; ring
      rw [he]
      exact div_pos (FlatCutoff.edge_pos 1 hdp) (OutgoingSchedule.sigma_denom_pos delta)
    nlinarith [mul_pos F.data.core.lam_pos hs]
  have hbound : ∀ y ∈ S, T ≤ y := by
    intro y hy
    by_contra hn
    have hhi : y < OutgoingDilation.patchClock F := by linarith
    have hh := hy.2
    rw [readLogScale_source W, assembled_logSlope_early W y (by linarith [hy.1]) hhi,
      OutgoingSchedule.slope_drop hy.1.le (by linarith)] at hh
    norm_num at hh
  have hnear : ∀ b : ℝ, T < b → ∃ y ∈ S, y < b := by
    intro b hb
    let delta := min ((b - T) / 2) (1 / 2 : ℝ)
    have hdp : 0 < delta := lt_min (by linarith) (by norm_num)
    have hdl : delta < 1 := (min_le_right _ _).trans_lt (by norm_num)
    refine ⟨T + delta, hmem delta hdp hdl, ?_⟩
    have := min_le_left ((b - T) / 2) (1 / 2 : ℝ)
    dsimp [delta]
    linarith
  exact csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    ⟨T + 1 / 2, hmem (1 / 2) (by norm_num) (by norm_num)⟩ hbound hnear

def readM (observed : Field) : ℝ := Real.log (secondRampStart observed - 11)

theorem readM_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    readM W.E = F.data.core.m := by
  rw [readM, secondRampStart_source W]
  have he : F.data.core.dropLength + 1 - 11 = Real.exp F.data.core.m := by
    dsimp only [OutgoingSchedule.Parameters.dropLength]
    ring
  rw [he, Real.log_exp]

def readP (observed : Field) : ℝ := observed (Real.exp (readLogScale observed), 0)

theorem readP_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    readP W.E = F.data.core.P := by
  rw [readP, readLogScale_source W, Real.exp_log W.controls.radius_pos]
  have he := assembled_early W 0 0 (by norm_num)
    (by linarith [patchClock_gt_two F]) (by norm_num [HeatedOutgoing.parameterDomain])
  rw [OutgoingSchedule.angular_ideal F.data.core.dropLength_pos.le le_rfl] at he
  simpa [OutgoingSchedule.shape] using he

def readWait (observed : Field) : ℝ :=
  Real.log (endpointRadius observed) - readLogScale observed - 13 / readRate observed -
    (Real.exp (readM observed) + 12)

theorem readWait_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    readWait W.E = F.data.core.wait := by
  rw [readWait, endpointRadius_source W, readLogScale_source W, readRate_source W, readM_source W,
    Real.log_mul W.controls.radius_pos.ne' (Real.exp_ne_zero _), Real.log_exp]
  dsimp only [OutgoingSchedule.Parameters.endpoint, OutgoingSchedule.Parameters.pulseStart,
    OutgoingSchedule.Parameters.pulseLength, OutgoingSchedule.Parameters.holdStart,
    OutgoingSchedule.Parameters.dropLength]
  ring

/-- Scalar validity for constructing the decoded parameters. This is not a
certificate that an arbitrary observation belongs to the source family. -/
structure Admissible (observed : Field) : Prop where
  P_pos : 0 < readP observed
  m_pos : 0 < readM observed
  rate_pos : 0 < readRate observed
  rate_lt : readRate observed < 1 / 10
  wait_gt : 25 < readWait observed
  height_pos : 0 < FullFieldRecovery.readHeight observed
  height_small : 2 * FullFieldRecovery.readHeight observed < readRate observed

def decodedCore (observed : Field) (ha : Admissible observed) : OutgoingSchedule.Parameters where
  P := readP observed
  m := readM observed
  lam := readRate observed
  wait := readWait observed
  P_pos := ha.P_pos
  m_pos := ha.m_pos
  lam_pos := ha.rate_pos
  lam_lt := ha.rate_lt
  wait_gt := ha.wait_gt

theorem assembled_admissible {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    Admissible W.E := by
  constructor
  · rw [readP_source W]; exact F.data.core.P_pos
  · rw [readM_source W]; exact F.data.core.m_pos
  · rw [readRate_source W]; exact F.data.core.lam_pos
  · rw [readRate_source W]; exact F.data.core.lam_lt
  · rw [readWait_source W]; exact F.data.core.wait_gt
  · rw [ObservedFieldRecovery.assembled_readHeight W]; exact F.data.h_pos
  · rw [ObservedFieldRecovery.assembled_readHeight W, readRate_source W]; exact F.data.h_small

theorem decodedCore_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (ha : Admissible W.E) : decodedCore W.E ha = F.data.core := by
  unfold decodedCore
  simp only [readP_source W, readM_source W, readRate_source W, readWait_source W]

theorem decodedHeightAdmissible (observed : Field) (ha : Admissible observed) :
    ObservedFieldRecovery.HeightAdmissible observed (decodedCore observed ha) :=
  ⟨ha.height_pos, ha.height_small⟩

def readCalibration (observed : Field) (ha : Admissible observed) : FullFieldRecovery.Calibration :=
  ObservedFieldRecovery.readCalibration observed (decodedCore observed ha)
    (decodedHeightAdmissible observed ha)

theorem readCalibration_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (ha : Admissible W.E) : readCalibration W.E ha =
      FullFieldRecovery.sourceCalibration F W.controls.radius := by
  unfold readCalibration
  simp only [decodedCore_source W ha]
  exact ObservedFieldRecovery.readCalibration_source W _

def recoveredE (observed : Field) (ha : Admissible observed) : Field :=
  SourceFieldRecovery.recoverOriginalE observed (decodedCore observed ha) (readCalibration observed ha)

def recoveredU (observed : Field) (ha : Admissible observed) : Field :=
  SourceFieldRecovery.recoverOriginalU observed (decodedCore observed ha) (readCalibration observed ha)

def recoveredLaterU (observed : Field) (ha : Admissible observed) : Field :=
  SourceFieldRecovery.recoverLaterU observed (decodedCore observed ha) (readCalibration observed ha)

theorem recoveredE_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (ha : Admissible W.E) (x eta : ℝ) (hx : 0 < x) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    recoveredE W.E ha (x, eta) = F.E (x, eta) := by
  unfold recoveredE
  rw [decodedCore_source W ha, readCalibration_source W ha]
  exact SourceFieldRecovery.recoverOriginalE_source W x eta hx heta

theorem recoveredU_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (ha : Admissible W.E) (x eta : ℝ) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    recoveredU W.E ha (x, eta) = F.U (x, eta) := by
  unfold recoveredU
  rw [decodedCore_source W ha, readCalibration_source W ha]
  exact SourceFieldRecovery.recoverOriginalU_source W x eta heta

theorem recoveredLaterU_source {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (ha : Admissible W.E) (X eta : ℝ) (hX : W.controls.heatJoin < X)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    recoveredLaterU W.E ha (X, eta) = W.U (X, eta) := by
  unfold recoveredLaterU
  rw [decodedCore_source W ha, readCalibration_source W ha]
  exact SourceFieldRecovery.recoverLaterU_source W X eta hX heta

/-- The actual prepared profile is recoverable from its complete exact
assembled E, without supplied core, scale, calibration, coefficients, or U. -/
theorem exists_matched_core_recovery (floor : ℝ) :
    ∃ W : NominalProfile.Witness SourceFieldRecovery.originalProfile,
      floor < W.controls.radius ∧ ∃ ha : Admissible W.E,
        ∀ x eta : ℝ, 0 < x → eta ∈ HeatedOutgoing.parameterDomain →
          recoveredE W.E ha (x, eta) = SourceFieldRecovery.originalE (x, eta) ∧
          recoveredU W.E ha (x, eta) = SourceFieldRecovery.originalU (x, eta) := by
  obtain ⟨W, hR, _⟩ := PreparedOutgoing.prepared.large_nominal floor 0 le_rfl
  refine ⟨W, hR, assembled_admissible W, ?_⟩
  intro x eta hx heta
  exact ⟨recoveredE_source W _ x eta hx heta, recoveredU_source W _ x eta heta⟩

end NavierStokes.CoreFieldRecovery
