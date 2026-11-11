import notes.SourceFieldRecovery

/-!
# Calibration from an observed tail and retained core metadata

The core schedule (P, m, lam, wait) is retained input. Height and radial scale
are read from the complete exact assembled angular field. This route uses the
unheated eta=1 boundary tail, so the distinct axis prefix cannot create a false
early marker. It does not infer an unknown core or recover finite/noisy samples.
All readers are noncomputable exact-real operators.
-/

noncomputable section

open Set

namespace NavierStokes.ObservedFieldRecovery

abbrev Field := FullFieldRecovery.Field

/-- Eventual equality on the boundary slice in logarithmic radius. -/
def HasLogTail (observed : Field) (C h r : ℝ) : Prop :=
  ∃ Z : ℝ, ∀ z : ℝ, Z ≤ z →
    observed (Real.exp z, 1) = C * Real.exp (-(1 / 2 + h) * (z - r))

theorem heated_hasLogTail (F : OutgoingProfile.Profile) (XR : ℝ)
    (c : ℝ → TerminalCompensation.Coeff) (hXR : 0 < XR) :
    HasLogTail (HeatedOutgoing.E F XR c) (OutgoingTail.powerConstant F.data)
      F.data.h (Real.log XR) := by
  refine ⟨Real.log XR + max (OutgoingTail.tailEnd F.data)
    (HeatTailEdit.switchStart F.data), ?_⟩
  intro z hz
  have ht : OutgoingTail.tailEnd F.data ≤ z - Real.log XR := by
    linarith [le_max_left (OutgoingTail.tailEnd F.data) (HeatTailEdit.switchStart F.data)]
  have hs : OutgoingDilation.switchRadius F XR ≤ Real.exp z := by
    calc
      _ = Real.exp (Real.log XR + HeatTailEdit.switchStart F.data) := by
        simp only [OutgoingDilation.switchRadius, OutgoingDilation.radius,
          Real.exp_add, Real.exp_log hXR]
      _ ≤ Real.exp z := Real.exp_le_exp.mpr (by
        linarith [le_max_right (OutgoingTail.tailEnd F.data) (HeatTailEdit.switchStart F.data)])
  have hc := OutgoingDilation.correction_zero_after_switch F XR (Real.exp z) hXR (c 1) hs
  have hnu : ParametricHeatTail.diffusion 1 = 0 := by
    norm_num [ParametricHeatTail.diffusion]
  have hp := RadialHeatProfile.profile_zero (a := 1 + F.data.h) (by linarith [F.data.h_pos])
  simp only [HeatedOutgoing.E, HeatedOutgoing.heatE, HeatedOutgoing.patchIncrement,
    hc, mul_zero, add_zero, HeatTailEdit.multiplier, hnu, mul_zero, zero_div, hp,
    sub_self, mul_zero, add_zero, mul_one]
  change F.logE (Real.log (Real.exp z / XR), 1) = _
  rw [Real.log_div (Real.exp_ne_zero z) hXR.ne', Real.log_exp]
  exact F.logE_eventual 1 ht

theorem assembled_hasLogTail {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) :
    HasLogTail W.E (OutgoingTail.powerConstant F.data) F.data.h
      (Real.log W.controls.radius) := by
  obtain ⟨Z, hZ⟩ := heated_hasLogTail F W.controls.radius W.heat.coefficients W.controls.radius_pos
  refine ⟨max Z (Real.log W.controls.radius), ?_⟩
  intro z hz
  have hR : W.controls.radius ≤ Real.exp z := by
    calc
      _ = Real.exp (Real.log W.controls.radius) := (Real.exp_log W.controls.radius_pos).symm
      _ ≤ Real.exp z := Real.exp_le_exp.mpr ((le_max_right _ _).trans hz)
  have he := (W.heat_agreement (p := (Real.exp z, 1)) (W.controls.heatJoin_lt_radius.trans_le hR)
    (show (1 : ℝ) ∈ HeatedOutgoing.parameterDomain by norm_num [HeatedOutgoing.parameterDomain])).2.1
  exact he.trans (hZ z ((le_max_left _ _).trans hz))

private theorem tail_ratio {observed : Field} {C h r Z : ℝ}
    (hC : 0 < C)
    (ht : ∀ z : ℝ, Z ≤ z →
      observed (Real.exp z, 1) = C * Real.exp (-(1 / 2 + h) * (z - r)))
    (z : ℝ) (hz : Z ≤ z) :
    Real.log (observed (Real.exp (z + 1), 1) / observed (Real.exp z, 1)) =
      -(1 / 2 + h) := by
  rw [ht (z + 1) (by linarith), ht z hz]
  have hquot : (C * Real.exp (-(1 / 2 + h) * (z + 1 - r))) /
      (C * Real.exp (-(1 / 2 + h) * (z - r))) = Real.exp (-(1 / 2 + h)) := by
    rw [show -(1 / 2 + h) * (z + 1 - r) =
      -(1 / 2 + h) * (z - r) + -(1 / 2 + h) by ring, Real.exp_add]
    field_simp
  rw [hquot, Real.log_exp]

theorem eventualSlopes_eq_singleton {observed : Field} {C h r : ℝ}
    (hC : 0 < C) (ht : HasLogTail observed C h r) :
    FullFieldRecovery.eventualSlopes observed = {-(1 / 2 + h)} := by
  obtain ⟨Z, hZ⟩ := ht
  ext s
  constructor
  · rintro ⟨B, hB⟩
    have hz := tail_ratio hC hZ (max B Z) (le_max_right _ _)
    rw [hB (max B Z) (le_max_left _ _)] at hz
    exact hz
  · intro hs
    have hs' : s = -(1 / 2 + h) := hs
    rw [hs']
    exact ⟨Z, fun z hz => tail_ratio hC hZ z hz⟩

theorem readHeight_eq {observed : Field} {C h r : ℝ}
    (hC : 0 < C) (ht : HasLogTail observed C h r) :
    FullFieldRecovery.readHeight observed = h := by
  unfold FullFieldRecovery.readHeight
  rw [eventualSlopes_eq_singleton hC ht, csSup_singleton]
  ring

theorem assembled_readHeight {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) : FullFieldRecovery.readHeight W.E = F.data.h :=
  readHeight_eq (OutgoingTail.powerConstant_pos F.data) (assembled_hasLogTail W)

/-- The retained core does not include h. These are the scalar inequalities
needed to build TailData after the observation has supplied h. -/
structure HeightAdmissible (observed : Field) (core : OutgoingSchedule.Parameters) : Prop where
  height_pos : 0 < FullFieldRecovery.readHeight observed
  height_small : 2 * FullFieldRecovery.readHeight observed < core.lam

def decodedData (observed : Field) (core : OutgoingSchedule.Parameters)
    (ha : HeightAdmissible observed core) : OutgoingTail.TailData where
  core := core
  h := FullFieldRecovery.readHeight observed
  h_pos := ha.height_pos
  h_small := ha.height_small

theorem assembled_heightAdmissible {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) : HeightAdmissible W.E F.data.core := by
  constructor
  · rw [assembled_readHeight W]
    exact F.data.h_pos
  · rw [assembled_readHeight W]
    exact F.data.h_small

theorem decodedData_eq {observed : Field} (d : OutgoingTail.TailData)
    (ha : HeightAdmissible observed d.core)
    (hh : FullFieldRecovery.readHeight observed = d.h) :
    decodedData observed d.core ha = d := by
  rcases d with ⟨core, height, hpos, hsmall⟩
  change FullFieldRecovery.readHeight observed = height at hh
  subst height
  rfl

/-- Possible logarithms of the dilation scale, using the source tail law.
No original Profile or correction coefficients are inputs. -/
def scaleCandidates (observed : Field) (d : OutgoingTail.TailData) : Set ℝ :=
  {r | HasLogTail observed (OutgoingTail.powerConstant d) d.h r}

def readScale (observed : Field) (d : OutgoingTail.TailData) : ℝ :=
  Real.exp (sSup (scaleCandidates observed d))

theorem HasLogTail.unique_shift {observed : Field} {C h r s : ℝ}
    (hC : 0 < C) (hh : 0 < h)
    (hr : HasLogTail observed C h r) (hs : HasLogTail observed C h s) : r = s := by
  obtain ⟨R, hR⟩ := hr
  obtain ⟨S, hS⟩ := hs
  have he := (hR (max R S) (le_max_left _ _)).symm.trans
    (hS (max R S) (le_max_right _ _))
  have hexp := mul_left_cancel₀ hC.ne' he
  have harg := Real.exp_injective hexp
  have ha : -(1 / 2 + h) ≠ 0 := by linarith
  have hsub := mul_left_cancel₀ ha harg
  linarith

theorem scaleCandidates_eq_singleton {observed : Field} (d : OutgoingTail.TailData)
    {r : ℝ} (ht : HasLogTail observed (OutgoingTail.powerConstant d) d.h r) :
    scaleCandidates observed d = {r} := by
  ext s
  constructor
  · intro hs
    exact HasLogTail.unique_shift (OutgoingTail.powerConstant_pos d) d.h_pos hs ht
  · intro hs
    have hs' : s = r := hs
    simpa only [scaleCandidates, hs', mem_ofPred_eq] using ht

theorem readScale_eq {observed : Field} (d : OutgoingTail.TailData)
    {XR : ℝ} (hXR : 0 < XR)
    (ht : HasLogTail observed (OutgoingTail.powerConstant d) d.h (Real.log XR)) :
    readScale observed d = XR := by
  rw [readScale, scaleCandidates_eq_singleton d ht, csSup_singleton, Real.exp_log hXR]

def calibrationFromData (observed : Field) (d : OutgoingTail.TailData) :
    FullFieldRecovery.Calibration where
  scale := readScale observed d
  rate := d.core.lam
  height := d.h
  patch := readScale observed d * Real.exp (d.core.pulseStart - 20)
  switch := readScale observed d * Real.exp (HeatTailEdit.switchStart d)

/-- Read the missing calibration from exact assembled E and retained core.
Scalar admissibility is not a certificate that arbitrary data are a source field. -/
def readCalibration (observed : Field) (core : OutgoingSchedule.Parameters)
    (ha : HeightAdmissible observed core) : FullFieldRecovery.Calibration :=
  calibrationFromData observed (decodedData observed core ha)

theorem readCalibration_source {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (ha : HeightAdmissible W.E F.data.core) :
    readCalibration W.E F.data.core ha =
      FullFieldRecovery.sourceCalibration F W.controls.radius := by
  unfold readCalibration
  rw [decodedData_eq F.data ha (assembled_readHeight W)]
  unfold calibrationFromData
  rw [readScale_eq F.data W.controls.radius_pos (assembled_hasLogTail W)]
  rfl

def recoveredE (observed : Field) (core : OutgoingSchedule.Parameters)
    (ha : HeightAdmissible observed core) : Field :=
  SourceFieldRecovery.recoverOriginalE observed core (readCalibration observed core ha)

def recoveredU (observed : Field) (core : OutgoingSchedule.Parameters)
    (ha : HeightAdmissible observed core) : Field :=
  SourceFieldRecovery.recoverOriginalU observed core (readCalibration observed core ha)

def recoveredLaterU (observed : Field) (core : OutgoingSchedule.Parameters)
    (ha : HeightAdmissible observed core) : Field :=
  SourceFieldRecovery.recoverLaterU observed core (readCalibration observed core ha)

theorem recoveredE_source {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (ha : HeightAdmissible W.E F.data.core)
    (x eta : ℝ) (hx : 0 < x) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    recoveredE W.E F.data.core ha (x, eta) = F.E (x, eta) := by
  unfold recoveredE
  rw [readCalibration_source W ha]
  exact SourceFieldRecovery.recoverOriginalE_source W x eta hx heta

theorem recoveredU_source {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (ha : HeightAdmissible W.E F.data.core)
    (x eta : ℝ) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    recoveredU W.E F.data.core ha (x, eta) = F.U (x, eta) := by
  unfold recoveredU
  rw [readCalibration_source W ha]
  exact SourceFieldRecovery.recoverOriginalU_source W x eta heta

theorem recoveredLaterU_source {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (ha : HeightAdmissible W.E F.data.core)
    (X eta : ℝ) (hX : W.controls.heatJoin < X)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    recoveredLaterU W.E F.data.core ha (X, eta) = W.U (X, eta) := by
  unfold recoveredLaterU
  rw [readCalibration_source W ha]
  exact SourceFieldRecovery.recoverLaterU_source W X eta hX heta

/-- The actual prepared source instance is recovered without supplying a
calibration, scale, height, reset coefficients, heat coefficients, or U data.
The original core metadata and the complete exact assembled E remain inputs. -/
theorem exists_matched_observed_recovery (floor : ℝ) :
    ∃ W : NominalProfile.Witness SourceFieldRecovery.originalProfile,
      floor < W.controls.radius ∧
      ∃ ha : HeightAdmissible W.E SourceFieldRecovery.originalProfile.data.core,
        ∀ x eta : ℝ, 0 < x → eta ∈ HeatedOutgoing.parameterDomain →
          recoveredE W.E SourceFieldRecovery.originalProfile.data.core ha (x, eta) =
            SourceFieldRecovery.originalE (x, eta) ∧
          recoveredU W.E SourceFieldRecovery.originalProfile.data.core ha (x, eta) =
            SourceFieldRecovery.originalU (x, eta) := by
  obtain ⟨W, hR, _⟩ := PreparedOutgoing.prepared.large_nominal floor 0 le_rfl
  refine ⟨W, hR, assembled_heightAdmissible W, ?_⟩
  intro x eta hx heta
  exact ⟨recoveredE_source W _ x eta hx heta, recoveredU_source W _ x eta heta⟩

end NavierStokes.ObservedFieldRecovery
