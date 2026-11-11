import NavierStokes.ExtendedHeatedOutgoing
import notes.AxialFromAngular

/-!
# Recovery of the outgoing field from its heated observations

Local source-derived investigation for Jess, 2026-11-11.
Source revision: f9e8bc5b38b6e212696e8a30e3e91517af887bbd.

STATUS AND SCOPE
This file compiles with the pinned Lean 4.34.0-rc2 toolchain (2026-11-11).
The field-restoration and U-composition theorems below are checked; the
audited proofs use only propext, Classical.choice, and Quot.sound, with no
unfinished-proof axiom. Logs are in notes/verification/.
The observable-marker identification argument is given in this comment,
not proved as a Lean theorem. In particular, the final E-only composition
still takes decoded-core and calibration equalities as explicit hypotheses.
The definitions are noncomputable exact-real operators; they are not an
executable inverse for a finite or rounded coordinate file.

The target is the entire pre-heat outgoing E,U field on X>0, |eta|<=1.
The first route assumes both complete, exact observed fields, generated as
    Eo = HeatedOutgoing.E F XR c,
    Uo = HeatedOutgoing.U F XR,
with XR>0 and the paper schedule
    F.data.core.wait = 60*log(1/F.data.core.lam).
No original F or correction coefficients are inputs to the readers below.
The source family supplies positive P,m,lam,h and wait>25. This is a recovery
of field values, not a claim that a PDE solution or Profile witness has been
numerically instantiated. It does not identify an Euler packet with F.
An alternative E-only route below removes the observed U input by using the
specific OutgoingProfile amplitude rule. Neither route needs the later heat
patch coefficients c as inputs.

## Complete exact-data calibration argument

Use z=log(X), the logarithm of the observed radial coordinate. Let
    z2 = inf {z : Uo(exp(z),1)=2},
    z0 = inf {z : Uo(exp(z),1)=0}.
Before the first pulse, Uo(exp(z),1)=dropCoefficient(m,z-log(XR)).
Its first half-height and zero markers are
    z2=log(XR)+exp(m/2), z0=log(XR)+exp(m).
The half-height marker is the first crossing: on 0<u<1, the smooth step has
    log(sigma(u)/(1-sigma(u))) = -1/u^2 + 1/(1-u)^2,
whose derivative is 2/u^3+2/(1-u)^3>0. Also sigma(1/2)=1/2.
The initial drop has no earlier zero, and the pulse starts strictly later.
Consequently, with t=(1+sqrt(1+4*(z0-z2)))/2,
    m=2*log(t), log(XR)=z2-t.
Sources: OutgoingSchedule.lean:26-27,207-214,302-306,507-509;
FlatCutoff.lean:26-27; HeatedOutgoing.lean:38; OutgoingDilation.lean:62.

For numerical calibration, prefer two INTERIOR levels to the flat zero
boundary. Let alpha be the unique solution sigma(alpha)=1/4 in (0,1/2),
and z3 the first level Uo(exp(z3),1)=3. Then z3=log(XR)+exp(alpha*m).
The function exp(m/2)-exp(alpha*m) is strictly increasing for m>=0, so
z2-z3 determines m by a one-dimensional solve; XR follows from z2.
This avoids identifying a smooth flat zero from rounded values. The separate
Python checks exercise this alternative against the source formulas.

Set H=exp(m)+12, the recovered holdStart. At y=H+1 and H+2, both later
edits are absent: patchClock=H+wait-20>H+5, and heat starts later still.
The original angular amplitude there has constant logarithmic slope
-(1/2+lam). Thus
    lam = -log(Eo(XR*exp(H+2),0)/Eo(XR*exp(H+1),0))-1/2.
The patch's physical start is then known from the paper schedule:
    R = XR*exp(H+60*log(1/lam)-20).
This use of the schedule equality is essential; an arbitrary wait parameter
would need its own identification step.
Sources: OutgoingSchedule.radialAmplitude_hold; OutgoingDilation.lean:407-420;
HeatedOutgoing.E_before_patch; ExtendedHeatedOutgoing.ScheduleBounds.wait_eq.

At eta=1 diffusion=0, so the heat multiplier is exactly one. The additive
patch is compactly supported. The original field has an eventual exact
power tail. Therefore
    log(Eo(exp(z+1),1)/Eo(exp(z),1)) = -(1/2+h)
for all sufficiently large z. Its unique eventual constant recovers h.
This is an eventual-tail operator, not an assertion that two arbitrary
finite observations are known to lie in the terminal tail.
Sources: ParametricHeatTail.diffusion; RadialHeatProfile.profile_zero;
OutgoingProfile.lean:116-123; TerminalCompensation.correction_support.

The switch radius is also observable, without TailData:
    K = sup {X>0 : Eo(X,0)=Eo(X,1)}.
Why this set has maximum K: after releaseStart the pre-heat field is
eta-independent, and releaseStart is before the switch. At X=K the heat
switch is zero, and the compensation patch has already ended. Hence the
two observations agree there. For EVERY X>K the patch is absent, the
original two slices agree and are positive, while the eta=0 multiplier is
strictly less than one and the eta=1 multiplier is one. Strictness follows
from sigma(u)>0 for u>0, profile(1+h,0)=1, and the strictly negative heat
profile derivative on nonnegative arguments. Thus they never agree above K.
Sources: OutgoingTail.finalAngular_eta_independent;
UniformAngularReset.correctedAngular_unchanged;
OutgoingDilation.patch_before_switch and switchRadius_eq;
HeatTailEdit.multiplier; RadialHeatProfile.lean:124-130,423-428.

An independent source-geometry route to the same switch is available after
decoding TailData: P=Eo(XR,0), with m,lam,h as recovered above and wait fixed
by the paper schedule. These recover every scalar field of TailData; then
K=XR*exp(HeatTailEdit.switchStart d). TailData has no reset coefficients.
The public flatten/release constants remain the source's fixed constants.
This route avoids locating the switch from a potentially tiny slice contrast.
Sources: OutgoingTail.TailData (103-107); OutgoingDilation.switchRadius_eq;
HeatedOutgoing.E_before_patch and entrance_before_patch.

## Restoration, with no correction-coefficient inputs

At the patch start, a(eta)=Eo(R,eta) is the unedited shaped amplitude.
Throughout R<=X<=R*exp(5), the unedited field is exactly
    a(eta)*(X/R)^(-(1/2+lam)).
Outside that patch the additive correction is zero. Divide by the known,
strictly positive heat multiplier to undo the heat edit. Finally put
X=XR*x to undo dilation. U is simply Uo(XR*x,eta), since the heat stage
does not alter U. This recovers E,U everywhere on the physical band.
H follows as sqrt(2*x)*E. The original pressure follows from its defining
integral of E^2 in log radius. All field-derived histories can then be
recomputed with the original source conventions.
Sources: OutgoingDilation.E_on_patch (504-525);
HeatedOutgoing.E_before_patch (148-160), correction_zero_outside (142-146),
and E/U definitions (27-38); HeatTailEdit.multiplier_bounds (63-72).

## If both the later heat coefficients c and observed U are missing

There is an alternative calibration from complete exact Eo alone. Put
    g(z)=log(Eo(exp(z),0)), r=log(XR), D=exp(m)+10.
Before the later edits, OutgoingSchedule.slope gives
    g'(r+y)=(3/5)*(1-sigma(y))-lam*sigma(y-(D+1))-1/2.
The FIRST occurrence of g'(z)=-1/5 is z=r+1/2: the first ramp is strictly
decreasing, sigma(1/2)=1/2, and the second ramp starts much later. Thus
    r = inf {z : g'(z)=-1/5} - 1/2.
After y=1 the slope is exactly -1/2 until the second ramp begins. Since
sigma(t)>0 for t>0, its first departure has infimum
    T = inf {y>1 : g'(r+y) != -1/2} = D+1 = exp(m)+11,
    m=log(T-11).
This identifies m without observing U. The clean-hold angular ratio above
then recovers lam, and P=Eo(exp(r),0). The same eventual tail, switch, and
patch restoration recover the entire pre-heat E. Both early ramps precede
core.endpoint and the later patch, by the source's schedule inequalities.
Sources: OutgoingSchedule.slope (108-109), radialAmplitude_hasDerivAt
(163-168), Parameters.dropLength/holdStart (302-303);
OutgoingProfile.logE_before (89-94); HeatedOutgoing.E_before_patch.

Recovering U requires one more SOURCE-SPECIFIC dependency, not a universal
inference from an angular field. P,m,lam,h and the fixed paper wait recover
TailData d (including its source-defined, noncomputable public constants).
Let Epre be the restored E, and for j=0,1 set
    y_j=d.releaseStart-3+2*j,
    b_j(eta)=Epre(exp(y_j),eta)/
        AngularMomentReset.baseE(lam,referenceAmplitude(d),y_j)-1.
These centers lie inside the earlier angular reset window. At each center
its own bump is 1 and the other is 0. Therefore b recovers the EARLIER
F.reset.coefficients on the physical eta band. These two coefficients are
distinct from the three LATER heat-patch coefficients c.
Sources: AngularMomentReset.template_at_zero, bump_support, relative,
modifiedE (460-461); UniformAngularReset.correctionCenter (1001),
corrected_matches_reference (1077-1082).

Finally the actual Profile definition fixes, rather than independently
supplies, its axial amplitude:
    A(eta)=CorrectedPulseAmplitude.amplitude d b eta,
    U(x,eta)=OutgoingSchedule.axial d.core A (log(x),eta).
The amplitude formula depends on b only at the same eta (its reset energy
is integrated in y, not eta). No off-band b extension is needed to recover
U on |eta|<=1. This is why missing observed U need not prevent recovery in
THIS source family. It would prevent this inference for arbitrary unrelated
E and U. Sources: OutgoingProfile.Profile.amp/logU/U (31-41);
CorrectedPulseAmplitude.constantTerm/discriminant/amplitude (52-87);
ResetEnergyBounds.resetDensity/resetEnergy (44-45,96-97).

UPDATE: notes/AxialFromAngular.lean removes the need to decode the earlier
reset coefficients too. With the restored E and recovered core schedule,
compute the normalized energy at trial amplitude zero. By the source's
totalEnergy_normalized identity that is the exact constant coefficient of
the amplitude polynomial. Its other two coefficients depend only on core.
The source's clamped positive-root formula then gives U. The checked
UFromField_source proof instantiates that identity for an actual Profile.
Unlike a bare zero-energy solve, it does not silently assume that every
Profile has Specification.energy_zero. The new recoveredUDirect definition
records this alternative; the coefficient-sampling route remains above.
At the end of this file, originalUFromObservedE_roundtrip composes the source
energy identity with actual angular restoration, after calibration;
laterUFromObservedE_roundtrip then applies X/XR. The E-only composition makes
the pending decoded-core and calibration equalities explicit hypotheses.

Independent numerical status is saved in notes/axial_recovery_audit.json:
four controlled analytic fixtures passed the direct energy inverse and both
U coordinate stages, with maximum absolute U error about 4.29e-14. They are
NOT actual Profile instances and do not test the full thermal/calibration
pipeline together. The Lean proofs now compile; those numerical scope
limitations and the pending marker-identification proof remain.

For the scheduled physical family, the source's
ExtendedHeatedOutgoing.ScheduleBounds.constantTerm_bound proves C<=-23/100;
there the clamp is inactive. Outside that certified regime a clamped root
need not have zero actual energy, and it can conceal errors in C. The direct
route uses the clamp exactly, without assuming that a finite observation
provider has established any of those regime inequalities.

The EOnly namespace below writes these exact-real operators explicitly.
Their marker and coefficient identification is the argument above, not a
compiled Lean theorem. In particular, T uses exact derivative equality at
a flat smooth transition. Rounded or incomplete samples cannot implement
that infimum reliably. The independent numerical E-only check instead uses
interior ramp levels and an explicitly supplied clean-hold observation
window. It checks that conditional calibration, not automatic recovery from
an arbitrary sample file, the terminal heat edit, or a certified Profile.

## Uniqueness and limits

For two members of this scheduled source family with identical complete
Eo,Uo, the observable markers above coincide, hence XR,lam,h,R,K coincide.
Their patch-start curves a coincide too. The same restoration formula
therefore gives identical original E,U on X>0, |eta|<=1. This establishes
field identifiability by the source-derived argument above.
For the E-only route the early angular markers replace the axial markers;
identical Eo then also gives identical recovered reset coefficients and the
same U through the source's fixed amplitude rule. This additional argument
has not been formally proved in Lean or tested end to end numerically.

It does NOT uniquely identify the unrestricted Profile record: its bound
coefficientBound can be increased while retaining exactly the same fields.
The construction below records that ambiguity explicitly. Nor does observing
the physical band specify arbitrary off-band extensions. Finite samples,
unknown coverage, noise, or rounded equality tests do not provide the infimum,
eventual tail, and last-equality operations used here. Very small heat changes
can be entirely lost in ordinary floating-point data. These limits remain
even though the exact-data field recovery is algebraically specified.
-/

noncomputable section

open Set Filter MeasureTheory

namespace NavierStokes.FullFieldRecovery

abbrev Field := (ℝ × ℝ) → ℝ
abbrev Profile := OutgoingProfile.Profile

def firstLevel (Uo : Field) (level : ℝ) : ℝ :=
  sInf {z : ℝ | Uo (Real.exp z, 1) = level}

def dropRoot (Uo : Field) : ℝ :=
  (1 + Real.sqrt (1 + 4 * (firstLevel Uo 0 - firstLevel Uo 2))) / 2

def readM (Uo : Field) : ℝ := 2 * Real.log (dropRoot Uo)

def readScale (Uo : Field) : ℝ :=
  Real.exp (firstLevel Uo 2 - dropRoot Uo)

def readHold (Uo : Field) : ℝ := Real.exp (readM Uo) + 12

def readRate (Eo Uo : Field) : ℝ :=
  -Real.log (Eo (readScale Uo * Real.exp (readHold Uo + 2), 0) /
    Eo (readScale Uo * Real.exp (readHold Uo + 1), 0)) - 1 / 2

def eventualSlopes (Eo : Field) : Set ℝ :=
  {s : ℝ | ∃ Z : ℝ, ∀ z : ℝ, Z ≤ z →
    Real.log (Eo (Real.exp (z + 1), 1) / Eo (Real.exp z, 1)) = s}

def readHeight (Eo : Field) : ℝ := -1 / 2 - sSup (eventualSlopes Eo)

def readSwitch (Eo : Field) : ℝ :=
  sSup {X : ℝ | 0 < X ∧ Eo (X, 0) = Eo (X, 1)}

def readPatch (Eo Uo : Field) : ℝ :=
  readScale Uo * Real.exp
    (readHold Uo + 60 * Real.log (1 / readRate Eo Uo) - 20)

structure Calibration where
  scale : ℝ
  rate : ℝ
  height : ℝ
  patch : ℝ
  switch : ℝ

/-- Defined for exact source-family observations. Invalid observations do not
carry a recovery guarantee; these total real operators are not input validators. -/
def readCalibration (Eo Uo : Field) : Calibration where
  scale := readScale Uo
  rate := readRate Eo Uo
  height := readHeight Eo
  patch := readPatch Eo Uo
  switch := readSwitch Eo

def restoreDilatedE (Eo : Field) (k : Calibration) (p : ℝ × ℝ) : ℝ :=
  if k.patch ≤ p.1 ∧ p.1 ≤ k.patch * Real.exp 5 then
    Eo (k.patch, p.2) * (p.1 / k.patch) ^ (-(1 / 2 + k.rate))
  else
    Eo p / HeatTailEdit.multiplier k.height (ParametricHeatTail.diffusion p.2) k.switch p.1

def restoreE (Eo : Field) (k : Calibration) (p : ℝ × ℝ) : ℝ :=
  restoreDilatedE Eo k (k.scale * p.1, p.2)

def restoreU (Uo : Field) (k : Calibration) (p : ℝ × ℝ) : ℝ :=
  Uo (k.scale * p.1, p.2)

def recoveredE (Eo Uo : Field) : Field := restoreE Eo (readCalibration Eo Uo)
def recoveredU (Eo Uo : Field) : Field := restoreU Uo (readCalibration Eo Uo)

def recoveredH (Eo Uo : Field) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (2 * p.1) * recoveredE Eo Uo p

def recoveredPi (Eo Uo : Field) (p : ℝ × ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ y in Ioi (Real.log p.1), recoveredE Eo Uo (Real.exp y, p.2) ^ 2

/-! Alternative reader with no observed U and no later heat coefficients.
These definitions record the source-derived argument in the opening comment;
they do not add a formal marker-identification theorem. -/
namespace EOnly

def logAngular (Eo : Field) (z : ℝ) : ℝ := Real.log (Eo (Real.exp z, 0))

def logSlope (Eo : Field) (z : ℝ) : ℝ := deriv (logAngular Eo) z

def readLogScale (Eo : Field) : ℝ :=
  sInf {z : ℝ | logSlope Eo z = -(1 / 5 : ℝ)} - 1 / 2

def secondRampStart (Eo : Field) : ℝ :=
  sInf {y : ℝ | 1 < y ∧ logSlope Eo (readLogScale Eo + y) ≠ -(1 / 2 : ℝ)}

def readM (Eo : Field) : ℝ := Real.log (secondRampStart Eo - 11)

def readHold (Eo : Field) : ℝ := Real.exp (readM Eo) + 12

def readRate (Eo : Field) : ℝ :=
  -(logAngular Eo (readLogScale Eo + readHold Eo + 2) -
    logAngular Eo (readLogScale Eo + readHold Eo + 1)) - 1 / 2

def readP (Eo : Field) : ℝ := Eo (Real.exp (readLogScale Eo), 0)

def readCalibration (Eo : Field) : Calibration where
  scale := Real.exp (readLogScale Eo)
  rate := readRate Eo
  height := readHeight Eo
  patch := Real.exp (readLogScale Eo) * Real.exp
    (readHold Eo + 60 * Real.log (1 / readRate Eo) - 20)
  switch := readSwitch Eo

def recoveredE (Eo : Field) : Field := restoreE Eo (readCalibration Eo)

/-- Scalar conditions needed to construct TailData. These inequalities alone
do NOT certify that an arbitrary observed field belongs to the source family. -/
structure Admissible (Eo : Field) : Prop where
  P_pos : 0 < readP Eo
  m_pos : 0 < readM Eo
  rate_pos : 0 < readRate Eo
  rate_lt : readRate Eo < 1 / 10
  height_pos : 0 < readHeight Eo
  height_small : 2 * readHeight Eo < readRate Eo

def decodedData (Eo : Field) (h : Admissible Eo) : OutgoingTail.TailData where
  core := OutgoingSchedule.paperParameters (readP Eo) (readM Eo) (readRate Eo)
    h.P_pos h.m_pos h.rate_pos h.rate_lt
  h := readHeight Eo
  h_pos := h.height_pos
  h_small := h.height_small

/-- Recover the TWO earlier reset coefficients, distinct from the THREE
later heat-patch coefficients omitted from the reader's inputs. -/
def readResetCoefficients (Eo : Field) (d : OutgoingTail.TailData) :
    ℝ → AngularMomentReset.Coeff := fun eta j =>
  let y := UniformAngularReset.correctionCenter d + 2 * (j.val : ℝ)
  recoveredE Eo (Real.exp y, eta) /
    AngularMomentReset.baseE d.core.lam (UniformAngularReset.referenceAmplitude d) y - 1

/-- Regenerates U by the actual Profile amplitude rule, using decoded data.
Correctness requires complete exact source-family observations, not merely
Admissible's scalar inequalities. No original F, c, or U is an input. -/
def recoveredU (Eo : Field) (h : Admissible Eo) (p : ℝ × ℝ) : ℝ :=
  let d := decodedData Eo h
  OutgoingSchedule.axial d.core
    (CorrectedPulseAmplitude.amplitude d (readResetCoefficients Eo d))
    (Real.log p.1, p.2)

/-- Direct energy route: earlier reset coefficients need not be decoded.
The separate AxialFromAngular source identity is checked; identifying the
E-only scalar calibration still requires its own proof. -/
def recoveredUDirect (Eo : Field) (h : Admissible Eo) : Field :=
  AxialFromAngular.UFromField (decodedData Eo h).core (recoveredE Eo)

end EOnly

/-- Forward parameters are used ONLY to state the restoration correctness
check. The observable reader definitions above do not receive F or c. -/
def sourceCalibration (F : Profile) (XR : ℝ) : Calibration where
  scale := XR
  rate := F.data.core.lam
  height := F.data.h
  patch := OutgoingDilation.patchRadius F XR
  switch := OutgoingDilation.switchRadius F XR

private theorem patch_start_value (F : Profile) (XR : ℝ)
    (c : ℝ → TerminalCompensation.Coeff) (eta : ℝ) (hXR : 0 < XR) :
    HeatedOutgoing.E F XR c (OutgoingDilation.patchRadius F XR, eta) =
      OutgoingDilation.shapedPatchAmplitude F eta := by
  have hR := OutgoingDilation.patchRadius_pos F XR hXR
  rw [HeatedOutgoing.E_before_patch F XR c eta _ hXR hR le_rfl]
  have hone : (1 : ℝ) ∈ Icc OutgoingDilation.compensationPatch.left
      OutgoingDilation.compensationPatch.right := by
    constructor
    · exact le_rfl
    · exact OutgoingDilation.compensationPatch.ordered.le
  have h := OutgoingDilation.E_on_patch F XR eta 1 hXR hone
  simpa only [mul_one, Real.one_rpow] using h

/-- Checked formal proof of restoration after scalar calibration. The
identification of readCalibration with sourceCalibration is the mathematical
marker argument in the opening comment, not a proved theorem in this file. -/
theorem restoreDilatedE_roundtrip (F : Profile) (XR : ℝ)
    (c : ℝ → TerminalCompensation.Coeff) (X eta : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    restoreDilatedE (HeatedOutgoing.E F XR c) (sourceCalibration F XR) (X, eta) =
      OutgoingDilation.E F XR (X, eta) := by
  let R := OutgoingDilation.patchRadius F XR
  have hR : 0 < R := OutgoingDilation.patchRadius_pos F XR hXR
  change (if R ≤ X ∧ X ≤ R * Real.exp 5 then
    HeatedOutgoing.E F XR c (R, eta) * (X / R) ^ (-(1 / 2 + F.data.core.lam)) else
    HeatedOutgoing.E F XR c (X, eta) /
      HeatTailEdit.multiplier F.data.h (ParametricHeatTail.diffusion eta)
        (OutgoingDilation.switchRadius F XR) X) = _
  by_cases hp : R ≤ X ∧ X ≤ R * Real.exp 5
  · rw [ite_eq_left hp, patch_start_value F XR c eta hXR]
    have hx : X / R ∈ Icc OutgoingDilation.compensationPatch.left
        OutgoingDilation.compensationPatch.right := by
      constructor
      · change 1 ≤ X / R
        exact (le_div_iff₀ hR).mpr (by simpa using hp.1)
      · change X / R ≤ Real.exp 5
        exact (div_le_iff₀ hR).mpr (by simpa only [mul_comm] using hp.2)
    have hb := OutgoingDilation.E_on_patch F XR eta (X / R) hXR hx
    have hcancel : OutgoingDilation.patchRadius F XR * (X / R) = X := by
      change R * (X / R) = X
      field_simp [hR.ne']
    simpa only [hcancel] using hb.symm
  · rw [ite_eq_right hp]
    have hx : X / R ∉ Icc OutgoingDilation.compensationPatch.left
        OutgoingDilation.compensationPatch.right := by
      intro hx
      apply hp
      constructor
      · have hl : (1 : ℝ) ≤ X / R := hx.1
        simpa using (le_div_iff₀ hR).mp hl
      · have hr : X / R ≤ Real.exp 5 := hx.2
        simpa only [mul_comm] using (div_le_iff₀ hR).mp hr
    have hc := HeatedOutgoing.correction_zero_outside
      (x := X / OutgoingDilation.patchRadius F XR) (c eta) hx
    have hm := (HeatTailEdit.multiplier_bounds (K := OutgoingDilation.switchRadius F XR) F.data.h_pos
      (ParametricHeatTail.diffusion_mem heta).1 hX).1.ne'
    simp only [HeatedOutgoing.E, HeatedOutgoing.heatE, HeatedOutgoing.patchIncrement,
      hc, mul_zero, add_zero]
    exact mul_div_cancel_right₀ _ hm

theorem restoreE_roundtrip (F : Profile) (XR : ℝ)
    (c : ℝ → TerminalCompensation.Coeff) (x eta : ℝ)
    (hXR : 0 < XR) (hx : 0 < x) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    restoreE (HeatedOutgoing.E F XR c) (sourceCalibration F XR) (x, eta) = F.E (x, eta) := by
  change restoreDilatedE (HeatedOutgoing.E F XR c) (sourceCalibration F XR)
    (XR * x, eta) = _
  rw [restoreDilatedE_roundtrip F XR c (XR * x) eta hXR (mul_pos hXR hx) heta]
  simp only [OutgoingDilation.E, mul_div_cancel_left₀ x hXR.ne']

theorem restoreU_roundtrip (F : Profile) (XR : ℝ) (x eta : ℝ) (hXR : XR ≠ 0) :
    restoreU (HeatedOutgoing.U F XR) (sourceCalibration F XR) (x, eta) = F.U (x, eta) := by
  simp only [restoreU, sourceCalibration, HeatedOutgoing.U, OutgoingDilation.U,
    mul_div_cancel_left₀ x hXR]

/-- Restored E supplies U by the direct energy route. No U observations,
original Profile, or heat/reset coefficients are arguments to this reader. -/
def originalUFromObservedE (Eo : Field) (core : OutgoingSchedule.Parameters)
    (k : Calibration) : Field :=
  AxialFromAngular.UFromField core (restoreE Eo k)

/-- The later outgoing U is the original reconstructed U in dilated coordinates. -/
def laterUFromObservedE (Eo : Field) (core : OutgoingSchedule.Parameters)
    (k : Calibration) (p : ℝ × ℝ) : ℝ :=
  originalUFromObservedE Eo core k (p.1 / k.scale, p.2)

/-- Checked full composition with the actual heated source field, after
scalar calibration. F appears in the correctness statement, not the reader.
No off-band extension of E is required for correctness at a physical eta. -/
theorem originalUFromObservedE_roundtrip (F : Profile) (XR : ℝ)
    (c : ℝ → TerminalCompensation.Coeff) (x eta : ℝ)
    (hXR : 0 < XR) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    originalUFromObservedE (HeatedOutgoing.E F XR c) F.data.core
      (sourceCalibration F XR) (x, eta) = F.U (x, eta) := by
  have hs : ∀ X : ℝ, 0 < X →
      restoreE (HeatedOutgoing.E F XR c) (sourceCalibration F XR) (X, eta) =
        F.E (X, eta) := by
    intro X hX
    exact restoreE_roundtrip F XR c X eta hXR hX heta
  calc
    _ = AxialFromAngular.UFromField F.data.core F.E (x, eta) :=
      AxialFromAngular.UFromField_congr_slice F.data.core
        (restoreE (HeatedOutgoing.E F XR c) (sourceCalibration F XR)) F.E eta x hs
    _ = F.U (x, eta) := congrFun (AxialFromAngular.UFromField_source F) (x, eta)

theorem laterUFromObservedE_roundtrip (F : Profile) (XR : ℝ)
    (c : ℝ → TerminalCompensation.Coeff) (X eta : ℝ)
    (hXR : 0 < XR) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    laterUFromObservedE (HeatedOutgoing.E F XR c) F.data.core
      (sourceCalibration F XR) (X, eta) = HeatedOutgoing.U F XR (X, eta) := by
  change originalUFromObservedE (HeatedOutgoing.E F XR c) F.data.core
    (sourceCalibration F XR) (X / XR, eta) = _
  rw [originalUFromObservedE_roundtrip F XR c (X / XR) eta hXR heta]
  rfl

/-- Makes the still-pending calibration obligations explicit. The core and
marker equalities must be established from observations before this theorem
can turn the E-only readers into an unconditional source-recovery result. -/
theorem EOnly.recoveredUDirect_roundtrip (F : Profile) (XR : ℝ)
    (c : ℝ → TerminalCompensation.Coeff)
    (h : EOnly.Admissible (HeatedOutgoing.E F XR c))
    (hcore : (EOnly.decodedData (HeatedOutgoing.E F XR c) h).core = F.data.core)
    (hcalibration : EOnly.readCalibration (HeatedOutgoing.E F XR c) = sourceCalibration F XR)
    (x eta : ℝ) (hXR : 0 < XR) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    EOnly.recoveredUDirect (HeatedOutgoing.E F XR c) h (x, eta) = F.U (x, eta) := by
  change AxialFromAngular.UFromField
    (EOnly.decodedData (HeatedOutgoing.E F XR c) h).core
    (restoreE (HeatedOutgoing.E F XR c) (EOnly.readCalibration (HeatedOutgoing.E F XR c)))
    (x, eta) = _
  rw [hcore, hcalibration]
  exact originalUFromObservedE_roundtrip F XR c x eta hXR heta

/-- A larger proof bound retains the same actual data and reset coefficients.
This demonstrates why recovering the field need not identify the whole record. -/
def enlargeBound (F : Profile) : Profile where
  data := F.data
  coefficientBound := F.coefficientBound + 1
  reset := {
    coefficients := F.reset.coefficients
    smooth := F.reset.smooth
    angular := F.reset.angular
    pressure := F.reset.pressure
    coefficient_bound := by
      intro eta
      exact (F.reset.coefficient_bound eta).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (pow_nonneg F.data.core.lam_pos.le 28))
    eta_derivative_bound := by
      intro eta
      exact (F.reset.eta_derivative_bound eta).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (pow_nonneg F.data.core.lam_pos.le 28))
    small_jets := F.reset.small_jets }

theorem enlargeBound_E (F : Profile) : (enlargeBound F).E = F.E := rfl
theorem enlargeBound_U (F : Profile) : (enlargeBound F).U = F.U := rfl

theorem enlargeBound_ne (F : Profile) : enlargeBound F ≠ F := by
  intro h
  have hb := congrArg OutgoingProfile.Profile.coefficientBound h
  change F.coefficientBound + 1 = F.coefficientBound at hb
  linarith

end NavierStokes.FullFieldRecovery
