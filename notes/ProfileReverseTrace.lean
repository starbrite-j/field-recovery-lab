import NavierStokes.ExtendedHeatedOutgoing
import NavierStokes.HeatSwitchHistoryDerivatives

/-!
# Local checkpoint: the profile reverse trace

Saved for Jess on 2026-11-11.
Source revision: f9e8bc5b38b6e212696e8a30e3e91517af887bbd.

VERIFICATION STATUS
The Lean declarations below compile with the pinned Lean 4.34.0-rc2 toolchain
(2026-11-11). Axiom checks for the thirteen audited recovery theorems report only
propext, Classical.choice, and Quot.sound, without unfinished-proof axioms.
The source-derived arguments in comments remain distinct from the checked
theorem statements, especially the unproved calibration-identification step.
This file is under notes/, outside the default library build globs.
Run the complete local check, including source dependencies and axiom audit:

    python3 notes/verify_recovery.py

Or, with the compiled source dependencies already present, check this file:

    lake env lean notes/ProfileReverseTrace.lean

RETURN THROUGH THE ACTUAL SOURCE ASSEMBLY (2026-11-11)
The fixed pre-heat source profile is PreparedOutgoing.prepared.profile.
See notes/SourceFieldRecovery.lean for its named originalE/originalU fields
and the earlier, log-coordinate scheduledLogE baseline. F is built from
TailData d, reset bound K and reset witness r, then retained in PreparedProfile.
The same F indexes the axis and outgoing stages of NominalProfile.Witness F.

The actual assembled W.E includes an axis section; it is not globally the
same input as HeatedOutgoing.E. The new reader fills the known outgoing ideal
prefix below heatJoin=XR*matchFraction, using core.P and XR, then applies the
checked heat/patch and direct-energy inverses. The source proves heatJoin<XR
and XR<patchRadius. The new proof identifies the completed observation with
HeatedOutgoing.E on positive radii in the physical eta band.

Checked recovery statements identify reconstructed E and U with the same
source F.E/F.U after supplied calibration. The reconstructed later outgoing U
agrees with the assembled W.U for X>heatJoin; the separately constructed axis
field is not identified with it. exists_matched_recovery instantiates the
route for PreparedOutgoing.prepared.profile and an actual matching witness.
This is symbolic source-level identification, not a numerical field extraction.
Automatic E-only calibration identification is still a separate proof obligation.

NEW EXACT-DATA RECOVERY ROUTE (2026-11-11)
See notes/FullFieldRecovery.lean for the newer observation-only reconstruction
of the pre-heat E,U field on X>0, |eta|<=1. It reads the scalar calibration
from complete exact observed fields, restores the reserved patch directly
from its known power curve, then divides out the heat multiplier and undoes
dilation. No original F or correction coefficients are inputs to its readers.
The source-derived marker-identification argument is written there; the
field-restoration proof scripts now compile. The older inverse formulas below
still use retained F and should not be mistaken for the newer observation-only
reader. The source theorem family has the paper wait schedule; arbitrary
finite/noisy observations and unrestricted off-band extensions are not covered.

MISSING c AND U (2026-11-11)
FullFieldRecovery.lean now also records an EOnly route. The early angular
logarithmic slope identifies scale and m without observing U. The earlier
two reset coefficients are then read from restored E at their bump centers,
and the source's CorrectedPulseAmplitude rule regenerates U. This requires
the scheduled source family and complete exact E, not just arbitrary angular
samples. The later three heat-patch coefficients remain unnecessary inputs.
The EOnly readers compile as definitions. Marker identification remains a
written argument, and no actual complete observed Profile has been recovered.

DIRECT ENERGY ROUTE, WITH BOTH U STAGES (2026-11-11)
See notes/AxialFromAngular.lean. The actual source identity
CorrectedPulseAmplitude.totalEnergy_normalized, evaluated at trial amplitude
zero, reads the amplitude polynomial's constant term directly from restored
E and the known core. Its quadratic and linear terms depend only on core.
Applying the actual clamped positive-root formula recovers Profile.amp,
then Profile.U. Neither set of correction coefficients needs to be sampled.
FullFieldRecovery.lean now composes this with angular restoration and records
both originalUFromObservedE and laterUFromObservedE. The latter evaluates the
former at X/XR, exactly as the source's OutgoingDilation.U does.

These Lean proof scripts now compile. The source identity is checked;
calibrating its inputs from arbitrary finite data is a
separate obligation. EOnly.recoveredUDirect_roundtrip leaves the decoded-core
and scalar-calibration equalities explicit rather than treating them as done.

Independent direct-energy audit:
    /Users/jj/.venvs/dedalus-test/bin/python notes/check_axial_from_angular.py --output notes/axial_recovery_audit.json
Four controlled Gaussian-field cases passed. Closed-form weighted integrals
independently check numerical quadrature; maximum absolute U error was
4.29e-14 for both original and rescaled later U. These fixtures exercise the
affine-in-amplitude energy identity, NOT an actual source Profile, source
Mathlib bump, thermal edit, or an integrated early-calibration-to-U example.
They do not replace an actual complete observed E dataset.

The audit also checks the clamp transition, a consequential omitted angular
tail, and rejection of out-of-coverage queries. In one active-clamp case,
omitting angular energy changes the constant term while leaving amplitude
unchanged: matching U alone cannot certify correct angular input. In the
scheduled physical source family, ScheduleBounds.constantTerm_bound instead
proves C<=-23/100, so the clamp is inactive for valid inputs there.

Numerical examples: lambda=1/120 gives log pulse length 1560, beyond float64
exp's finite range (~709.78); lambda^28 is ~6.07e-59, and float64 rounds
1+lambda^28 to 1. Log radius and normalized weighted fields avoid intermediate
coordinate overflow, but cannot recover observations already rounded away.

Independent numerical calibration checks:
    python3 notes/check_recovery_calibration.py
Nine cases passed using observed interior axial levels and angular samples
computed by independent quadrature of the source slope. Maximum absolute
errors were about 1.67e-14 for m, 8.0e-15 for log(scale), 1.26e-15 for lam,
2.27e-11 for log(patch radius), and 2.85e-14 for the clean patch curve.
These checks do not instantiate a certified Profile/PDE witness and do not
numerically validate the eventual-tail or last-equality extraction steps.
Nine additional E-only early calibration cases passed, using numerical
derivatives of independently integrated angular samples and a known clean
hold window. Maximum errors were about 1.44e-10 for m and 6.53e-10 for the
log patch radius. They do not test the full U regeneration or automatically
locate valid observation windows in arbitrary data.

CURRENT FOCUS: STARTING PROFILE AND CONSTRUCTION LINEAGE
The immediate task is to locate the starting mathematical profile and follow
which later constructions use it. Numerical recovery formulas below are
secondary to this source map.

1. ScheduledProfileChoice.lean:43-50 constructs core, then d:TailData,
   obtains its angular reset r, and creates F:Profile := <d,K,r>.
2. PreparedOutgoing.lean:53-70 obtains that constructed F and stores it as
   PreparedProfile.profile := F.
3. NominalProfile.lean:2481-2487 defines Witness(F:Profile) with both
   axis:AxisStage F and heat:ExtendedHeatedOutgoing.Witness F ... .
   Both stages are indexed by the same F input.
4. HeatedOutgoing.lean:27-36 computes the outgoing heat edit from that F:
   dilated F.E is multiplied by the heat multiplier and receives the patch.
5. NominalProfile.lean:2305-2306 explicitly uses
   ExtendedHeatedOutgoing.E F c.radius coef in the assembled angular field.
   Witness.E at 2497 supplies W.heat.coefficients to that construction.
   On the physical band, extendedE_physical and heatedE_after identify
   the outgoing part with HeatedOutgoing.E of the same F.
6. NominalConeAssembly.lean:1386-1405 carries d.profile through its family,
   matching witness, and resulting NominalProfile.Witness d.profile.

This is a direct source lineage for the outgoing heat edits. F remains an
explicit input; the edits define new field functions rather than mutating F.
F itself already includes the earlier angular reset. That earlier lineage is
OutgoingSchedule.angular -> OutgoingTail.flattened -> finalAngular ->
UniformAngularReset.correctedAngular = F.logE. The record and its earlier
field-construction stages should be distinguished when naming a starting point.

BEFORE F: INPUTS, BASELINE FIELDS, AND THE RESET DEPENDENCY
In the scheduled constructor, the immediate inputs are d, K, and r, not an
earlier Profile record. d contains the schedule core and the tail height h.

1. OutgoingSchedule.lean:978-983 builds core from P, m, and lam, with
   wait := 60 * log (1 / lam). ScheduledProfileChoice.lean:29-43 selects K
   and lam before building this core; lines 48-50 add h, obtain r, and build F.
   In the prepared construction, PreparedOutgoing.lean:38-55 first chooses
   the cone parameter M, sets P := max 2 (amplitudeThreshold M), and supplies
   M as the schedule's m. These are mathematical parameter choices.
2. OutgoingSchedule.lean:128-137 defines the baseline angular field from a
   radial amplitude and shape eta := 1 / (1 + eta^2). The axial baseline is
   initialAxial at line 252; axial at 497-499 adds the scheduled pulse.
3. OutgoingTail.lean:475-479 multiplies angular by flattenFactor.
   finalAngular at 557-559 adds the release and tail factors. This function
   is the complete angular field immediately before the angular reset.
4. UniformAngularReset.lean:845-847 integrates this same finalAngular into
   fullHistory. normalizedDebt_eq_actual at 867-870 identifies the reset
   target with its actual endpoint discrepancy. The reset construction at
   957-966 applies its solver to normalizedDebt d eta and stores the resulting
   coefficients. Thus the corrective coefficients depend on the earlier field.
5. UniformAngularReset.lean:1063-1064 multiplies finalAngular by
   1 + relative (...). OutgoingProfile.lean:34-35 makes that result F.logE.

The baseline is also explicitly identifiable inside F: OutgoingProfile.lean:
89-103 states that F.logE equals the scheduled angular field through the core
endpoint; for y <= 0, F.logE(y,eta) = P * shape eta * exp(y/10) and
F.logU(y,eta) = 4*eta. These are spatial log-coordinate regions, not dates.
This source lineage identifies the pre-reset mathematical field and the
specific operation applied to it. No numerical profile was instantiated.

ADDITIONAL SOURCE CLUES: UNIQUENESS, LOCALIZATION, PARABOLIC SCALING
"Localized lopitian" is provisionally matched to R3/LocalizedLaplacian.lean.
The clone also contains local Lipschitz results and L'Hopital uses; these
are different mathematical operations and the provisional match may change.

1. R3/WholeSpaceUniqueness.lean:72-97 compares a CandidateProperties 1
   velocity u with a smooth, uniformly finite-energy velocity v having the
   same forcing, divergence-free condition, and zero initial velocity. It
   concludes u=v on every closed interval [0,T] with T<1. The H3 alternative
   is R3/H3CandidateUniqueness.lean:90-114, for positive viscosity and its
   stated H3 strong-solution class. These compare full PDE velocities.
2. R3/LocalizedLaplacian.lean:125-150 gives the compactly weighted
   integration-by-parts identity: a negative weighted gradient-square term
   plus the cutoff-Laplacian term. R3/LocalizedDifferenceEnergy.lean:169
   uses it for w=u-v. The resulting difference_energy_balance is used by
   R3/WholeSpaceComparisonClosure.lean:135; that module closes comparison
   with WholeSpaceEnergyLimit at line 68. WholeSpaceUniqueness.lean:64
   then invokes the comparison closure. These are actual source uses.
3. R3/ParabolicDefinitions.lean:10-24 defines clock l t=l^2*(t-1)+1
   and rescales space and the velocity/pressure/force amplitudes. The
   compressedCandidate theorem in R3/ParabolicScaling.lean:95-115 retains
   viscosity, the finite-energy property, and speed-unboundedness at time 1.
   PeriodicPaperTheorem.lean:160 explicitly applies this theorem.
4. Closer to the outgoing heat exterior, WholeDomainHeatGeometry.lean:15-25
   defines parabolicLinear as a continuous linear equivalence with an explicit
   inverse, scaling time by a and space by sqrt(a) in the inverse direction.
   This coordinate equivalence and the actual heat equation are separate
   constructions. RadialHeatProfile.lean:635 states a forward heat equation.

This adds downstream comparison and coordinate tools to the earlier profile
lineage. Uniqueness conclusions require their stated common data and solution
classes; they do not identify arbitrary altered profiles from shared moments.

SOURCE PHOTOS AND THE OTHER MEANING OF F (2026-11-11)
Seven new Messages photos, IMG_5757.png through IMG_5763.png, match the
2026-02-01 conversation "Hum and Balance", ID
697f9409-d928-8327-8277-e230f273c6a3. Matching text was checked in raw
conversations-004.json at array index 95 as well as the math PDF selection.
The raw source SHA-256 matches its saved PDF manifest:
000092ea62bd4854f1b6be104dfc3adf17baaa2c18703184234820b2150cc36a.

The Desktop Mathematical-Conversations-August-2026-Export.pdf has 1497 pages;
its SHA-256 matches the split manifest:
0d692f6d73f3366f9773205fb8e953b190d754f3c5afaa9ca9a3d82c2b7f8395.
All pages were text-searched for the source equations. Matching passages on
pages 375-377 and 1452-1454 were read; pages 377 and 1452 were also rendered
and visually checked. This was targeted source review, not a full math audit.

1. Pages 375-376: x describes proposed conversational behavior; K describes
   its allowed region. The update is projected gradient descent:
   x_(t+1) = projection_K (x_t - eta * grad F(x_t)).
   F is an objective function here. The ten-line version defines
   F(x)=E(x)+lambda*R(x); these numerical functions remain unspecified.
2. Page 377: the later sketch introduces Phi(x;kappa)=E(x)+kappa*H(x),
   a logarithmic barrier, primal/dual updates, and a proposed Lyapunov gate.
   Its displayed argmin line lacks an explicit feasible-set restriction;
   the stated projection/feasibility guarantee requires further work.
3. Raw message eefb5f11-40c5-42d0-943e-c37fdaaa09dc contains derive_params:
   SHA-256 of phrase+'|'+nonce deterministically supplies kappa in [0.1,10]
   and six coordinates in [-1,1]. This reply is absent from the curated
   PDF's message-page manifest. The photos therefore add missing context.
4. Page 1452 records Jess's earlier correction that the mark preceding Gamma
   was an underscore. The intended notation is integral_subscript_Gamma,
   labeling the path. My initial reading of it as a negative multiplier was
   mistaken. The original photo also displays a literal exponent caret.

These are distinct mathematical roles: the photo's F is a scalar objective,
the circle-integral symbol is an operation, and this repository's F is the
OutgoingProfile.Profile record. A connection needs an explicit mapping of
states, fields, or operations; a shared letter does not supply that mapping.
The separate x/y coordinate file has not yet been identified.

EXACT UNCHANGED PROFILE / FIELD RESULTS (2026-11-11)
Returned to the clone at Jess's request. The following preserve functions or
fields themselves under the named operations, beyond preservation of moments.

1. SimilarityHomogeneity.lean:253-256 identifies two chart descriptions of
   the same physical point. chartTransition_inverse at 295-298 undoes that
   chart change. chartProfile_transition at 333-337 states, for an arbitrary
   inner-coordinate profile F, exact equality of its values after the chart
   transition. Hypotheses include 0<h<1/2, positive chart scales, and positive
   backward time. This changes the chart while retaining the profile value.
2. LocalPotentialRebundle.lean:24-30 subtracts a component J from the
   potential and adds curl J to the direct field. velocity_eq_original at
   96-109 identifies the complete recombined velocity with the previous
   velocity, pointwise for every t<1 under the smooth-sum hypothesis.
   velocity_eq_original_germ at 111-119 gives neighborhood equality too.
   LocalPaperTheorem.lean:151 explicitly uses this velocity equality.
3. Euler/PacketCommonRadius.lean:45-59 enlarges the budget radius while
   retaining fullProfile by rfl. fullProfile is the continuous scalar time
   profile defined in Euler/TransversePacketBudget.lean:91-92.
   Euler/PacketInitializedCanonicalRadius.lean:67-68 retains that same whole
   function in the initialized budget, again by rfl.
4. Euler/CylinderSobolevDerivatives.lean:22-30 drops the highest derivative
   bookkeeping level. value_truncateOperator at 75-78 states that its
   underlying L2 field is exactly the same. L2 equality is equality of field
   equivalence classes; it should not be mislabeled as pointwise equality
   of arbitrary representatives.

Scope: the heat edit is a different operation. HeatedOutgoing.lean:27-38
retains U exactly as the dilated base U, but defines E as base E times a heat
multiplier plus a patch increment. E_before_patch at 148-160 gives exact
equality with the base E on 0<X<=patchRadius; it is not a global equality.
The original F remains an explicit input and can be evaluated directly.
No source bridge from Euler's packet fullProfile to the NavierStokes outgoing
F was found in the checked references/import paths. These results identify
exact preservation for specified transformations, not one unchanged field
across every stage of the construction. No new proof compilation was run.

WHAT THE INVERSE USES
F is the retained OutgoingProfile.Profile, not a profile inferred from output
samples. Its data and angular-reset coefficients are available explicitly.
XR and the three heat-compensation coefficients c are also inputs. The inverse
identities use those same inputs. They do not solve for an unknown F or unknown
transformation parameters from the heated field alone.

ORDERED BACKWARD STEPS
1. Subtract the additive heat-compensation patch.
2. Divide by the positive heat multiplier on the physical parameter band.
3. Undo radial dilation X = XR * x; in logarithmic coordinates x = exp y.
4. Divide by the angular-reset multiplier, using F.reset.coefficients.
5. Divide out the release exponential and normalized tail-shape factor.
6. Divide by the flattening exponential to reach OutgoingSchedule.angular.
7. Account for the signed reset energy when comparing axial amplitudes.
8. On the axial branch, subtract the scheduled pulse and its moment repair
   to recover initialAxial; a sample within the main pulse can recover amp.
9. With TailData and XR supplied, sample the two earlier reset centers in
   the untouched region of the heated output to recover its reset coefficients
   pointwise in eta. The placement argument and precision limits are recorded
   below; the sampler's cancellation identity is given explicitly.

These steps reverse the stated angular-field construction with its retained
inputs. The scheduled core itself is another explicit construction, rather
than an assertion that every preceding choice has been uniquely recovered.
-/

noncomputable section

open Set MeasureTheory

namespace NavierStokes.ProfileReverseTrace

abbrev Profile := OutgoingProfile.Profile
abbrev HeatCoeff := TerminalCompensation.Coeff

private theorem cancel_product (a m : ℝ) (hm : m ≠ 0) : a * m / m = a := by
  field_simp [hm]

/-! ## Steps 1-3: heat compensation, heat multiplier, and radial dilation -/

def heatMultiplier (F : Profile) (XR : ℝ) (p : ℝ × ℝ) : ℝ :=
  HeatTailEdit.multiplier F.data.h (ParametricHeatTail.diffusion p.2)
    (OutgoingDilation.switchRadius F XR) p.1

/-- The literal definition of the heated field, with the two edits separated.
Source: HeatedOutgoing.lean:27-36. -/
theorem heated_decomposition (F : Profile) (XR : ℝ) (c : ℝ → HeatCoeff)
    (p : ℝ × ℝ) :
    HeatedOutgoing.E F XR c p =
      OutgoingDilation.E F XR p * heatMultiplier F XR p +
        HeatedOutgoing.patchIncrement F XR c p := rfl

/-- Positivity is conditional on positive radius and the physical eta band.
Sources: HeatTailEdit.multiplier_bounds; ParametricHeatTail.diffusion_mem. -/
theorem heatMultiplier_pos (F : Profile) (XR : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ HeatedOutgoing.domain) : 0 < heatMultiplier F XR p :=
  (HeatTailEdit.multiplier_bounds F.data.h_pos
    (ParametricHeatTail.diffusion_mem hp.2).1 hp.1).1

theorem undo_heat (F : Profile) (XR : ℝ) (c : ℝ → HeatCoeff)
    {p : ℝ × ℝ} (hp : p ∈ HeatedOutgoing.domain) :
    (HeatedOutgoing.E F XR c p - HeatedOutgoing.patchIncrement F XR c p) /
        heatMultiplier F XR p = OutgoingDilation.E F XR p := by
  have hm : heatMultiplier F XR p ≠ 0 := ne_of_gt (heatMultiplier_pos F XR hp)
  rw [heated_decomposition, add_sub_cancel_right]
  exact cancel_product _ _ hm

/-- Source: OutgoingDilation.lean:61. XR is retained coordinate-scale data. -/
theorem undo_dilation (F : Profile) (XR x eta : ℝ) (hXR : XR ≠ 0) :
    OutgoingDilation.E F XR (XR * x, eta) = F.E (x, eta) := by
  simp only [OutgoingDilation.E, mul_div_cancel_left₀ x hXR]

theorem undo_heat_in_log_coordinates (F : Profile) (XR : ℝ)
    (c : ℝ → HeatCoeff) (y eta : ℝ) (hXR : 0 < XR)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    (HeatedOutgoing.E F XR c (XR * Real.exp y, eta) -
        HeatedOutgoing.patchIncrement F XR c (XR * Real.exp y, eta)) /
        heatMultiplier F XR (XR * Real.exp y, eta) = F.logE (y, eta) := by
  have hp : (XR * Real.exp y, eta) ∈ HeatedOutgoing.domain :=
    ⟨mul_pos hXR (Real.exp_pos y), heta⟩
  rw [undo_heat F XR c hp, undo_dilation F XR (Real.exp y) eta hXR.ne']
  change F.logE (Real.log (Real.exp y), eta) = F.logE (y, eta)
  rw [Real.log_exp]

/-! ## Step 4: undo the earlier two-bump angular reset -/

def resetMultiplier (F : Profile) (p : ℝ × ℝ) : ℝ :=
  1 + AngularMomentReset.relative (F.reset.coefficients p.2)
    (p.1 - UniformAngularReset.correctionCenter F.data)

/-- Sources: OutgoingProfile.Profile.logE; UniformAngularReset.correctedAngular. -/
theorem reset_decomposition (F : Profile) (p : ℝ × ℝ) :
    F.logE p = OutgoingTail.finalAngular F.data p * resetMultiplier F p := rfl

/-- The reset witness gives a nonvanishing factor everywhere, not just on
the physical eta band. Source: UniformAngularReset.ResetWitness.small_jets. -/
theorem resetMultiplier_bounds (F : Profile) (p : ℝ × ℝ) :
    (1 / 2 : ℝ) ≤ resetMultiplier F p ∧ resetMultiplier F p ≤ 3 / 2 := by
  have h := abs_le.mp (F.reset.small_jets p.2
    (p.1 - UniformAngularReset.correctionCenter F.data)).1
  dsimp [resetMultiplier]
  constructor <;> linarith [h.1, h.2]

theorem resetMultiplier_pos (F : Profile) (p : ℝ × ℝ) :
    0 < resetMultiplier F p := by
  have h := (resetMultiplier_bounds F p).1
  linarith

theorem undo_reset (F : Profile) (p : ℝ × ℝ) :
    F.logE p / resetMultiplier F p = OutgoingTail.finalAngular F.data p := by
  rw [reset_decomposition]
  exact cancel_product _ _ (ne_of_gt (resetMultiplier_pos F p))

/-! ## Steps 5-6: undo release, the terminal tail factor, and flattening -/

def releaseFactor (d : OutgoingTail.TailData) (y : ℝ) : ℝ :=
  Real.exp (OutgoingTail.releaseAdjustment d (y - d.releaseStart))

def tailFactor (d : OutgoingTail.TailData) (y : ℝ) : ℝ :=
  OutgoingTail.tailShape d (y - OutgoingTail.tailStart d) / (1 - d.rho)

theorem releaseFactor_pos (d : OutgoingTail.TailData) (y : ℝ) :
    0 < releaseFactor d y := Real.exp_pos _

theorem tailFactor_pos (d : OutgoingTail.TailData) (y : ℝ) :
    0 < tailFactor d y := by
  exact div_pos (OutgoingTail.tailShape_pos d _) (by linarith [d.rho_lt_half])

/-- Source: OutgoingTail.finalAngular, immediately before its positivity proof. -/
theorem tail_decomposition (d : OutgoingTail.TailData) (p : ℝ × ℝ) :
    OutgoingTail.finalAngular d p =
      OutgoingTail.flattened d p * releaseFactor d p.1 * tailFactor d p.1 := rfl

theorem undo_release_and_tail (d : OutgoingTail.TailData) (p : ℝ × ℝ) :
    OutgoingTail.finalAngular d p / (releaseFactor d p.1 * tailFactor d p.1) =
      OutgoingTail.flattened d p := by
  have hr := ne_of_gt (releaseFactor_pos d p.1)
  have ht := ne_of_gt (tailFactor_pos d p.1)
  rw [tail_decomposition]
  field_simp [hr, ht]

theorem flattenFactor_pos (d : OutgoingTail.TailData) (p : ℝ × ℝ) :
    0 < OutgoingTail.flattenFactor d p := by
  unfold OutgoingTail.flattenFactor
  exact Real.exp_pos _

theorem undo_flattening (d : OutgoingTail.TailData) (p : ℝ × ℝ) :
    OutgoingTail.flattened d p / OutgoingTail.flattenFactor d p =
      OutgoingSchedule.angular d.core.P d.core.dropLength d.core.lam p := by
  unfold OutgoingTail.flattened
  exact cancel_product _ _ (ne_of_gt (flattenFactor_pos d p))

/-- All pre-heat angular modifications collected in their forward order. -/
def upstreamMultiplier (F : Profile) (p : ℝ × ℝ) : ℝ :=
  OutgoingTail.flattenFactor F.data p * releaseFactor F.data p.1 *
    tailFactor F.data p.1 * resetMultiplier F p

theorem upstreamMultiplier_pos (F : Profile) (p : ℝ × ℝ) :
    0 < upstreamMultiplier F p :=
  mul_pos
    (mul_pos (mul_pos (flattenFactor_pos F.data p) (releaseFactor_pos F.data p.1))
      (tailFactor_pos F.data p.1))
    (resetMultiplier_pos F p)

theorem logE_decomposition (F : Profile) (p : ℝ × ℝ) :
    F.logE p =
      OutgoingSchedule.angular F.data.core.P F.data.core.dropLength F.data.core.lam p *
        upstreamMultiplier F p := by
  rw [reset_decomposition F p, tail_decomposition F.data p]
  unfold OutgoingTail.flattened upstreamMultiplier
  ring

theorem undo_to_scheduled_core (F : Profile) (p : ℝ × ℝ) :
    F.logE p / upstreamMultiplier F p =
      OutgoingSchedule.angular F.data.core.P F.data.core.dropLength F.data.core.lam p := by
  rw [logE_decomposition]
  exact cancel_product _ _ (ne_of_gt (upstreamMultiplier_pos F p))

/-- The complete angular-field inverse, with the original inputs supplied. -/
theorem heated_to_scheduled_core (F : Profile) (XR : ℝ) (c : ℝ → HeatCoeff)
    (y eta : ℝ) (hXR : 0 < XR) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    ((HeatedOutgoing.E F XR c (XR * Real.exp y, eta) -
        HeatedOutgoing.patchIncrement F XR c (XR * Real.exp y, eta)) /
        heatMultiplier F XR (XR * Real.exp y, eta)) /
        upstreamMultiplier F (y, eta) =
      OutgoingSchedule.angular F.data.core.P F.data.core.dropLength F.data.core.lam
        (y, eta) := by
  rw [undo_heat_in_log_coordinates F XR c y eta hXR heta]
  exact undo_to_scheduled_core F (y, eta)

/-! ## Step 7: retain the energy cost when comparing axial fields -/

/-- Pressure neutrality is an unweighted logarithmic integral. It does not
assert that the differently weighted energy change vanishes. -/
theorem reset_pressure_neutral (F : Profile) (eta : ℝ) :
    (∫ y, F.logE (y, eta) ^ 2 - OutgoingTail.finalAngular F.data (y, eta) ^ 2) = 0 :=
  F.reset.pressure_neutral eta

theorem reset_energy_balance (F : Profile) (A eta : ℝ) :
    CorrectedPulseAmplitude.totalEnergy F.data F.reset.coefficients A eta =
      PulseAmplitude.totalEnergy F.data A eta -
        ResetEnergyBounds.resetEnergy F.data F.reset.coefficients eta / 2 :=
  CorrectedPulseAmplitude.totalEnergy_eq F.data F.reset.coefficients A eta

theorem amplitude_constant_keeps_shift (F : Profile) (eta : ℝ) :
    CorrectedPulseAmplitude.constantTerm F.data F.reset.coefficients eta =
      PulseAmplitude.constantTerm F.data eta -
        CorrectedPulseAmplitude.energyShift F.data F.reset.coefficients eta := rfl

/-! ## Step 8: the scheduled axial field and its main-pulse amplitude -/

/-- Source: OutgoingProfile.Profile.logU and OutgoingSchedule.axial. -/
theorem axial_pulse_decomposition (F : Profile) (y eta : ℝ) :
    F.logU (y, eta) =
      OutgoingSchedule.initialAxial F.data.core.m (y, eta) +
        OutgoingSchedule.angular F.data.core.P F.data.core.dropLength F.data.core.lam
          (y, eta) *
        OutgoingSchedule.pulseRatio F.data.core F.amp (y - F.data.core.pulseStart, eta) :=
  rfl

theorem undo_axial_pulse (F : Profile) (y eta : ℝ) :
    F.logU (y, eta) -
        OutgoingSchedule.angular F.data.core.P F.data.core.dropLength F.data.core.lam
          (y, eta) *
        OutgoingSchedule.pulseRatio F.data.core F.amp (y - F.data.core.pulseStart, eta) =
      OutgoingSchedule.initialAxial F.data.core.m (y, eta) := by
  rw [axial_pulse_decomposition]
  ring

/-- The later moment-repair bumps are absent on this main-pulse interval.
Source: OutgoingSchedule.pulseRatio_on_main_pulse. -/
theorem axial_on_main_pulse (F : Profile) (y eta : ℝ)
    (hy : y - F.data.core.pulseStart ≤ 11 / F.data.core.lam) :
    F.logU (y, eta) =
      OutgoingSchedule.initialAxial F.data.core.m (y, eta) +
        OutgoingSchedule.angular F.data.core.P F.data.core.dropLength F.data.core.lam
          (y, eta) * F.amp eta *
        OutgoingSchedule.mainPulse (F.data.core.lam * (y - F.data.core.pulseStart)) := by
  rw [axial_pulse_decomposition,
    OutgoingSchedule.pulseRatio_on_main_pulse F.data.core F.amp eta hy]
  ring

/-- A conditional inverse from an interior axial value, with core parameters
retained. The pulse must be nonzero at the chosen sample. -/
theorem recover_axial_amplitude (F : Profile) (y eta : ℝ)
    (hy : y - F.data.core.pulseStart ≤ 11 / F.data.core.lam)
    (hm : OutgoingSchedule.mainPulse
      (F.data.core.lam * (y - F.data.core.pulseStart)) ≠ 0) :
    (F.logU (y, eta) - OutgoingSchedule.initialAxial F.data.core.m (y, eta)) /
        (OutgoingSchedule.angular F.data.core.P F.data.core.dropLength F.data.core.lam
          (y, eta) *
        OutgoingSchedule.mainPulse (F.data.core.lam * (y - F.data.core.pulseStart))) =
      F.amp eta := by
  have he := (OutgoingSchedule.angular_pos F.data.core.P_pos F.data.core.dropLength
    F.data.core.lam (y, eta)).ne'
  rw [axial_on_main_pulse F y eta hy]
  field_simp [he, hm]
  ring

/-- In particular, phase 1 is a nonzero sample: mainPulse(1) >= 49/50.
It occurs at y = pulseStart + 1/lam, inside the uncorrected main pulse. -/
theorem mainPulse_one_pos : 0 < OutgoingSchedule.mainPulse 1 := by
  have h := PulseAmplitude.mainPulse_lower (z := 1) (by norm_num) (by norm_num)
  linarith

/-! ## Step 9: read earlier reset coefficients from observed field values -/

def resetSampleClock (d : OutgoingTail.TailData) (j : Fin 2) : ℝ :=
  d.releaseStart - 3 + 2 * (j.val : ℝ)

/-- The unreset baseline at a sample center, computable from TailData alone. -/
def resetBaseline (d : OutgoingTail.TailData) (j : Fin 2) : ℝ :=
  AngularMomentReset.baseE d.core.lam (UniformAngularReset.referenceAmplitude d)
    (resetSampleClock d j)

theorem resetBaseline_pos (d : OutgoingTail.TailData) (j : Fin 2) :
    0 < resetBaseline d j := by
  unfold resetBaseline AngularMomentReset.baseE
  exact mul_pos (UniformAngularReset.referenceAmplitude_pos d) (Real.exp_pos _)

/-- This reader takes an observed angular field, TailData, and the radial
scale. It does not take either set of reset/heat-compensation coefficients. -/
def readResetCoefficient (d : OutgoingTail.TailData) (XR : ℝ)
    (observed : ℝ × ℝ → ℝ) (eta : ℝ) (j : Fin 2) : ℝ :=
  observed (XR * Real.exp (resetSampleClock d j), eta) / resetBaseline d j - 1

/-- Algebraic cancellation once the center sample equation is supplied.
The repository support/placement argument that supplies this equation for
the heated field is recorded in checkpoint M below; it is not additionally
formalized as an unconditional source-instantiation theorem in this file. -/
theorem readResetCoefficient_of_sample (d : OutgoingTail.TailData) (XR : ℝ)
    (observed : ℝ × ℝ → ℝ) (eta : ℝ) (b : AngularMomentReset.Coeff) (j : Fin 2)
    (hobs : observed (XR * Real.exp (resetSampleClock d j), eta) =
      resetBaseline d j * (1 + b j)) :
    readResetCoefficient d XR observed eta j = b j := by
  unfold readResetCoefficient
  rw [hobs]
  have hb : resetBaseline d j ≠ 0 := ne_of_gt (resetBaseline_pos d j)
  field_simp [hb]
  ring

/-!
## Additional checkpoints established during the source trace

A. Preserved M and J do not identify the full angular field.
   HeatedOutgoing.M_unchanged is definitional; J_unchanged follows because the
   edited regions have zero axial U. This holds for arbitrary heat-patch
   coefficients, without requiring their three moment equations.
   Comparing against the undilated original also requires different scales:
       M_d(X) = XR * F.M(eta, X/XR),
       J_d(X) = XR * sqrt(XR) * F.J(eta, X/XR).
   Sources for the scales: OutgoingDilation.M_scaling and J_scaling.
   Source: HeatedOutgoing.lean:425-456.

B. There are three distinct physical moment checks.
   TerminalCompensation.physicalMoments_eq gives diagonal scales
       2*a^2,  2*R*a^2,  R*sqrt(2*R)*a.
   Residual = physicalMoments + physicalDebt. For the associated integrable
   profile changes its rows give changes in axis datum (-row 0 / 2), totalS
   (-row 1 / 2), and renormalized angular integral (row 2). The third check
   integrates the change in H; it is different from J, which integrates H*U.
   Source: HeatedOutgoing.changeRow and its decomposition/integral theorems.

C. Small-solution uniqueness is local and uses the full normalized target.
   The normalized moment map is Q(c) = B*c + A(c,c). If both coefficient
   vectors lie in the permitted radius r, beta bounds the inverse linear
   map, kappa bounds the bilinear term, and 4*beta*kappa*r <= 1, then
       norm(c - c*) <= 2*beta*norm(Q(c) - Q(c*)).
   For an exact target this also gives an error bound from normalized
   residual. Normalize physical residual rows by the three scales in B.
   Source: UniformAngularReset.quadratic_solution_distance, used by
   TerminalCompensation.exists_normalized_compensation.

D. Full histories retain more information than a few endpoint moments.
   In logarithmic radius y the actual histories satisfy
       d(logI)/dy  = exp(3*y/2) * logE,
       d(logS)/dy  = exp(y) * (F.logU^2 - logE^2/2),
       d(logPi)/dy = logE^2/2.
   Here logE is the EDITED field. Recovering the pre-edit field still uses
   the inverse and side data above.
   Source: HeatSwitchHistoryDerivatives.logI_hasDerivAt,
   logS_hasDerivAt, logPi_hasDerivAt.

E. Endpoint values do not settle endpoint derivatives.
   At eta = 1, diffusion = 0, multiplier = 1, and all physical heat debts
   vanish. Nevertheless, for K >= 1 the actual angular debt has strictly
   positive derivative within [-1,1] at eta = 1.
   Derived consequence, not a new formal theorem in this checkpoint:
   writing L(c) for normalized moment row 2, any differentiable compensating
   family obeys
       L(c'(1)) = -angularDebt'(1)/(R*sqrt(2*R)*a(1)) < 0.
   This follows by differentiating its third cancellation equation; its
   value at 1 gives L(c(1)) = 0, removing the amplitude-derivative term.
   Source: ParametricHeatTail.physical_debts_zero and
   physicalAngular_endpoint_derivative_pos; TerminalCompensation.physicalMoments_eq.

F. Parameter derivatives include the coefficient derivatives.
   HeatSwitchCone.controls includes c(eta) and derivWithin c at eta.
   The exact chain rule is realize_parameter_derivative. FirstJetWithinBound
   also controls the parameter derivative of amplitude * correction.

G. One extended coefficient branch supplies the physical-band branch.
   ExtendedHeatedOutgoing.Witness.physical reuses w.coefficients exactly.
   Its physical_coefficients theorem is rfl, and fields_eq_physical proves
   equality of E, U, H, Pi on the physical band.

H. Smooth continuation across zero diffusion is a separate construction.
   HeatProfileExtension uses the actual right endpoint jets, a Borel-series
   left branch, and EndpointExtension.glue. Every endpoint derivative
   matches. Smoothness and endpoint derivatives alone do not uniquely
   determine an extension: adding a smooth bump supported in (-3/4,-1/2)
   changes the negative side while preserving the nonnegative side and
   every derivative at zero. This nonuniqueness example is a mathematical
   derivation, not a formal theorem supplied by this checkpoint. It does
   not replace the particular extension chosen in the repository.

I. Euler supplies a separate explicitly constructed initialDatum.
   Source: Euler/PacketFiniteLifespan.lean:18. No identification of that
   datum with this OutgoingProfile.Profile has been established in this
   trace. The retained F directly supplies the pre-heat profile used here.

J. Conditioning bounds have different scopes.
   The reset multiplier is in [1/2,3/2], so its inverse amplifies additive
   value error by at most 2 when coefficients are exact. Earlier, using
   h < 1/20, physical diffusion in [0,1], and switch K >= 1, we derived the
   heat multiplier bound m > 179/200, hence 1/m < 200/179. That numerical
   heat bound has not been formalized in this checkpoint. Positivity of
   every factor is not a uniform numerical conditioning bound for the
   entire upstream product over all radii.

K. Three samples can identify the three additive heat-patch coefficients
   when its base model, R, a, and lam are supplied. If z_j is the center
   of bump j, disjoint support and bump_at_center give
       editedE(R*z_j,eta) = a * (z_j^(-1/2-lam) + c_j(eta)),
       c_j(eta) = editedE(R*z_j,eta)/a - z_j^(-1/2-lam).
   The centers are at fractions 3/14, 1/2, 11/14 of the patch width from
   its left endpoint. a is the positive shaped patch amplitude. This is
   an algebraic derivation from the patch model and bump definitions,
   not a separate compiled theorem in this checkpoint.
   Sources: TerminalCompensation.lower, upper, bump, bumps_disjoint,
   physicalProfile; LocalizedMomentRepair.bump_at_center;
   HeatedOutgoing.E_on_patch.

L. The scheduled core already contains an earlier two-row axial repair.
   OutgoingSchedule.axial = initialAxial + angular * pulseRatio, with
   pulseRatio = amp * mainPulse + correction. The correction is chosen
   from the actual prefix and pulse debts to close both mass and angular
   moments at the pulse endpoint, for every amplitude function.
   Sources: OutgoingSchedule.debt, correction_exact, massMoment_endpoint,
   angularMoment_endpoint. Energy is a further condition used to select
   the actual F.amp; the endpoint moment equalities alone do not select it.
   In the main pulse the repair is zero, giving recover_axial_amplitude
   above. At phase 1 the pulse is >= 49/50, so that sample is nonzero.

M. The earlier reset coefficients can be read from the output of the heat
   stage, with TailData d and XR > 0 supplied, without supplying those
   coefficients or the later heat-patch coefficients to the reader.
   For j = 0,1, take
       y_j = d.releaseStart - 3 + 2*j,
       X_j = XR * exp(y_j),
       B_j = baseE(lam, referenceAmplitude(d), y_j).
   At the center of each reset bump that bump is 1 and the other is 0.
   Hence correctedAngular(y_j,eta) = B_j * (1 + b_j(eta)).
   The support/placement argument is:
     - The later additive heat patch has logarithmic interval
       [pulseStart-20, pulseStart-15], before the core pulse.
     - Both y_j are after flattenEnd and inside (releaseStart-4,releaseStart).
     - Both y_j are before switchStart = tailStart + 1/5.
     - Thus HeatedOutgoing.E_between_patch_and_switch applies at X_j,
       so the heated field there equals the radially dilated original.
   Consequently readResetCoefficient(d,XR,heatedE,eta,j) = b_j(eta).
   This placement and center-sampling conclusion is a source-derived
   argument; the new formal theorem above only proves the final algebraic
   cancellation under its explicit sample-equation hypothesis.
   Sources: AngularMomentReset.template_at_zero, bump, bumps_disjoint;
   UniformAngularReset.correctionCenter, original_matches_reference,
   correctedAngular; OutgoingDilation.patchClock,
   patchClock_end_before_pulse; HeatedOutgoing.E_between_patch_and_switch.
   Two values recover the coefficients at ONE eta; recovering functions
   across the band needs the two sampling curves, not just two scalar values.

N. Exact coefficient recovery can be numerically sensitive.
   If an observed sample has additive error eps_j with B_j known exactly,
       recovered_b_j - b_j = eps_j / B_j.
   Relative to B(flattenEnd) = radialAmplitude(flattenEnd)/2, the baseline
   ratios at the two centers are exactly
       exp(-(1/2+lam)*(30*log(1/lam)-3)),
       exp(-(1/2+lam)*(30*log(1/lam)-1)).
   A local scalar evaluation at lam=0.05 gave about 1.77660535e-21 and
   5.91380550e-22. These are ratios from the schedule formula, not a claim
   that a numerical ResetWitness has been instantiated at that lambda.
   An illustrative precision check, also not a repository witness, used
   B=1e-40 and b=1e-20 in observed=B*(1+b). With 100-digit Decimal the
   recovery was 1e-20; ordinary float recovery was zero. This shows why
   exact real-number identities do not guarantee a robust finite-precision
   implementation, or recovery from already rounded observations.
   Retained coefficients avoid this particular extraction step. This is
   compatible with the reset's bounded multiplicative inverse when its
   coefficients are already supplied (checkpoint J).

O. Calibrate the radial coordinate before treating the sampler as a full
   reconstruction from observations. On the ideal prefix 0 < X <= XR,
       E(X,eta) = P*shape(eta)*(X/XR)^(1/10),
       U(X,eta) = 4*eta.
   For positive X and XR, this rewrites as
       E(X,eta) = (P*XR^(-1/10))*shape(eta)*X^(1/10).
   Thus observations restricted to E and U on a common ideal-prefix region
   determine the combined normalization P*XR^(-1/10), and cannot separate
   P from XR without further information. The algebraic prefix example
   (P,XR)=(2,1) and (4,1024) gives the same E and U for 0 < X <= 1.
   This is an example of the prefix formulas, not a pair of fully evaluated
   compensation witnesses. It makes no assertion that the complete fields,
   pressure constants, transition regions, or their other parameters agree.
   Stored scale/parameter data or additional observations outside this
   restricted set can supply information that the prefix samples omit.
   Sources: HeatedOutgoing.CompensationWitness.ideal_prefix;
   OutgoingDilation.ideal_prefix; OutgoingProfile.Profile.E_ideal, U_ideal.

P. More of the axial field can provide the missing radial calibration.
   This is a source-derived reconstruction under an exact, noiseless curve
   and correct identification of its INITIAL pre-pulse drop. It is not
   a formalized marker-detection theorem in this checkpoint.
   At eta=1, before the core pulse,
       U(X,1) = dropCoefficient(m, log(X/XR)).
   The transition definition has sigma(1/2)=1/2 because its two edge values
   coincide. For m>0 and XR>0 this gives the half-height marker U=2 at
       y_half = exp(m/2),  X_half = XR*exp(exp(m/2)).
   The first zero plateau starts at
       y_zero = exp(m),    X_zero = XR*exp(exp(m)).
   The marker is before pulseStart because pulseStart=exp(m)+12+wait,
   with wait>25. Positivity of the edge at 1-log(y)/m shows the initial
   drop remains positive for 1<y<exp(m); the explicit edge formula also
   makes sigma strictly increasing on (0,1), so the initial half-height
   marker is unique. These extra positivity/uniqueness observations are
   mathematical derivations from the definitions, not newly compiled lemmas.
   In LOG physical coordinates let
       z_half = log(X_half), z_zero = log(X_zero), D = z_zero-z_half.
   Setting t=exp(m/2)>1 gives D=t^2-t, hence
       t = (1 + sqrt(1+4*D))/2,
       m = 2*log(t),
       log(XR) = z_half-t.
   The heat stage leaves U unchanged apart from radial dilation, so the
   formulas do not require either set of angular compensation coefficients.
   Local 80-digit Decimal checks recovered the input scalar pairs
   (m,XR)=(0.1,0.001), (1,3), (3,1e10) up to rounding near 1e-79.
   These checks cover only the marker-calibration formulas, not full
   instantiated profile witnesses or a noisy field-recovery algorithm.
   Locating a flat zero boundary from noisy samples is a separate problem;
   exact marker positions must not be assumed available in such data.
   Sources: OutgoingSchedule.sigma, dropCoefficient_eq, dropCoefficient_late,
   Parameters.pulseStart, axial_before_pulse; FlatCutoff.edge;
   HeatedOutgoing.U; OutgoingDilation.U.

Q. Once XR is calibrated, the normalization P is directly observable at
   the ideal-prefix boundary on another parameter slice:
       P = E_heated(XR, 0).
   This follows by substituting X=XR and eta=0 into ideal_prefix, since
   shape(0)=1 and 1^(1/10)=1. It does not identify every other TailData
   parameter. Sources: HeatedOutgoing.CompensationWitness.ideal_prefix;
   OutgoingSchedule.shape.
-/

def compensationResidual (F : Profile) (XR : ℝ) (c : ℝ → HeatCoeff)
    (eta : ℝ) : HeatCoeff :=
  TerminalCompensation.physicalMoments OutgoingDilation.compensationPatch F.data.core.lam
    (OutgoingDilation.patchRadius F XR) (OutgoingDilation.shapedPatchAmplitude F eta)
    (c eta) + ParametricTerminalCompensation.physicalDebt F.data
      (OutgoingDilation.switchRadius F XR) eta

theorem compensationResidual_zero (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {eta : ℝ}
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    compensationResidual F XR w.coefficients eta = 0 := w.moments eta heta

theorem heat_debts_at_endpoint (d : OutgoingTail.TailData) (K : ℝ) :
    ParametricHeatTail.physicalPressure d K 1 = 0 ∧
      ParametricHeatTail.physicalEnergy d K 1 = 0 ∧
      ParametricHeatTail.physicalAngular d K 1 = 0 := by
  apply ParametricHeatTail.physical_debts_zero d K
  norm_num [ParametricHeatTail.diffusion]

theorem angular_debt_endpoint_derivative_pos (d : OutgoingTail.TailData)
    {K : ℝ} (hK : 1 ≤ K) :
    0 < derivWithin (ParametricHeatTail.physicalAngular d K) (Icc (-1 : ℝ) 1) 1 :=
  ParametricHeatTail.physicalAngular_endpoint_derivative_pos d hK

end NavierStokes.ProfileReverseTrace
