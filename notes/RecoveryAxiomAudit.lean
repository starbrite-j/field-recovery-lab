import notes.FullFieldRecovery
import notes.ProfileReverseTrace
import notes.SourceFieldRecovery
import notes.ObservedFieldRecovery

/-!
The output of these commands is saved by notes/verify_recovery.py. The audit
checks proof dependencies, not just whether the source text contains `sorry`.
Standard foundational axioms are recorded explicitly. The original E-only
decoded-core and calibration equalities remain hypotheses of that theorem.
ObservedFieldRecovery proves the calibration for exact assembled E with a
retained core, without assuming the calibration it is supposed to recover.
-/

#print axioms NavierStokes.AxialFromAngular.constantFromField_source
#print axioms NavierStokes.AxialFromAngular.UFromField_source
#print axioms NavierStokes.AxialFromAngular.UFromField_congr_slice
#print axioms NavierStokes.FullFieldRecovery.restoreDilatedE_roundtrip
#print axioms NavierStokes.FullFieldRecovery.restoreE_roundtrip
#print axioms NavierStokes.FullFieldRecovery.originalUFromObservedE_roundtrip
#print axioms NavierStokes.FullFieldRecovery.laterUFromObservedE_roundtrip
#print axioms NavierStokes.FullFieldRecovery.EOnly.recoveredUDirect_roundtrip
#print axioms NavierStokes.ProfileReverseTrace.heated_to_scheduled_core
#print axioms NavierStokes.SourceFieldRecovery.recoverOriginalE_source
#print axioms NavierStokes.SourceFieldRecovery.recoverOriginalU_source
#print axioms NavierStokes.SourceFieldRecovery.recoverLaterU_source
#print axioms NavierStokes.SourceFieldRecovery.exists_matched_recovery

#print axioms NavierStokes.ObservedFieldRecovery.heated_hasLogTail
#print axioms NavierStokes.ObservedFieldRecovery.assembled_hasLogTail
#print axioms NavierStokes.ObservedFieldRecovery.eventualSlopes_eq_singleton
#print axioms NavierStokes.ObservedFieldRecovery.assembled_readHeight
#print axioms NavierStokes.ObservedFieldRecovery.scaleCandidates_eq_singleton
#print axioms NavierStokes.ObservedFieldRecovery.readCalibration_source
#print axioms NavierStokes.ObservedFieldRecovery.recoveredE_source
#print axioms NavierStokes.ObservedFieldRecovery.recoveredU_source
#print axioms NavierStokes.ObservedFieldRecovery.recoveredLaterU_source
#print axioms NavierStokes.ObservedFieldRecovery.exists_matched_observed_recovery
