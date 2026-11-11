import notes.FullFieldRecovery
import notes.ProfileReverseTrace
import notes.SourceFieldRecovery

/-!
The output of these commands is saved by notes/verify_recovery.py. The audit
checks proof dependencies, not just whether the source text contains `sorry`.
Standard foundational axioms are recorded explicitly. The E-only decoded-core
and calibration equalities remain hypotheses of the corresponding theorem.
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
