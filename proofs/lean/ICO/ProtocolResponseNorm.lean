import ICO.ProtocolHaarOutput
import ICO.MHPurifiedResponseNorm

namespace ICO.ProtocolHaarOutput
open Matrix QIT ICO.SequentialIsometry ICO.RecordingHistory
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
universe u
set_option maxHeartbeats 1800000
variable {A M O H : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
  [Fintype H] [DecidableEq H]

theorem rankOne_trace_re_norm_sq (v : H → ℂ) :
    (rankOneMatrix v).trace.re=‖WithLp.toLp 2 v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Matrix.trace,Matrix.diag,rankOneMatrix_apply,Complex.mul_re,
    pow_two]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Complex.normSq_apply,pow_two] using (Complex.sq_norm (v i)).symm

theorem response_norm_sq {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ)
    (t : ℕ) (U : Matrix.unitaryGroup A ℂ) :
    ‖response tail v t U‖^2=(rankOneMatrix v).trace.re := by
  have htrace : (visibleDensity tail v t U).trace=(rankOneMatrix v).trace := by
    rw [visibleDensity_evolution]
    exact tailEvolution_trace tail _
      (ICO.SwitchObservable.hidden_basis_kraus_complete _ U.property.1 U.property.2) _ t
  have herase := eraseHistory.tracePreserving
    (rankOneMatrix (ICO.ProtocolLudersTrajectory.run tail (U:CMatrix A) v t))
  change (visibleDensity tail v t U).trace=
    (rankOneMatrix (ICO.ProtocolLudersTrajectory.run tail (U:CMatrix A) v t)).trace at herase
  have hh := congrArg Complex.re (herase.symm.trans htrace)
  rw [rankOne_trace_re_norm_sq] at hh
  exact hh

theorem response_norm_one {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ)
    (hv : (rankOneMatrix v).trace.re=1) (t : ℕ) (U : Matrix.unitaryGroup A ℂ) :
    ‖response tail v t U‖=1 := by
  have h := response_norm_sq tail v t U
  rw [hv] at h
  nlinarith [norm_nonneg (response tail v t U)]

theorem purified_response_norm_one {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ)
    (hv : (rankOneMatrix v).trace.re=1) (t : ℕ) (C D : Matrix.unitaryGroup A ℂ) :
    ‖ICO.MHHaarPurifiedMixture.purifiedResponse (response tail v t) C D‖=1 :=
  ICO.MHPurifiedResponseNorm.purifiedResponse_norm_one _ (response_norm_one tail v hv t) C D

#print axioms response_norm_one
#print axioms purified_response_norm_one
end
end ICO.ProtocolHaarOutput
