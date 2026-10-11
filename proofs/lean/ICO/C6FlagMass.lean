import ICO.C6HistoryVisible

namespace ICO.C6FlagMass
open Matrix QIT ICO.C6HistoryVisible ICO.C6BirthFlags ICO.C6NativeFresh
  ICO.C6PairedTrajectory ICO.MHBoundedRecording ICO.MHFockRotationErasure
  ICO.MHDecompressionErasure ICO.RecordingPurifiedProtocol
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 900000
set_option Elab.async false

theorem pure_mass {X:Type*} [Fintype X] [DecidableEq X] (v:X→ℂ) :
    (rankOneMatrix v).trace.re=‖WithLp.toLp 2 v‖^2 := by
  rw [rankOneMatrix_trace,EuclideanSpace.norm_sq_eq]
  simp [dotProduct,Complex.sq_norm,Complex.normSq_apply]

variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem visible_mass {T n:ℕ} (v:InputCutoff (α:=A) T×Public (A:=A) μ n→ℂ) :
    (ICO.C6HistoryVisible.visible v).trace.re=‖WithLp.toLp 2 v‖^2 := by
  classical
  unfold ICO.C6HistoryVisible.visible
  rw [(erasePrivate (A:=A) (μ:=μ) n).tracePreserving,fockVisible,partialTraceB_trace,pure_mass]
  have he:‖WithLp.toLp 2 (v ∘ (ICO.MHFockKnownOperation.queryMemoryFirst T (Public (A:=A) μ n)).symm)‖=
      ‖WithLp.toLp 2 v‖ :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (ICO.MHFockKnownOperation.queryMemoryFirst T (Public (A:=A) μ n))).norm_map _
  rw [he]

theorem flagRun_mass {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) :
    (∑κ:History Bool q,‖flagRun h H K
      (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) q κ‖^2)=
        ‖freshVector h H K z q‖^2 := by
  have he:=congrArg (fun X:CMatrix ((A×Bool)×μ q)=>X.trace.re)
    (visible_fresh_flags h ht H K z)
  simp only [Matrix.trace_sum,Complex.re_sum,visible_mass,WithLp.toLp_ofLp] at he
  exact he.symm

theorem flagRun_mass_le_one {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) :
    (∑κ:History Bool q,‖flagRun h H K
      (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) q κ‖^2)≤1 := by
  rw [flagRun_mass h ht H K z]
  have hh:=freshVector_norm h ht H K hK z hz q
  nlinarith [norm_nonneg (freshVector h H K z q)]

#print axioms flagRun_mass_le_one
end
end ICO.C6FlagMass
