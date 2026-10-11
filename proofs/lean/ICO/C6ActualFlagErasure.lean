import ICO.C6PermanentFlags
import ICO.C6PartialFlagErasure
import ICO.C6NativeFresh

namespace ICO.C6ActualFlagErasure
open Matrix QIT ICO.C6PermanentFlags ICO.C6PartialFlagErasure
  ICO.C6FlagPrefixRun ICO.C6FlagSlices ICO.C6BirthFlags ICO.C6RetainedHistory
  ICO.C6HistoryCoordinates ICO.C6HistoryPrefixSteps ICO.C6FixedHistoryBasis
  ICO.C6ResidualModes ICO.C6NumberRotationAlgebra ICO.C6CacheHistorySpan
  ICO.C6NativeFresh ICO.C6FlagVacuum ICO.C6PairedTrajectory
  ICO.MHBoundedRecording ICO.MHRectangularAction ICO.RecordingPurifiedProtocol
  ICO.MHDecompressionErasure ICO.MHFockKnownOperation
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem prefixHistory_self {J:Type*} {q:ℕ} (η:History J q) :
    prefixHistory η q le_rfl=η := by
  apply (historyEquiv J q).injective
  rw [prefixHistory_coords]

theorem vacuum_slice (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (T:ℕ)
    (z:A×Public (A:=A) μ 0→ℂ) (η:History (A×Bool) 0) :
    rectAct (Matrix.kronecker (rotatedNumber U S 0 T) (1:CMatrix (Bool×μ 0)))
      (slice η (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)))=
        slice η (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) := by
  rw [←slice_tensor]
  have he:=congrArg (WithLp.toLp 2) (vacuum_rotated_number U S T z)
  change rectAct (Matrix.kronecker (rotatedNumber U S 0 T)
    (1:CMatrix (Public (A:=A) μ 0))) (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z))=
      WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z) at he
  rw [he]

theorem outcome_flag_erasure {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (η:History (A×Bool) q) :
    fockVisible T (WithLp.ofLp (slice η (freshVector h H K z q)))=
      ∑κ:History Bool q,fockVisible T (WithLp.ofLp
        (slice η (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) q κ))) := by
  let z0:=WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)
  letI : Nonempty (History Bool q):=⟨(historyEquiv Bool q).symm (fun _=>false)⟩
  obtain ⟨U,labels,hinj,hcol,hP⟩:=actual_history_basis H q η
  have hc:∀i,column U (labels i)=mode (vectors H q η) i := by
    intro i; ext a; exact hcol i a
  let active:Finset (Fin q):=Finset.univ.filter (fun i=>residual (vectors H q η) i≠0)
  let labelsAll:Fin q→A:=fun i=>if hi:residual (vectors H q η) i≠0 then labels ⟨i,hi⟩
    else Classical.arbitrary A
  let w:History Bool q→InputCutoff (α:=A) T×(Bool×μ q)→ℂ:=fun κ=>
    WithLp.ofLp (slice η (flagRun h H K z0 q κ))
  have hw:∀κ s,s∈active→Matrix.kronecker
      (rotatedNumber U {labelsAll s} (if historyEquiv Bool q κ s then 1 else 0) T)
        (1:CMatrix (Bool×μ q))*ᵥw κ=w κ := by
    intro κ s hs
    have ha:residual (vectors H q η) s≠0:=by simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and] using hs
    have hh:=prefixRun_numbers h ht H K z0 η U labels hinj hc hP
      (fun a=>vacuum_slice U {labels a} T z _) q le_rfl κ ⟨s,ha⟩
    simp only [prefixRun,prefixHistory_self,pastFlag,dif_pos s.isLt] at hh
    simpa only [labelsAll,dif_pos ha,rectAct,Matrix.toEuclideanLin_apply,WithLp.ofLp_toLp,w] using congrArg WithLp.ofLp hh
  have hz:∀κ s,s∉active→historyEquiv Bool q κ s=true→w κ=0 := by
    intro κ s hs hb
    have ha:residual (vectors H q η) s=0 := by
      simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hs
    have hh:=prefixRun_inactive h H K z0 η U labels hP q le_rfl κ s ha
      (by simpa only [pastFlag,dif_pos s.isLt] using hb)
    simpa only [prefixRun,prefixHistory_self,WithLp.ofLp_zero,w] using
      congrArg WithLp.ofLp hh
  have he:=partial_flags_erasure U T active labelsAll (historyEquiv Bool q)
    (historyEquiv Bool q).injective w hw hz
  have hsum:(∑κ,w κ)=WithLp.ofLp (slice η (freshVector h H K z q)) := by
    have hh:=flagRun_sum h H K z0 q
    have hs:=congrArg (fun x=>WithLp.ofLp (slice η x)) hh
    funext p
    simpa only [slice,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply,w,freshVector,z0] using congrFun hs p
  rw [hsum] at he
  exact he

#print axioms outcome_flag_erasure
end
end ICO.C6ActualFlagErasure
