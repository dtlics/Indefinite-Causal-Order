import ICO.C6FlagPrefixRun

namespace ICO.C6PermanentFlags
open Matrix QIT ICO.C6FlagPrefixRun ICO.C6FlagSlices ICO.C6FlagCore ICO.C6NumberStageTransfer
  ICO.C6BirthFlags ICO.C6RetainedHistory ICO.C6HistoryCoordinates ICO.C6HistoryPrefixSteps
  ICO.C6FixedHistoryBasis ICO.C6ResidualModes ICO.C6ResidualCoordinates ICO.C6ResidualSpan
  ICO.C6CacheSpanProjection ICO.C6NumberRotationAlgebra ICO.C6CacheHistorySpan
  ICO.MHBoundedRecording ICO.MHFockKnownOperation ICO.MHRectangularAction
  ICO.RecordingPurifiedProtocol ICO.C6PairedTrajectory
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem prefixRun_numbers {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (η:History (A×Bool) q) (U:Matrix.unitaryGroup A ℂ)
    (labels:Active (vectors H q η)→A) (hinj:Function.Injective labels)
    (hcol:∀i,column U (labels i)=mode (vectors H q η) i)
    (hP:∀n (hn:n≤q),historyProjection (vectors H n (prefixHistory η n hn))=
      spanProjection U (activeIndices (vectors H q η) labels n))
    (hz:∀s:Active (vectors H q η),rectAct
      (Matrix.kronecker (rotatedNumber U {labels s} 0 T) (1:CMatrix (Bool×μ 0)))
      (slice (prefixHistory η 0 (Nat.zero_le q)) z)=slice (prefixHistory η 0 (Nat.zero_le q)) z)
    (n:ℕ) (hn:n≤q) (κ:History Bool n) (s:Active (vectors H q η)) :
    rectAct (Matrix.kronecker (rotatedNumber U {labels s}
      (if pastFlag κ s.val.val then 1 else 0) T) (1:CMatrix (Bool×μ n)))
      (prefixRun h H K z η n hn κ)=prefixRun h H K z η n hn κ := by
  induction n with
  | zero=>simpa only [pastFlag_zero,Bool.false_eq_true,if_false,prefixRun,flagRun] using hz s
  | succ n ih=>
    rcases κ with ⟨f,κ⟩
    let i:Fin q:=⟨n,by omega⟩
    let B:=activeIndices (vectors H q η) labels n
    have hB:historyProjection (prior (vectors H q η) i)=spanProjection U B := by
      rw [←prior_actual H η i]
      exact hP n (by omega)
    rw [prefixRun_core_step h H K z η n hn κ f U B hB]
    cases f with
    | false=>
      rw [pastFlag_succ_false]
      exact action_preserves _ _ _
        (stage_preserves U {labels s} _ T _ _ _
          (core_retrieval h ht (vectors H q η) i U B {labels s} hB _)) _
        (ih (by omega) κ)
    | true=>
      by_cases ha:residual (vectors H q η) i=0
      · rw [core_birth_zero h (vectors H q η) i ha U B hB]
        simp [Matrix.kronecker,rectAct]
      · let a:Active (vectors H q η):=⟨i,ha⟩
        by_cases he:a=s
        · subst s
          have hp:pastFlag κ a.val.val=false:=pastFlag_self κ
          have hh:=ih (by omega) κ
          rw [hp] at hh
          rw [pastFlag_succ]
          simp only [show a.val.val=n from rfl,ite_true]
          exact action_sandwich _ _ _
            (stage_sandwich U {labels a} 0 1 T _ _ _
              (core_birth_new h ht (vectors H q η) a U (labels a) (hcol a) B hB)) _ hh
        · have hai:labels a∉({labels s}:Finset A) := by
            simp only [Finset.mem_singleton]
            exact fun h=>he (hinj h)
          have hsn:s.val.val≠n := by
            intro heq
            apply he
            apply Subtype.ext
            apply Fin.ext
            exact heq.symm
          rw [pastFlag_succ,if_neg hsn]
          exact action_preserves _ _ _
            (stage_preserves U {labels s} _ T _ _ _
              (core_birth_other h ht (vectors H q η) a U (labels a) (hcol a)
                B {labels s} hB hai _)) _ (ih (by omega) κ)

theorem prefixRun_inactive {q t T:ℕ} (h:t+1≤T)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (η:History (A×Bool) q) (U:Matrix.unitaryGroup A ℂ)
    (labels:Active (vectors H q η)→A)
    (hP:∀n (hn:n≤q),historyProjection (vectors H n (prefixHistory η n hn))=
      spanProjection U (activeIndices (vectors H q η) labels n))
    (n:ℕ) (hn:n≤q) (κ:History Bool n) (s:Fin q)
    (hs:residual (vectors H q η) s=0) (hb:pastFlag κ s.val=true) :
    prefixRun h H K z η n hn κ=0 := by
  induction n with
  | zero=>simp [pastFlag_zero] at hb
  | succ n ih=>
    rcases κ with ⟨f,κ⟩
    let i:Fin q:=⟨n,by omega⟩
    let B:=activeIndices (vectors H q η) labels n
    have hB:historyProjection (prior (vectors H q η) i)=spanProjection U B := by
      rw [←prior_actual H η i]
      exact hP n (by omega)
    rw [prefixRun_core_step h H K z η n hn κ f U B hB]
    rw [pastFlag_succ] at hb
    by_cases he:s.val=n
    · have hsi:s=i:=Fin.ext he
      subst s
      simp only [show i.val=n from rfl,ite_true] at hb
      subst f
      rw [core_birth_zero h (vectors H q η) i hs U B hB]
      simp [Matrix.kronecker,rectAct]
    · rw [if_neg he] at hb
      rw [ih (by omega) κ hb,map_zero]


theorem prefixRun_unoccupied {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (η:History (A×Bool) q) (U:Matrix.unitaryGroup A ℂ)
    (labels:Active (vectors H q η)→A)
    (hcol:∀i,column U (labels i)=mode (vectors H q η) i)
    (hP:∀n (hn:n≤q),historyProjection (vectors H n (prefixHistory η n hn))=
      spanProjection U (activeIndices (vectors H q η) labels n))
    (S:Finset A)
    (hz:rectAct (Matrix.kronecker (rotatedNumber U S 0 T) (1:CMatrix (Bool×μ 0)))
      (slice (prefixHistory η 0 (Nat.zero_le q)) z)=slice (prefixHistory η 0 (Nat.zero_le q)) z)
    (n:ℕ) (hn:n≤q) (κ:History Bool n)
    (hS:∀a:Active (vectors H q η),a.val.val<n→labels a∉S) :
    rectAct (Matrix.kronecker (rotatedNumber U S 0 T) (1:CMatrix (Bool×μ n)))
      (prefixRun h H K z η n hn κ)=prefixRun h H K z η n hn κ := by
  induction n with
  | zero=>exact hz
  | succ n ih=>
    rcases κ with ⟨f,κ⟩
    let i:Fin q:=⟨n,by omega⟩
    let B:=activeIndices (vectors H q η) labels n
    have hB:historyProjection (prior (vectors H q η) i)=spanProjection U B := by
      rw [←prior_actual H η i]
      exact hP n (by omega)
    have hh:=ih (by omega) κ (fun a ha=>hS a (by omega))
    rw [prefixRun_core_step h H K z η n hn κ f U B hB]
    cases f with
    | false=>
      exact action_preserves _ _ _
        (stage_preserves U S 0 T _ _ _
          (core_retrieval h ht (vectors H q η) i U B S hB 0)) _ hh
    | true=>
      by_cases ha:residual (vectors H q η) i=0
      · rw [core_birth_zero h (vectors H q η) i ha U B hB]
        simp [Matrix.kronecker,rectAct]
      · let a:Active (vectors H q η):=⟨i,ha⟩
        exact action_preserves _ _ _
          (stage_preserves U S 0 T _ _ _
            (core_birth_other h ht (vectors H q η) a U (labels a) (hcol a)
              B S hB (hS a (by change n<n+1; omega)) 0)) _ hh

#print axioms prefixRun_unoccupied

#print axioms prefixRun_numbers
#print axioms prefixRun_inactive
end
end ICO.C6PermanentFlags

