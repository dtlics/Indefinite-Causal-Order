import ICO.C6AcceptedModes
import ICO.C6ActualFlagErasure
import ICO.C6ActualResidualWeight

namespace ICO.C6ActualAcceptedModes
open Matrix QIT ICO.C6AcceptedModes ICO.C6AcceptedIndices ICO.C6FlagCount
  ICO.C6ActualFlagErasure ICO.C6PermanentFlags ICO.C6FlagPrefixRun ICO.C6FlagSlices
  ICO.C6BirthFlags ICO.C6RetainedHistory ICO.C6HistoryCoordinates ICO.C6HistoryPrefixSteps
  ICO.C6FixedHistoryBasis ICO.C6ResidualModes ICO.C6HistoryConjugation
  ICO.C6ActualResidualWeight ICO.C6RightImageErasure ICO.C6OrthogonalModeBirth
  ICO.C6CacheSpanProjection ICO.C6CacheWeights ICO.MHBoundedRecording
  ICO.C6PairedTrajectory ICO.RecordingPurifiedProtocol
noncomputable section
set_option maxHeartbeats 1300000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem valid_bar {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (κ:History Bool n)
    (hv:Valid v κ) : Valid (fun i=>bar (v i)) κ := by
  intro i hi hh
  have he:=residual_bar_norm v i
  rw [hh,norm_zero] at he
  exact hv i hi (norm_eq_zero.mp he.symm)

def rightVectors (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n) :
    Fin n→EuclideanSpace ℂ A :=fun i=>bar (vectors H n η i)

theorem rightVectors_snoc (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (b:Bool) (j:A) : rightVectors H (n+1) ((j,b),η)=
      Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) (rightVectors H n η)
        (bar (WithLp.toLp 2 (ICO.C6ChoiceMeasurement.queryVector H (b,j)))) := by
  funext i
  cases i using Fin.lastCases with
  | last=>simp only [rightVectors,vectors_snoc,Fin.snoc_last]
  | cast i=>simp only [rightVectors,vectors_snoc,Fin.snoc_castSucc]

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem actual_valid {q t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (η:History (A×Bool) q) (κ:History Bool q)
    (hv:slice η (flagRun h H K z q κ)≠0) : Valid (vectors H q η) κ := by
  obtain ⟨U,labels,hinj,hcol,hP⟩:=actual_history_basis H q η
  intro i hi hh
  have hz:=prefixRun_inactive h H K z η U labels hP q le_rfl κ i hh
    (by simpa only [pastFlag,dif_pos i.isLt] using hi)
  apply hv
  simpa only [prefixRun,prefixHistory_self] using hz

theorem actual_right_modes_orthonormal {q t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (η:History (A×Bool) q) (κ:History Bool q)
    (hv:slice η (flagRun h H K z q κ)≠0) :
    Orthonormal ℂ (modes (rightVectors H q η) κ) :=
  modes_orthonormal _ _ (valid_bar _ _ (actual_valid h H K z η κ hv))

def oldActive (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (hv:Valid (rightVectors H n η) κ) (b:Bool) (j:A) :
    Fin (flagCount n κ)→Active (rightVectors H (n+1) ((j,b),η)) :=
  fun k=>⟨(selected n κ k).castSucc,by
    rw [rightVectors_snoc,residual_snoc_cast]
    exact hv _ (selected_flag n κ k)⟩

theorem oldActive_injective (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (hv:Valid (rightVectors H n η) κ) (b:Bool) (j:A) :
    Function.Injective (oldActive H n η κ hv b j) := by
  intro k l hkl
  exact selected_injective n κ (Fin.castSucc_injective n (congrArg Subtype.val hkl))

theorem oldActive_prior (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (hv:Valid (rightVectors H n η) κ) (b:Bool) (j:A)
    (k:Fin (flagCount n κ)) : (oldActive H n η κ hv b j k).val<Fin.last n :=
  (selected n κ k).isLt

theorem oldActive_modes (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (hv:Valid (rightVectors H n η) κ) (b:Bool) (j:A) :
    (fun k=>C6ResidualModes.mode (rightVectors H (n+1) ((j,b),η))
      (oldActive H n η κ hv b j k))=modes (rightVectors H n η) κ := by
  funext k
  change C6ResidualModes.mode (rightVectors H (n+1) ((j,b),η)) (selected n κ k).castSucc=_
  rw [rightVectors_snoc,mode_snoc_cast]
  rfl

variable {M:Type} [Fintype M] [DecidableEq M]

theorem birth_erasure (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (hv:Valid (rightVectors H n η) κ) (b:Bool) (j:A)
    (X:CMatrix (M×(A×(Fin (flagCount n κ)→A)))) :
    let B:=selectedRaw (flagCount n κ)
      (fun x=>residual (rightVectors H (n+1) ((j,b),η)) (Fin.last n) x)*
        Matrix.kronecker (1:CMatrix A) (directEncoding (modes (rightVectors H n η) κ))
    partialTraceB (Matrix.kronecker (1:CMatrix M) B*X*
      (Matrix.kronecker (1:CMatrix M) B)ᴴ)=
        (((overlapWeight (outcomeBasis H b) (historyProjection (vectors H n η)) j/
          (Fintype.card A:ℝ):ℝ):ℂ)) • partialTraceB X := by
  have hh:=actual_birth_erasure_all H n (flagCount n κ) η b j
    (oldActive H n η κ hv b j) (oldActive_injective H n η κ hv b j)
    (oldActive_prior H n η κ hv b j) X
  have he:(fun k=>C6ResidualModes.mode (fun s=>bar (vectors H (n+1) ((j,b),η) s))
      (oldActive H n η κ hv b j k))=modes (rightVectors H n η) κ :=
    oldActive_modes H n η κ hv b j
  dsimp only at hh
  rw [he] at hh
  exact hh

#print axioms actual_right_modes_orthonormal
#print axioms birth_erasure
end
end ICO.C6ActualAcceptedModes

