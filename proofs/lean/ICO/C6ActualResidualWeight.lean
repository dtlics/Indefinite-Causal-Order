import ICO.C6HistoryConjugation
import ICO.C6RetainedHistory
import ICO.C6HistoryImageErasure

/-! The physical copied outcome history determines exactly the overlap weight
of the reduced cache birth. Right-label conjugation is kept explicit. -/
namespace ICO.C6ActualResidualWeight
open QIT ICO.C6ResidualModes ICO.C6HistoryConjugation ICO.C6CacheHistorySpan
  ICO.C6CacheSpanProjection ICO.C6CacheWeights ICO.C6RetainedHistory
  ICO.C6ChoiceMeasurement ICO.C6HistoryImageErasure ICO.C6RightImageErasure
  ICO.C6OrthogonalModeBirth
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem prior_snoc {s:ℕ} (v:Fin s→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A) :
    prior (Fin.snoc v x) (Fin.last s)=v := by
  funext j
  change Fin.snoc (α:=fun _:Fin (s+1)=>EuclideanSpace ℂ A) v x j.castSucc=v j
  exact Fin.snoc_castSucc _ _ _

theorem next_weight {s:ℕ} (v:Fin s→EuclideanSpace ℂ A)
    (U:Matrix.unitaryGroup A ℂ) (j:A) :
    ‖residual (fun k=>bar (Fin.snoc (α:=fun _:Fin (s+1)=>EuclideanSpace ℂ A) v (column U j) k)) (Fin.last s)‖^2=
      overlapWeight U (historyProjection v) j := by
  rw [right_residual_weight (Fin.snoc (α:=fun _:Fin (s+1)=>EuclideanSpace ℂ A) v (column U j)) (Fin.last s) U j
    (Fin.snoc_last _ _),prior_snoc]
  rfl

def outcomeBasis (H:Matrix.unitaryGroup A ℂ) (b:Bool) : Matrix.unitaryGroup A ℂ :=
  if b then H else 1

theorem actual_column (H:Matrix.unitaryGroup A ℂ) (b:Bool) (j:A) :
    WithLp.toLp 2 (queryVector H (b,j))=column (outcomeBasis H b) j := by
  cases b <;> ext a <;> rfl

theorem actual_next_weight (H:Matrix.unitaryGroup A ℂ) (s:ℕ)
    (η:ICO.RecordingPurifiedProtocol.History (A×Bool) s) (b:Bool) (j:A) :
    ‖residual (fun k=>bar (vectors H (s+1) ((j,b),η) k)) (Fin.last s)‖^2=
      overlapWeight (outcomeBasis H b) (historyProjection (vectors H s η)) j := by
  rw [vectors_snoc,actual_column]
  exact next_weight _ _ _

variable {M:Type} [Fintype M] [DecidableEq M]

/-- Actual selected birth, after the known middle outcome and right-record
erasure, has the cache's overlap weight. The active indices encode any
previous accepted-birth subsequence of this complete private history. -/
theorem actual_birth_erasure (H:Matrix.unitaryGroup A ℂ) (s n:ℕ)
    (η:ICO.RecordingPurifiedProtocol.History (A×Bool) s) (b:Bool) (j:A)
    (hi:residual (fun k=>bar (vectors H (s+1) ((j,b),η) k)) (Fin.last s)≠0)
    (old:Fin n→Active (fun k=>bar (vectors H (s+1) ((j,b),η) k)))
    (hinj:Function.Injective old) (hprior:∀k,(old k).val<Fin.last s)
    (X:CMatrix (M×(A×(Fin n→A)))) :
    let history:=fun k=>bar (vectors H (s+1) ((j,b),η) k)
    let B:=selectedRaw n (fun x=>residual history (Fin.last s) x)*Matrix.kronecker (1:CMatrix A)
      (directEncoding (fun k=>C6ResidualModes.mode history (old k)))
    partialTraceB (Matrix.kronecker (1:CMatrix M) B*X*
      (Matrix.kronecker (1:CMatrix M) B).conjTranspose)=
      (((overlapWeight (outcomeBasis H b) (historyProjection (vectors H s η)) j/
        (Fintype.card A:ℝ):ℝ):ℂ)) • partialTraceB X := by
  let history:=fun k=>bar (vectors H (s+1) ((j,b),η) k)
  let i:Active history:=⟨Fin.last s,hi⟩
  have hfresh:∀k,old k≠i := by
    intro k he
    have hv:=congrArg Subtype.val he
    have hh:=hprior k
    rw [hv] at hh
    exact (lt_irrefl _ hh)
  have he:=accepted_residual_erasure history i old hinj hfresh X
  dsimp only [i,history] at he
  rw [actual_next_weight H s η b j] at he
  exact he

/-- The same exact reduced map for all outcomes, including those whose
fresh residual vanishes. Previous accepted indices are strictly earlier. -/
theorem actual_birth_erasure_all (H:Matrix.unitaryGroup A ℂ) (s n:ℕ)
    (η:ICO.RecordingPurifiedProtocol.History (A×Bool) s) (b:Bool) (j:A)
    (old:Fin n→Active (fun k=>bar (vectors H (s+1) ((j,b),η) k)))
    (hinj:Function.Injective old) (hprior:∀k,(old k).val<Fin.last s)
    (X:CMatrix (M×(A×(Fin n→A)))) :
    let history:=fun k=>bar (vectors H (s+1) ((j,b),η) k)
    let B:=selectedRaw n (fun x=>residual history (Fin.last s) x)*Matrix.kronecker (1:CMatrix A)
      (directEncoding (fun k=>C6ResidualModes.mode history (old k)))
    partialTraceB (Matrix.kronecker (1:CMatrix M) B*X*
      (Matrix.kronecker (1:CMatrix M) B).conjTranspose)=
      (((overlapWeight (outcomeBasis H b) (historyProjection (vectors H s η)) j/
        (Fintype.card A:ℝ):ℝ):ℂ)) • partialTraceB X := by
  by_cases hi:residual (fun k=>bar (vectors H (s+1) ((j,b),η) k)) (Fin.last s)=0
  · have hw:=actual_next_weight H s η b j
    rw [hi,norm_zero,zero_pow (by decide : 2≠0)] at hw
    rw [←hw,zero_div,Complex.ofReal_zero,zero_smul]
    exact inactive_residual_erasure _ _ hi _ X
  · exact actual_birth_erasure H s n η b j hi old hinj hprior X

#print axioms actual_next_weight
#print axioms actual_birth_erasure
#print axioms actual_birth_erasure_all
end
end ICO.C6ActualResidualWeight
