import ICO.C6BosonicBlocks

/-! The private outcome and public-operation blocks are literal query maps. -/
namespace ICO.C6BosonicStageBlocks
open QIT ICO.C6BosonicBlocks ICO.C6BosonicReencoding ICO.C6FockQueryMatrix
  ICO.C6RetainedHistory ICO.C6PairedTrajectory ICO.C6FockChoiceMeasurement
  ICO.C6FockPairs ICO.C6ChoiceMeasurement ICO.C6SharedStages ICO.RecordingPublicStep
  ICO.RecordingPublicHistory ICO.LudersUnitaryStages ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2300000
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem query_zero (T:ℕ) : queryMatrix (0:CMatrix A) T=0 := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  by_cases hs:s=s'
  · subst s'; rw [queryMatrix_entry_same]; simp
  · rw [queryMatrix_entry_other _ T _ _ hs]; rfl

theorem middle_block (T:ℕ) (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (o:Middle (A:=A) μ i) (j:Public (A:=A) μ i) :
    block (middleStage T H i) o j=
      if o.1=o.2.1.2 ∧ j.1=o.2.1.2 ∧ o.2.2=j.2 then
        queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (o.2.1.2,o.2.1.1)))) T else 0 := by
  rw [middleStage,known_block]
  have he : (fun a x=>middleQuery H (a,o) (x,j))=
      if o.1=o.2.1.2 ∧ j.1=o.2.1.2 ∧ o.2.2=j.2 then
        rankOne (WithLp.toLp 2 (queryVector H (o.2.1.2,o.2.1.1))) else 0 := by
    ext a x
    simp only [middleQuery,Matrix.submatrix_apply,regroup,Equiv.symm_mk,Equiv.coe_fn_mk]
    rw [middle_entry]
    change (if o.1=o.2.1.2 ∧ j.1=o.2.1.2 ∧ o.2.2=j.2 then
      queryVector H (o.2.1.2,o.2.1.1) a*star (queryVector H (o.2.1.2,o.2.1.1) x) else 0)=_
    split_ifs <;> rfl
  rw [he]
  split_ifs
  · rfl
  · exact query_zero T

theorem public_block (T:ℕ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (o:Public (A:=A) μ (i+1)) (j:Middle (A:=A) μ i) :
    block (publicStage T K i) o j=
      if o.2.1=(j.2.1,j.2.2.1) then
        queryMatrix (fun a x=>K i ((a,o.1),o.2.2) ((x,j.1),j.2.2.2)) T else 0 := by
  rw [publicStage,known_block]
  have he : (fun a x=>publicQuery (K i) (a,o) (x,j))=
      if o.2.1=(j.2.1,j.2.2.1) then
        (fun a x=>K i ((a,o.1),o.2.2) ((x,j.1),j.2.2.2)) else 0 := by
    ext a x
    simp only [publicQuery,publicStep,Matrix.submatrix_apply,regroup,Equiv.symm_mk,
      Equiv.coe_fn_mk,regroupInput,historyKnown]
    change (if o.2.1=(j.2.1,j.2.2.1) then K i ((a,o.1),o.2.2) ((x,j.1),j.2.2.2) else 0)=_
    split_ifs <;> rfl
  erw [he]
  split_ifs
  · rfl
  · exact query_zero T

#print axioms middle_block
#print axioms public_block
end
end ICO.C6BosonicStageBlocks
