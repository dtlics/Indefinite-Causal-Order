import ICO.C6FockNumberContinuation

/-! Creating in a selected fresh coordinate mode records its exact occupation. -/
namespace ICO.C6NumberSelection
open Matrix QIT ICO.C6FockNumber ICO.C6FockNumberContinuation ICO.C6PolarFock
  ICO.C6BosonicCacheSupport ICO.C6BosonicFockSupport ICO.C6BosonicSupport
  ICO.MHBoundedRecording ICO.MHFockKnownOperation
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def querySelected (S:Finset A) (T:ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  Matrix.diagonal (fun i=>if i.2.1∈S then 1 else 0)

theorem selected_birth_shift (S:Finset A) (k:ℕ) {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rightNumber S (k+1) T*(querySelected S T*polarRightOnFock h)*rightNumber S k T=
      (querySelected S T*polarRightOnFock h)*rightNumber S k T := by
  ext o i
  simp only [rightNumber,rightDiagonal,querySelected,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hi:labelNumber S i.1.2=k
  · by_cases hq:o.2.1∈S
    · by_cases hg:polarRightOnFock h o i=0
      · simp [hg]
      · have hn:=right_number_step S h ht o i hg
        simp only [hi,if_pos hq] at hn
        simp [hi,hq,hn]
    · simp [hq]
  · simp [hi]

theorem selected_birth_bit (S:Finset A) {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (v:InputCutoff (α:=A) T→ℂ) (hv:rightNumber S 0 T*ᵥv=v) :
    rightNumber S 1 T*ᵥ(querySelected S T*ᵥ(polarRightOnFock h*ᵥv))=
      querySelected S T*ᵥ(polarRightOnFock h*ᵥv) := by
  calc
    _ = (rightNumber S 1 T*(querySelected S T*polarRightOnFock h)*rightNumber S 0 T)*ᵥv := by
      simp only [←Matrix.mulVec_mulVec,hv]
    _ = _ := by rw [selected_birth_shift S 0 h ht]; simp only [←Matrix.mulVec_mulVec,hv]

theorem rightNumber_supported (S:Finset A) (k T:ℕ) (v:InputCutoff (α:=A) T→ℂ)
    (hv:rightNumber S k T*ᵥv=v) (i:InputCutoff (α:=A) T) (hi:v i≠0) :
    labelNumber S i.1.2=k := by
  have he:=congrFun hv i
  simp only [rightNumber,rightDiagonal,Matrix.mulVec_diagonal] at he
  by_contra hn
  rw [if_neg hn,zero_mul] at he
  exact hi he.symm

#print axioms selected_birth_bit
end
end ICO.C6NumberSelection
