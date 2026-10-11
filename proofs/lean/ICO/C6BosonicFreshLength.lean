import ICO.C6BosonicLocalInverse

/-! A fresh inverse can add at most one right record. -/
namespace ICO.C6BosonicFreshLength
open QIT ICO.C6BosonicLocalInverse ICO.C6BosonicLengthMasks ICO.C6BosonicQueryAlgebra
  ICO.C6BosonicHistorySupport ICO.C6BosonicFockRotated ICO.C6CacheSpanProjection
  ICO.C6PolarFock ICO.C6FockQueryMatrix ICO.C6BosonicFreshContraction
  ICO.C6PolarLengths ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem mask_nested (m T : ℕ) :
    rightLengthMask (α:=A) (m+1) T*rightLengthMask m T=rightLengthMask m T := by
  rw [rightLengthMask_diagonal,rightLengthMask_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  by_cases hi : i.1.1.val.2.val≤m
  · have hh : i.1.1.val.2.val≤m+1 := Nat.le_trans hi (Nat.le_succ m)
    simp [hi,hh]
  · simp [hi]

theorem right_mask_step (m : ℕ) {t T : ℕ} (h : t+1≤T) :
    rightLengthMask (m+1) T*polarRightOnFock (α:=A) h*rightLengthMask m T=
      polarRightOnFock h*rightLengthMask m T := by
  rw [rightLengthMask_diagonal,rightLengthMask_diagonal]
  ext o i
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hi : i.1.1.val.2.val≤m
  · by_cases hg : polarRightOnFock h o i=0
    · simp [hg]
    · have hl := (right_lengths h o i hg).2
      have ho : o.1.1.val.2.val≤m+1 := by omega
      simp [hi,ho]
  · simp [hi]

theorem fresh_mask_step (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    (m : ℕ) {t T : ℕ} (h : t+1≤T) :
    rightLengthMask (m+1) T*
      freshInverse (polarLeftOnFock h) (polarRightOnFock h) (rotatedFresh U S T)*rightLengthMask m T=
      freshInverse (polarLeftOnFock h) (polarRightOnFock h) (rotatedFresh U S T)*rightLengthMask m T := by
  let R := rightLengthMask (α:=A) m T
  let R' := rightLengthMask (α:=A) (m+1) T
  let F := polarLeftOnFock (α:=A) h
  let G := polarRightOnFock (α:=A) h
  let Q := rotatedFresh U S T
  have hf : R*F=F*R := left_mask m h
  have hfa : R*F.conjTranspose=F.conjTranspose*R := left_adjoint_mask m h
  have hfa' : R'*F.conjTranspose=F.conjTranspose*R' := left_adjoint_mask (m+1) h
  have hnest : R'*R=R := mask_nested m T
  have hG : R'*G*R=G*R := right_mask_step m h
  have hE : R*(1-F*F.conjTranspose)=(1-F*F.conjTranspose)*R := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
    rw [←Matrix.mul_assoc R F,hf,Matrix.mul_assoc F R,hfa]
    simp only [Matrix.mul_assoc]
  have hQ : R'*Q=Q*R' := by
    rw [show Q=1-queryMatrix (spanProjection U S) T from rotatedFresh_complement U S T]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
    have hh : R'*queryMatrix (spanProjection U S) T=queryMatrix (spanProjection U S) T*R' :=
      mask_family (queryFamily (spanProjection U S)) (m+1) T
    rw [hh]
  have h1 : R'*F.conjTranspose*R=F.conjTranspose*R := by
    rw [hfa',Matrix.mul_assoc,hnest]
  have h2 : R'*(Q*G*(1-F*F.conjTranspose))*R=Q*G*(1-F*F.conjTranspose)*R := by
    calc
      _ = Q*(R'*G*R)*(1-F*F.conjTranspose) := by
        simp only [Matrix.mul_assoc]
        rw [←Matrix.mul_assoc R' Q,hQ]
        rw [←hE]
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hG]
        simp only [Matrix.mul_assoc]
        rw [hE]
  change R'*(F.conjTranspose+Q*G*(1-F*F.conjTranspose))*R=
    (F.conjTranspose+Q*G*(1-F*F.conjTranspose))*R
  simp only [Matrix.mul_add,Matrix.add_mul]
  rw [h1,h2]

#print axioms right_mask_step
#print axioms fresh_mask_step
end
end ICO.C6BosonicFreshLength
