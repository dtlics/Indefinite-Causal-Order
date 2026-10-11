import ICO.C6BosonicCacheSupport
import ICO.C6PolarFockEntries
import ICO.C6BosonicRightSupport
import ICO.MHFockKnownOperation

/-! Actual permanent right-label occupation sectors on the common Fock space. -/
namespace ICO.C6FockNumber
open Matrix QIT ICO.C6BosonicCacheSupport ICO.C6BosonicSupport ICO.C6BosonicRightSupport
  ICO.C6BosonicRight ICO.C6BosonicPolar ICO.C6PolarReindex ICO.C6PolarFockEntries
  ICO.C6PolarFock ICO.C6BosonicFockSupport ICO.MHProfileTranspose ICO.MHFockSwap
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockOracle ICO.RecordingCopyIdentity
  ICO.MHFockKnownOperation ICO.MHFockProjection
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def rightNumber (S:Finset A) (k T:ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  rightDiagonal (fun _ p=>if labelNumber S p=k then 1 else 0) T

theorem rightNumber_adjoint (S:Finset A) (k T:ℕ) :
    (rightNumber S k T)ᴴ=rightNumber S k T := by
  ext i j
  by_cases h:i=j
  · subst j; simp [rightNumber,rightDiagonal,Matrix.conjTranspose_apply]
  · simp [rightNumber,rightDiagonal,Matrix.conjTranspose_apply,h,Ne.symm h]

theorem left_preserves_number (S:Finset A) (k:ℕ) {t T:ℕ} (h:t+1≤T) :
    rightNumber S k T*polarLeftOnFock h=polarLeftOnFock h*rightNumber S k T :=
  fock_rightDiagonal _ h

theorem retrieval_preserves_number (S:Finset A) (k:ℕ) {t T:ℕ} (h:t+1≤T) :
    rightNumber S k T*(polarLeftOnFock h)ᴴ=(polarLeftOnFock h)ᴴ*rightNumber S k T := by
  have he:=congrArg Matrix.conjTranspose (left_preserves_number S k h)
  simpa only [Matrix.conjTranspose_mul,rightNumber_adjoint] using he.symm

theorem left_image_number_step (S:Finset A) {n:ℕ} (hn:n<Fintype.card A)
    (o:ICO.C6BosonicPolar.Sector (A:=A) (n+1)) (i:ICO.C6BosonicPolar.Sector (A:=A) n)
    (he:leftPolar n o i≠0) :
    labelNumber S (profileTranspose (n+1) o.2)=
      labelNumber S (profileTranspose n i.2)+(if o.1∈S then 1 else 0) := by
  have hh:=congrFun (congrFun (rightPolar_number S hn
    (labelNumber S (profileTranspose n i.2))) (sectorTranspose (n+1) o)) (sectorTranspose n i)
  have hc:rightPolar n (sectorTranspose (n+1) o) (sectorTranspose n i)=leftPolar n o i := by
    rw [rightPolar_transpose]
    change leftPolar n (o.1,profileTranspose _ (profileTranspose _ o.2))
      (i.1,profileTranspose _ (profileTranspose _ i.2))=_
    rw [profileTranspose_involutive,profileTranspose_involutive]
  simp only [rightOutputNumber,targetNumberProjection,Matrix.diagonal_mul,Matrix.mul_diagonal,hc] at hh
  change (if labelNumber S (profileTranspose (n+1) o.2)=
      labelNumber S (profileTranspose n i.2)+(if o.1∈S then 1 else 0) then (1:ℂ) else 0)*
      leftPolar n o i=leftPolar n o i*(if labelNumber S (profileTranspose n i.2)=
      labelNumber S (profileTranspose n i.2) then 1 else 0) at hh
  by_contra hz
  simp only [if_neg hz,ite_true,zero_mul,mul_one] at hh
  exact he hh.symm

theorem right_number_step (S:Finset A) {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (o i:InputCutoff (α:=A) T) (hG:polarRightOnFock h o i≠0) :
    labelNumber S o.1.2=labelNumber S i.1.2+(if o.2.1∈S then 1 else 0) := by
  have he:polarLeftOnFock h (recordSwap o) (recordSwap i)≠0 := by
    rw [←right_swap_entry h]
    simpa only [recordSwap_involutive] using hG
  obtain ⟨j,hj,hji⟩:=mul_entry_nonzero _ _ _ _ he
  obtain ⟨k,hok,hkj⟩:=mul_entry_nonzero _ _ _ _ hj
  have ho:recordSwap o=outputEmbed h k:=basisEmbedding_support _ _ _ hok
  have hi:recordSwap i=inputEmbed (Nat.le_trans (Nat.le_succ t) h) j := by
    apply basisEmbedding_support
    intro hz
    apply hji
    simp only [Matrix.conjTranspose_apply,hz,star_zero]
  have hb:k.1=j.1 := by
    by_contra hn
    exact hkj (by simp [boundedPolar,Matrix.blockDiagonal'_apply,hn])
  have ho':o=recordSwap (outputEmbed h k) := by
    simpa only [recordSwap_involutive] using congrArg recordSwap ho
  have hi':i=recordSwap (inputEmbed (Nat.le_trans (Nat.le_succ t) h) j) := by
    simpa only [recordSwap_involutive] using congrArg recordSwap hi
  rw [ho',hi']
  rcases k with ⟨b,o'⟩
  rcases j with ⟨b',i'⟩
  dsimp only at hb
  subst b'
  have hn:b.1.val.1.val<Fintype.card A := by have hh:=b.1.property; omega
  have hentry:leftPolar b.1.val.1.val o' i'≠0 := by
    simpa only [boundedPolar,Matrix.blockDiagonal'_apply_eq] using hkj
  exact left_image_number_step S hn o' i' hentry

/-- Every later fresh birth outside S preserves the already recorded S-count. -/
theorem fresh_birth_preserves_number (S:Finset A) (k:ℕ) {t T:ℕ}
    (h:t+1≤T) (ht:t<Fintype.card A) :
    rightNumber S k T*(queryFresh S T*polarRightOnFock h)=
      (queryFresh S T*polarRightOnFock h)*rightNumber S k T := by
  ext o i
  simp only [rightNumber,rightDiagonal,queryFresh,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hq:o.2.1∈S
  · simp [hq]
  · by_cases hg:polarRightOnFock h o i=0
    · simp [hg]
    · have hn:=right_number_step S h ht o i hg
      simp only [if_neg hq,add_zero] at hn
      simp only [if_pos hq,if_neg hq,one_mul,hn]
      exact mul_comm _ _

#print axioms right_number_step
#print axioms fresh_birth_preserves_number
end
end ICO.C6FockNumber
