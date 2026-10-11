import ICO.C6PolarLengths
import ICO.C6FockQueryMatrix
import ICO.C6BosonicHistorySupport
import ICO.C6NumberRotationAlgebra
import ICO.MHRectangularAction

/-! Exact, separate left/right degrees of the actual Fock operators. -/
namespace ICO.C6FockLengthShift
open Matrix QIT ICO.C6PolarFock ICO.C6PolarLengths ICO.MHBoundedRecording
  ICO.MHFockSpace ICO.MHFockProjection ICO.MHFockOracle ICO.MHFockSwap
  ICO.MHFockRotation ICO.MHFockTransport ICO.MHFockKnownOperation
  ICO.C6FockQueryMatrix ICO.C6BosonicHistorySupport ICO.C6BosonicFockRotated
  ICO.C6NumberRotationAlgebra ICO.C6FockNumber ICO.RecordingCopyIdentity
  ICO.MHRectangularAction
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def leftDegree {T:ℕ} (i:InputCutoff (α:=A) T) : ℤ := i.1.1.val.1.val
def rightDegree {T:ℕ} (i:InputCutoff (α:=A) T) : ℤ := i.1.1.val.2.val

def Shift {T:ℕ} (M:CMatrix (InputCutoff (α:=A) T)) (l r:ℤ) : Prop :=
  ∀o i,M o i≠0→leftDegree o=leftDegree i+l ∧ rightDegree o=rightDegree i+r

theorem shift_mul {T:ℕ} (M N:CMatrix (InputCutoff (α:=A) T)) {l r l' r':ℤ}
    (hM:Shift M l r) (hN:Shift N l' r') : Shift (M*N) (l+l') (r+r') := by
  intro o i h
  obtain ⟨j,hm,hn⟩:=mul_entry_nonzero M N o i h
  obtain ⟨hl,hr⟩:=hM o j hm
  obtain ⟨hl',hr'⟩:=hN j i hn
  constructor <;> linarith

theorem shift_adjoint {T:ℕ} (M:CMatrix (InputCutoff (α:=A) T)) {l r:ℤ}
    (hM:Shift M l r) : Shift M.conjTranspose (-l) (-r) := by
  intro o i h
  have hm:M i o≠0:=by intro hz;exact h (by simp [Matrix.conjTranspose_apply,hz])
  obtain ⟨hl,hr⟩:=hM i o hm
  constructor <;> linarith

theorem shift_diagonal {T:ℕ} (d:InputCutoff (α:=A) T→ℂ) : Shift (Matrix.diagonal d) 0 0 := by
  intro o i h
  have he:o=i:=by by_contra hn;exact h (Matrix.diagonal_apply_ne' _ (Ne.symm hn))
  subst i
  exact ⟨by simp,by simp⟩

theorem shift_one (T:ℕ) : Shift (1:CMatrix (InputCutoff (α:=A) T)) 0 0 := by
  convert shift_diagonal (fun _:InputCutoff (α:=A) T=>(1:ℂ)) using 1

theorem shift_sub {T:ℕ} (M N:CMatrix (InputCutoff (α:=A) T)) {l r:ℤ}
    (hM:Shift M l r) (hN:Shift N l r) : Shift (M-N) l r := by
  intro o i h
  by_cases hm:M o i=0
  · have hn:N o i≠0:=by intro hn;exact h (by simp [Matrix.sub_apply,hm,hn])
    exact hN o i hn
  · exact hM o i hm

theorem shift_family (F:∀n r,CMatrix (ICO.MHSectorCovariance.Sector (α:=A) n r)) (T:ℕ) :
    Shift (inputFamily F T) 0 0 := by
  intro o i h
  have he:o.1.1=i.1.1:=by
    by_contra hn
    exact h (inputFamily_other F T o i hn)
  constructor
  · simpa only [leftDegree,add_zero] using congrArg (fun s:Lengths T=>(s.val.1.val:ℤ)) he
  · simpa only [rightDegree,add_zero] using congrArg (fun s:Lengths T=>(s.val.2.val:ℤ)) he

theorem shift_left {t T:ℕ} (h:t+1≤T) : Shift (polarLeftOnFock (α:=A) h) 1 0 := by
  intro o i ho
  obtain ⟨hl,hr⟩:=left_lengths h o i ho
  constructor
  · dsimp [leftDegree]
    exact_mod_cast hl
  · simpa only [rightDegree,add_zero] using congrArg (fun n:ℕ=>(n:ℤ)) hr

theorem shift_left_image {t T:ℕ} (h:t+1≤T) :
    Shift (polarLeftOnFock (α:=A) h*(polarLeftOnFock h)ᴴ) 0 0 := by
  simpa using shift_mul _ _ (shift_left (A:=A) h) (shift_adjoint _ (shift_left (A:=A) h))

theorem raw_left_lengths {t T:ℕ} (h:t+1≤T) (o i:InputCutoff (α:=A) T)
    (hA:symmetricOnFock h o i≠0) :
    o.1.1.val.1.val=i.1.1.val.1.val+1 ∧ o.1.1.val.2.val=i.1.1.val.2.val := by
  obtain ⟨j,hj,hji⟩:=mul_entry_nonzero _ _ o i hA
  obtain ⟨k,hok,hkj⟩:=mul_entry_nonzero _ _ o j hj
  have ho:=basisEmbedding_support (outputEmbed h) o k hok
  have hi:i=inputEmbed (Nat.le_trans (Nat.le_succ t) h) j := by
    apply basisEmbedding_support
    intro hz
    apply hji
    simp only [Matrix.conjTranspose_apply,hz,star_zero]
  have hblock:k.1=j.1 := by
    by_contra hn
    exact hkj (by simp [boundedSymmetricInsertion,Matrix.blockDiagonal'_apply,hn])
  have hl:=congrArg (fun b:Block (α:=A) t=>b.1.val.1.val) hblock
  have hr:=congrArg (fun b:Block (α:=A) t=>b.1.val.2.val) hblock
  rw [ho,hi]
  exact ⟨congrArg (fun n:ℕ=>n+1) hl,hr⟩

theorem raw_right_lengths {t T:ℕ} (h:t+1≤T) (o i:InputCutoff (α:=A) T)
    (hA:symmetricRightOnFock h o i≠0) :
    o.1.1.val.1.val=i.1.1.val.1.val ∧ o.1.1.val.2.val=i.1.1.val.2.val+1 := by
  obtain ⟨j,hj,hji⟩:=mul_entry_nonzero _ _ o i hA
  obtain ⟨k,hok,hkj⟩:=mul_entry_nonzero _ _ o j hj
  have ho:=basisEmbedding_support (recordSwapEquiv T) o k hok
  have hi:j=recordSwap i := by
    apply basisEmbedding_support (recordSwapEquiv T)
    simpa only [swapMatrix_selfAdjoint] using hji
  have hs:=raw_left_lengths h k j hkj
  rw [hi] at hs
  rw [ho]
  exact ⟨hs.2,hs.1⟩

theorem shift_raw_right {t T:ℕ} (h:t+1≤T) : Shift (symmetricRightOnFock (α:=A) h) 0 1 := by
  intro o i ho
  obtain ⟨hl,hr⟩:=raw_right_lengths h o i ho
  constructor
  · simpa only [leftDegree,add_zero] using congrArg (fun n:ℕ=>(n:ℤ)) hl
  · dsimp [rightDegree]
    exact_mod_cast hr

#print axioms shift_raw_right
end
end ICO.C6FockLengthShift
