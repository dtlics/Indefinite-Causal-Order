import ICO.C6PolarFock

/-! The actual polar creators add exactly one record in the appropriate register. -/
namespace ICO.C6PolarLengths
open QIT ICO.C6PolarFock ICO.MHBoundedRecording ICO.MHFockSpace
  ICO.MHFockProjection ICO.MHFockSwap ICO.MHFockOracle ICO.RecordingCopyIdentity
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
set_option Elab.async false
variable {α:Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem left_lengths {t T:ℕ} (h:t+1≤T) (o i:InputCutoff (α:=α) T)
    (hA:polarLeftOnFock h o i≠0) :
    o.1.1.val.1.val=i.1.1.val.1.val+1 ∧ o.1.1.val.2.val=i.1.1.val.2.val := by
  obtain ⟨j,hj,hji⟩ := mul_entry_nonzero _ _ o i hA
  obtain ⟨k,hok,hkj⟩ := mul_entry_nonzero _ _ o j hj
  have ho := basisEmbedding_support (outputEmbed h) o k hok
  have hi : i=inputEmbed (Nat.le_trans (Nat.le_succ t) h) j := by
    apply basisEmbedding_support
    intro hz
    apply hji
    simp only [Matrix.conjTranspose_apply,hz,star_zero]
  have hblock : k.1=j.1 := by
    by_contra hn
    exact hkj (by simp [boundedPolar,Matrix.blockDiagonal'_apply,hn])
  have hl := congrArg (fun b:Block (α:=α) t => b.1.val.1.val) hblock
  have hr := congrArg (fun b:Block (α:=α) t => b.1.val.2.val) hblock
  rw [ho,hi]
  exact ⟨congrArg (fun n:ℕ => n+1) hl,hr⟩

theorem right_lengths {t T:ℕ} (h:t+1≤T) (o i:InputCutoff (α:=α) T)
    (hA:polarRightOnFock h o i≠0) :
    o.1.1.val.1.val=i.1.1.val.1.val ∧ o.1.1.val.2.val=i.1.1.val.2.val+1 := by
  obtain ⟨j,hj,hji⟩ := mul_entry_nonzero _ _ o i hA
  obtain ⟨k,hok,hkj⟩ := mul_entry_nonzero _ _ o j hj
  have ho := basisEmbedding_support (recordSwapEquiv T) o k hok
  have hi : j=recordSwap i := by
    apply basisEmbedding_support (recordSwapEquiv T)
    simpa only [swapMatrix_selfAdjoint] using hji
  have hs := left_lengths h k j hkj
  rw [hi] at hs
  rw [ho]
  exact ⟨hs.2,hs.1⟩

#print axioms left_lengths
#print axioms right_lengths
end
end ICO.C6PolarLengths
