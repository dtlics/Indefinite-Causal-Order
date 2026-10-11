import ICO.C6BosonicRightSupport
import ICO.MHFockRotationErasure

/-! A private branch flag is erasable only after permanent private support
has been established. These lemmas make that final implication exact. -/
namespace ICO.C6PermanentErasure
open Matrix QIT ICO.MHDecompressionErasure
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {H R J:Type*} [Fintype H] [DecidableEq H] [Fintype R] [DecidableEq R]
  [Fintype J] [DecidableEq J]

theorem family_at (tag:R→J) (v:J→H×R→ℂ)
    (hv:∀j i,v j i≠0→tag i.2=j) (x:H) (r:R) :
    (∑j,v j (x,r))=v (tag r) (x,r) := by
  apply Finset.sum_eq_single (tag r)
  · intro j hj hne
    by_contra hz
    exact hne (hv j (x,r) hz).symm
  · simp

/-- Permanent occupations in the final private record kill every off-diagonal
birth-flag block, even when the images are entangled with the learner. -/
theorem coherent_family_erasure (tag:R→J) (v:J→H×R→ℂ)
    (hv:∀j i,v j i≠0→tag i.2=j) :
    partialTraceB (rankOneMatrix (∑j,v j))=
      ∑j,partialTraceB (rankOneMatrix (v j)) := by
  ext x y
  simp only [Matrix.sum_apply,partialTraceB,rankOneMatrix_apply,Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [family_at tag v hv]
  symm
  apply Finset.sum_eq_single (tag r)
  · intro j hj hne
    have hz : v j (x,r)=0 := by
      by_contra h
      exact hne (hv j (x,r) h).symm
    simp [hz]
  · simp

/-- An actual operator that preserves a private flag sector preserves it for
arbitrary amplitudes and entanglement. This is iterated before erasing flags. -/
theorem sector_preserved {K S:Type*} [Fintype K] [DecidableEq K]
    [Fintype S] [DecidableEq S]
    (tagIn:R→J) (tagOut:S→J) (M:Matrix (K×S) (H×R) ℂ)
    (hM:∀o i,M o i≠0→tagOut o.2=tagIn i.2)
    (j:J) (v:H×R→ℂ) (hv:∀i,v i≠0→tagIn i.2=j) :
    ∀o,(M*ᵥv) o≠0→tagOut o.2=j := by
  intro o ho
  obtain ⟨i,_,hi⟩:=Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hm,hv'⟩:=mul_ne_zero_iff.mp hi
  exact (hM o i hm).trans (hv i hv')

#print axioms coherent_family_erasure
#print axioms sector_preserved
end
end ICO.C6PermanentErasure
