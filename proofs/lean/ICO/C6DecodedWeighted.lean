import ICO.C6DecodedStageErasure
import ICO.C6CacheVisibleOutput

/-! Exact erasure of the private image register in every literal branch.
Both the measurement outcome and retrieval/birth histories remain retained. -/
namespace ICO.C6DecodedWeighted
open Matrix QIT ICO.C6DecodedHistory ICO.C6DecodedStageErasure
  ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache ICO.C6GradedTransport
  ICO.C6WeightedHistory ICO.C6WeightedHistorySupport ICO.C6RawFlagSlices
  ICO.RecordingPurifiedProtocol ICO.C6FlagCount
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem rankOne_conjugate {a b:Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (D:Matrix b a ℂ) (v:a→ℂ) :
    rankOneMatrix (D*ᵥv)=conjugate D (rankOneMatrix v) := by
  rw [conjugate_apply,rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]

theorem run_erasure (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:ImageCache (A:=A) 0 (Bool×μ 0)→ℂ)
    (n:ℕ) (hn:n≤Q) (η:History (A×Bool) n) (κ:History Bool n) :
    conjugate (embed Q (historyGrade Q n hn κ))
      (partialTraceB (rankOneMatrix (ICO.C6DecodedHistory.run H K z n η κ)))=
      weightedRun Q hpos hQ H (fun i=>smallKnown (K i))
        (partialTraceB (rankOneMatrix z)) n η κ := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    have hp:n≤Q:=by omega
    have hi:n<Q:=by omega
    rcases η with ⟨⟨j,b⟩,η⟩
    rcases κ with ⟨f,κ⟩
    have he:=stage_erasure Q hpos hQ H K n hi η κ j b f
      (rankOneMatrix (ICO.C6DecodedHistory.run H K z n η κ))
    have hi':=congrArg (branches Q hpos hQ H (fun i=>smallKnown (K i))
      (weight H) n η κ (j,b) f) (ih hp η κ)
    have hf:=he.trans hi'
    have hv:=congrArg (fun X=>conjugate (embed Q (historyGrade Q (n+1) hn (f,κ)))
      (partialTraceB X)) (rankOne_conjugate (stage H K n η κ j b f)
        (ICO.C6DecodedHistory.run H K z n η κ))
    exact hv.trans hf

theorem branch_visible (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:ImageCache (A:=A) 0 (Bool×μ 0)→ℂ)
    (n:ℕ) (hn:n≤Q) (η:History (A×Bool) n) (κ:History Bool n) :
    (ICO.C6CacheVisibleOutput.output Q).map
      (weightedRun Q hpos hQ H (fun i=>smallKnown (K i))
        (partialTraceB (rankOneMatrix z)) n η κ)=
      ((ICO.C6CacheVisible.sectorVisible (flagCount n κ)).map
        (partialTraceB (rankOneMatrix (ICO.C6DecodedHistory.run H K z n η κ)))).submatrix
          (Equiv.prodAssoc A Bool (μ n)) (Equiv.prodAssoc A Bool (μ n)) := by
  rw [←run_erasure Q hpos hQ H K z n hn η κ,
    ICO.C6CacheVisibleOutput.output_apply,visible_included]
  rfl

theorem visible_erasure (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:ImageCache (A:=A) 0 (Bool×μ 0)→ℂ) (n:ℕ) (hn:n≤Q) :
    (ICO.C6CacheVisibleOutput.output Q).map
      (ICO.C6ClassicalHistoryRun.erase (H:=fun i=>Graded (A:=A) Q (Bool×μ i)) n
        (weightedRun Q hpos hQ H (fun i=>smallKnown (K i))
          (partialTraceB (rankOneMatrix z)) n))=
      ∑η:History (A×Bool) n,∑κ:History Bool n,
        ((ICO.C6CacheVisible.sectorVisible (flagCount n κ)).map
          (partialTraceB (rankOneMatrix (ICO.C6DecodedHistory.run H K z n η κ)))).submatrix
            (Equiv.prodAssoc A Bool (μ n)) (Equiv.prodAssoc A Bool (μ n)) := by
  simp only [ICO.C6ClassicalHistoryRun.erase,map_sum]
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro κ _
  exact branch_visible Q hpos hQ H K z n hn η κ

#print axioms run_erasure
#print axioms branch_visible
#print axioms visible_erasure
end
end ICO.C6DecodedWeighted
