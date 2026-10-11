import ICO.C6RawInverseError
import ICO.C6FlagSlices

namespace ICO.C6RawStageError
open Matrix QIT ICO.C6RawFlags ICO.C6RawFlagContraction ICO.C6RawInverseError
  ICO.C6FlagStack ICO.C6BirthFlags ICO.C6RetainedHistory ICO.C6HistoryControlled
  ICO.C6PairedTrajectory ICO.C6PolarFock ICO.C6FlagSlices
  ICO.MHBoundedRecording ICO.MHRectangularAction ICO.RecordingPurifiedProtocol
  ICO.MHFockKnownOperation
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem slice_controlled {T i:ℕ} (D:History (A×Bool) i→CMatrix (InputCutoff (α:=A) T))
    (η:History (A×Bool) i)
    (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ i)) :
    slice (A:=A) (μ:=μ) (T:=T) (i:=i) η (rectAct (controlled (M:=μ i) D) v)=
      rectAct (Matrix.kronecker (D η) (1:CMatrix (Bool×μ i))) (slice (i:=i) η v) := by
  ext ⟨o,b,m⟩
  change (∑x,controlled (M:=μ i) D (o,(b,(η,m))) x*v x)=
    (Matrix.kronecker (D η) (1:CMatrix (Bool×μ i))*ᵥ
      (fun p=>v (p.1,(p.2.1,(η,p.2.2))))) (o,(b,m))
  rw [tensor_identity_entry,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [controlled_entry,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]

theorem controlled_fix_of_slices {T i:ℕ}
    (D:History (A×Bool) i→CMatrix (InputCutoff (α:=A) T))
    (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ i))
    (hv:∀η,rectAct (Matrix.kronecker (D η) (1:CMatrix (Bool×μ i))) (slice (i:=i) η v)=slice (i:=i) η v) :
    rectAct (controlled (M:=μ i) D) v=v := by
  ext ⟨o,b,η,m⟩
  have hh:=hv η
  rw [←slice_controlled] at hh
  exact congrArg (fun w:EuclideanSpace ℂ (InputCutoff (α:=A) T×(Bool×μ i))=>w (o,(b,m))) hh

theorem stage_difference_energy {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (i m:ℕ) (hm:m<Fintype.card A)
    (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ i))
    (hv:rectAct (controlled (M:=μ i) (comparisonMask H i m T)) v=v) :
    (∑b:Bool,‖rectAct (flagStage h H K i b-rawFlagStage h H K i b) v‖^2)≤
      ((m:ℝ)/Fintype.card A)^2*‖v‖^2 := by
  let L:=publicStage T K i*Matrix.kronecker (polarLeftOnFock h)
    (1:CMatrix (Middle (A:=A) μ i))*middleStage T H i
  let D:=fun b=>controlled (M:=μ i) (fun η=>flagInverse h H i η b)-
    controlled (M:=μ i) (fun η=>rawFlagInverse h H i η b)
  have hL:‖L‖≤1 := by
    apply ICO.C6FockPairs.mul_norm_le_one
    · apply ICO.C6FockPairs.mul_norm_le_one
      · exact publicStage_norm T K hK i
      · exact (tensor_identity_norm_le _).trans (polarLeftOnFock_norm_le h ht)
    · exact middleStage_norm T H i
  have hd:=stack_energy (fun b=>D b*controlled (M:=μ i) (comparisonMask H i m T))
    ((m:ℝ)/Fintype.card A) (by positivity) (controlled_difference_stack h ht H i m hm (μ i)) v
  simp only [rectAct_mul,hv] at hd
  calc
    _ ≤ ∑b:Bool,‖rectAct (D b) v‖^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have he:flagStage h H K i b-rawFlagStage h H K i b=L*D b := by
        simp only [flagStage,rawFlagStage,L,D,Matrix.mul_sub]
      rw [he,rectAct_mul]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (rectAct_norm_le _ _).trans
        ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))
    _ ≤ _ := hd

#print axioms stage_difference_energy
end
end ICO.C6RawStageError

