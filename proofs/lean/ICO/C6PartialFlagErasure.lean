import ICO.C6RotatedFlagErasure

/-! Permanent flags on active residual modes suffice; branches with an
inactive birth bit vanish. No artificial occupation of an inactive mode is assumed. -/
namespace ICO.C6PartialFlagErasure
open Matrix QIT ICO.C6RotatedNumberContinuation ICO.C6NumberRotationAlgebra
  ICO.C6FockNumber ICO.C6FockFlagErasure ICO.C6BosonicCacheSupport ICO.C6BosonicSupport
  ICO.MHFockRotationErasure ICO.MHFockRotation ICO.MHSectorCovariance
  ICO.MHFockKnownOperation ICO.MHBoundedRecording ICO.MHDecompressionErasure
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 800000
set_option Elab.async false
variable {A M I J:Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Nonempty J]

theorem partial_flags_erasure (U:Matrix.unitaryGroup A ℂ) (T:ℕ)
    (active:Finset I) (labels:I→A) (code:J→I→Bool) (hinj:Function.Injective code)
    (v:J→InputCutoff (α:=A) T×M→ℂ)
    (hv:∀j s,s∈active→Matrix.kronecker
      (rotatedNumber U {labels s} (if code j s then 1 else 0) T) (1:CMatrix M)*ᵥv j=v j)
    (hz:∀j s,s∉active→code j s=true→v j=0) :
    fockVisible T (∑j,v j)=∑j,fockVisible T (v j) := by
  let R:CMatrix (InputCutoff (α:=A) T×M):=
    Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)
  let w:J→InputCutoff (α:=A) T×M→ℂ:=fun j=>Rᴴ*ᵥv j
  have hRR:R*Rᴴ=1:=(tensorUnitary (fockQ U 1 T) 1).property.2
  have hRi:Rᴴ*R=1:=(tensorUnitary (fockQ U 1 T) 1).property.1
  have hw:∀j,R*ᵥw j=v j := by
    intro j
    simp only [w,Matrix.mulVec_mulVec,hRR,Matrix.one_mulVec]
  have hf:∀j,fockVisible T (w j)=fockVisible T (v j) := by
    intro j
    rw [←hw j]
    exact (rotation_visible U 1 T (w j)).symm
  have hfix:∀j s,s∈active→Matrix.kronecker
      (rightNumber {labels s} (if code j s then 1 else 0) T) (1:CMatrix M)*ᵥw j=w j := by
    intro j s hs
    have he:=congrArg (fun x=>Rᴴ*ᵥx) (hv j s hs)
    rw [rotated_number_tensor] at he
    change Rᴴ*ᵥ((R*Matrix.kronecker (rightNumber {labels s} (if code j s then 1 else 0) T)
      (1:CMatrix M)*Rᴴ)*ᵥv j)=Rᴴ*ᵥv j at he
    simp only [Matrix.mulVec_mulVec] at he
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,hRi,Matrix.one_mul] at he
    simpa only [w,Matrix.mulVec_mulVec] using he
  have hnumber:∀j x,w j x≠0→∀s,s∈active→
      labelNumber {labels s} (records x.1).2.2=if code j s then 1 else 0 := by
    intro j x hx s hs
    have hd:Matrix.kronecker (rightNumber {labels s} (if code j s then 1 else 0) T)
        (1:CMatrix M)=Matrix.diagonal (fun y:InputCutoff (α:=A) T×M=>
          if labelNumber {labels s} y.1.1.2=(if code j s then 1 else 0) then 1 else 0) := by
      rw [rightNumber,rightDiagonal]
      change Matrix.kronecker (Matrix.diagonal _) (Matrix.diagonal (fun _:M=>(1:ℂ)))=_
      rw [Matrix.kronecker,Matrix.diagonal_kronecker_diagonal]
      simp only [mul_one]
    have he:=congrFun (hfix j s hs) x
    rw [hd,Matrix.mulVec_diagonal] at he
    by_contra hn
    change ¬labelNumber {labels s} x.1.1.2=(if code j s then 1 else 0) at hn
    rw [if_neg hn,zero_mul] at he
    exact hx he.symm
  let bits:Records (α:=A) T→I→Bool:=fun R s=>
    if s∈active then decide (labelNumber {labels s} R.2.2=1) else false
  have hbits:∀j x,w j x≠0→bits (records x.1)=code j := by
    intro j x hx
    funext s
    by_cases hs:s∈active
    · simp only [bits,if_pos hs,hnumber j x hx s hs]
      cases code j s <;> simp
    · simp only [bits,if_neg hs]
      by_cases hb:code j s=true
      · have he:w j=0 := by simp only [w,hz j s hs hb,Matrix.mulVec_zero]
        exact False.elim (hx (by rw [he]; rfl))
      · exact (Bool.eq_false_iff.mpr hb).symm
  have he:=coherent_fock_erasure T (fun R=>Function.invFun code (bits R)) w (by
    intro j x hx
    change Function.invFun code (bits (records x.1))=j
    rw [hbits j x hx]
    exact Function.leftInverse_invFun hinj j)
  have hsum:R*ᵥ(∑j,w j)=∑j,v j := by
    rw [Matrix.mulVec_sum]
    simp only [hw]
  calc
    _ = fockVisible T (R*ᵥ(∑j,w j)) := by rw [hsum]
    _ = fockVisible T (∑j,w j) := rotation_visible U 1 T _
    _ = ∑j,fockVisible T (w j) := he
    _ = _ := by simp only [hf]

#print axioms partial_flags_erasure
end
end ICO.C6PartialFlagErasure
