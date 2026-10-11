import ICO.C6RotatedNumberContinuation
import ICO.C6FockFlagErasure

/-! Final occupation flags may be read in one fixed adapted basis without
altering the accessible marginal. This includes arbitrary entangled memory. -/
namespace ICO.C6RotatedFlagErasure
open Matrix QIT ICO.C6RotatedNumberContinuation ICO.C6NumberRotationAlgebra
  ICO.C6FockNumber ICO.C6FockFlagErasure ICO.C6BosonicCacheSupport ICO.C6BosonicSupport
  ICO.MHFockRotationErasure ICO.MHFockRotation ICO.MHSectorCovariance
  ICO.MHFockKnownOperation ICO.MHBoundedRecording ICO.MHDecompressionErasure
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option Elab.async false
variable {A M I:Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype I] [DecidableEq I]

theorem rotated_flags_erasure (U:Matrix.unitaryGroup A ℂ) (T:ℕ) (labels:I→A)
    (v:(I→Bool)→InputCutoff (α:=A) T×M→ℂ)
    (hv:∀b s,Matrix.kronecker (rotatedNumber U {labels s} (if b s then 1 else 0) T)
      (1:CMatrix M)*ᵥv b=v b) :
    fockVisible T (∑b,v b)=∑b,fockVisible T (v b) := by
  let R:CMatrix (InputCutoff (α:=A) T×M):=
    Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)
  let w:(I→Bool)→InputCutoff (α:=A) T×M→ℂ:=fun b=>Rᴴ*ᵥv b
  have hRR:R*Rᴴ=1:=(tensorUnitary (fockQ U 1 T) 1).property.2
  have hRi:Rᴴ*R=1:=(tensorUnitary (fockQ U 1 T) 1).property.1
  have hw:∀b,R*ᵥw b=v b := by
    intro b
    simp only [w,Matrix.mulVec_mulVec,hRR,Matrix.one_mulVec]
  have hf:∀b,fockVisible T (w b)=fockVisible T (v b) := by
    intro b
    rw [←hw b]
    exact (rotation_visible U 1 T (w b)).symm
  have hfix:∀b s,Matrix.kronecker (rightNumber {labels s} (if b s then 1 else 0) T)
      (1:CMatrix M)*ᵥw b=w b := by
    intro b s
    have he:=congrArg (fun x=>Rᴴ*ᵥx) (hv b s)
    rw [rotated_number_tensor] at he
    change Rᴴ*ᵥ((R*Matrix.kronecker (rightNumber {labels s} (if b s then 1 else 0) T)
      (1:CMatrix M)*Rᴴ)*ᵥv b)=Rᴴ*ᵥv b at he
    simp only [Matrix.mulVec_mulVec] at he
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,hRi,Matrix.one_mul] at he
    simpa only [w,Matrix.mulVec_mulVec] using he
  have hwflags:∀b i,w b i≠0→∀s,labelNumber {labels s} (records i.1).2.2=if b s then 1 else 0 := by
    intro b i hi s
    have hd:Matrix.kronecker (rightNumber {labels s} (if b s then 1 else 0) T) (1:CMatrix M)=
        Matrix.diagonal (fun j:InputCutoff (α:=A) T×M=>
          if labelNumber {labels s} j.1.1.2=(if b s then 1 else 0) then 1 else 0) := by
      rw [rightNumber,rightDiagonal]
      change Matrix.kronecker (Matrix.diagonal _) (Matrix.diagonal (fun _:M=>(1:ℂ)))=_
      rw [Matrix.kronecker,Matrix.diagonal_kronecker_diagonal]
      simp only [mul_one]
    have he:=congrFun (hfix b s) i
    rw [hd,Matrix.mulVec_diagonal] at he
    by_contra hn
    change ¬labelNumber {labels s} i.1.1.2=(if b s then 1 else 0) at hn
    rw [if_neg hn,zero_mul] at he
    exact hi he.symm
  have he:=number_flags_erasure T (fun s R=>labelNumber {labels s} R.2.2) w hwflags
  have hsum:R*ᵥ(∑b,w b)=∑b,v b := by
    rw [Matrix.mulVec_sum]
    simp only [hw]
  calc
    _ = fockVisible T (R*ᵥ(∑b,w b)) := by rw [hsum]
    _ = fockVisible T (∑b,w b) := rotation_visible U 1 T _
    _ = ∑b,fockVisible T (w b) := he
    _ = _ := by simp only [hf]

#print axioms rotated_flags_erasure
end
end ICO.C6RotatedFlagErasure
