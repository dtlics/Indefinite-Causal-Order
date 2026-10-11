import ICO.MHFockTrajectory
import ICO.MHWRecordSwap
import ICO.MHInverseCovariance
import ICO.MHMemoryMeanDomain

namespace ICO.MHRecordingChoiceOperators
open Matrix QIT ICO.MHFockTrajectory ICO.MHWRecordSwap ICO.MHWLengths
  ICO.MHWEmbedding ICO.MHWDomainProjection ICO.MHFockProjection ICO.MHFockAlgebra
  ICO.MHFockSwap ICO.MHFockOracle ICO.MHFockBothCovariance ICO.MHFockSpace
  ICO.MHBoundedRecording ICO.MHFockKnownOperation
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 512
variable {A : Type*} [Fintype A] [DecidableEq A]

def choiceGram {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (inv : Bool) :
    CMatrix (InputCutoff (α:=A) T) := (Wchoice hT inv).conjTranspose*Wchoice hT inv

def choiceDomain {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (hq : q≤T) (inv : Bool) :
    CMatrix (InputCutoff (α:=A) T) := choiceGram hT inv*sourceProjection hq

def choiceRestrictedV {q T : ℕ} (hq : q+1≤T) (inv : Bool) :
    CMatrix (InputCutoff (α:=A) T) :=
  Vchoice hq inv*sourceProjection (Nat.le_trans (Nat.le_succ q) hq)

theorem choiceGram_projection {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (inv : Bool) :
    IsStarProjection (choiceGram hT inv) := by
  cases inv with
  | false => exact recordW_initial_projection hT
  | true =>
    simp only [choiceGram,Wchoice,if_true,Matrix.conjTranspose_conjTranspose]
    rw [←recordGram_swap hT]
    nth_rw 2 [←swapMatrix_selfAdjoint]
    exact isometry_projection _ _ (swapMatrix_gram T) (recordW_initial_projection hT)

theorem choiceGram_cutoff_commute {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q≤T) (inv : Bool) : Commute (sourceProjection (α:=A) hq) (choiceGram hT inv) := by
  cases inv with
  | false => exact recordGram_cutoff_commute hq hT
  | true =>
    simp only [choiceGram,Wchoice,if_true,Matrix.conjTranspose_conjTranspose]
    rw [←recordGram_swap hT]
    exact ((source_commute_swap hq).mul_right (recordGram_cutoff_commute hq hT)).mul_right
      (source_commute_swap hq)

theorem choiceDomain_projection {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q≤T) (inv : Bool) : IsStarProjection (choiceDomain hT hq inv) :=
  (choiceGram_projection hT inv).mul (sourceProjection_projection hq)
    (choiceGram_cutoff_commute hT hq inv).symm

theorem bij_mul_choiceGram {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (inv : Bool) :
    bijProjection T*choiceGram hT inv=choiceGram hT inv := by
  cases inv with
  | false => exact bij_mul_recordGram hT
  | true =>
    have hh := congrArg (fun M : CMatrix (InputCutoff (α:=A) T) => swapMatrix T*M*swapMatrix T)
      (bij_mul_recordGram hT)
    dsimp only at hh
    rw [swap_mul,bijProjection_swap] at hh
    simpa only [recordGram_swap,choiceGram,Wchoice,if_true,
      Matrix.conjTranspose_conjTranspose] using hh

theorem bij_mul_choiceDomain {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q≤T) (inv : Bool) : bijProjection T*choiceDomain hT hq inv=choiceDomain hT hq inv := by
  rw [choiceDomain,←Matrix.mul_assoc,bij_mul_choiceGram]

theorem choiceMissing_projection {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q≤T) (inv : Bool) : IsStarProjection (bijProjection T-choiceDomain hT hq inv) :=
  (choiceDomain_projection hT hq inv).sub_of_mul_eq_right (bij_projection T)
    (bij_mul_choiceDomain hT hq inv)

theorem choice_low_overlap {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q+1≤T) (hqd : q<Fintype.card A) (inv : Bool) :
    (Wchoice hT inv).conjTranspose*choiceRestrictedV hq inv=
      choiceDomain hT (Nat.le_trans (Nat.le_succ q) hq) inv := by
  cases inv with
  | false =>
    simpa only [Wchoice,Vchoice,choiceRestrictedV,choiceDomain,choiceGram,if_false,
      Bool.false_eq_true,Matrix.mul_assoc] using recordW_overlap_low hq hT hqd
  | true =>
    simpa only [Wchoice,Vchoice,choiceRestrictedV,choiceDomain,choiceGram,if_true,
      if_pos rfl,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
      using recordW_inverse_overlap_low hq hT hqd

theorem Wchoice_norm_le {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (inv : Bool) :
    ‖Wchoice hT inv‖≤1 := by
  cases inv with
  | false => exact recordW_norm_le (α:=A) hT
  | true =>
    change ‖(recordW hT).conjTranspose‖≤1
    rw [Matrix.l2_opNorm_conjTranspose]
    exact recordW_norm_le (α:=A) hT

theorem Vchoice_norm_le {q T : ℕ} (hq : q+1≤T) (hqd : q<Fintype.card A) (inv : Bool) :
    ‖Vchoice (α:=A) hq inv‖≤1 := by
  cases inv with
  | false => exact fullOracle_norm_le (α:=A) hq hqd
  | true =>
    change ‖(fullOracle (α:=A) hq).conjTranspose‖≤1
    rw [Matrix.l2_opNorm_conjTranspose]
    exact fullOracle_norm_le (α:=A) hq hqd

theorem tensor_projection {H M : Type*} [Fintype H] [DecidableEq H]
    [Fintype M] [DecidableEq M] (P : CMatrix H) (hP : IsStarProjection P) :
    IsStarProjection (Matrix.kronecker P (1 : CMatrix M)) := by
  constructor
  · change Matrix.kronecker P (1 : CMatrix M)*Matrix.kronecker P 1=_
    simp only [Matrix.kronecker]
    rw [←Matrix.mul_kronecker_mul,hP.isIdempotentElem.eq,Matrix.mul_one]
  · change (Matrix.kronecker P (1 : CMatrix M)).conjTranspose=_
    have hs : P.conjTranspose=P := hP.isSelfAdjoint.star_eq
    simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,hs]

theorem memory_low_overlap {M : Type*} [Fintype M] [DecidableEq M]
    {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q+1≤T) (hqd : q<Fintype.card A) (inv : Bool) :
    (Matrix.kronecker (Wchoice hT inv) (1 : CMatrix M)).conjTranspose*
      Matrix.kronecker (choiceRestrictedV hq inv) (1 : CMatrix M)=
    Matrix.kronecker (choiceDomain hT (Nat.le_trans (Nat.le_succ q) hq) inv) (1 : CMatrix M) := by
  simp only [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,choice_low_overlap hT hq hqd inv,Matrix.mul_one]

#print axioms choice_low_overlap
#print axioms choiceMissing_projection
#print axioms memory_low_overlap
end
end ICO.MHRecordingChoiceOperators
