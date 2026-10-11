import ICO.C6BosonicSupport

/-! Forward and backward support in an allowed coordinate label subspace. -/
namespace ICO.C6BosonicLabelSupport
open QIT ICO.C6BosonicPolar ICO.C6BosonicSupport
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def LabelsIn (S : Finset A) {n : ℕ} (p : TensorPowerProfile (A×A) n) : Prop :=
  ∀ z : A×A, z.1 ∉ S → p.val z=0

instance (S : Finset A) {n : ℕ} (p : TensorPowerProfile (A×A) n) :
    Decidable (LabelsIn S p) := Classical.propDecidable _

theorem labelsIn_iff (S : Finset A) {n : ℕ} (p : TensorPowerProfile (A×A) n) :
    LabelsIn S p ↔ labelNumber Sᶜ p=0 := by
  simp [labelNumber,LabelsIn,Finset.sum_eq_zero_iff]

def recordSupport (S : Finset A) (n : ℕ) : CMatrix (Sector (A:=A) n) :=
  Matrix.diagonal (fun i => if LabelsIn S i.2 then 1 else 0)

def inputSupport (S : Finset A) (n : ℕ) : CMatrix (Sector (A:=A) n) :=
  Matrix.diagonal (fun i => if i.1∈S ∧ LabelsIn S i.2 then 1 else 0)

theorem recordSupport_eq (S : Finset A) (n : ℕ) :
    recordSupport S n=targetNumberProjection Sᶜ n 0 := by
  ext i j
  simp only [recordSupport,targetNumberProjection,labelsIn_iff]

theorem inputSupport_eq (S : Finset A) (n : ℕ) :
    inputSupport S n=sourceNumberProjection Sᶜ n 0 := by
  ext i j
  simp only [inputSupport,sourceNumberProjection,Matrix.diagonal_apply,labelsIn_iff]
  by_cases h : i=j
  · subst j
    by_cases hi : i.1∈S <;> simp [hi]
  · simp [h]

theorem leftPolar_support (S : Finset A) {n : ℕ} (hn : n<Fintype.card A) :
    recordSupport S (n+1)*leftPolar (A:=A) n=leftPolar n*inputSupport S n := by
  rw [recordSupport_eq,inputSupport_eq]
  exact leftPolar_number Sᶜ hn 0

theorem leftPolar_adjoint_support (S : Finset A) {n : ℕ} (hn : n<Fintype.card A) :
    inputSupport S n*(leftPolar (A:=A) n).conjTranspose=
      (leftPolar n).conjTranspose*recordSupport S (n+1) := by
  have h := congrArg Matrix.conjTranspose (leftPolar_support S hn)
  simpa only [Matrix.conjTranspose_mul,inputSupport_eq,recordSupport_eq,
    sourceNumberProjection_adjoint,targetNumberProjection_adjoint] using h.symm

theorem leftPolar_image_support_commute (S : Finset A) {n : ℕ} (hn : n<Fintype.card A) :
    recordSupport S (n+1)*(leftPolar (A:=A) n*(leftPolar n).conjTranspose)=
      (leftPolar n*(leftPolar n).conjTranspose)*recordSupport S (n+1) := by
  rw [←Matrix.mul_assoc,leftPolar_support S hn,Matrix.mul_assoc,
    leftPolar_adjoint_support S hn,←Matrix.mul_assoc]

theorem forward_supported (S : Finset A) {n : ℕ} (hn : n<Fintype.card A)
    (v : Sector (A:=A) n → ℂ) (hv : (inputSupport S n).mulVec v=v) :
    (recordSupport S (n+1)).mulVec ((leftPolar n).mulVec v)=(leftPolar n).mulVec v := by
  rw [Matrix.mulVec_mulVec,leftPolar_support S hn,←Matrix.mulVec_mulVec,hv]

theorem backward_supported (S : Finset A) {n : ℕ} (hn : n<Fintype.card A)
    (v : Sector (A:=A) (n+1) → ℂ) (hv : (recordSupport S (n+1)).mulVec v=v) :
    (inputSupport S n).mulVec ((leftPolar n).conjTranspose.mulVec v)=
      (leftPolar n).conjTranspose.mulVec v := by
  rw [Matrix.mulVec_mulVec,leftPolar_adjoint_support S hn,←Matrix.mulVec_mulVec,hv]

#print axioms forward_supported
#print axioms backward_supported
end
end ICO.C6BosonicLabelSupport
