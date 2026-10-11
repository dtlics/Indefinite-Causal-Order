import ICO.C6BosonicLabelSupport
import ICO.MHWordProfiles

/-! Occupation-label support is exactly the first-quantized support in the
corresponding tensor-product label subspace. -/
namespace ICO.C6BosonicWordSupport
open QIT ICO.C6BosonicLabelSupport ICO.MHSymmetric ICO.MHWordProfiles
  ICO.MHCreationCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
variable {A : Type*} [Fintype A] [DecidableEq A]

def wordAllowed (S : Finset A) : ∀ n, TensorPower (A×A) n → Prop
  | 0,_ => True
  | n+1,w => w.1.1∈S ∧ wordAllowed S n w.2

instance wordAllowedDecidable (S : Finset A) (n : ℕ) (w : TensorPower (A×A) n) :
    Decidable (wordAllowed S n w) := Classical.propDecidable _

theorem profile_allowed (S : Finset A) (n : ℕ) (w : TensorPower (A×A) n) :
    LabelsIn S (wordProfile w) ↔ wordAllowed S n w := by
  induction n with
  | zero =>
    cases w
    simp [LabelsIn,wordProfile,wordAllowed,tensorPowerTypeProfile]
  | succ n ih =>
    rcases w with ⟨z,w⟩
    constructor
    · intro h
      have hz : z.1∈S := by
        by_contra hn
        have hh := h z hn
        change tensorPowerTypeProfile (n+1) (z,w) z=0 at hh
        rw [tensorPowerTypeProfile_succ] at hh
        simp at hh
      refine ⟨hz,(ih w).mp ?_⟩
      intro a ha
      have hh := h a ha
      change tensorPowerTypeProfile (n+1) (z,w) a=0 at hh
      rw [tensorPowerTypeProfile_succ] at hh
      change tensorPowerTypeProfile n w a=0
      omega
    · rintro ⟨hz,hw⟩
      have hh := (ih w).mpr hw
      intro a ha
      have hza : z≠a := by intro he; subst a; exact ha hz
      change tensorPowerTypeProfile (n+1) (z,w) a=0
      rw [tensorPowerTypeProfile_succ,if_neg hza,zero_add]
      exact hh a ha

def wordSupport (S : Finset A) (n : ℕ) : CMatrix (TensorPower (A×A) n) :=
  Matrix.diagonal (fun w => if wordAllowed S n w then 1 else 0)

def profileSupport (S : Finset A) (n : ℕ) : CMatrix (TensorPowerProfile (A×A) n) :=
  Matrix.diagonal (fun p => if LabelsIn S p then 1 else 0)

theorem support_intertwine (S : Finset A) (n : ℕ) :
    wordSupport S n*occupationEmbedding n=occupationEmbedding n*profileSupport S n := by
  ext w p
  simp only [wordSupport,profileSupport,Matrix.diagonal_mul,Matrix.mul_diagonal,
    occupationEmbedding,tensorPowerProfileUnitVector_apply]
  by_cases hw : w∈tensorPowerProfileClass p
  · have hh : wordAllowed S n w ↔ LabelsIn S p := by
      rw [←wordProfile_of_mem p w hw]
      exact (profile_allowed S n w).symm
    simp only [if_pos hw,hh]
    split_ifs <;> simp
  · simp [hw]

theorem support_compression (S : Finset A) (n : ℕ) :
    (occupationEmbedding (a:=A×A) n).conjTranspose*wordSupport S n*occupationEmbedding n=
      profileSupport S n := by
  rw [Matrix.mul_assoc,support_intertwine,←Matrix.mul_assoc,
    occupationEmbedding_gram,Matrix.one_mul]

theorem wordSupport_zero (S : Finset A) : wordSupport S 0=1 := by
  ext i j
  simp only [wordSupport,Matrix.diagonal_apply,Matrix.one_apply,wordAllowed]
  split_ifs <;> simp_all

theorem wordSupport_succ (S : Finset A) (n : ℕ) :
    wordSupport S (n+1)=Matrix.kronecker
      (Matrix.kronecker (Matrix.diagonal (fun x : A => if x∈S then (1:ℂ) else 0)) (1:CMatrix A))
      (wordSupport S n) := by
  ext i j
  simp only [wordSupport,Matrix.diagonal_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  rcases i with ⟨⟨a,b⟩,w⟩
  rcases j with ⟨⟨c,e⟩,v⟩
  have he : (((a,b),w) : TensorPower (A×A) (n+1))=((c,e),v) ↔ a=c ∧ b=e ∧ w=v := by
    constructor
    · intro h
      cases h
      exact ⟨rfl,rfl,rfl⟩
    · rintro ⟨rfl,rfl,rfl⟩
      rfl
  simp only [he,wordAllowed]
  by_cases hac : a=c <;> by_cases hbe : b=e <;> by_cases hwv : w=v <;>
    simp_all [Prod.mk.injEq]
  all_goals first | (intro hh; cases hh; simp_all) | (split_ifs <;> simp_all)

theorem rotation_adjoint_embedding (U : Matrix.unitaryGroup (A×A) ℂ) (n : ℕ) :
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (A×A) n)).conjTranspose*
      occupationEmbedding n=occupationEmbedding n*(occupationRotation U n).conjTranspose := by
  have hU : (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (A×A) n)).conjTranspose*
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (A×A) n))=1 :=
    unitaryTensorPowerMatrix_star_mul_self U n
  have hR : occupationRotation U n*(occupationRotation U n).conjTranspose=1 :=
    (symmetricRotation U n).property.2
  have hh := congrArg (fun M =>
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (A×A) n)).conjTranspose*M*
      (occupationRotation U n).conjTranspose) (occupationRotation_intertwine U n)
  simp only [←Matrix.mul_assoc,hU,Matrix.one_mul] at hh
  simpa only [Matrix.mul_assoc,hR,Matrix.mul_one] using hh.symm

theorem rotated_support_compression (U : Matrix.unitaryGroup (A×A) ℂ) (S : Finset A) (n : ℕ) :
    (occupationEmbedding (a:=A×A) n).conjTranspose*
      ((unitaryTensorPowerMatrix U n : CMatrix (TensorPower (A×A) n))*wordSupport S n*
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (A×A) n)).conjTranspose)*
          occupationEmbedding n=
      occupationRotation U n*profileSupport S n*(occupationRotation U n).conjTranspose := by
  have hleft : (occupationEmbedding (a:=A×A) n).conjTranspose*
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (A×A) n))=
      occupationRotation U n*(occupationEmbedding (a:=A×A) n).conjTranspose := by
    have hh := congrArg Matrix.conjTranspose (rotation_adjoint_embedding U n)
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] using hh
  simp only [Matrix.mul_assoc]
  rw [rotation_adjoint_embedding]
  simp only [←Matrix.mul_assoc]
  rw [hleft]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (occupationEmbedding (a:=A×A) n).conjTranspose (wordSupport S n),
    ←Matrix.mul_assoc ((occupationEmbedding (a:=A×A) n).conjTranspose*wordSupport S n)
      (occupationEmbedding n),support_compression]

#print axioms support_intertwine
#print axioms rotated_support_compression
end
end ICO.C6BosonicWordSupport
