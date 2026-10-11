import ICO.C6BosonicPolar

/-! Exact occupation selection for the actual polar creator.  These identities
are valid on the entire particle sector, not only on a chosen trajectory. -/
namespace ICO.C6BosonicSupport
open QIT ICO.C6Polar ICO.C6BosonicPolar ICO.C6BosonicBounds
  ICO.MHOccupationCounts ICO.MHCreationCoefficients ICO.MHOccupationCovariance
  ICO.MHERecordingApprox ICO.MHCreationCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2000000

section General
variable {a b : Type*} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]
local instance normMatrixNonUnitalCStar (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance normMatrixCStar (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩

theorem gram_intertwine (E : Matrix b a ℂ) (P : CMatrix a) (Q : CMatrix b)
    (hP : P.conjTranspose=P) (hQ : Q.conjTranspose=Q)
    (h : Q*E=E*P) : Commute (gram E) P := by
  have ha := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_mul,hP,hQ] at ha
  change E.conjTranspose*E*P=P*(E.conjTranspose*E)
  rw [Matrix.mul_assoc,←h,←Matrix.mul_assoc,ha,Matrix.mul_assoc]

theorem polar_intertwine (E : Matrix b a ℂ) (hg : IsUnit (gram E))
    (P : CMatrix a) (Q : CMatrix b)
    (hP : P.conjTranspose=P) (hQ : Q.conjTranspose=Q)
    (h : Q*E=E*P) : Q*polar E=polar E*P := by
  have hc : Commute (root E) P := by
    simpa only [root,psdSqrt,CFC.sqrt_eq_cfc] using
      (gram_intertwine E P Q hP hQ h).cfc_nnreal NNReal.sqrt
  have hi : P*(root E)⁻¹=(root E)⁻¹*P := by
    calc
      _ = (root E)⁻¹*(root E*P)*(root E)⁻¹ := by
        rw [←Matrix.mul_assoc,inv_mul_root E hg,Matrix.one_mul]
      _ = (root E)⁻¹*(P*root E)*(root E)⁻¹ := by rw [hc.eq]
      _ = _ := by rw [Matrix.mul_assoc,Matrix.mul_assoc,root_mul_inv E hg,Matrix.mul_one]
  simp only [polar]
  rw [←Matrix.mul_assoc,h,Matrix.mul_assoc,hi,←Matrix.mul_assoc]

end General
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def labelNumber (S : Finset A) {n : ℕ} (p : TensorPowerProfile (A×A) n) : ℕ :=
  ∑ z : A×A, if z.1 ∈ S then p.val z else 0

theorem labelNumber_increment (S : Finset A) {n : ℕ}
    (p : TensorPowerProfile (A×A) n) (x y : A) :
    labelNumber S (incrementProfile (x,y) p)=labelNumber S p+(if x∈S then 1 else 0) := by
  unfold labelNumber
  simp only [incrementProfile_apply]
  have he (z : A×A) : (if z.1∈S then (if (x,y)=z then 1 else 0)+p.val z else 0)=
      (if (x,y)=z then (if x∈S then 1 else 0) else 0)+(if z.1∈S then p.val z else 0) := by
    by_cases hz : (x,y)=z
    · subst z; split_ifs <;> simp_all
    · simp only [if_neg hz,zero_add]
  simp only [he,Finset.sum_add_distrib]
  simp [Nat.add_comm]

def sourceNumberProjection (S : Finset A) (n k : ℕ) : CMatrix (Sector (A:=A) n) :=
  Matrix.diagonal (fun i => if labelNumber S i.2+(if i.1∈S then 1 else 0)=k then 1 else 0)

def targetNumberProjection (S : Finset A) (n k : ℕ) : CMatrix (Sector (A:=A) n) :=
  Matrix.diagonal (fun i => if labelNumber S i.2=k then 1 else 0)

theorem sourceNumberProjection_adjoint (S : Finset A) (n k : ℕ) :
    (sourceNumberProjection (A:=A) S n k).conjTranspose=sourceNumberProjection S n k := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [sourceNumberProjection,Matrix.conjTranspose_apply,Matrix.diagonal_apply]
  · simp [sourceNumberProjection,Matrix.conjTranspose_apply,Matrix.diagonal_apply,h,Ne.symm h]

theorem targetNumberProjection_adjoint (S : Finset A) (n k : ℕ) :
    (targetNumberProjection (A:=A) S n k).conjTranspose=targetNumberProjection S n k := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [targetNumberProjection,Matrix.conjTranspose_apply,Matrix.diagonal_apply]
  · simp [targetNumberProjection,Matrix.conjTranspose_apply,Matrix.diagonal_apply,h,Ne.symm h]

theorem symmetricInsertion_number (S : Finset A) (n k : ℕ) :
    targetNumberProjection S (n+1) k * symmetricInsertion (α:=A) n =
      symmetricInsertion (α:=A) n * sourceNumberProjection S n k := by
  ext o i
  simp only [targetNumberProjection,sourceNumberProjection,Matrix.diagonal_mul,
    Matrix.mul_diagonal,symmetricInsertion_eq,Matrix.smul_apply,smul_eq_mul,
    occupationLeftCreator,creationOccupation_basis_entry]
  by_cases h : o.2=incrementProfile (i.1,o.1) i.2
  · rw [if_pos h]
    have hn := labelNumber_increment S i.2 i.1 o.1
    rw [h] at ⊢
    rw [hn]
    split_ifs <;> ring
  · simp [h]

theorem leftPolar_number (S : Finset A) {n : ℕ} (hn : n<Fintype.card A) (k : ℕ) :
    targetNumberProjection S (n+1) k * leftPolar (A:=A) n =
      leftPolar n * sourceNumberProjection S n k :=
  polar_intertwine _ (gram_isUnit _ (gram_defect_lt_one hn)) _ _
    (sourceNumberProjection_adjoint S n k)
    (targetNumberProjection_adjoint S (n+1) k) (symmetricInsertion_number S n k)

/-- A polar creation preserves every exact label-number sector. Taking the
complement of an allowed set and number zero gives the usual support rule. -/
theorem leftPolar_number_supported (S : Finset A) {n : ℕ} (hn : n<Fintype.card A)
    (k : ℕ) (v : Sector (A:=A) n → ℂ)
    (hv : (sourceNumberProjection S n k).mulVec v=v) :
    (targetNumberProjection S (n+1) k).mulVec ((leftPolar n).mulVec v)=
      (leftPolar n).mulVec v := by
  rw [Matrix.mulVec_mulVec,leftPolar_number S hn k,←Matrix.mulVec_mulVec,hv]

#print axioms leftPolar_number
#print axioms leftPolar_number_supported
end
end ICO.C6BosonicSupport
