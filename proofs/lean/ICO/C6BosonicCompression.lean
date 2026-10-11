import ICO.C6BosonicRight
import ICO.C6BosonicGram

/-! A rank-k query compression of the inverse bosonic creator. -/
namespace ICO.C6BosonicCompression
open QIT ICO.C6BosonicRight ICO.C6BosonicPolar ICO.C6BosonicBounds
  ICO.C6BosonicCCR ICO.C6BosonicDecode ICO.C6BosonicGram
  ICO.MHOccupationCovariance ICO.MHCreationCovariance ICO.RecordingCopyIdentity
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def queryProjection (S : Finset A) (n : ℕ) : CMatrix (Sector (A:=A) n) :=
  Matrix.diagonal (fun i => if i.1 ∈ S then 1 else 0)

def compressedCreator (S : Finset A) (n : ℕ) :
    Matrix (Sector (A:=A) (n+1)) (Sector (A:=A) n) ℂ :=
  queryProjection S (n+1) * occupationRightCreator (α:=A) n

theorem compressedCreator_entry (S : Finset A) (n : ℕ)
    (o : Sector (A:=A) (n+1)) (i : Sector (A:=A) n) :
    compressedCreator S n o i =
      if o.1 ∈ S then creator n (o.1,i.1) o.2 i.2 else 0 := by
  simp [compressedCreator,queryProjection,Matrix.diagonal_mul,occupationRightCreator,
    creator,ite_mul]

theorem compressedCreator_gram_entry (S : Finset A) (n : ℕ)
    (i j : Sector (A:=A) n) :
    ((compressedCreator S n).conjTranspose * compressedCreator S n) i j =
      ∑ x ∈ S, ((creator n (x,i.1)).conjTranspose * creator n (x,j.1)) i.2 j.2 := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,compressedCreator_entry,
    Fintype.sum_prod_type]
  simp only [apply_ite star,star_zero,ite_mul,mul_ite,zero_mul,mul_zero,ite_self]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_mem]
  simp

def normalCompression (S : Finset A) (n : ℕ) : CMatrix (Sector (A:=A) (n+1)) :=
  fun i j => ∑ x ∈ S,
    (creator n (x,j.1) * (creator n (x,i.1)).conjTranspose) i.2 j.2

theorem compressedCreator_succ_gram (S : Finset A) (n : ℕ) :
    (compressedCreator S (n+1)).conjTranspose * compressedCreator S (n+1) =
      (S.card : ℂ) • (1 : CMatrix (Sector (A:=A) (n+1))) + normalCompression S n := by
  ext i j
  rw [compressedCreator_gram_entry]
  simp only [canonical_commutator,Matrix.add_apply,Finset.sum_add_distrib,
    normalCompression,Prod.mk.injEq,true_and]
  by_cases h : i.1=j.1 <;>
    simp [h,Matrix.smul_apply,Matrix.one_apply,Prod.ext_iff]

def swapImage (n : ℕ) (x : Decoded (A:=A) n) : Decoded (A:=A) n :=
  (x.2.1.2,((x.2.1.1,x.1),x.2.2))

theorem swapImage_involutive (n : ℕ) : Function.Involutive (swapImage (A:=A) n) := by
  intro x
  rcases x with ⟨x,⟨⟨y,z⟩,p⟩⟩
  rfl

def imageExchange (S : Finset A) (n : ℕ) : CMatrix (Decoded (A:=A) n) :=
  Matrix.diagonal (fun o => if o.2.1.1 ∈ S then 1 else 0) *
    basisEmbedding (swapImage n)

theorem imageExchange_norm (S : Finset A) (n : ℕ) : ‖imageExchange (A:=A) S n‖ ≤ 1 := by
  let P : CMatrix (Decoded (A:=A) n) :=
    Matrix.diagonal (fun o => if o.2.1.1 ∈ S then 1 else 0)
  have hP : IsStarProjection P := by
    constructor
    · change P*P=P
      ext i j
      by_cases h : i=j
      · subst j; simp [P,Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply]
      · simp [P,Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply,h,Ne.symm h]
    · change P.conjTranspose=P
      ext i j
      by_cases h : i=j
      · subst j; simp [P,Matrix.conjTranspose_apply]
      · simp [P,Matrix.conjTranspose_apply,h,Ne.symm h]
  have hS := ICO.RecordingProcess.isometry_matrix_norm_le _
    (basisEmbedding_gram (swapImage (A:=A) n) (swapImage_involutive n).injective)
  exact (Matrix.l2_opNorm_mul P (basisEmbedding (swapImage n))).trans
    ((mul_le_mul (IsStarProjection.norm_le P hP) hS (norm_nonneg _) (by norm_num)).trans_eq (by ring))

theorem imageExchange_queryStack_entry (S : Finset A) (n : ℕ)
    (o : Decoded (A:=A) n) (i : Sector (A:=A) (n+1)) :
    (imageExchange (A:=A) S n * queryStack (A:=A) n) o i =
      if o.2.1.1 ∈ S then
        (if o.2.1.2=i.1 then star (creator n (o.2.1.1,o.1) i.2 o.2.2) else 0) else 0 := by
  rw [imageExchange,Matrix.mul_assoc,Matrix.diagonal_mul,Matrix.mul_apply]
  have he (z : Decoded (A:=A) n) :
      basisEmbedding (swapImage n) o z = if z=swapImage n o then 1 else 0 := by
    change (if o=swapImage n z then 1 else 0)=_
    congr 1
    apply propext
    constructor
    · intro h; rw [h,swapImage_involutive n]
    · intro h; rw [h,swapImage_involutive n]
  simp only [he,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    queryStack,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
    swapImage,annihilationStack]

theorem normalCompression_eq (S : Finset A) (n : ℕ) :
    normalCompression (A:=A) S n =
      (queryStack n).conjTranspose * imageExchange S n * queryStack n := by
  ext i j
  rw [Matrix.mul_assoc,Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply,imageExchange_queryStack_entry]
  simp only [queryStack,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
    annihilationStack,Fintype.sum_prod_type]
  simp only [apply_ite star,star_zero,star_star,ite_mul,one_mul,zero_mul,mul_ite,mul_zero,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_ite_mem]
  simp only [normalCompression,Matrix.mul_apply,Matrix.conjTranspose_apply]
  simp

theorem normalCompression_norm (S : Finset A) (n : ℕ) :
    ‖normalCompression (A:=A) S n‖ ≤ n+1 := by
  have hstack : ‖queryStack (A:=A) n‖ * ‖queryStack (A:=A) n‖ ≤ n+1 := by
    rw [←Matrix.l2_opNorm_conjTranspose_mul_self,queryStack_gram,norm_smul]
    have hI := IsStarProjection.norm_le
      (1 : CMatrix (Sector (A:=A) (n+1))) (IsStarProjection.one _)
    rw [Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hI (by positivity)).trans_eq (by norm_num)
  rw [normalCompression_eq]
  calc
    _ ≤ (‖(queryStack (A:=A) n).conjTranspose‖ * ‖imageExchange S n‖) * ‖queryStack n‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖queryStack (A:=A) n‖ * ‖queryStack n‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (imageExchange_norm S n) (norm_nonneg _))
          (norm_nonneg _)).trans_eq (by ring)
    _ ≤ n+1 := hstack

#print axioms normalCompression_eq
#print axioms normalCompression_norm
end
end ICO.C6BosonicCompression
