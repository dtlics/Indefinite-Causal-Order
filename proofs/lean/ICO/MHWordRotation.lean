import ICO.MHWordProfileGram
import ICO.MHRightCovariance
import ICO.EqualityTwirl

/-! Product rotations on finite record words and their exact selected-slot split. -/
namespace ICO.MHWordRotation
open Matrix QIT ICO.MHWordDistinct ICO.MHWordProfiles ICO.MHSymmetric
  ICO.MHCreationCovariance ICO.MHRightCovariance
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
variable {A J K : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

def piMatrix (U : J → Matrix.unitaryGroup K ℂ) : CMatrix (J → K) :=
  fun o i => ∏ j, (U j : CMatrix K) (o j) (i j)

theorem piMatrix_isometry (U : J → Matrix.unitaryGroup K ℂ) :
    (piMatrix U).conjTranspose * piMatrix U = 1 := by
  ext o i
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,piMatrix,star_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : J) (x : K) =>
    star ((U j : CMatrix K) x (o j)) * (U j : CMatrix K) x (i j))]
  have he (j : J) : (∑ x : K, star ((U j : CMatrix K) x (o j)) *
      (U j : CMatrix K) x (i j)) = if o j=i j then 1 else 0 := by
    have hh := congrArg (fun M : CMatrix K => M (o j) (i j))
      (Matrix.UnitaryGroup.star_mul_self (U j))
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using hh
  simp_rw [he]
  simp only [Fintype.prod_boole,← funext_iff,Matrix.one_apply]

def piUnitary (U : J → Matrix.unitaryGroup K ℂ) : Matrix.unitaryGroup (J → K) ℂ :=
  ⟨piMatrix U,Matrix.mem_unitaryGroup_iff'.mpr (piMatrix_isometry U)⟩

def wordUnitary (C : Matrix.unitaryGroup A ℂ)
    (E : J → Matrix.unitaryGroup (A × A) ℂ) : Matrix.unitaryGroup (WordBasis A J) ℂ :=
  ⟨Matrix.kronecker (C : CMatrix A) (piMatrix E),
    Matrix.kronecker_mem_unitary C.property (piUnitary E).property⟩

def tensorUnitary {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (U : Matrix.unitaryGroup X ℂ) (V : Matrix.unitaryGroup Y ℂ) : Matrix.unitaryGroup (X × Y) ℂ :=
  ⟨Matrix.kronecker (U : CMatrix X) (V : CMatrix Y),
    Matrix.kronecker_mem_unitary U.property V.property⟩

def spectatorUnitary (i : J) (Q : Matrix.unitaryGroup A ℂ)
    (E : J → Matrix.unitaryGroup (A × A) ℂ) : Matrix.unitaryGroup (Spectator A i) ℂ :=
  tensorUnitary Q (piUnitary (fun j : Other i => E j.val))

theorem selected_slot_factor (C : Matrix.unitaryGroup A ℂ)
    (E : J → Matrix.unitaryGroup (A × A) ℂ) (i : J)
    (P Q : Matrix.unitaryGroup A ℂ)
    (hE : (E i : CMatrix (A × A)) = Matrix.kronecker (P : CMatrix A) (Q : CMatrix A)) :
    (wordUnitary C E : CMatrix (WordBasis A J)) =
      (Matrix.kronecker (spectatorUnitary i Q E : CMatrix (Spectator A i))
        (Matrix.kronecker (C : CMatrix A) (P : CMatrix A))).submatrix (slotEquiv i) (slotEquiv i) := by
  ext o p
  change (C : CMatrix A) o.1 p.1 * (∏ j, (E j : CMatrix (A × A)) (o.2 j) (p.2 j)) = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i,hE]
  simp only [Matrix.submatrix_apply,slotEquiv,spectatorUnitary,tensorUnitary,piUnitary,
    piMatrix,Matrix.kronecker,Matrix.kroneckerMap_apply]
  change (C : CMatrix A) o.1 p.1 * (((P : CMatrix A) (o.2 i).1 (p.2 i).1 *
      (Q : CMatrix A) (o.2 i).2 (p.2 i).2) *
      ∏ j : Other i, (E j.val : CMatrix (A × A)) (o.2 j.val) (p.2 j.val)) =
    ((Q : CMatrix A) (o.2 i).2 (p.2 i).2 *
      ∏ j : Other i, (E j.val : CMatrix (A × A)) (o.2 j.val) (p.2 j.val)) *
      ((C : CMatrix A) o.1 p.1 * (P : CMatrix A) (o.2 i).1 (p.2 i).1)
  ring

def transposeUnitary (D : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup A ℂ :=
  ⟨(D : CMatrix A).transpose,Matrix.transpose_mem_unitaryGroup_iff.mpr D.property⟩

def conjugateUnitary (C : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup A ℂ :=
  transposeUnitary C⁻¹

def recordUnitary (R : Finset J) (C D : Matrix.unitaryGroup A ℂ) (j : J) :
    Matrix.unitaryGroup (A × A) ℂ :=
  if j ∈ R then rightEdgeUnitary D⁻¹ C⁻¹ else leftEdgeUnitary C D

def recordOutputUnitary (R : Finset J) (D : Matrix.unitaryGroup A ℂ) (j : J) :
    Matrix.unitaryGroup A ℂ := if j ∈ R then D⁻¹ else transposeUnitary D

def turn (R : Finset J) (C D : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup (WordBasis A J) ℂ :=
  wordUnitary C (recordUnitary R C D)

theorem conjugateUnitary_value (C : Matrix.unitaryGroup A ℂ) :
    (conjugateUnitary C : CMatrix A) = (C : CMatrix A).map star := by
  ext i j
  simp [conjugateUnitary,transposeUnitary,Matrix.UnitaryGroup.inv_val,
    Matrix.transpose_apply,Matrix.conjTranspose_apply]

theorem turn_left_split (R : Finset J) (C D : Matrix.unitaryGroup A ℂ) (i : J) (hi : i ∉ R) :
    (turn R C D : CMatrix (WordBasis A J)) =
      (Matrix.kronecker
        (spectatorUnitary i (transposeUnitary D) (recordUnitary R C D) : CMatrix (Spectator A i))
        (ICO.EqualityTwirl.sameTensor C)).submatrix (slotEquiv i) (slotEquiv i) := by
  apply selected_slot_factor
  simp only [recordUnitary,if_neg hi,leftEdgeUnitary,transposeUnitary]

theorem turn_right_split (R : Finset J) (C D : Matrix.unitaryGroup A ℂ) (i : J) (hi : i ∈ R) :
    (turn R C D : CMatrix (WordBasis A J)) =
      (Matrix.kronecker
        (spectatorUnitary i D⁻¹ (recordUnitary R C D) : CMatrix (Spectator A i))
        (ICO.EqualityTwirl.conjugateTensor C)).submatrix (slotEquiv i) (slotEquiv i) := by
  have hh := selected_slot_factor C (recordUnitary R C D) i (conjugateUnitary C) D⁻¹
    (by simp only [recordUnitary,if_pos hi,inverse_rightEdgeUnitary,conjugateUnitary_value,
      Matrix.UnitaryGroup.inv_val,Matrix.star_eq_conjTranspose])
  simpa only [turn,conjugateUnitary_value,ICO.EqualityTwirl.conjugateTensor] using hh

#print axioms selected_slot_factor
#print axioms turn_left_split
#print axioms turn_right_split
end
end ICO.MHWordRotation



