import ICO.C6BosonicRight
import ICO.C6BosonicSupport
import ICO.C6BosonicCompression

/-! The inverse creator changes label occupation only in its output-query mode. -/
namespace ICO.C6BosonicRightSupport
open QIT ICO.C6Polar ICO.C6BosonicPolar ICO.C6BosonicRight ICO.C6BosonicSupport
  ICO.C6BosonicCompression ICO.MHOccupationCovariance ICO.MHCreationCoefficients
  ICO.MHOccupationCounts
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def rightOutputNumber (S : Finset A) (n k : ℕ) : CMatrix (Sector (A:=A) n) :=
  Matrix.diagonal (fun i => if labelNumber S i.2=k+(if i.1∈S then 1 else 0) then 1 else 0)

theorem rightOutputNumber_adjoint (S : Finset A) (n k : ℕ) :
    (rightOutputNumber S n k).conjTranspose=rightOutputNumber S n k := by
  rw [rightOutputNumber,Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  simp only [Function.comp_apply,Pi.star_apply]
  split_ifs <;> simp

theorem rightInsertion_number (S : Finset A) (n k : ℕ) :
    rightOutputNumber S (n+1) k * rightInsertion (A:=A) n =
      rightInsertion n * targetNumberProjection S n k := by
  ext o i
  simp only [rightOutputNumber,targetNumberProjection,Matrix.diagonal_mul,
    Matrix.mul_diagonal,rightInsertion,Matrix.smul_apply,smul_eq_mul,
    occupationRightCreator,creationOccupation_basis_entry]
  by_cases h : o.2=incrementProfile (o.1,i.1) i.2
  · rw [if_pos h,h,labelNumber_increment]
    have he : labelNumber S i.2+(if o.1∈S then 1 else 0)=k+(if o.1∈S then 1 else 0) ↔
        labelNumber S i.2=k := Nat.add_right_cancel_iff
    simp only [he]
    split_ifs <;> ring
  · simp [h]

theorem rightPolar_number (S : Finset A) {n : ℕ} (hn : n<Fintype.card A) (k : ℕ) :
    rightOutputNumber S (n+1) k * rightPolar (A:=A) n =
      rightPolar n * targetNumberProjection S n k :=
  polar_intertwine _ (gram_isUnit _ (rightInsertion_defect_lt_one hn)) _ _
    (targetNumberProjection_adjoint S n k)
    (rightOutputNumber_adjoint S (n+1) k) (rightInsertion_number S n k)

theorem number_query_selection (S : Finset A) (n k : ℕ) :
    targetNumberProjection S n (k+1) * queryProjection S n * rightOutputNumber S n k =
      queryProjection S n * rightOutputNumber S n k := by
  ext i j
  simp only [targetNumberProjection,queryProjection,rightOutputNumber,
    Matrix.diagonal_mul,Matrix.diagonal_apply]
  by_cases h : i=j
  · subst j
    by_cases hi : i.1∈S <;> simp [hi]
  · simp [h]

/-- Projecting a new birth onto S increases its exact S-occupation by one.
In particular, a new mode orthogonal to all older labels leaves a permanent
number-sector record, which is stronger than current-time orthogonality. -/
theorem selected_birth_number (S : Finset A) {n : ℕ} (hn : n<Fintype.card A)
    (k : ℕ) (v : Sector (A:=A) n → ℂ)
    (hv : (targetNumberProjection S n k).mulVec v=v) :
    (targetNumberProjection S (n+1) (k+1)).mulVec
      ((queryProjection S (n+1)).mulVec ((rightPolar n).mulVec v)) =
      (queryProjection S (n+1)).mulVec ((rightPolar n).mulVec v) := by
  have hR : (rightOutputNumber S (n+1) k).mulVec ((rightPolar n).mulVec v)=
      (rightPolar n).mulVec v := by
    rw [Matrix.mulVec_mulVec,rightPolar_number S hn k,←Matrix.mulVec_mulVec,hv]
  calc
    _ = (targetNumberProjection S (n+1) (k+1)).mulVec
        ((queryProjection S (n+1)).mulVec
          ((rightOutputNumber S (n+1) k).mulVec ((rightPolar n).mulVec v))) := by rw [hR]
    _ = _ := by
      simp only [Matrix.mulVec_mulVec,←Matrix.mul_assoc]
      rw [number_query_selection]
      simp only [←Matrix.mulVec_mulVec]
      rw [hR]

#print axioms rightPolar_number
#print axioms selected_birth_number
end
end ICO.C6BosonicRightSupport
