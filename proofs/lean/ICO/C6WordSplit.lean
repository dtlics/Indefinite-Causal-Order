import ICO.C6BosonicPolar
import ICO.C6LabelSymmetry

/-! Exact separation of first-quantized record labels and images. -/
namespace ICO.C6WordSplit
open QIT Matrix ICO.MHCreationCovariance ICO.MHSymmetric ICO.C6LabelSymmetry
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem edge_rotation_split (U : Matrix.unitaryGroup A ℂ) (n : ℕ)
    (x y : TensorPower (A × A) n) :
    (unitaryTensorPowerMatrix (leftEdgeUnitary U 1) n :
      CMatrix (TensorPower (A × A) n)) x y =
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n))
        (tensorPowerProdEquiv A A n x).1 (tensorPowerProdEquiv A A n y).1 *
      (if (tensorPowerProdEquiv A A n x).2 = (tensorPowerProdEquiv A A n y).2
        then 1 else 0) := by
  induction n with
  | zero =>
    cases x
    cases y
    simp [tensorPowerProdEquiv, unitaryTensorPowerMatrix, Matrix.one_apply]
    rfl
  | succ n ih =>
    rcases x with ⟨⟨a, b⟩, xs⟩
    rcases y with ⟨⟨c, e⟩, ys⟩
    change ((U : CMatrix A) a c * (1 : CMatrix A) e b) *
      (unitaryTensorPowerMatrix (leftEdgeUnitary U 1) n :
        CMatrix (TensorPower (A × A) n)) xs ys = _
    rw [ih]
    change ((U : CMatrix A) a c * (1 : CMatrix A) e b) *
      ((unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n)) _ _ *
        (if _ then 1 else 0)) =
      ((U : CMatrix A) a c * (unitaryTensorPowerMatrix U n :
        CMatrix (TensorPower A n)) _ _) *
        (if (b, (tensorPowerProdEquiv A A n xs).2) =
          (e, (tensorPowerProdEquiv A A n ys).2) then 1 else 0)
    by_cases hbe : b = e <;>
      by_cases hs : (tensorPowerProdEquiv A A n xs).2 =
        (tensorPowerProdEquiv A A n ys).2 <;>
      simp [tensorPowerProdEquiv, Matrix.one_apply, Prod.mk.injEq, hbe, hs, eq_comm, mul_assoc]

def labelImageEquiv (n : ℕ) :
    TensorPower (A × A) n ≃ TensorPower A n × TensorPower A n :=
  tensorPowerProdEquiv A A n

theorem occupation_label_intertwine (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Matrix.kronecker (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n))
      (1 : CMatrix (TensorPower A n)) *
      (occupationEmbedding (a := A × A) n).submatrix (labelImageEquiv n).symm id =
    (occupationEmbedding (a := A × A) n).submatrix (labelImageEquiv n).symm id *
      occupationRotation (leftEdgeUnitary U 1) n := by
  have h := congrArg (fun B => B.submatrix (labelImageEquiv n).symm id)
    (occupationRotation_intertwine (leftEdgeUnitary U 1) n)
  dsimp only at h
  rw [← Matrix.submatrix_mul_equiv _ _ (labelImageEquiv n).symm
    (labelImageEquiv n).symm id] at h
  have he : (unitaryTensorPowerMatrix (leftEdgeUnitary U 1) n :
      CMatrix (TensorPower (A × A) n)).submatrix
        (labelImageEquiv n).symm (labelImageEquiv n).symm =
      Matrix.kronecker (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n))
        (1 : CMatrix (TensorPower A n)) := by
    ext x y
    simpa [labelImageEquiv, Matrix.kronecker_apply, Matrix.one_apply] using
      edge_rotation_split U n ((labelImageEquiv n).symm x) ((labelImageEquiv n).symm y)
  rw [he] at h
  rw [← Matrix.submatrix_mul_equiv (occupationEmbedding (a := A × A) n)
    (occupationRotation (leftEdgeUnitary U 1) n) (labelImageEquiv n).symm
    (Equiv.refl _) id] at h
  exact h

#print axioms occupation_label_intertwine
end
end ICO.C6WordSplit
