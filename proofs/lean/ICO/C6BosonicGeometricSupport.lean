import ICO.C6BosonicWordSupport
import ICO.C6CacheSpanProjection
import ICO.C6WordPower

/-! Basis-independent occupation support and monotonicity under enlargement
of the actual span of private label vectors. -/
namespace ICO.C6BosonicGeometricSupport
open QIT ICO.C6BosonicWordSupport ICO.C6WordPower ICO.C6CacheSpanProjection
  ICO.C6BosonicFreshRotated ICO.MHSymmetric ICO.MHCreationCovariance
  ICO.C6BosonicFockRotated ICO.MHSectorCovariance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
variable {A : Type*} [Fintype A] [DecidableEq A]

def edgeProjection (P : CMatrix A) : CMatrix (A×A) := Matrix.kronecker P 1

def occupationSupport (P : CMatrix A) (n : ℕ) : CMatrix (TensorPowerProfile (A×A) n) :=
  (occupationEmbedding (a:=A×A) n).conjTranspose*wordPower (edgeProjection P) n*occupationEmbedding n

theorem wordSupport_power (S : Finset A) (n : ℕ) :
    wordPower (edgeProjection (coordinateProjection S)) n=wordSupport S n := by
  induction n with
  | zero => exact (wordSupport_zero S).symm
  | succ n ih => rw [wordPower_succ,ih,wordSupport_succ]; rfl

theorem edge_rotation (U : Matrix.unitaryGroup A ℂ) :
    (leftEdgeUnitary U 1:CMatrix (A×A))=Matrix.kronecker (U:CMatrix A) (1:CMatrix A) := by
  ext ⟨a,b⟩ ⟨c,e⟩
  simp [leftEdgeUnitary,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,eq_comm]

theorem edge_conjugate (U : Matrix.unitaryGroup A ℂ) (S : Finset A) :
    edgeProjection (spanProjection U S)=
      (leftEdgeUnitary U 1:CMatrix (A×A))*edgeProjection (coordinateProjection S)*
        (leftEdgeUnitary U 1:CMatrix (A×A)).conjTranspose := by
  rw [edge_rotation]
  simp only [edgeProjection,spanProjection,Matrix.kronecker,Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.one_mul]

theorem geometric_word (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (n : ℕ) :
    wordPower (edgeProjection (spanProjection U S)) n=
      (unitaryTensorPowerMatrix (leftEdgeUnitary U 1) n:CMatrix (TensorPower (A×A) n))*
        wordSupport S n*
          (unitaryTensorPowerMatrix (leftEdgeUnitary U 1) n:CMatrix (TensorPower (A×A) n)).conjTranspose := by
  rw [edge_conjugate,wordPower_conjugate,wordSupport_power]

theorem occupationSupport_rotated (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (n : ℕ) :
    occupationSupport (spanProjection U S) n=
      occupationRotation (leftEdgeUnitary U 1) n*profileSupport S n*
        (occupationRotation (leftEdgeUnitary U 1) n).conjTranspose := by
  rw [occupationSupport,geometric_word,rotated_support_compression]

theorem geometric_intertwine (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (n : ℕ) :
    wordPower (edgeProjection (spanProjection U S)) n*occupationEmbedding n=
      occupationEmbedding n*occupationSupport (spanProjection U S) n := by
  rw [geometric_word,occupationSupport_rotated]
  simp only [Matrix.mul_assoc]
  rw [rotation_adjoint_embedding]
  rw [←Matrix.mul_assoc (wordSupport S n) (occupationEmbedding n),support_intertwine]
  simp only [←Matrix.mul_assoc]
  rw [occupationRotation_intertwine]

theorem edge_absorption (P Q : CMatrix A) (h : Q*P=P) :
    edgeProjection Q*edgeProjection P=edgeProjection P := by
  simp only [edgeProjection,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,h,Matrix.one_mul]

theorem occupationSupport_absorption (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    (Q : CMatrix A) (h : Q*spanProjection U S=spanProjection U S) (n : ℕ) :
    occupationSupport Q n*occupationSupport (spanProjection U S) n=
      occupationSupport (spanProjection U S) n := by
  calc
    _ = (occupationEmbedding (a:=A×A) n).conjTranspose*wordPower (edgeProjection Q) n*
        (occupationEmbedding n*occupationSupport (spanProjection U S) n) := by
      simp only [occupationSupport,Matrix.mul_assoc]
    _ = (occupationEmbedding (a:=A×A) n).conjTranspose*
        (wordPower (edgeProjection Q) n*wordPower (edgeProjection (spanProjection U S)) n)*
        occupationEmbedding n := by rw [←geometric_intertwine]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [←wordPower_mul,edge_absorption _ _ h]; rfl

theorem history_occupation_monotone {s : ℕ} (v : Fin s → EuclideanSpace ℂ A)
    (x : EuclideanSpace ℂ A) (n : ℕ) :
    occupationSupport (historyProjection (Fin.snoc v x)) n*occupationSupport (historyProjection v) n=
      occupationSupport (historyProjection v) n :=
  occupationSupport_absorption (historyUnitary v) (historyIndices v) _ (historyProjection_snoc v x) n

#print axioms occupationSupport_rotated
#print axioms geometric_intertwine
#print axioms history_occupation_monotone
end
end ICO.C6BosonicGeometricSupport
