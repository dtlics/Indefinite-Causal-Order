import ICO.OraclePadding

/-! # Finite query-memory embeddings with a channel retraction

An injection of memory basis indices induces an isometry. Its inverse on the
image is extended to a trace-preserving channel by resetting the orthogonal
complement to a fixed basis state.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.ClassicalDilation

namespace ICO.MemoryEmbedding

set_option maxHeartbeats 300000
noncomputable section
universe u
variable {A M N : Type u}
variable [Fintype A] [Fintype M] [Fintype N]
variable [DecidableEq A] [DecidableEq M] [DecidableEq N]

def embedding (e : M ↪ N) : Matrix N M ℂ := fun n m => if n = e m then 1 else 0

theorem embedding_isometry (e : M ↪ N) :
    (embedding e).conjTranspose * embedding e = 1 := by
  ext i j
  simp [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    apply_ite, ite_mul, mul_ite, e.injective.eq_iff]
  aesop

def retractKraus (e : M ↪ N) (m₀ : M) : Option N → Matrix M N ℂ
  | none => (embedding e).conjTranspose
  | some n => Matrix.single m₀ n (1 : ℂ) * (1 - embedding e * (embedding e).conjTranspose)

theorem retract_complete (e : M ↪ N) (m₀ : M) :
    (∑ k : Option N, (retractKraus e m₀ k).conjTranspose * retractKraus e m₀ k) = 1 := by
  have hsingle (n : N) : (Matrix.single m₀ n (1 : ℂ)).conjTranspose *
      Matrix.single m₀ n (1 : ℂ) = Matrix.single n n (1 : ℂ) := by
    simp [Matrix.single_mul_single_same]
  have hP : (embedding e * (embedding e).conjTranspose) *
      (embedding e * (embedding e).conjTranspose) = embedding e * (embedding e).conjTranspose := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (embedding e).conjTranspose,
      embedding_isometry]
    simp
  simp only [Fintype.sum_option, retractKraus, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose]
  have hs : (∑ n : N,
      (1 - embedding e * (embedding e).conjTranspose) *
        (Matrix.single m₀ n (1 : ℂ)).conjTranspose *
          (Matrix.single m₀ n (1 : ℂ) * (1 - embedding e * (embedding e).conjTranspose))) =
      (1 - embedding e * (embedding e).conjTranspose) *
        (1 - embedding e * (embedding e).conjTranspose) := by
    simp only [← Matrix.mul_assoc]
    simp_rw [Matrix.mul_assoc (1 - embedding e * (embedding e).conjTranspose)
      (Matrix.single m₀ _ (1 : ℂ)).conjTranspose, hsingle]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  rw [hs]
  simp [Matrix.mul_sub, Matrix.sub_mul, hP]

theorem retractKraus_embedding (e : M ↪ N) (m₀ : M) (k : Option N) :
    retractKraus e m₀ k * embedding e = if k = none then 1 else 0 := by
  cases k with
  | none => simpa [retractKraus] using embedding_isometry e
  | some n =>
    simp only [retractKraus, Option.some_ne_none, ite_false, Matrix.mul_assoc,
      Matrix.sub_mul, Matrix.one_mul, embedding_isometry, Matrix.mul_one, sub_self,
      Matrix.mul_zero]

def retractChannel (e : M ↪ N) (m₀ : M) : Channel N M where
  map := MatrixMap.ofKraus (retractKraus e m₀)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using retract_complete e m₀)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem retract_embedding_identity (e : M ↪ N) (m₀ : M) (X : CMatrix M) :
    (retractChannel e m₀).map (embedding e * X * (embedding e).conjTranspose) = X := by
  unfold retractChannel MatrixMap.ofKraus
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have hterm (k : Option N) :
      retractKraus e m₀ k * (embedding e * X * (embedding e).conjTranspose) *
        (retractKraus e m₀ k).conjTranspose = if k = none then X else 0 := by
    rw [show retractKraus e m₀ k * (embedding e * X * (embedding e).conjTranspose) *
        (retractKraus e m₀ k).conjTranspose =
      (retractKraus e m₀ k * embedding e) * X *
        (retractKraus e m₀ k * embedding e).conjTranspose by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [retractKraus_embedding]
    split <;> simp_all
  simp_rw [hterm]
  simp

def queryEmbedding (e : M ↪ N) : Matrix (A × N) (A × M) ℂ :=
  Matrix.kronecker (1 : CMatrix A) (embedding e)

theorem queryEmbedding_isometry (e : M ↪ N) :
    (queryEmbedding (A := A) e).conjTranspose * queryEmbedding (A := A) e =
      (1 : CMatrix (A × M)) := by
  have hs : (queryEmbedding (A := A) e).conjTranspose =
      Matrix.kronecker (1 : CMatrix A) (embedding e).conjTranspose := by
    ext i j
    by_cases hij : i.1 = j.1
    all_goals
    simp [queryEmbedding, Matrix.conjTranspose_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, eq_comm, apply_ite, hij]
  rw [hs, queryEmbedding]
  calc
    _ = Matrix.kronecker ((1 : CMatrix A) * 1)
        ((embedding e).conjTranspose * embedding e) :=
      (Matrix.mul_kronecker_mul (1 : CMatrix A) 1 (embedding e).conjTranspose (embedding e)).symm
    _ = _ := by simp [embedding_isometry]

theorem queryEmbedding_commutes (e : M ↪ N) (U : CMatrix A) :
    Matrix.kronecker U (1 : CMatrix N) * queryEmbedding e =
      queryEmbedding e * Matrix.kronecker U (1 : CMatrix M) := by
  unfold queryEmbedding
  calc
    _ = Matrix.kronecker (U * 1) ((1 : CMatrix N) * embedding e) :=
      (Matrix.mul_kronecker_mul U (1 : CMatrix A) (1 : CMatrix N) (embedding e)).symm
    _ = Matrix.kronecker ((1 : CMatrix A) * U) (embedding e * (1 : CMatrix M)) := by simp
    _ = _ := Matrix.mul_kronecker_mul (1 : CMatrix A) U (embedding e) (1 : CMatrix M)

def queryInjection (e : M ↪ N) : A × M ↪ A × N where
  toFun am := (am.1, e am.2)
  inj' := by
    intro x y h
    exact Prod.ext (congrArg (fun z : A × N => z.1) h)
      (e.injective (congrArg (fun z : A × N => z.2) h))

theorem embedding_queryInjection (e : M ↪ N) :
    embedding (queryInjection (A := A) e) = queryEmbedding e := by
  ext i j
  simp [embedding, queryInjection, queryEmbedding, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, ite_and]
  split <;> split <;> simp_all

def queryRetraction (e : M ↪ N) (a₀ : A) (m₀ : M) : Channel (A × N) (A × M) :=
  retractChannel (queryInjection e) (a₀, m₀)

theorem queryRetraction_identity (e : M ↪ N) (a₀ : A) (m₀ : M)
    (X : CMatrix (A × M)) :
    (queryRetraction e a₀ m₀).map
      (queryEmbedding e * X * (queryEmbedding e).conjTranspose) = X := by
  rw [← embedding_queryInjection]
  exact retract_embedding_identity (queryInjection e) (a₀, m₀) X

theorem queryRetraction_oracle (e : M ↪ N) (a₀ : A) (m₀ : M)
    (U : Matrix.unitaryGroup A ℂ) (X : CMatrix (A × M)) :
    (queryRetraction e a₀ m₀).map ((oracleChannel U).map
      (queryEmbedding e * X * (queryEmbedding e).conjTranspose)) =
      (oracleChannel U).map X := by
  have hs : (oracleChannel U).map
      (queryEmbedding e * X * (queryEmbedding e).conjTranspose) =
      queryEmbedding e * ((oracleChannel U).map X) * (queryEmbedding e).conjTranspose := by
    simp only [oracleChannel_apply]
    let L : CMatrix (A × N) := Matrix.kronecker (U : CMatrix A) 1
    let B : CMatrix (A × M) := Matrix.kronecker (U : CMatrix A) 1
    let E : Matrix (A × N) (A × M) ℂ := queryEmbedding e
    change L * (E * X * E.conjTranspose) * L.conjTranspose =
      E * (B * X * B.conjTranspose) * E.conjTranspose
    have hcomm : L * E = E * B := queryEmbedding_commutes e (U : CMatrix A)
    calc
      _ = ((L * E) * X) * (L * E).conjTranspose := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hcomm]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hs, queryRetraction_identity]

end
end ICO.MemoryEmbedding

