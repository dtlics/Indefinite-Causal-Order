import ICO.MemoryEmbedding

/-! # Preserve a one-query normal form under an embedding of private memory -/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.ClassicalDilation ICO.MemoryEmbedding

namespace ICO.LiftQueryMemory

set_option maxHeartbeats 250000
noncomputable section
universe u
variable {A B M N O : Type u}
variable [Fintype A] [Fintype B] [Fintype M] [Fintype N] [Fintype O]
variable [DecidableEq A] [DecidableEq B] [DecidableEq M] [DecidableEq N] [DecidableEq O]

def liftNormalForm (R : ICO.OneQueryTree.NormalForm B (A × M) O)
    (e : M ↪ N) (a₀ : A) (m₀ : M) : ICO.OneQueryTree.NormalForm B (A × N) O where
  Branch := R.Branch
  pre :=
    { op := fun j => queryEmbedding (A := A) e * R.pre.op j
      complete := by
        have hj (j : R.Branch) :
            (queryEmbedding (A := A) e * R.pre.op j).conjTranspose *
              (queryEmbedding (A := A) e * R.pre.op j) = (R.pre.op j).conjTranspose * R.pre.op j := by
          rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
            ← Matrix.mul_assoc (queryEmbedding (A := A) e).conjTranspose, queryEmbedding_isometry]
          simp
        simp_rw [hj]
        exact R.pre.complete }
  post := fun j => (R.post j).comp (queryRetraction e a₀ m₀)

theorem liftNormalForm_map (R : ICO.OneQueryTree.NormalForm B (A × M) O)
    (e : M ↪ N) (a₀ : A) (m₀ : M) (U : Matrix.unitaryGroup A ℂ) :
    ((liftNormalForm R e a₀ m₀).channel (oracleChannel U)).map =
      (R.channel (oracleChannel U)).map := by
  ext X i j
  simp only [ICO.OneQueryTree.NormalForm.channel_apply, liftNormalForm, Channel.comp,
    LinearMap.comp_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hs : (queryEmbedding (A := A) e * R.pre.op k) * X *
      (queryEmbedding (A := A) e * R.pre.op k).conjTranspose =
      queryEmbedding (A := A) e * (R.pre.op k * X * (R.pre.op k).conjTranspose) *
        (queryEmbedding (A := A) e).conjTranspose := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hs, queryRetraction_oracle]

end
end ICO.LiftQueryMemory

