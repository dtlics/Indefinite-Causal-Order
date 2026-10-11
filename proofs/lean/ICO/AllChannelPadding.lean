import ICO.MemoryEmbedding
import ICO.AllChannelDilation

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.MemoryEmbedding ICO.OraclePadding ICO.ClassicalDilation

namespace ICO.AllChannelPadding
set_option maxHeartbeats 800000
noncomputable section
variable {A C M N I : Type} [Fintype A] [Fintype C] [Fintype M] [Fintype N] [Fintype I]
  [DecidableEq A] [DecidableEq C] [DecidableEq M] [DecidableEq N] [DecidableEq I]

theorem embedded_oracle (e : M ↪ N) (U : I → CMatrix A) (X : CMatrix (A × M)) :
    ICO.AllChannelDilation.oracleMap U
      (queryEmbedding e * X * (queryEmbedding e)ᴴ) =
        queryEmbedding e * ICO.AllChannelDilation.oracleMap U X * (queryEmbedding e)ᴴ := by
  simp only [ICO.AllChannelDilation.oracleMap,MatrixMap.ofKraus,
    LinearMap.coe_mk,AddHom.coe_mk,Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Matrix.kronecker (U i) (1 : CMatrix N) *
      (queryEmbedding e * X * (queryEmbedding e)ᴴ) *
      (Matrix.kronecker (U i) (1 : CMatrix N))ᴴ =
      (Matrix.kronecker (U i) (1 : CMatrix N) * queryEmbedding (A:=A) e) * X *
      (Matrix.kronecker (U i) (1 : CMatrix N) * queryEmbedding (A:=A) e)ᴴ by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]]
  rw [queryEmbedding_commutes]
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem retracted_oracle (e : M ↪ N) (a₀ : A) (m₀ : M)
    (U : I → CMatrix A) (X : CMatrix (A × M)) :
    (queryRetraction e a₀ m₀).map (ICO.AllChannelDilation.oracleMap U
      (queryEmbedding e * X * (queryEmbedding e)ᴴ)) =
        ICO.AllChannelDilation.oracleMap U X := by
  rw [embedded_oracle,queryRetraction_identity]

theorem complete_basis_trace (U : I → CMatrix A) (hU : ∑ i,(U i)ᴴ*U i=1) (a₀ : A) :
    (∑ i,(rankOneMatrix (U i *ᵥ basisVector a₀)).trace)=1 := by
  have h := congrFun (congrFun hU a₀) a₀
  simpa [rankOneMatrix_apply,basisVector,Matrix.trace,Matrix.diag_apply,
    Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.sum_apply,mul_comm] using h

/-- A real call to any trace-preserving noisy channel on a discarded register
has exactly the identity action on the retained arbitrary input. -/
theorem discarded_oracle_identity (U : I → CMatrix A)
    (hU : ∑ i,(U i)ᴴ*U i=1) (a₀ : A) (X : CMatrix C) :
    (discardChannel (A:=A) (C:=C)).map
      (ICO.AllChannelDilation.oracleMap U (pad a₀ * X * (pad a₀)ᴴ)) = X := by
  simp only [ICO.AllChannelDilation.oracleMap,MatrixMap.ofKraus,
    LinearMap.coe_mk,AddHom.coe_mk]
  rw [map_sum]
  have hterm (i : I) : (discardChannel (A:=A) (C:=C)).map
      (Matrix.kronecker (U i) (1 : CMatrix C) * (pad a₀ * X * (pad a₀)ᴴ) *
        (Matrix.kronecker (U i) (1 : CMatrix C))ᴴ) =
        (rankOneMatrix (U i *ᵥ basisVector a₀)).trace • X := by
    change MatrixMap.ofKraus (discardKraus (A:=A) (C:=C)) _ = _
    rw [discard_apply]
    have hs : Matrix.kronecker (U i) (1 : CMatrix C) * (pad a₀ * X * (pad a₀)ᴴ) *
        (Matrix.kronecker (U i) (1 : CMatrix C))ᴴ =
        tensorVector (U i *ᵥ basisVector a₀) * X * (tensorVector (U i *ᵥ basisVector a₀))ᴴ := by
      rw [← oracle_tensorVector]
      simp only [pad,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [hs,tensorVector_sandwich,partialTraceA_kronecker]
    rfl
  simp_rw [hterm]
  rw [← Finset.sum_smul,complete_basis_trace U hU,one_smul]

def queryEmbedChannel (e : M ↪ N) : Channel (A × M) (A × N) :=
  isometryChannel (queryEmbedding e) (queryEmbedding_isometry e)

theorem retracted_oracle_map (e : M ↪ N) (a₀ : A) (m₀ : M) (U : I → CMatrix A) :
    (queryRetraction e a₀ m₀).map.comp
      ((ICO.AllChannelDilation.oracleMap U).comp (queryEmbedChannel e).map) =
        ICO.AllChannelDilation.oracleMap U := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply,queryEmbedChannel,isometryChannel_apply]
  exact retracted_oracle e a₀ m₀ U X

#print axioms discarded_oracle_identity
#print axioms retracted_oracle_map
end
end ICO.AllChannelPadding
