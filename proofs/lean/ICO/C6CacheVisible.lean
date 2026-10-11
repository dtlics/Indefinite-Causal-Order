import ICO.C6GradedCache
import ICO.C6ReindexChannel
import ICO.C6PrivateIsometry

/-! Literal erasure of the finite private cache register. The visible channel
is defined on all matrices, and commutes with arbitrary known operations on
the query and visible memory, including rectangular isometries. -/
namespace ICO.C6CacheVisible
open QIT Matrix ICO.C6GradedCache ICO.C6CacheKnownOperation
  ICO.C6CacheReference ICO.C6CacheQueryBound ICO.C6CacheDecode ICO.C6SectorChannel ICO.C6MatrixCovariance
  ICO.MHSymmetric
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
universe u
variable {A M N : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

def sectorVisible (r : ℕ) : Channel (Cache (A := A) (M := M) r) (A×M) :=
  (Channel.traceOutLeft (TensorPowerProfile (A×A) r) (A×M)).comp
    (ICO.C6ReindexChannel.channel (externalEquiv r M).symm)

theorem sectorVisible_apply (r : ℕ) (X : CMatrix (Cache (A := A) (M := M) r)) :
    (sectorVisible r).map X =
      partialTraceA (X.submatrix (externalEquiv r M).symm (externalEquiv r M).symm) := by
  simp only [sectorVisible, Channel.comp, LinearMap.comp_apply,
    Channel.traceOutLeft_map, ICO.C6ReindexChannel.apply]

def visible (Q : ℕ) : Channel (Graded (A := A) Q M) (A×M) :=
  sectorChannel (fun r : Fin (Q+1) => sectorVisible (A := A) (M := M) r.val)

theorem visible_apply (Q : ℕ) (X : CMatrix (Graded (A := A) Q M)) :
    (visible Q).map X = ∑r : Fin (Q+1),
      (sectorVisible r.val).map ((embed Q r).conjTranspose*X*embed Q r) := by
  exact sector_apply _ X

theorem partialTraceA_known {R B C : Type*} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (K : Matrix C B ℂ) (X : CMatrix (R×B)) :
    partialTraceA (Matrix.kronecker (1 : CMatrix R) K*X*
      (Matrix.kronecker (1 : CMatrix R) K).conjTranspose) =
      K*partialTraceA X*K.conjTranspose := by
  have hb (r : R) := ICO.C6PrivateIsometry.sandwich_block K X r r
  ext c e
  change (∑r : R, (ICO.C6PrivateIsometry.block
    (Matrix.kronecker (1 : CMatrix R) K*X*
    (Matrix.kronecker (1 : CMatrix R) K).conjTranspose) r r) c e) = _
  simp_rw [hb]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, partialTraceA,
    ICO.C6PrivateIsometry.block, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext b
  rw [Finset.sum_comm]

theorem sectorVisible_known (r : ℕ) (K : Matrix (A×N) (A×M) ℂ)
    (X : CMatrix (Cache (A := A) (M := M) r)) :
    (sectorVisible r).map (externalLift r K*X*(externalLift r K).conjTranspose) =
      K*(sectorVisible r).map X*K.conjTranspose := by
  rw [sectorVisible_apply, sectorVisible_apply]
  have hs : (externalLift r K*X*(externalLift r K).conjTranspose).submatrix
      (externalEquiv r N).symm (externalEquiv r N).symm =
      Matrix.kronecker (1 : CMatrix (TensorPowerProfile (A×A) r)) K*
        X.submatrix (externalEquiv r M).symm (externalEquiv r M).symm*
        (Matrix.kronecker (1 : CMatrix (TensorPowerProfile (A×A) r)) K).conjTranspose := by
    rw [← Matrix.submatrix_mul_equiv _ _ _ (externalEquiv r M).symm,
      ← Matrix.submatrix_mul_equiv _ _ _ (externalEquiv r M).symm]
    simp only [externalLift, Matrix.conjTranspose_submatrix, Matrix.submatrix_submatrix,
      Function.comp_def, Equiv.apply_symm_apply]
    rfl
  rw [hs, partialTraceA_known]

#print axioms visible
#print axioms sectorVisible_known
end
end ICO.C6CacheVisible
