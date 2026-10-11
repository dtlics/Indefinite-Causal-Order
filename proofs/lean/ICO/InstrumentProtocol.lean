import ICO.ProtocolControl
import ICO.FirstLabelledQuery

namespace ICO.SequentialIsometry
open Matrix QIT ICO.ControlledIsometry ICO.InstrumentCompression
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 1800000
variable {A B M O I J : Type u} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype M] [DecidableEq M]
  [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

def instrumentStack (instrument : Instrument B (A×M) J) :
    Matrix (A×((j:J)×M)) B ℂ :=
  fun o b => instrument.op o.2.1 (o.1,o.2.2) b

theorem instrumentStack_isometry (instrument : Instrument B (A×M) J) :
    (instrumentStack instrument).conjTranspose*instrumentStack instrument=1 := by
  ext b c
  have h := congrFun (congrFun instrument.complete b) c
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type] at h
  simp only [instrumentStack,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,Fintype.sum_sigma]
  rw [Finset.sum_comm]
  exact h

theorem instrumentStack_block (instrument : Instrument B (A×M) J) (X : CMatrix B)
    (j:J) (a b:A) (m n:M) :
    (instrumentStack instrument*X*(instrumentStack instrument).conjTranspose)
      (a,⟨j,m⟩) (b,⟨j,n⟩) =
    (instrument.op j*X*(instrument.op j).conjTranspose) (a,m) (b,n) := rfl

theorem instrument_oracle_block (instrument : Instrument B (A×M) J)
    (U : I → CMatrix A) (X : CMatrix B) (j:J) :
    (permutation (distrib A (fun _ : J => M)) *
      ICO.AllChannelDilation.oracleMap U
        (instrumentStack instrument*X*(instrumentStack instrument).conjTranspose) *
      (permutation (distrib A (fun _ : J => M))).conjTranspose).submatrix (Sigma.mk j) (Sigma.mk j) =
    ICO.AllChannelDilation.oracleMap U (branchMap instrument j X) := by
  rw [permutation_sandwich]
  ext x y
  simp only [Matrix.submatrix_apply,distrib,Equiv.coe_fn_symm_mk]
  rw [ICO.OracleLift.oracleMap_lift,ICO.OracleLift.oracleMap_lift,branchMap_apply]
  rfl

/-- The instrument outcome is stored coherently in public memory. The controlled
continuation retains it through the final erasure, which reproduces the original
classical branch sum even though off-diagonal amplitudes were never measured. -/
def Protocol.instrumentQuery {q : ℕ} (instrument : Instrument B (A×M) J)
    (tail : J → Protocol A (A×M) O q) : Protocol A B O (q+1) :=
  .query (instrumentStack instrument) (instrumentStack_isometry instrument)
    ((Protocol.controlled tail).precompose (permutation (distrib A (fun _ : J => M)))
      (permutation_isometry _))

theorem Protocol.instrumentQuery_map {q : ℕ} (instrument : Instrument B (A×M) J)
    (tail : J → Protocol A (A×M) O q) (U : I → CMatrix A) (X : CMatrix B) :
    (Protocol.instrumentQuery instrument tail).map U X =
      ∑ j, (tail j).map U (ICO.AllChannelDilation.oracleMap U (branchMap instrument j X)) := by
  change (((Protocol.controlled tail).precompose
    (permutation (distrib A (fun _ : J => M))) (permutation_isometry _)).map U)
      (ICO.AllChannelDilation.oracleMap U (singleMap (instrumentStack instrument) X)) = _
  rw [Protocol.precompose_map]
  simp only [LinearMap.comp_apply,singleMap_apply]
  rw [Protocol.controlled_map]
  apply Finset.sum_congr rfl
  intro j hj
  rw [instrument_oracle_block]

#print axioms Protocol.instrumentQuery_map
end
end ICO.SequentialIsometry
