import ICO.EmbeddedSwitch
import ICO.AllChannelDilation

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.QubitEmbedding ICO.EmbeddedSwitch

namespace ICO.EmbeddingChannels
set_option maxHeartbeats 700000
noncomputable section

variable {A B C M I : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype M] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq M] [DecidableEq I]

def krausChannel (K : I → Matrix B A ℂ) (hK : ∑ i,(K i)ᴴ * K i=1) : Channel A B where
  map := MatrixMap.ofKraus K
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using hK)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem tensor_mul (X : Matrix B A ℂ) (Y : Matrix A C ℂ) :
    Matrix.kronecker (X*Y) (1 : CMatrix M) =
      Matrix.kronecker X (1 : CMatrix M)*Matrix.kronecker Y (1 : CMatrix M) := by
  simpa [Matrix.kronecker] using Matrix.mul_kronecker_mul X Y (1 : CMatrix M) 1

theorem tensor_complete (K : I → Matrix B A ℂ) (hK : ∑ i,(K i)ᴴ * K i=1) :
    (∑ i,(Matrix.kronecker (K i) (1 : CMatrix M))ᴴ*
      Matrix.kronecker (K i) (1 : CMatrix M))=1 := by
  have hp (i : I) : (Matrix.kronecker (K i) (1 : CMatrix M))ᴴ*
      Matrix.kronecker (K i) (1 : CMatrix M)=Matrix.kronecker ((K i)ᴴ*K i) (1 : CMatrix M) := by
    have hs : (Matrix.kronecker (K i) (1 : CMatrix M))ᴴ =
        Matrix.kronecker (K i)ᴴ (1 : CMatrix M) := by
      simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker (K i) (1 : CMatrix M)
    rw [hs,← tensor_mul]
  simp_rw [hp]
  ext x y
  have ht := congrFun (congrFun hK x.1) y.1
  simp only [Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap_apply] at *
  rw [← Finset.sum_mul,ht]
  simp only [Matrix.one_apply,Prod.ext_iff,ite_and]
  split_ifs <;> simp_all

def withMemoryChannel (K : I → Matrix B A ℂ) (hK : ∑ i,(K i)ᴴ*K i=1) :
    Channel (A × M) (B × M) :=
  krausChannel (fun i => Matrix.kronecker (K i) (1 : CMatrix M)) (tensor_complete K hK)

def encodeChannel {d : Nat} (hd : 2≤d) : Channel (Fin 2) (Fin d) :=
  ICO.ClassicalDilation.isometryChannel (encode hd) (encode_isometry hd)

def decodeChannel {d : Nat} (hd : 2≤d) : Channel (Fin d) (Fin 2) :=
  krausChannel (decode hd) (decode_complete hd)

def encodeMemory {d : Nat} (hd : 2≤d) : Channel (Fin 2 × M) (Fin d × M) :=
  ICO.ClassicalDilation.isometryChannel (Matrix.kronecker (encode hd) (1 : CMatrix M))
    (ICO.ClassicalDilation.isometry_kronecker_one (encode hd) (encode_isometry hd))

def decodeMemory {d : Nat} (hd : 2≤d) : Channel (Fin d × M) (Fin 2 × M) :=
  withMemoryChannel (decode hd) (decode_complete hd)

def extendedFamily {d : Nat} (hd : 2≤d) (U : I → CMatrix (Fin 2)) :
    I × Option (Fin d) → CMatrix (Fin d) := fun ir => extend hd (U ir.1) ir.2

theorem extendedFamily_complete {d : Nat} (hd : 2≤d) (U : I → CMatrix (Fin 2))
    (hU : ∑ i,(U i)ᴴ*U i=1) :
    (∑ i,(extendedFamily hd U i)ᴴ*extendedFamily hd U i)=1 := by
  simpa [extendedFamily,Fintype.sum_prod_type] using extended_complete hd U hU

theorem extend_memory {d : Nat} (hd : 2≤d) (U : CMatrix (Fin 2)) (r : Option (Fin d)) :
    Matrix.kronecker (extend hd U r) (1 : CMatrix M) =
      Matrix.kronecker (encode hd) (1 : CMatrix M)*Matrix.kronecker U (1 : CMatrix M)*
        Matrix.kronecker (decode hd r) (1 : CMatrix M) := by
  simp only [extend,tensor_mul]

/-- A query to the extended higher-dimensional channel is implemented by the
fixed decoder, one qubit query, and the fixed encoder, even with private memory. -/
theorem extended_oracle_map {d : Nat} (hd : 2≤d) (U : I → CMatrix (Fin 2)) :
    ICO.AllChannelDilation.oracleMap (M:=M) (extendedFamily hd U) =
      (encodeMemory (M:=M) hd).map.comp
        ((ICO.AllChannelDilation.oracleMap (M:=M) U).comp (decodeMemory (M:=M) hd).map) := by
  ext X a b
  simp only [ICO.AllChannelDilation.oracleMap,extendedFamily,MatrixMap.ofKraus,
    LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_prod_type,extend_memory,
    encodeMemory,decodeMemory,withMemoryChannel,krausChannel,
    ICO.ClassicalDilation.isometryChannel,LinearMap.comp_apply,
    Matrix.conjTranspose_mul,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]
  simp

#print axioms extended_oracle_map
end
end ICO.EmbeddingChannels
