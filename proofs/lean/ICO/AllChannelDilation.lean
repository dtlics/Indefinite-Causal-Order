import ICO.ClassicalDilation

/-! Rectangular-output Stinespring realizations of adaptive ordered circuits.
The input, oracle register, and retained output may all be different spaces;
the oracle interface accepts arbitrary complete Kraus families. -/
open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.ClassicalDilation

namespace ICO.AllChannelDilation
set_option maxHeartbeats 600000
noncomputable section
universe u
variable {A M N J K P O I T : Type u}
variable [Fintype A] [Fintype M] [Fintype N] [Fintype J] [Fintype K]
  [Fintype P] [Fintype O] [Fintype I] [Fintype T]
variable [DecidableEq A] [DecidableEq M] [DecidableEq N] [DecidableEq J]
  [DecidableEq K] [DecidableEq P] [DecidableEq O] [DecidableEq I] [DecidableEq T]

def postKraus (post : Matrix (O × K) (A × N) ℂ) (k : K) : Matrix O (A × N) ℂ :=
  fun f en => post (f,k) en

def circuitKraus (pre : Matrix (A × M) P ℂ)
    (mid : Matrix (A × N) (A × M) ℂ) (post : Matrix (O × K) (A × N) ℂ)
    (U V : CMatrix A) (k : K) : Matrix O P ℂ :=
  postKraus post k * Matrix.kronecker V (1 : CMatrix N) * mid *
    Matrix.kronecker U (1 : CMatrix M) * pre

def controlledPost (W : J → Matrix (O × K) (A × M) ℂ) :
    Matrix (O × (K × J)) (A × (M × J)) ℂ :=
  fun fkj emj => if fkj.2.2 = emj.2.2 then W emj.2.2 (fkj.1,fkj.2.1) (emj.1,emj.2.1) else 0

theorem controlledPost_complete (W : J → Matrix (O × K) (A × M) ℂ)
    (hW : ∀ j, (W j)ᴴ * W j = 1) : (controlledPost W)ᴴ * controlledPost W = 1 := by
  ext i j
  rcases i with ⟨e,m,h⟩
  rcases j with ⟨e',m',h'⟩
  by_cases hh : h=h'
  · subst h'
    have ht := congrFun (congrFun (hW h) (e,m)) (e',m')
    simpa [controlledPost,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_prod_type,apply_ite,Matrix.one_apply,Prod.ext_iff] using ht
  · simp [controlledPost,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_prod_type,apply_ite,Matrix.one_apply,Prod.ext_iff,hh,eq_comm]

theorem controlledPost_oracle_entry (W : J → Matrix (O × K) (A × M) ℂ)
    (V : CMatrix A) (k : K) (j h : J) (f : O) (e : A) (m : M) :
    (postKraus (controlledPost W) (k,j) * Matrix.kronecker V (1 : CMatrix (M × J))) f (e,(m,h)) =
      if j=h then (postKraus (W j) k * Matrix.kronecker V (1 : CMatrix M)) f (e,m) else 0 := by
  rw [ICO.OrderedCircuit.mul_kronecker_identity_entry]
  by_cases hj : j=h
  · subst h
    simp only [ite_true]
    rw [ICO.OrderedCircuit.mul_kronecker_identity_entry]
    simp [postKraus,controlledPost]
  · simp [postKraus,controlledPost,hj]

theorem controlledPost_oracle_stack (W : J → Matrix (O × K) (A × M) ℂ)
    (instrument : Instrument (A × M) (A × M) J) (V : CMatrix A) (k : K) (j : J) :
    postKraus (controlledPost W) (k,j) * Matrix.kronecker V (1 : CMatrix (M × J)) *
      stackMid instrument =
        postKraus (W j) k * Matrix.kronecker V (1 : CMatrix M) * instrument.op j := by
  ext f i
  conv_lhs => rw [Matrix.mul_apply,Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp_rw [controlledPost_oracle_entry]
  conv_rhs => rw [Matrix.mul_apply,Fintype.sum_prod_type]
  simp [stackMid,Fintype.sum_prod_type,ite_mul]

theorem circuitKraus_controlled (pre : Matrix (A × M) P ℂ)
    (instrument : Instrument (A × M) (A × M) J)
    (W : J → Matrix (O × K) (A × M) ℂ) (U V : CMatrix A) (k : K) (j : J) :
    circuitKraus pre (stackMid instrument) (controlledPost W) U V (k,j) =
      postKraus (W j) k * Matrix.kronecker V (1 : CMatrix M) * instrument.op j *
        Matrix.kronecker U (1 : CMatrix M) * pre := by
  unfold circuitKraus
  rw [controlledPost_oracle_stack]

def normalMid (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) O) :
    Matrix (A × (M × R.Branch)) (A × M) ℂ := stackMid R.pre

def normalPost (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) O) :
    Matrix (O × (((A × M) × O) × R.Branch)) (A × (M × R.Branch)) ℂ :=
  controlledPost (fun j => channelIsometry (R.post j))

theorem normalMid_complete (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) O) :
    (normalMid R)ᴴ * normalMid R = 1 := stackMid_complete R.pre

theorem normalPost_complete (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) O) :
    (normalPost R)ᴴ * normalPost R = 1 :=
  controlledPost_complete _ (fun j => channelIsometry_complete (R.post j))

def oracleMap (U : I → CMatrix A) : MatrixMap (A × M) (A × M) :=
  MatrixMap.ofKraus (fun i => Matrix.kronecker (U i) (1 : CMatrix M))

theorem oracle_complete (U : I → CMatrix A) (hU : ∑ i, (U i)ᴴ * U i = 1) :
    (∑ i, (Matrix.kronecker (U i) (1 : CMatrix M))ᴴ *
      Matrix.kronecker (U i) (1 : CMatrix M)) = 1 := by
  have hp (i : I) : (Matrix.kronecker (U i) (1 : CMatrix M))ᴴ *
      Matrix.kronecker (U i) (1 : CMatrix M) = Matrix.kronecker ((U i)ᴴ * U i) (1 : CMatrix M) := by
    have hs : (Matrix.kronecker (U i) (1 : CMatrix M))ᴴ =
        Matrix.kronecker (U i)ᴴ (1 : CMatrix M) := by
      simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker (U i) (1 : CMatrix M)
    rw [hs]
    simpa using (Matrix.mul_kronecker_mul (U i)ᴴ (U i) (1 : CMatrix M) 1).symm
  simp_rw [hp]
  ext x y
  have ht := congrFun (congrFun hU x.1) y.1
  simp only [Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap_apply] at *
  rw [← Finset.sum_mul,ht]
  simp only [Matrix.one_apply,Prod.ext_iff,ite_and]
  split_ifs <;> simp_all

def oracleChannel (U : I → CMatrix A) (hU : ∑ i, (U i)ᴴ * U i = 1) :
    Channel (A × M) (A × M) where
  map := oracleMap U
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using oracle_complete (M:=M) U hU)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

/-- A single pair of arbitrary Kraus matrices, with the classical history
retained in the discarded environment. No unitarity hypothesis is used. -/
theorem normalForm_kraus_map (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) O)
    (pre : Matrix (A × M) P ℂ) (U V : CMatrix A) (X : CMatrix P) :
    MatrixMap.ofKraus (circuitKraus pre (normalMid R) (normalPost R) U V) X =
      ∑ j : R.Branch, (R.post j).map
        (Matrix.kronecker V (1 : CMatrix M) * R.pre.op j * Matrix.kronecker U (1 : CMatrix M) *
          pre * X * preᴴ * (Matrix.kronecker U (1 : CMatrix M))ᴴ * (R.pre.op j)ᴴ *
            (Matrix.kronecker V (1 : CMatrix M))ᴴ) := by
  unfold normalMid normalPost
  have hfamily : circuitKraus pre (stackMid R.pre)
      (controlledPost (fun j => channelIsometry (R.post j))) U V =
      (fun kj => postKraus (channelIsometry (R.post kj.2)) kj.1 *
        Matrix.kronecker V (1 : CMatrix M) * R.pre.op kj.2 *
          Matrix.kronecker U (1 : CMatrix M) * pre) := by
    funext kj
    exact circuitKraus_controlled pre R.pre _ _ _ kj.1 kj.2
  rw [hfamily]
  simp_rw [channelKraus_map]
  simp only [MatrixMap.ofKraus,LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rfl

theorem normalForm_channel_map (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) O)
    (pre : Matrix (A × M) P ℂ) (U : I → CMatrix A) (V : T → CMatrix A)
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) (X : CMatrix P) :
    (∑ i, ∑ j, MatrixMap.ofKraus
      (circuitKraus pre (normalMid R) (normalPost R) (U i) (V j)) X) =
      (R.channel (oracleChannel V hV)).map
        ((oracleChannel U hU).map (pre * X * preᴴ)) := by
  simp_rw [normalForm_kraus_map]
  rw [ICO.OneQueryTree.NormalForm.channel_apply]
  simp only [oracleChannel,oracleMap,MatrixMap.ofKraus,LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.mul_sum,Matrix.sum_mul,map_sum,Matrix.mul_assoc]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  exact Finset.sum_comm

#print axioms normalForm_channel_map
end
end ICO.AllChannelDilation
