import ICO.OrderedCircuit
import ICO.OneQueryTree

/-! # Retaining intermediate classical histories in an ordered circuit

A complete Kraus instrument is stacked into an isometry. Outcome-dependent
postprocessing is controlled on the retained history register, and its output
environment also retains that history. All completeness equations are proved.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression

namespace ICO.ClassicalDilation

set_option maxHeartbeats 200000
noncomputable section

universe u
variable {A M J K I O : Type u}
variable [Fintype A] [Fintype M] [Fintype J] [Fintype K] [Fintype I] [Fintype O]
variable [DecidableEq A] [DecidableEq M] [DecidableEq J] [DecidableEq K]
variable [DecidableEq I] [DecidableEq O]

def channelKraus (channel : Channel I O) : (I × O) → Matrix O I ℂ :=
  Classical.choose (MatrixMap.exists_kraus_of_choi_psd channel.map channel.completelyPositive)

theorem channelKraus_map (channel : Channel I O) :
    channel.map = MatrixMap.ofKraus (channelKraus channel) :=
  Classical.choose_spec (MatrixMap.exists_kraus_of_choi_psd channel.map channel.completelyPositive)

def channelIsometry (channel : Channel I O) : Matrix (O × (I × O)) I ℂ :=
  MatrixMap.krausStinespringMatrix (channelKraus channel)

theorem channelIsometry_complete (channel : Channel I O) :
    (channelIsometry channel).conjTranspose * channelIsometry channel = 1 := by
  apply MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
  apply MatrixMap.krausAdjoint_one_of_tracePreserving
  rw [← channelKraus_map]
  exact channel.tracePreserving

theorem channelIsometry_output (channel : Channel I O) (X : CMatrix I) :
    partialTraceB (channelIsometry channel * X * (channelIsometry channel).conjTranspose) =
      channel.map X := by
  rw [channelKraus_map]
  ext y y'
  simp [partialTraceB, MatrixMap.ofKraus, channelIsometry,
    MatrixMap.krausStinespringMatrix, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, mul_assoc]

def isometryChannel (W : Matrix O I ℂ) (hW : W.conjTranspose * W = 1) : Channel I O where
  map := MatrixMap.ofKraus (fun (_ : PUnit.{u + 1}) => W)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using hW)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem isometryChannel_apply (W : Matrix O I ℂ) (hW : W.conjTranspose * W = 1)
    (X : CMatrix I) : (isometryChannel W hW).map X = W * X * W.conjTranspose := by
  simp [isometryChannel, MatrixMap.ofKraus]

theorem isometry_kronecker_one (W : Matrix O I ℂ) (hW : W.conjTranspose * W = 1) :
    (Matrix.kronecker W (1 : CMatrix M)).conjTranspose *
      Matrix.kronecker W (1 : CMatrix M) = 1 := by
  have hstar : (Matrix.kronecker W (1 : CMatrix M)).conjTranspose =
      Matrix.kronecker W.conjTranspose (1 : CMatrix M) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker W (1 : CMatrix M)
  rw [hstar]
  calc
    _ = Matrix.kronecker (W.conjTranspose * W) ((1 : CMatrix M) * 1) :=
      (Matrix.mul_kronecker_mul W.conjTranspose W (1 : CMatrix M) 1).symm
    _ = 1 := by simp [hW]

def oracleChannel (U : Matrix.unitaryGroup A ℂ) : Channel (A × M) (A × M) :=
  isometryChannel (Matrix.kronecker (U : CMatrix A) (1 : CMatrix M))
    (isometry_kronecker_one _ (Matrix.UnitaryGroup.star_mul_self U))

theorem oracleChannel_apply (U : Matrix.unitaryGroup A ℂ) (X : CMatrix (A × M)) :
    (oracleChannel U).map X =
      Matrix.kronecker (U : CMatrix A) (1 : CMatrix M) * X *
        (Matrix.kronecker (U : CMatrix A) (1 : CMatrix M)).conjTranspose :=
  isometryChannel_apply _ _ X

/-- Store the actual instrument outcome alongside the private memory. -/
def stackMid (instrument : Instrument (A × M) (A × M) J) :
    Matrix (A × (M × J)) (A × M) ℂ :=
  fun amj bm => instrument.op amj.2.2 (amj.1, amj.2.1) bm

theorem stackMid_complete (instrument : Instrument (A × M) (A × M) J) :
    (stackMid instrument).conjTranspose * stackMid instrument = 1 := by
  ext i j
  have h := congrFun (congrFun instrument.complete i) j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type] at h
  change (∑ amj : A × (M × J),
    star (instrument.op amj.2.2 (amj.1, amj.2.1) i) *
      instrument.op amj.2.2 (amj.1, amj.2.1) j) = _
  simp only [Fintype.sum_prod_type]
  have hswap :
      (∑ a : A, ∑ m : M, ∑ k : J,
        star (instrument.op k (a, m) i) * instrument.op k (a, m) j) =
      ∑ k : J, ∑ a : A, ∑ m : M,
        star (instrument.op k (a, m) i) * instrument.op k (a, m) j := by
    simpa only [Fintype.sum_prod_type] using
      (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun (am : A × M) (k : J) =>
          star (instrument.op k am i) * instrument.op k am j))
  rw [hswap]
  exact h

/-- The final channel reads the classical history and retains it in the
discarded environment, preventing interference between different histories. -/
def controlledPost (W : J → Matrix (A × K) (A × M) ℂ) :
    Matrix (A × (K × J)) (A × (M × J)) ℂ :=
  fun fkj emj => if fkj.2.2 = emj.2.2 then W emj.2.2 (fkj.1, fkj.2.1) (emj.1, emj.2.1) else 0

theorem controlledPost_complete (W : J → Matrix (A × K) (A × M) ℂ)
    (hW : ∀ j, (W j).conjTranspose * W j = 1) :
    (controlledPost W).conjTranspose * controlledPost W = 1 := by
  ext i j
  rcases i with ⟨e, m, h⟩
  rcases j with ⟨e', m', h'⟩
  by_cases hh : h = h'
  · subst h'
    have ht := congrFun (congrFun (hW h) (e, m)) (e', m')
    simpa [controlledPost, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, apply_ite, Matrix.one_apply, Prod.ext_iff] using ht
  · simp [controlledPost, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, apply_ite, Matrix.one_apply, Prod.ext_iff, hh, eq_comm]

theorem controlledPost_oracle_entry (W : J → Matrix (A × K) (A × M) ℂ)
    (V : CMatrix A) (k : K) (j h : J) (f e : A) (m : M) :
    (ICO.OrderedCircuit.postKraus (controlledPost W) (k, j) *
      Matrix.kronecker V (1 : CMatrix (M × J))) f (e, (m, h)) =
      if j = h then
        (ICO.OrderedCircuit.postKraus (W j) k * Matrix.kronecker V (1 : CMatrix M)) f (e, m)
      else 0 := by
  rw [ICO.OrderedCircuit.mul_kronecker_identity_entry]
  by_cases hj : j = h
  · subst h
    simp only [ite_true]
    rw [ICO.OrderedCircuit.mul_kronecker_identity_entry]
    simp [ICO.OrderedCircuit.postKraus, controlledPost]
  · simp [ICO.OrderedCircuit.postKraus, controlledPost, hj]

theorem controlledPost_oracle_stack (W : J → Matrix (A × K) (A × M) ℂ)
    (instrument : Instrument (A × M) (A × M) J) (V : CMatrix A) (k : K) (j : J) :
    ICO.OrderedCircuit.postKraus (controlledPost W) (k, j) *
      Matrix.kronecker V (1 : CMatrix (M × J)) * stackMid instrument =
        ICO.OrderedCircuit.postKraus (W j) k * Matrix.kronecker V (1 : CMatrix M) *
          instrument.op j := by
  ext f i
  conv_lhs => rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp_rw [controlledPost_oracle_entry]
  conv_rhs => rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [stackMid, Fintype.sum_prod_type, ite_mul]

theorem circuitKraus_controlled (pre : Matrix (A × M) A ℂ)
    (instrument : Instrument (A × M) (A × M) J)
    (W : J → Matrix (A × K) (A × M) ℂ) (U V : CMatrix A) (k : K) (j : J) :
    ICO.OrderedCircuit.circuitKraus pre (stackMid instrument) (controlledPost W) U V (k, j) =
      ICO.OrderedCircuit.postKraus (W j) k * Matrix.kronecker V (1 : CMatrix M) *
        instrument.op j * Matrix.kronecker U (1 : CMatrix M) * pre := by
  unfold ICO.OrderedCircuit.circuitKraus
  rw [controlledPost_oracle_stack]

def normalMid (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A) :
    Matrix (A × (M × R.Branch)) (A × M) ℂ := stackMid R.pre

def normalPost (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A) :
    Matrix (A × (((A × M) × A) × R.Branch)) (A × (M × R.Branch)) ℂ :=
  controlledPost (fun j => channelIsometry (R.post j))

theorem normalMid_complete (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A) :
    (normalMid R).conjTranspose * normalMid R = 1 := stackMid_complete R.pre

theorem normalPost_complete (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A) :
    (normalPost R).conjTranspose * normalPost R = 1 :=
  controlledPost_complete _ (fun j => channelIsometry_complete (R.post j))

/-- Retaining the extracted classical history realizes the entire adaptive
continuation by the actual ordered pre/mid/post circuit, for every oracle pair. -/
theorem normalForm_circuit_map (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A)
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (X : CMatrix A) :
    MatrixMap.ofKraus
      (ICO.OrderedCircuit.circuitKraus pre (normalMid R) (normalPost R)
        (U : CMatrix A) (V : CMatrix A)) X =
      (R.channel (oracleChannel V)).map
        ((oracleChannel U).map (pre * X * pre.conjTranspose)) := by
  unfold normalMid normalPost
  have hfamily :
      ICO.OrderedCircuit.circuitKraus pre (stackMid R.pre)
        (controlledPost (fun j => channelIsometry (R.post j)))
        (U : CMatrix A) (V : CMatrix A) =
      (fun kj => ICO.OrderedCircuit.postKraus (channelIsometry (R.post kj.2)) kj.1 *
        Matrix.kronecker (V : CMatrix A) (1 : CMatrix M) * R.pre.op kj.2 *
          Matrix.kronecker (U : CMatrix A) (1 : CMatrix M) * pre) := by
    funext kj
    exact circuitKraus_controlled pre R.pre _ _ _ kj.1 kj.2
  rw [hfamily]
  rw [ICO.OneQueryTree.NormalForm.channel_apply, oracleChannel_apply]
  simp_rw [oracleChannel_apply, channelKraus_map]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rfl

end
end ICO.ClassicalDilation
