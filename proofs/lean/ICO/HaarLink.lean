import ICO.HaarFrame

/-!+# Positive linking of the two independent Haar frames

The link matrix contracts the two intermediate target wires against the
unnormalized Bell bra. Its entries and the resulting positive sandwich are
defined explicitly, so positivity of the link is a proved matrix property.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.CausalReverse ICO.HaarFrame

namespace ICO.HaarLink

set_option maxHeartbeats 1500000

noncomputable section

universe u v w

/-- A finite sum over a private wire, as a rectangular contraction matrix. -/
def contractionMatrix {I : Type u} {T : Type v} {J : Type w}
    [Fintype T] [DecidableEq J] (wire : I → T → J) : Matrix I J ℂ :=
  fun i j => ∑ t : T, if wire i t = j then 1 else 0

theorem contraction_mul_apply {I : Type u} {T : Type v} {J : Type w}
    {K : Type*} [Fintype T] [Fintype J] [DecidableEq J]
    (wire : I → T → J) (M : Matrix J K ℂ) (i : I) (j : K) :
    (contractionMatrix wire * M) i j = ∑ t : T, M (wire i t) j := by
  simp only [Matrix.mul_apply, contractionMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

theorem mul_contraction_adjoint_apply {I : Type u} {T : Type v} {J : Type w}
    {K : Type*} [Fintype T] [Fintype J] [DecidableEq J]
    (wire : I → T → J) (M : Matrix K J ℂ) (i : K) (j : I) :
    (M * (contractionMatrix wire).conjTranspose) i j =
      ∑ t : T, M i (wire j t) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, contractionMatrix,
    star_sum, apply_ite, star_one, star_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp

/-- The sandwich entry is the double sum over the connected ket and bra wires. -/
theorem contraction_sandwich_apply {I : Type u} {T : Type v} {J : Type w}
    [Fintype T] [Fintype J] [DecidableEq J]
    (wire : I → T → J) (M : CMatrix J) (i j : I) :
    (contractionMatrix wire * M * (contractionMatrix wire).conjTranspose) i j =
      ∑ t : T, ∑ s : T, M (wire i t) (wire j s) := by
  rw [mul_contraction_adjoint_apply]
  simp_rw [contraction_mul_apply]
  rw [Finset.sum_comm]

/-- Sandwiching by a fixed rectangular matrix preserves Loewner order. -/
theorem sandwich_mono {I : Type u} {J : Type v}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : Matrix I J ℂ) {X Y : CMatrix J} (hXY : X ≤ Y) :
    L * X * L.conjTranspose ≤ L * Y * L.conjTranspose := by
  rw [Matrix.le_iff] at hXY ⊢
  convert hXY.mul_mul_conjTranspose_same L using 1
  simp [Matrix.mul_sub, Matrix.sub_mul]

variable {A : Type u} [Fintype A] [DecidableEq A]

abbrev FrameWires (A : Type u) := (A × A) × (A × A)

/-- Place the six external wires and common intermediate value `t` into the
two frames: `((a,t),(b,f))` for `U` and `((c,P),(e,t))` for `V`. -/
def frameWire (i : SixWires A) (t : A) : FrameWires A × FrameWires A :=
  (((i.1.1.2, t), (i.1.1.1.2, i.2)),
    ((i.1.1.1.1.2, i.1.1.1.1.1), (i.1.2, t)))

/-- Unnormalized Bell-bra contraction on the two intermediate target wires. -/
def linkMatrix : Matrix (SixWires A) (FrameWires A × FrameWires A) ℂ :=
  contractionMatrix frameWire

def link (M : CMatrix (FrameWires A × FrameWires A)) : CMatrix (SixWires A) :=
  linkMatrix * M * linkMatrix.conjTranspose

theorem link_apply (M : CMatrix (FrameWires A × FrameWires A)) (i j : SixWires A) :
    link M i j = ∑ t : A, ∑ s : A, M (frameWire i t) (frameWire j s) :=
  contraction_sandwich_apply frameWire M i j

theorem link_pos {M : CMatrix (FrameWires A × FrameWires A)} (hM : M.PosSemidef) :
    (link M).PosSemidef := hM.mul_mul_conjTranspose_same linkMatrix

theorem link_mono {M N : CMatrix (FrameWires A × FrameWires A)} (hMN : M ≤ N) :
    link M ≤ link N := sandwich_mono linkMatrix hMN

theorem link_add (M N : CMatrix (FrameWires A × FrameWires A)) :
    link (M + N) = link M + link N := by
  simp [link, Matrix.mul_add, Matrix.add_mul]

theorem link_smul (z : ℂ) (M : CMatrix (FrameWires A × FrameWires A)) :
    link (z • M) = z • link M := by
  simp [link, Matrix.mul_smul, Matrix.smul_mul]

/-- The leading Bell-pair part of one Haar frame. -/
def frameMain [Nonempty A] : CMatrix (FrameWires A) :=
  Matrix.kronecker (bellMatrix A) (bellMatrix A)

def frameUpper [Nontrivial A] : CMatrix (FrameWires A) :=
  frameMain + (frameBeta A : ℂ) • (1 : CMatrix (FrameWires A))

theorem frameMain_pos [Nonempty A] : (frameMain (A := A)).PosSemidef :=
  (bellMatrix_pos (A := A)).kronecker (bellMatrix_pos (A := A))

theorem haarFrame_pos [Nontrivial A] : (haarFrame (A := A)).PosSemidef := by
  have hb : (0 : ℂ) ≤ (frameBeta A : ℂ) := by
    exact_mod_cast frameBeta_nonneg (A := A)
  have hc : (1 - bellMatrix A).PosSemidef := Matrix.le_iff.mp (bellMatrix_le_one (A := A))
  rw [haarFrame_eq_bell_complement (A := A), ← frameBeta_cast (A := A)]
  exact (frameMain_pos (A := A)).add ((hc.kronecker hc).smul hb)

theorem frameUpper_pos [Nontrivial A] : (frameUpper (A := A)).PosSemidef := by
  have hb : (0 : ℂ) ≤ (frameBeta A : ℂ) := by
    exact_mod_cast frameBeta_nonneg (A := A)
  exact (frameMain_pos (A := A)).add (Matrix.PosSemidef.one.smul hb)

theorem kronecker_mono_left {I : Type*} {J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X Y : CMatrix I} {T : CMatrix J} (hXY : X ≤ Y) (hT : T.PosSemidef) :
    Matrix.kronecker X T ≤ Matrix.kronecker Y T := by
  rw [Matrix.le_iff] at hXY ⊢
  convert hXY.kronecker hT using 1
  ext i j
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, sub_mul]

/-- Independence is represented by the tensor product of the two frames;
the product can be bounded before applying the positive link. -/
theorem two_frames_le_upper [Nontrivial A] :
    Matrix.kronecker (haarFrame (A := A)) (haarFrame (A := A)) ≤
      Matrix.kronecker (frameUpper (A := A)) (frameUpper (A := A)) := by
  have h : haarFrame (A := A) ≤ frameUpper (A := A) := haarFrame_le_bell_add_identity (A := A)
  exact (kronecker_mono_right (haarFrame_pos (A := A)) h).trans
    (kronecker_mono_left h (frameUpper_pos (A := A)))

/-- The sole Bell test on the output pair `(b,f)`. -/
def singleBellBF [Nonempty A] : CMatrix (SixWires A) :=
  (Matrix.kronecker (1 : CMatrix (FrameWires A)) (bellMatrix A)).submatrix
    (bellPairing A) (bellPairing A)

/-- The sole Bell test on the input pair `(P,c)`. -/
def singleBellPC [Nonempty A] : CMatrix (SixWires A) :=
  (Matrix.kronecker (Matrix.kronecker (bellMatrix A) (1 : CMatrix (A × A)))
    (1 : CMatrix (A × A))).submatrix (bellPairing A) (bellPairing A)

theorem singleBellBF_le_one [Nonempty A] : singleBellBF (A := A) ≤ 1 := by
  have h := submatrix_mono
    (kronecker_mono_right (Matrix.PosSemidef.one : (1 : CMatrix (FrameWires A)).PosSemidef)
      (bellMatrix_le_one (A := A))) (bellPairing A)
  simpa [singleBellBF] using h

theorem singleBellPC_le_one [Nonempty A] : singleBellPC (A := A) ≤ 1 := by
  have h := submatrix_mono
    (kronecker_one_le_one (A := A × A)
      (kronecker_one_le_one (A := A × A) (bellMatrix_le_one (A := A))))
    (bellPairing A)
  simpa [singleBellPC] using h

/-- Linking two Bell-pair terms creates the missing `(a,e)` Bell pair and a
factor `1/d`. -/
theorem link_main_main [Nonempty A] :
    link (Matrix.kronecker (frameMain (A := A)) frameMain) =
      (Fintype.card A : ℂ)⁻¹ • tripleBell := by
  ext i j
  rw [link_apply]
  simp [frameMain, frameWire, Matrix.kronecker, Matrix.kroneckerMap_apply,
    bellMatrix_entry, tripleBell, bellPairing, Matrix.submatrix, Matrix.smul_apply,
    div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm,
    mul_comm, eq_comm]
  <;> simp only [← ite_and, and_comm, and_left_comm, and_assoc]

theorem link_main_identity [Nonempty A] :
    link (Matrix.kronecker (frameMain (A := A)) (1 : CMatrix (FrameWires A))) =
      (Fintype.card A : ℂ)⁻¹ • singleBellBF := by
  ext i j
  rw [link_apply]
  simp [frameMain, frameWire, Matrix.kronecker, Matrix.kroneckerMap_apply,
    bellMatrix_entry, singleBellBF, bellPairing, Matrix.submatrix, Matrix.smul_apply,
    Matrix.one_apply, Prod.ext_iff, ite_and, div_eq_mul_inv, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, eq_comm]
  <;> simp only [← ite_and, and_comm, and_left_comm, and_assoc]

theorem link_identity_main [Nonempty A] :
    link (Matrix.kronecker (1 : CMatrix (FrameWires A)) (frameMain (A := A))) =
      (Fintype.card A : ℂ)⁻¹ • singleBellPC := by
  ext i j
  rw [link_apply]
  simp [frameMain, frameWire, Matrix.kronecker, Matrix.kroneckerMap_apply,
    bellMatrix_entry, singleBellPC, bellPairing, Matrix.submatrix, Matrix.smul_apply,
    Matrix.one_apply, Prod.ext_iff, ite_and, div_eq_mul_inv, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, eq_comm]
  <;> simp only [← ite_and, and_comm, and_left_comm, and_assoc]

theorem link_identity_identity :
    link (Matrix.kronecker (1 : CMatrix (FrameWires A)) (1 : CMatrix (FrameWires A))) =
      (Fintype.card A : ℂ) • (1 : CMatrix (SixWires A)) := by
  ext i j
  rw [link_apply]
  simp [frameWire, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, Matrix.one_apply, Prod.ext_iff, ite_and,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, eq_comm]
  <;> simp only [← ite_and, and_comm, and_left_comm, and_assoc]

end

end ICO.HaarLink
