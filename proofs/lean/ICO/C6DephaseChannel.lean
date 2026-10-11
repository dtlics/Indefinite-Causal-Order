import ICO.C6InvariantDephase
import ICO.LudersDilation

/-! Literal channel interpretation of the invariant-label matrix bound. -/
namespace ICO.C6DephaseChannel
open QIT Matrix ICO.C6LabelSymmetry ICO.C6ConditionalCommon ICO.C6InvariantDephase
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1400000
universe u
variable {A M Z : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype Z] [DecidableEq Z]

def pinchingKraus (j : A) : CMatrix (A × M) :=
  Matrix.kronecker (Matrix.single j j (1 : ℂ)) 1

def pinchingMap : MatrixMap (A × M) (A × M) := MatrixMap.ofKraus pinchingKraus

theorem pinchingKraus_complete :
    (∑ j : A, (pinchingKraus (M := M) j).conjTranspose * pinchingKraus j) = 1 := by
  simp only [pinchingKraus, Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.conjTranspose_single, star_one]
  simp_rw [← Matrix.mul_kronecker_mul, Matrix.single_mul_single_same, one_mul]
  ext x y
  rcases x with ⟨a, m⟩
  rcases y with ⟨b, l⟩
  by_cases hab : a = b <;> by_cases hml : m = l <;>
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single,
      Matrix.one_apply, hab, hml, Prod.mk.injEq, eq_comm]
  have hz : ∀ x : A, ¬ (a = x ∧ b = x) := fun x h => hab (h.1.trans h.2.symm)
  simp [hz]

def pinchingChannel : Channel (A × M) (A × M) where
  map := pinchingMap
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using pinchingKraus_complete (A := A) (M := M))
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem pinching_apply (X : CMatrix (A × M)) :
    pinchingMap X = QIT.Classical.blockDiagonal (fun j : A =>
      X.submatrix (fun i : M => (j, i)) (fun i : M => (j, i))) := by
  ext u v
  rcases u with ⟨a, x⟩
  rcases v with ⟨b, y⟩
  by_cases hab : a = b
  all_goals
  simp [pinchingMap, MatrixMap.ofKraus, pinchingKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.single, Matrix.one_apply,
    QIT.Classical.blockDiagonal, apply_ite, ite_and, eq_comm, hab]

def headMatrix (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    CMatrix (A × (TensorPower A n × Z)) :=
  ω.submatrix (Equiv.prodAssoc A (TensorPower A n) Z).symm
    (Equiv.prodAssoc A (TensorPower A n) Z).symm

theorem pinching_head (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    pinchingMap (headMatrix n ω) = dephased n ω := by
  rw [pinching_apply]
  rfl

theorem head_partialTrace (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    partialTraceA (headMatrix n ω) = ∑ a : A, conditional n ω a := by
  ext x y
  simp [partialTraceA, headMatrix, conditional, Matrix.sum_apply]
  rfl

theorem depolarizing_head (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    (ICO.RecordingDepolarizing.withMemory (α := A) (μ := TensorPower A n × Z)).map
      (headMatrix n ω) = depolarized n ω := by
  rw [ICO.RecordingDepolarizing.withMemory_apply, head_partialTrace]
  simp only [ICO.RecordingWrapperDistance.uniformOutput,
    ICO.RecordingDistance.memoryOutput, depolarized, average, one_div]

theorem invariant_pinching_bound (n : ℕ)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) (hpos : ω.PosSemidef)
    (hω : CommonInvariant (n + 1) ω) :
    traceNorm (pinchingChannel.map (headMatrix n ω) -
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := TensorPower A n × Z)).map
        (headMatrix n ω)) ≤ 6 * (n : ℝ) * ω.trace.re / (Fintype.card A : ℝ) := by
  change traceNorm (pinchingMap (headMatrix n ω) - _) ≤ _
  rw [pinching_head, depolarizing_head]
  exact dephasing_traceNorm_bound n ω hpos hω

#print axioms pinchingChannel
#print axioms invariant_pinching_bound
end
end ICO.C6DephaseChannel
