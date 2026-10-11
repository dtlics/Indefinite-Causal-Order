import ICO.RecordingRemovalNorm
import ICO.RecordingKnownOperation
import ICO.RecordingSupportCompression
import ICO.PureHybrid

/-!
# Purified recording-process recurrence

Known operations are lifted query-and-memory isometries. The two recurrences
use the actual inverse recording, private copy, and either V or A. In this
norm comparison the memory may even contain earlier private copies; the
visible-channel comparison separately restricts operations to accessible
memory and traces the private registers.
-/

namespace ICO.RecordingProcess

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingPartialIsometry ICO.RecordingOracleAlgebra ICO.RecordingCopyIdentity
  ICO.RecordingSupportCompression ICO.RecordingRemovalNorm ICO.RecordingKnownOperation
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

variable {a b c : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

def action (A : Matrix b a ℂ) : EuclideanSpace ℂ a →L[ℂ] EuclideanSpace ℂ b :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A

omit [DecidableEq b] in
theorem action_apply (A : Matrix b a ℂ) (x : EuclideanSpace ℂ a) :
    action A x = WithLp.toLp 2 (A *ᵥ x) :=
  rfl

omit [DecidableEq b] in
theorem action_norm (A : Matrix b a ℂ) : ‖action A‖ = ‖A‖ := rfl

theorem action_mul (A : Matrix c b ℂ) (B : Matrix b a ℂ) (x : EuclideanSpace ℂ a) :
    action (A * B) x = action A (action B x) := by
  simp only [action_apply, Matrix.mulVec_mulVec]

omit [DecidableEq b] in
theorem isometry_matrix_norm_le (J : Matrix b a ℂ) (hJ : J.conjTranspose * J = 1) :
    ‖J‖ ≤ 1 := by
  have h := IsStarProjection.norm_le (1 : CMatrix a) (IsStarProjection.one _)
  rw [← hJ, Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg J]

omit [Fintype a] [DecidableEq a] in
theorem basisEmbedding_adjoint_mulVec (f : a → b) (ψ : b → ℂ) :
    (basisEmbedding f).conjTranspose *ᵥ ψ = ψ ∘ f := by
  funext i
  simp only [Matrix.mulVec, dotProduct, basisEmbedding, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, id_eq, Matrix.one_apply, Function.comp_apply]
  simp

theorem compressed_vector_norm_le (f : a → b) (hf : Function.Injective f)
    (ψ : b → ℂ) : ‖WithLp.toLp 2 (ψ ∘ f)‖ ≤ ‖WithLp.toLp 2 ψ‖ := by
  have hJ := isometry_matrix_norm_le (basisEmbedding f) (basisEmbedding_gram f hf)
  have hAdj : ‖(basisEmbedding f).conjTranspose‖ ≤ 1 := by
    rwa [Matrix.l2_opNorm_conjTranspose]
  have h := Matrix.l2_opNorm_mulVec (basisEmbedding f).conjTranspose (WithLp.toLp 2 ψ)
  rw [basisEmbedding_adjoint_mulVec] at h
  exact le_trans h (by nlinarith [norm_nonneg (WithLp.toLp 2 ψ)])

variable {α μ ν : Type*} [Fintype α] [DecidableEq α]
  [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]

def wrapperMatrix (G : CMatrix (Basis α)) :
    Matrix (Basis α × (α × μ)) (Basis α × μ) ℂ :=
  Matrix.kronecker G (1 : CMatrix (α × μ)) * copyQuery *
    Matrix.kronecker inverseRecording (1 : CMatrix μ)

def stepMatrix (G : CMatrix (Basis α)) (K : Matrix (α × ν) (α × (α × μ)) ℂ) :
    Matrix (Basis α × ν) (Basis α × μ) ℂ := knownOperation K * wrapperMatrix G

theorem wrapperMatrix_A_mulVec (ψ : Basis α × μ → ℂ) :
    wrapperMatrix leftInsertion *ᵥ ψ = modifiedWrapper ψ := by
  simp only [wrapperMatrix, Matrix.mulVec_mulVec, modifiedWrapper]
  rw [Matrix.mul_assoc]

theorem wrapperMatrix_norm_le (G : CMatrix (Basis α))
    (hG : IsStarProjection (G.conjTranspose * G)) :
    ‖wrapperMatrix (μ := μ) G‖ ≤ 1 := by
  classical
  letI : Fintype (Basis α × μ) := inferInstance
  letI : Fintype (Basis α × (α × μ)) := inferInstance
  have h1 := partial_isometry_tensor_norm_le (μ := α × μ) G hG
  have h2 := isometry_matrix_norm_le (copyQuery (α := α) (μ := μ)) copyQuery_isometry
  have h3 := partial_isometry_tensor_norm_le (μ := μ) (inverseRecording (α := α))
    inverse_initial_projection
  unfold wrapperMatrix
  calc
    _ ≤ (‖Matrix.kronecker G (1 : CMatrix (α × μ))‖ * ‖copyQuery (α := α) (μ := μ)‖) *
        ‖Matrix.kronecker (inverseRecording (α := α)) (1 : CMatrix μ)‖ :=
      le_trans (Matrix.l2_opNorm_mul _ _)
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 : ℝ) * 1 * 1 :=
      mul_le_mul (mul_le_mul h1 h2 (norm_nonneg (copyQuery (α := α) (μ := μ)))
        (by norm_num)) h3
        (norm_nonneg (Matrix.kronecker (inverseRecording (α := α)) (1 : CMatrix μ)))
        (by norm_num)
    _ = 1 := by ring

theorem stepMatrix_norm_le (G : CMatrix (Basis α))
    (hG : IsStarProjection (G.conjTranspose * G))
    (K : Matrix (α × ν) (α × (α × μ)) ℂ) (hK : K.conjTranspose * K = 1) :
    ‖stepMatrix G K‖ ≤ 1 := by
  classical
  letI : Fintype (Basis α × ν) := inferInstance
  letI : Fintype (Basis α × (α × μ)) := inferInstance
  unfold stepMatrix
  calc
    _ ≤ ‖(knownOperation K : Matrix (Basis α × ν) (Basis α × (α × μ)) ℂ)‖ *
        ‖wrapperMatrix (μ := μ) G‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (1 : ℝ) * 1 := mul_le_mul (knownOperation_norm_le K hK)
      (wrapperMatrix_norm_le G hG) (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

theorem tensor_sub (A B : CMatrix (Basis α)) :
    Matrix.kronecker (A - B) (1 : CMatrix μ) =
      Matrix.kronecker A (1 : CMatrix μ) - Matrix.kronecker B 1 := by
  ext i j
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]

theorem wrapper_difference_matrix :
    wrapperMatrix (μ := μ) (forwardRecording (α := α)) - wrapperMatrix leftInsertion =
      Matrix.kronecker (forwardRecording - leftInsertion) (1 : CMatrix (α × μ)) *
        copyQuery * Matrix.kronecker inverseRecording (1 : CMatrix μ) := by
  unfold wrapperMatrix
  rw [← Matrix.sub_mul, ← Matrix.sub_mul, tensor_sub]

/-- The local bound for the actual inverse/copy/V and inverse/copy/A
    wrappers, on any normalized supported purified prefix. -/
theorem wrapper_local_error (m : ℕ) (hm : m + 1 < Fintype.card α)
    (ψ : Basis α × μ → ℂ) (hnorm : ‖WithLp.toLp 2 ψ‖ ≤ 1)
    (hψ : ∀ i, ψ i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) :
    ‖action (wrapperMatrix forwardRecording) (WithLp.toLp 2 ψ) -
      action (wrapperMatrix leftInsertion) (WithLp.toLp 2 ψ)‖ ≤
      2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (m + 1 : ℕ))) := by
  classical
  let ζ : Basis α × μ → ℂ :=
    Matrix.kronecker inverseRecording (1 : CMatrix μ) *ᵥ ψ
  let θ := ζ ∘ boundedMemoryEmbed (m + 1)
  have hζsupport : ∀ i, ζ i ≠ 0 → i.1.2.1.card + i.1.2.2.card ≤ m + 1 := by
    intro i hi
    exact (inverse_with_memory_support ψ m hψ i hi).2.2
  have hrecover : basisEmbedding (boundedMemoryEmbed (m + 1)) *ᵥ θ = ζ :=
    bounded_compression_recovers (m + 1) ζ hζsupport
  have hInv := partial_isometry_tensor_norm_le (μ := μ) (inverseRecording (α := α))
    inverse_initial_projection
  have hζnorm : ‖WithLp.toLp 2 ζ‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_mulVec (Matrix.kronecker inverseRecording (1 : CMatrix μ))
      (WithLp.toLp 2 ψ)
    exact le_trans h ((mul_le_mul hInv hnorm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have hθnorm : ‖WithLp.toLp 2 θ‖ ≤ 1 :=
    (compressed_vector_norm_le _ (boundedMemoryEmbed_injective (m + 1)) ζ).trans hζnorm
  have heq :
      (wrapperMatrix forwardRecording - wrapperMatrix leftInsertion) *ᵥ ψ =
      (Matrix.kronecker (forwardRecording - leftInsertion) (1 : CMatrix (α × μ)) *
        boundedCopiedEmbedding (m + 1)) *ᵥ θ := by
    rw [wrapper_difference_matrix]
    simp only [boundedCopiedEmbedding, ← Matrix.mulVec_mulVec]
    rw [hrecover]
  rw [action_apply, action_apply, ← WithLp.toLp_sub, ← Matrix.sub_mulVec, heq]
  have h := Matrix.l2_opNorm_mulVec
    (Matrix.kronecker (forwardRecording (α := α) - leftInsertion)
      (1 : CMatrix (α × μ)) * boundedCopiedEmbedding (m + 1)) (WithLp.toLp 2 θ)
  have hbound := replacementOnCopied_norm_le (μ := μ) (m + 1) hm
  have hnonneg : 0 ≤ 2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (m + 1 : ℕ))) := by positivity
  exact le_trans h ((mul_le_mul hbound hθnorm (norm_nonneg _) hnonneg).trans (by simp))

theorem step_local_error (m : ℕ) (hm : m + 1 < Fintype.card α)
    (K : Matrix (α × ν) (α × (α × μ)) ℂ) (hK : K.conjTranspose * K = 1)
    (ψ : Basis α × μ → ℂ) (hnorm : ‖WithLp.toLp 2 ψ‖ ≤ 1)
    (hψ : ∀ i, ψ i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) :
    ‖action (stepMatrix forwardRecording K) (WithLp.toLp 2 ψ) -
      action (stepMatrix leftInsertion K) (WithLp.toLp 2 ψ)‖ ≤
      2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (m + 1 : ℕ))) := by
  rw [stepMatrix, stepMatrix, action_mul, action_mul, ← map_sub]
  have hKnown : ‖action (knownOperation K)‖ ≤ 1 := by
    rw [action_norm]
    exact knownOperation_norm_le K hK
  have h := (action (knownOperation K)).le_of_opNorm_le
    hKnown
    (action (wrapperMatrix forwardRecording) (WithLp.toLp 2 ψ) -
      action (wrapperMatrix leftInsertion) (WithLp.toLp 2 ψ))
  simp only [one_mul] at h
  exact h.trans (wrapper_local_error m hm ψ hnorm hψ)

theorem process_norm_le
    (M : ℕ → Type*) [∀ t, Fintype (M t)] [∀ t, DecidableEq (M t)]
    (ψ : (t : ℕ) → Basis α × M t → ℂ)
    (G : CMatrix (Basis α)) (hG : IsStarProjection (G.conjTranspose * G))
    (K : (t : ℕ) → Matrix (α × M (t + 1)) (α × (α × M t)) ℂ)
    (hK : ∀ t, (K t).conjTranspose * K t = 1)
    (h0 : ‖WithLp.toLp 2 (ψ 0)‖ ≤ 1)
    (hstep : ∀ t, ψ (t + 1) = stepMatrix G (K t) *ᵥ ψ t) :
    ∀ t, ‖WithLp.toLp 2 (ψ t)‖ ≤ 1 := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
      rw [hstep t]
      have h := Matrix.l2_opNorm_mulVec (stepMatrix G (K t)) (WithLp.toLp 2 (ψ t))
      exact le_trans h ((mul_le_mul (stepMatrix_norm_le G hG (K t) (hK t)) ih
        (norm_nonneg _) (by norm_num)).trans (by norm_num))

/-- Actual purified recording processes differ by the accumulated local
    removal error. Only the Haar-to-recording comparison lies outside this
    theorem; the recurrence, support and contraction premises are explicit. -/
theorem recording_hybrid_norm_le
    (M : ℕ → Type*) [∀ t, Fintype (M t)] [∀ t, DecidableEq (M t)]
    (ψ χ : (t : ℕ) → Basis α × M t → ℂ)
    (K : (t : ℕ) → Matrix (α × M (t + 1)) (α × (α × M t)) ℂ)
    (hK : ∀ t, (K t).conjTranspose * K t = 1)
    (hinit : ψ 0 = χ 0) (hnorm : ‖WithLp.toLp 2 (ψ 0)‖ ≤ 1)
    (hempty : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hmod : ∀ t, ψ (t + 1) = stepMatrix leftInsertion (K t) *ᵥ ψ t)
    (hrec : ∀ t, χ (t + 1) = stepMatrix forwardRecording (K t) *ᵥ χ t)
    (q : ℕ) (hqd : 2 * q < Fintype.card α) :
    ‖WithLp.toLp 2 (ψ q) - WithLp.toLp 2 (χ q)‖ ≤
      (q : ℝ) * (2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (2 * q : ℕ)))) := by
  have hA : IsStarProjection (leftInsertion.conjTranspose * leftInsertion : CMatrix (Basis α)) := by
    rw [left_gram_eq_projection]
    exact domainProjection_isStarProjection
  have hnorms := process_norm_le M ψ leftInsertion hA K hK hnorm hmod
  have hmod' (t : ℕ) : ψ (t + 1) = knownOperation (K t) *ᵥ modifiedWrapper (ψ t) := by
    rw [hmod t, stepMatrix, ← Matrix.mulVec_mulVec, wrapperMatrix_A_mulVec]
  have hsupp := iterated_modified_wrapper_support M ψ K hempty hmod'
  let δ := 2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (2 * q : ℕ)))
  have hδ (t : ℕ) (ht : t < q) :
      2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (2 * t + 1 : ℕ))) ≤ δ := by
    have hd : (0 : ℝ) < (Fintype.card α : ℝ) - (2 * q : ℕ) := by
      have h : ((2 * q : ℕ) : ℝ) < Fintype.card α := by exact_mod_cast hqd
      linarith
    have hsmall : ((2 * t + 1 : ℕ) : ℝ) ≤ (2 * q : ℕ) := by
      exact_mod_cast (show 2 * t + 1 ≤ 2 * q by omega)
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (one_div_le_one_div_of_le hd (sub_le_sub_left hsmall _))) (by norm_num)
  have hhybrid := ICO.PureHybrid.vector_hybrid_upto
    (fun t => WithLp.toLp 2 (ψ t)) (fun t => WithLp.toLp 2 (χ t))
    (fun t => action (stepMatrix forwardRecording (K t))) (fun _ => δ) q
    (congrArg (WithLp.toLp 2) hinit)
    (fun t _ => by rw [action_norm]; exact stepMatrix_norm_le _ forward_initial_projection _ (hK t))
    (fun t _ => by dsimp only; rw [hrec t, action_apply])
    (by
      intro t ht
      dsimp only
      rw [hmod t]
      change ‖action (stepMatrix leftInsertion (K t)) (WithLp.toLp 2 (ψ t)) -
        action (stepMatrix forwardRecording (K t)) (WithLp.toLp 2 (ψ t))‖ ≤ δ
      rw [norm_sub_rev]
      exact (step_local_error (2 * t) (by omega) (K t) (hK t) (ψ t) (hnorms t)
        (hsupp t)).trans (hδ t ht))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, δ] using hhybrid

end
end ICO.RecordingProcess
