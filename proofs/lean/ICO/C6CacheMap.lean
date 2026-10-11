import ICO.RecordingDepolarizing
import ICO.RecordingCopyIdentity
import QIT.Core.Channel

/-! The literal retrieval/birth cache, prior to instantiation with the
bosonic polar creators.  The two outputs carry a private classical branch
and sector tag.  CP and TP are proved for every input matrix, so this gives
the needed extension even on histories absent from an earlier process.
This file does not assert the recording-to-cache comparison. -/

namespace ICO.C6CacheMap
open QIT ICO.RecordingCopyIdentity
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section

variable {a b c : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

def conjugate (K : Matrix b a ℂ) : MatrixMap a b :=
  MatrixMap.ofKraus (fun _ : Unit => K)

@[simp] theorem conjugate_apply (K : Matrix b a ℂ) (X : CMatrix a) :
    conjugate K X = K * X * K.conjTranspose := by
  simp [conjugate, MatrixMap.ofKraus]

theorem conjugate_cp (K : Matrix b a ℂ) :
    MatrixMap.IsCompletelyPositive (conjugate K) :=
  MatrixMap.ofKraus_completelyPositive _

theorem conjugate_trace (K : Matrix b a ℂ) (X : CMatrix a) :
    (conjugate K X).trace = (K.conjTranspose * K * X).trace := by
  rw [conjugate_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

theorem conjugate_trace_of_isometry (K : Matrix b a ℂ)
    (hK : K.conjTranspose * K = 1) (X : CMatrix a) :
    (conjugate K X).trace = X.trace := by
  rw [conjugate_trace, hK, Matrix.one_mul]

def image (F : Matrix b a ℂ) : CMatrix b := F * F.conjTranspose

theorem image_adjoint (F : Matrix b a ℂ) : (image F).conjTranspose = image F := by
  simp [image, Matrix.conjTranspose_mul]

theorem image_sq (F : Matrix b a ℂ) (hF : F.conjTranspose * F = 1) :
    image F * image F = image F := by
  simp only [image, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.conjTranspose F, hF, Matrix.one_mul]

theorem complement_sq (F : Matrix b a ℂ) (hF : F.conjTranspose * F = 1) :
    (1 - image F) * (1 - image F) = 1 - image F := by
  have h := image_sq F hF
  noncomm_ring [h]

def retrieval (F : Matrix b a ℂ) (Δ : Channel a a) : MatrixMap b b :=
  (conjugate F).comp (Δ.map.comp (conjugate F.conjTranspose))

@[simp] theorem retrieval_apply (F : Matrix b a ℂ) (Δ : Channel a a) (X : CMatrix b) :
    retrieval F Δ X = F * Δ.map (F.conjTranspose * X * F) * F.conjTranspose := by
  simp [retrieval]

theorem retrieval_cp (F : Matrix b a ℂ) (Δ : Channel a a) :
    MatrixMap.IsCompletelyPositive (retrieval F Δ) :=
  MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp F)
    (MatrixMap.isCompletelyPositive_comp _ _ Δ.completelyPositive
      (conjugate_cp F.conjTranspose))

theorem retrieval_trace (F : Matrix b a ℂ) (hF : F.conjTranspose * F = 1)
    (Δ : Channel a a) (X : CMatrix b) :
    (retrieval F Δ X).trace = (image F * X).trace := by
  change (conjugate F (Δ.map (conjugate F.conjTranspose X))).trace = _
  rw [conjugate_trace_of_isometry F hF, Δ.tracePreserving, conjugate_trace]
  simp [image]

def birth (F : Matrix b a ℂ) (G : Matrix c b ℂ) (Ω : Channel b b) : MatrixMap b c :=
  (conjugate G).comp (Ω.map.comp (conjugate (1 - image F)))

@[simp] theorem birth_apply (F : Matrix b a ℂ) (G : Matrix c b ℂ)
    (Ω : Channel b b) (X : CMatrix b) :
    birth F G Ω X = G * Ω.map ((1 - image F) * X * (1 - image F)) * G.conjTranspose := by
  simp [birth, Matrix.conjTranspose_sub, image_adjoint]

theorem birth_cp (F : Matrix b a ℂ) (G : Matrix c b ℂ) (Ω : Channel b b) :
    MatrixMap.IsCompletelyPositive (birth F G Ω) :=
  MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp G)
    (MatrixMap.isCompletelyPositive_comp _ _ Ω.completelyPositive
      (conjugate_cp (1 - image F)))

theorem birth_trace (F : Matrix b a ℂ) (hF : F.conjTranspose * F = 1)
    (G : Matrix c b ℂ) (hG : G.conjTranspose * G = 1)
    (Ω : Channel b b) (X : CMatrix b) :
    (birth F G Ω X).trace = ((1 - image F) * X).trace := by
  change (conjugate G (Ω.map (conjugate (1 - image F) X))).trace = _
  rw [conjugate_trace_of_isometry G hG, Ω.tracePreserving, conjugate_trace]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, image_adjoint,
    complement_sq F hF]

def cacheMap (F : Matrix b a ℂ) (G : Matrix c b ℂ)
    (Δ : Channel a a) (Ω : Channel b b) : MatrixMap b (b ⊕ c) :=
  (conjugate (basisEmbedding (Sum.inl : b → b ⊕ c))).comp (retrieval F Δ) +
  (conjugate (basisEmbedding (Sum.inr : c → b ⊕ c))).comp (birth F G Ω)

theorem cp_add {Φ Ψ : MatrixMap a b} (hΦ : MatrixMap.IsCompletelyPositive Φ)
    (hΨ : MatrixMap.IsCompletelyPositive Ψ) : MatrixMap.IsCompletelyPositive (Φ + Ψ) := by
  change (MatrixMap.choi (Φ + Ψ)).PosSemidef
  have h : MatrixMap.choi (Φ + Ψ) = MatrixMap.choi Φ + MatrixMap.choi Ψ := by
    ext i j
    rfl
  rw [h]
  exact hΦ.add hΨ

theorem cache_cp (F : Matrix b a ℂ) (G : Matrix c b ℂ)
    (Δ : Channel a a) (Ω : Channel b b) :
    MatrixMap.IsCompletelyPositive (cacheMap F G Δ Ω) :=
  cp_add (MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _) (retrieval_cp F Δ))
    (MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _) (birth_cp F G Ω))

theorem cache_trace (F : Matrix b a ℂ) (hF : F.conjTranspose * F = 1)
    (G : Matrix c b ℂ) (hG : G.conjTranspose * G = 1)
    (Δ : Channel a a) (Ω : Channel b b) :
    MatrixMap.IsTracePreserving (cacheMap F G Δ Ω) := by
  intro X
  change ((conjugate (basisEmbedding (Sum.inl : b → b ⊕ c)) (retrieval F Δ X)) +
    (conjugate (basisEmbedding (Sum.inr : c → b ⊕ c)) (birth F G Ω X))).trace = _
  rw [Matrix.trace_add,
    conjugate_trace_of_isometry _ (basisEmbedding_gram _ Sum.inl_injective),
    conjugate_trace_of_isometry _ (basisEmbedding_gram _ Sum.inr_injective),
    retrieval_trace F hF, birth_trace F hF G hG, ← Matrix.trace_add,
    ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]

/-- Literal sector-tagged CPTP cache.  For C6, Ω is complete depolarization
of the external query with the cache/memory retained. -/
def cacheChannel (F : Matrix b a ℂ) (hF : F.conjTranspose * F = 1)
    (G : Matrix c b ℂ) (hG : G.conjTranspose * G = 1)
    (Δ : Channel a a) (Ω : Channel b b) : Channel b (b ⊕ c) where
  map := cacheMap F G Δ Ω
  completelyPositive := cache_cp F G Δ Ω
  tracePreserving := cache_trace F hF G hG Δ Ω
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ (cache_cp F G Δ Ω)

#print axioms cache_trace
#print axioms cacheChannel
end
end ICO.C6CacheMap
