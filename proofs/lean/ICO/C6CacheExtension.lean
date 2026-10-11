import ICO.C6CachePreparation

/-! The uniform cache is a genuine channel on every input. The weighted
cache is a CP trace-nonincreasing map and has an exact positive deficit. -/
namespace ICO.C6CacheExtension
open QIT ICO.C6CacheMap ICO.C6CacheWeighted ICO.C6CacheWeights
  ICO.RecordingCopyIdentity
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2000000
variable {a b c ι : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

def extension (F : Matrix b a ℂ) (Δ : Channel a a)
    (Φ : ι → Channel b c) (w : ι → ℝ) : MatrixMap b (b ⊕ (ι×c)) :=
  (conjugate (basisEmbedding (Sum.inl : b → b ⊕ (ι×c)))).comp (retrieval F Δ) +
  (conjugate (basisEmbedding (Sum.inr : (ι×c) → b ⊕ (ι×c)))).comp
    ((weighted Φ w).comp (conjugate (1-image F)))

theorem extension_cp (F : Matrix b a ℂ) (Δ : Channel a a)
    (Φ : ι → Channel b c) (w : ι → ℝ) (hw : ∀ j,0≤w j) :
    MatrixMap.IsCompletelyPositive (extension F Δ Φ w) :=
  cp_add (MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _) (retrieval_cp F Δ))
    (MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
      (MatrixMap.isCompletelyPositive_comp _ _ (weighted_cp Φ w hw) (conjugate_cp _)))

theorem complement_trace (F : Matrix b a ℂ) (hF : F.conjTranspose*F=1)
    (X : CMatrix b) :
    (conjugate (1-image F) X).trace=((1-image F)*X).trace := by
  rw [conjugate_trace,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,
    image_adjoint,complement_sq F hF]

theorem extension_trace (F : Matrix b a ℂ) (hF : F.conjTranspose*F=1)
    (Δ : Channel a a) (Φ : ι → Channel b c) (w : ι → ℝ) (X : CMatrix b) :
    (extension F Δ Φ w X).trace=(image F*X).trace+
      (((∑ j,w j)/(Fintype.card ι:ℝ)):ℂ)*((1-image F)*X).trace := by
  change Matrix.trace ((_+_) : CMatrix (b ⊕ (ι×c)))=_
  rw [Matrix.trace_add]
  change (conjugate (basisEmbedding (Sum.inl : b → b ⊕ (ι×c))) (retrieval F Δ X)).trace+
    (conjugate (basisEmbedding (Sum.inr : (ι×c) → b ⊕ (ι×c)))
      (weighted Φ w (conjugate (1-image F) X))).trace=_
  rw [conjugate_trace_of_isometry _ (basisEmbedding_gram _ Sum.inl_injective),
    conjugate_trace_of_isometry _ (basisEmbedding_gram _ Sum.inr_injective),
    retrieval_trace F hF,weighted_trace,complement_trace F hF]

theorem uniform_extension_trace (F : Matrix b a ℂ) (hF : F.conjTranspose*F=1)
    (Δ : Channel a a) (Φ : ι → Channel b c) :
    MatrixMap.IsTracePreserving (extension F Δ Φ (fun _ => 1)) := by
  intro X
  rw [extension_trace F hF]
  have hd : (Fintype.card ι:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have he : ((∑ _j : ι,(1 : ℝ))/(Fintype.card ι:ℝ))=1 := by simp [hd]
  rw [←Complex.ofReal_div]
  rw [he,Complex.ofReal_one,one_mul,←Matrix.trace_add,←Matrix.add_mul,
    add_sub_cancel,Matrix.one_mul]

def uniformExtension (F : Matrix b a ℂ) (hF : F.conjTranspose*F=1)
    (Δ : Channel a a) (Φ : ι → Channel b c) : Channel b (b ⊕ (ι×c)) where
  map := extension F Δ Φ (fun _ => 1)
  completelyPositive := extension_cp F Δ Φ _ (fun _ => by norm_num)
  tracePreserving := uniform_extension_trace F hF Δ Φ
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _
    (extension_cp F Δ Φ _ (fun _ => by norm_num))

theorem extension_sub (F : Matrix b a ℂ) (Δ : Channel a a)
    (Φ : ι → Channel b c) (w : ι → ℝ) :
    extension F Δ Φ (fun _=>1)-extension F Δ Φ w=
      (conjugate (basisEmbedding (Sum.inr : (ι×c) → b ⊕ (ι×c)))).comp
        ((weighted Φ (fun _=>1)-weighted Φ w).comp (conjugate (1-image F))) := by
  ext X i j
  simp only [extension,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.comp_apply,
    map_sub,Matrix.sub_apply,Matrix.add_apply]
  ring

theorem extension_deficit_cp (F : Matrix b a ℂ) (Δ : Channel a a)
    (Φ : ι → Channel b c) (w : ι → ℝ) (hw : ∀ j,w j≤1) :
    MatrixMap.IsCompletelyPositive (extension F Δ Φ (fun _=>1)-extension F Δ Φ w) := by
  rw [extension_sub]
  exact MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
    (MatrixMap.isCompletelyPositive_comp _ _ (deficit_cp Φ w hw) (conjugate_cp _))

theorem extension_TNI (F : Matrix b a ℂ) (hF : F.conjTranspose*F=1)
    (Δ : Channel a a) (Φ : ι → Channel b c) (w : ι → ℝ)
    (hw0 : ∀ j,0≤w j) (hw1 : ∀ j,w j≤1) :
    MatrixMap.TraceNonincreasingCP (extension F Δ Φ w) where
  completelyPositive := extension_cp F Δ Φ w hw0
  traceNonincreasing := by
    intro X hX
    have hp := MatrixMap.isCompletelyPositive_mapsPositive _ (extension_deficit_cp F Δ Φ w hw1) X hX
    have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
    change 0≤((extension F Δ Φ (fun _=>1) X-extension F Δ Φ w X).trace).re at ht
    rw [Matrix.trace_sub,uniform_extension_trace F hF,Complex.sub_re] at ht
    linarith

theorem extension_deficit (F : Matrix b a ℂ) (hF : F.conjTranspose*F=1)
    (Δ : Channel a a) (Φ : ι → Channel b c) (w : ι → ℝ)
    (hw : ∀ j,w j≤1) (X : CMatrix b) (hX : X.PosSemidef) :
    traceNorm (extension F Δ Φ (fun _=>1) X-extension F Δ Φ w X)=
      ((∑ j : ι,(1-w j))/(Fintype.card ι:ℝ))*(((1-image F)*X).trace).re := by
  have hp := MatrixMap.isCompletelyPositive_mapsPositive _ (extension_deficit_cp F Δ Φ w hw) X hX
  change (extension F Δ Φ (fun _=>1) X-extension F Δ Φ w X).PosSemidef at hp
  rw [traceNorm_posSemidef_eq_trace_re _ hp]
  change (((extension F Δ Φ (fun _=>1)-extension F Δ Φ w) X).trace).re=_
  rw [extension_sub]
  change (conjugate (basisEmbedding (Sum.inr : (ι×c) → b ⊕ (ι×c)))
    ((weighted Φ (fun _=>1)-weighted Φ w) (conjugate (1-image F) X))).trace.re=_
  rw [conjugate_trace_of_isometry _ (basisEmbedding_gram _ Sum.inr_injective),
    weighted_sub,weighted_trace,complement_trace F hF]
  simp

theorem actual_extension_deficit (F : Matrix b a ℂ) (hF : F.conjTranspose*F=1)
    (Δ : Channel a a) (Φ : ι → Channel b c) (U : Matrix.unitaryGroup ι ℂ)
    (P : CMatrix ι) (hP : IsStarProjection P) (X : CMatrix b) (hX : X.PosSemidef) :
    traceNorm (extension F Δ Φ (fun _=>1) X-extension F Δ Φ (overlapWeight U P) X)=
      (P.trace.re/(Fintype.card ι:ℝ))*(((1-image F)*X).trace).re := by
  rw [extension_deficit F hF Δ Φ _ (overlapWeight_le_one U P hP) X hX,
    overlapWeight_deficit]

#print axioms uniformExtension
#print axioms extension_TNI
#print axioms actual_extension_deficit
end
end ICO.C6CacheExtension
