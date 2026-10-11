import ICO.C6CacheMap
import QIT.States.TraceNorm.PositivePart

/-! A retained-outcome weighted CP instrument and its uniform extension.
Every map is defined on all input matrices, including zero-probability histories. -/
namespace ICO.C6CacheWeighted
open QIT ICO.C6CacheMap ICO.RecordingCopyIdentity
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2000000
variable {a b ι : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem cp_real_smul (Φ : MatrixMap a b) (hΦ : MatrixMap.IsCompletelyPositive Φ)
    (r : ℝ) (hr : 0≤r) : MatrixMap.IsCompletelyPositive ((r:ℂ) • Φ) := by
  change (MatrixMap.choi ((r:ℂ) • Φ)).PosSemidef
  have he : MatrixMap.choi ((r:ℂ) • Φ)=(r:ℂ) • MatrixMap.choi Φ := by
    ext i j
    rfl
  rw [he]
  exact hΦ.smul (by exact_mod_cast hr)

theorem cp_sum (Φ : ι → MatrixMap a b) (hΦ : ∀ j,MatrixMap.IsCompletelyPositive (Φ j)) :
    MatrixMap.IsCompletelyPositive (∑ j,Φ j) := by
  change (MatrixMap.choi (∑ j,Φ j)).PosSemidef
  have he : MatrixMap.choi (∑ j,Φ j)=∑ j,MatrixMap.choi (Φ j) := by
    ext i j
    simp [MatrixMap.choi,Matrix.sum_apply]
  rw [he]
  exact Matrix.posSemidef_sum Finset.univ (fun j _ => hΦ j)

def tagged (Φ : ι → Channel a b) (j : ι) : MatrixMap a (ι×b) :=
  (conjugate (basisEmbedding (fun x : b => (j,x)))).comp (Φ j).map

theorem tagged_cp (Φ : ι → Channel a b) (j : ι) :
    MatrixMap.IsCompletelyPositive (tagged Φ j) :=
  MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _) (Φ j).completelyPositive

theorem tagged_trace (Φ : ι → Channel a b) (j : ι) (X : CMatrix a) :
    (tagged Φ j X).trace=X.trace := by
  change (conjugate (basisEmbedding (fun x : b => (j,x))) ((Φ j).map X)).trace=X.trace
  rw [conjugate_trace_of_isometry _ (basisEmbedding_gram _ (by
    intro x y h; exact congrArg Prod.snd h)),(Φ j).tracePreserving]

def weighted (Φ : ι → Channel a b) (w : ι → ℝ) : MatrixMap a (ι×b) :=
  ∑ j, ((w j/(Fintype.card ι:ℝ)):ℂ) • tagged Φ j

theorem weighted_cp (Φ : ι → Channel a b) (w : ι → ℝ) (hw : ∀ j,0≤w j) :
    MatrixMap.IsCompletelyPositive (weighted Φ w) := by
  apply cp_sum
  intro j
  simpa only [Complex.ofReal_div] using cp_real_smul _ (tagged_cp Φ j)
    (w j/(Fintype.card ι:ℝ)) (div_nonneg (hw j) (Nat.cast_nonneg _))

theorem weighted_trace (Φ : ι → Channel a b) (w : ι → ℝ) (X : CMatrix a) :
    (weighted Φ w X).trace=(((∑ j,w j)/(Fintype.card ι:ℝ)):ℂ)*X.trace := by
  simp only [weighted,LinearMap.sum_apply,LinearMap.smul_apply,Matrix.trace_sum,
    Matrix.trace_smul,tagged_trace,smul_eq_mul]
  rw [←Finset.sum_mul,←Finset.sum_div,Complex.ofReal_sum]

theorem weighted_sub (Φ : ι → Channel a b) (w v : ι → ℝ) :
    weighted Φ w-weighted Φ v=weighted Φ (fun j => w j-v j) := by
  ext X i j
  simp only [weighted,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Complex.ofReal_sub]
  ring

theorem uniform_trace (Φ : ι → Channel a b) :
    MatrixMap.IsTracePreserving (weighted Φ (fun _ => 1)) := by
  intro X
  rw [weighted_trace]
  have hd : (Fintype.card ι:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hd]

def uniformChannel (Φ : ι → Channel a b) : Channel a (ι×b) where
  map := weighted Φ (fun _ => 1)
  completelyPositive := weighted_cp Φ _ (fun _ => by norm_num)
  tracePreserving := uniform_trace Φ
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _
    (weighted_cp Φ _ (fun _ => by norm_num))

theorem deficit_cp (Φ : ι → Channel a b) (w : ι → ℝ) (hw : ∀ j,w j≤1) :
    MatrixMap.IsCompletelyPositive (weighted Φ (fun _ => 1)-weighted Φ w) := by
  rw [weighted_sub]
  exact weighted_cp Φ _ (fun j => sub_nonneg.mpr (hw j))

theorem deficit_traceNorm (Φ : ι → Channel a b) (w : ι → ℝ)
    (hw : ∀ j,w j≤1) (X : CMatrix a) (hX : X.PosSemidef) :
    traceNorm (weighted Φ (fun _ => 1) X - weighted Φ w X) =
      ((∑ j : ι, (1 - w j))/(Fintype.card ι:ℝ))*X.trace.re := by
  have hp := MatrixMap.isCompletelyPositive_mapsPositive _ (deficit_cp Φ w hw) X hX
  change (weighted Φ (fun _=>1) X-weighted Φ w X).PosSemidef at hp
  rw [traceNorm_posSemidef_eq_trace_re _ hp]
  change (((weighted Φ (fun _=>1)-weighted Φ w) X).trace).re=_
  rw [weighted_sub,weighted_trace]
  simp

theorem weighted_TNI (Φ : ι → Channel a b) (w : ι → ℝ)
    (hw0 : ∀ j,0≤w j) (hw1 : ∀ j,w j≤1) :
    MatrixMap.TraceNonincreasingCP (weighted Φ w) where
  completelyPositive := weighted_cp Φ w hw0
  traceNonincreasing := by
    intro X hX
    have hp := MatrixMap.isCompletelyPositive_mapsPositive _ (deficit_cp Φ w hw1) X hX
    have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
    change 0≤((weighted Φ (fun _=>1) X-weighted Φ w X).trace).re at ht
    rw [Matrix.trace_sub,uniform_trace Φ,Complex.sub_re] at ht
    linarith

#print axioms deficit_traceNorm
#print axioms weighted_TNI
end
end ICO.C6CacheWeighted
