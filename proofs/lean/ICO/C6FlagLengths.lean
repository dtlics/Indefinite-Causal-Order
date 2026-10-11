import ICO.C6FlagDegree
import ICO.C6BosonicStageLength
import ICO.MHFockTrajectory

/-! Each individual retained birth/retrieval branch has exactly as many
left and right records as true birth flags. No cancellation argument is used. -/
namespace ICO.C6FlagLengths
open Matrix QIT ICO.C6FlagDegree ICO.C6FockLengthShift ICO.C6FlagCount
  ICO.C6BirthFlags ICO.C6RawFlags ICO.C6RetainedHistory ICO.C6PairedTrajectory
  ICO.C6BosonicStageLength ICO.C6FockQueryMatrix ICO.MHFockTrajectory
  ICO.MHBoundedRecording ICO.MHRectangularAction ICO.RecordingPurifiedProtocol
  ICO.RecordingCopyIdentity ICO.MHFockProjection
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {M N:Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

def ExactLengths {T:ℕ} (v:InputCutoff (α:=A) T×M→ℂ) (l r:ℤ) : Prop :=
  ∀o,v o≠0→leftDegree o.1=l ∧ rightDegree o.1=r

theorem action_lengths {T:ℕ}
    (F:Matrix (InputCutoff (α:=A) T×N) (InputCutoff (α:=A) T×M) ℂ)
    {l r l' r':ℤ} (hF:MemShift F l r)
    (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×M))
    (hv:ExactLengths (WithLp.ofLp v) l' r') :
    ExactLengths (WithLp.ofLp (rectAct F v)) (l'+l) (r'+r) := by
  intro o ho
  change (F*ᵥWithLp.ofLp v) o≠0 at ho
  obtain ⟨i,_,hi⟩:=Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hm,hn⟩:=mul_ne_zero_iff.mp hi
  obtain ⟨hl,hr⟩:=hF o i hm
  obtain ⟨hl',hr'⟩:=hv i hn
  constructor <;> linarith

theorem initial_lengths (T:ℕ) (z:A×M→ℂ) : ExactLengths (initial T z) 0 0 := by
  intro o ho
  obtain ⟨i,_,hi⟩:=Finset.exists_ne_zero_of_sum_ne_zero ho
  have he:=basisEmbedding_support (initialEmbed T) o i (mul_ne_zero_iff.mp hi).1
  subst o
  exact ⟨rfl,rfl⟩

theorem mask_of_lengths {T:ℕ} (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×M))
    {l r:ℤ} (hv:ExactLengths (WithLp.ofLp v) l r) (m:ℕ) (hm:r≤(m:ℤ)) :
    rectAct (memoryMask (A:=A) m T M) v=v := by
  have he:memoryMask (A:=A) m T M=Matrix.diagonal (fun i:InputCutoff (α:=A) T×M=>
      if i.1.1.1.val.2.val≤m then (1:ℂ) else 0) := by
    ext o i
    simp only [memoryMask,rightLengthMask_diagonal,Matrix.kronecker,
      Matrix.kroneckerMap_apply,Matrix.diagonal_apply,Matrix.one_apply]
    by_cases h1:o.1=i.1 <;> by_cases h2:o.2=i.2 <;>
      simp [h1,h2,Prod.ext_iff]
  apply WithLp.ofLp_injective
  change (memoryMask (A:=A) m T M)*ᵥWithLp.ofLp v=WithLp.ofLp v
  rw [he]
  funext o
  by_cases hz:WithLp.ofLp v o=0
  · simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,hz]
  · have hr:((o.1.1.1.val.2.val:ℕ):ℤ)=r:=(hv o hz).2
    have hb:o.1.1.1.val.2.val≤m:=by omega
    simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,hb]

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem flagRun_lengths {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (hz:ExactLengths (WithLp.ofLp z) 0 0) (n:ℕ) (κ:History Bool n) :
    ExactLengths (WithLp.ofLp (flagRun h H K z n κ))
      (flagCount n κ) (flagCount n κ) := by
  induction n with
  | zero=>exact hz
  | succ n ih=>
    have hs:=action_lengths _ (flagStage_degree h H K n κ.1) _ (ih κ.2)
    cases hf:κ.1 <;> simpa only [flagRun,flagCount,hf,Bool.false_eq_true,↓reduceIte,
      Nat.cast_add,Nat.cast_zero,Nat.cast_one] using hs

theorem rawFlagRun_lengths {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (hz:ExactLengths (WithLp.ofLp z) 0 0) (n:ℕ) (κ:History Bool n) :
    ExactLengths (WithLp.ofLp (rawFlagRun h H K z n κ))
      (flagCount n κ) (flagCount n κ) := by
  induction n with
  | zero=>exact hz
  | succ n ih=>
    have hs:=action_lengths _ (rawFlagStage_degree h H K n κ.1) _ (ih κ.2)
    cases hf:κ.1 <;> simpa only [rawFlagRun,flagCount,hf,Bool.false_eq_true,↓reduceIte,
      Nat.cast_add,Nat.cast_zero,Nat.cast_one] using hs

theorem flagRun_mask {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (hz:ExactLengths (WithLp.ofLp z) 0 0) (n:ℕ) (κ:History Bool n) :
    rectAct (memoryMask (A:=A) n T (Public (A:=A) μ n)) (flagRun h H K z n κ)=
      flagRun h H K z n κ :=
  mask_of_lengths _ (flagRun_lengths h H K z hz n κ) n (by exact_mod_cast flagCount_le n κ)

theorem rawFlagRun_mask {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (hz:ExactLengths (WithLp.ofLp z) 0 0) (n:ℕ) (κ:History Bool n) :
    rectAct (memoryMask (A:=A) n T (Public (A:=A) μ n)) (rawFlagRun h H K z n κ)=
      rawFlagRun h H K z n κ :=
  mask_of_lengths _ (rawFlagRun_lengths h H K z hz n κ) n (by exact_mod_cast flagCount_le n κ)

#print axioms flagRun_mask
#print axioms rawFlagRun_lengths
end
end ICO.C6FlagLengths
