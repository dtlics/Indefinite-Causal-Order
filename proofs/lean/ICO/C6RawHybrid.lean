import ICO.C6RawStageError
import ICO.C6FlaggedHybrid
import ICO.C6ActualRightSupport
import ICO.C6FlagLengths
import ICO.C6FlagMass

/-! Actual polar-to-raw flagged comparison, with all prefix support and
contraction hypotheses derived from the physical finite recording process. -/
namespace ICO.C6RawHybrid
open Matrix QIT ICO.C6RawFlags ICO.C6RawFlagContraction ICO.C6RawInverseError
  ICO.C6RawStageError ICO.C6FlaggedHybrid ICO.C6FlagStack ICO.C6FlagMass
  ICO.C6BirthFlags ICO.C6RetainedHistory ICO.C6HistoryControlled ICO.C6FlagSlices
  ICO.C6FlagLengths ICO.C6ActualRightSupport ICO.C6BosonicBlocks ICO.C6BosonicStageLength
  ICO.C6PairedTrajectory ICO.C6PolarFock ICO.C6MatrixTrajectory
  ICO.MHBoundedRecording ICO.MHRectangularAction ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1700000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem actual_comparison_mask {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (i:ℕ) (κ:History Bool i) :
    rectAct (controlled (M:=μ i) (comparisonMask H i i T))
      (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ)=
      flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ := by
  let v:=flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ
  have hN:rectAct (controlled (M:=μ i) (historyZero H i T)) v=v :=
    controlled_fix_of_slices _ _ (fun η=>canonical_right_zero h ht H K z η κ)
  have hR:rectAct (memoryMask (A:=A) i T (Public (A:=A) μ i)) v=v :=
    flagRun_mask h H K _ (initial_lengths T z) i κ
  have he:controlled (M:=μ i) (comparisonMask H i i T)=
      controlled (M:=μ i) (historyZero H i T)*memoryMask (A:=A) i T (Public (A:=A) μ i) := by
    rw [memoryMask,←controlled_const,controlled_mul]
    rfl
  change rectAct (controlled (M:=μ i) (comparisonMask H i i T)) v=v
  rw [he,rectAct_mul,hR,hN]

theorem branch_flag_eq {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0)) (n:ℕ) :
    branchRun (E:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (flagStage h H K) z n=
      flagRun h H K z n := by
  induction n with
  | zero=>rfl
  | succ n ih=>funext κ; simp only [branchRun,flagRun,ih]

theorem branch_raw_eq {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0)) (n:ℕ) :
    branchRun (E:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (rawFlagStage h H K) z n=
      rawFlagRun h H K z n := by
  induction n with
  | zero=>rfl
  | succ n ih=>funext κ; simp only [branchRun,rawFlagRun,ih]

theorem flag_raw_distance {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) (hn:n≤Fintype.card A) :
    ‖pack (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) n)-
      pack (rawFlagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) n)‖≤
        ∑i∈Finset.range n,(i:ℝ)/Fintype.card A := by
  rw [←branch_flag_eq,←branch_raw_eq]
  apply branch_distance
  · intro i hi; positivity
  · intro i hi; exact raw_stage_stack_norm h ht H K hK i
  · intro i hi
    rw [branch_flag_eq]
    have hloc:=fun κ:History Bool i=>stage_difference_energy h ht H K hK i i (by omega) _
      (actual_comparison_mask h ht H K z i κ)
    calc
      _ ≤ ∑κ:History Bool i,((i:ℝ)/Fintype.card A)^2*
          ‖flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ‖^2 :=
        Finset.sum_le_sum (fun κ _=>hloc κ)
      _ = ((i:ℝ)/Fintype.card A)^2*∑κ:History Bool i,
          ‖flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ‖^2 := by rw [Finset.mul_sum]
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (flagRun_mass_le_one h ht H K hK z hz)
          (sq_nonneg ((i:ℝ)/Fintype.card A))

theorem flag_packed_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) :
    ‖pack (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) n)‖≤1 := by
  have hh:=flagRun_mass_le_one (q:=n) h ht H K hK z hz
  rw [←pack_norm_sq] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num:(0:ℝ)≤1)).mp (by simpa only [one_pow] using hh)

theorem raw_packed_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) :
    ‖pack (rawFlagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) n)‖≤1 := by
  rw [←branch_raw_eq,packed_run]
  apply run_norm
  · intro i
    exact carry_norm (K:=History Bool i) (rawFlagStage h H K i) 1 (by norm_num)
      (raw_stage_stack_norm h ht H K hK i)
  · have hh:‖WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)‖≤1 := by
      rwa [ICO.MHFockRunIsometry.initial_norm T (WithLp.toLp 2 z)]
    have hs:‖pack (branchRun (E:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
        (rawFlagStage h H K) (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) 0)‖^2≤1 := by
      rw [pack_norm_sq]
      simp only [branchRun]
      change (∑_:PUnit,‖WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)‖^2)≤1
      simp only [Fintype.sum_unique]
      nlinarith [norm_nonneg (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z))]
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num:(0:ℝ)≤1)).mp (by simpa only [one_pow] using hs)

#print axioms flag_raw_distance
#print axioms raw_packed_norm
end
end ICO.C6RawHybrid


