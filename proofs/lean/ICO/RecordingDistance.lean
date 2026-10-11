import ICO.FreshOutputDistance
import QIT.Classical.CQState
import QIT.Channels.Diamond

/-!
# Quantum-memory fresh-output bounds and adaptive hybrids

The lemmas here apply to positive, possibly subnormalized memory blocks.
They do not assert that a particular recording oracle produces those blocks;
that oracle-to-mixture identity is a separate obligation.
-/

namespace ICO.RecordingDistance

open QIT
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {a b α ι : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype α] [DecidableEq α]
  [Fintype ι] [DecidableEq ι]

/-- Absolute real homogeneity of the trace norm, including negative weights. -/
theorem traceNorm_real_smul_abs (c : ℝ) (M : CMatrix a) :
    traceNorm ((c : ℂ) • M) = |c| * traceNorm M := by
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
    exact traceNorm_real_smul_eq hc M
  · have hn : 0 ≤ -c := by linarith
    have h := traceNorm_real_smul_eq hn M
    simpa only [Complex.ofReal_neg, neg_smul, traceNorm_neg,
      abs_of_neg (lt_of_not_ge hc)] using h

/-- A classical output distribution accompanied by one unnormalized memory block. -/
def memoryOutput (p : α → ℝ) (T : CMatrix a) : CMatrix (α × a) :=
  QIT.Classical.blockDiagonal (fun x => (p x : ℂ) • T)

/-- Classical total variation multiplies the mass of an arbitrary positive
    quantum memory block. There is no restriction on the memory dimension. -/
theorem memoryOutput_distance (p q : α → ℝ) (T : CMatrix a)
    (hT : T.PosSemidef) :
    normalizedTraceDistance (memoryOutput p T) (memoryOutput q T) =
      ((∑ x, |p x - q x|) / 2) * T.trace.re := by
  unfold normalizedTraceDistance traceNormDistance memoryOutput
  rw [← QIT.Classical.blockDiagonal_sub, QIT.Classical.traceNorm_blockDiagonal]
  have hsub (x : α) : (p x : ℂ) • T - (q x : ℂ) • T =
      ((p x - q x : ℝ) : ℂ) • T := by rw [Complex.ofReal_sub, sub_smul]
  simp_rw [hsub, traceNorm_real_smul_abs, traceNorm_posSemidef_eq_trace_re T hT]
  rw [← Finset.sum_mul]
  ring

/-- A forbidden set of `k` output labels costs exactly `k/d` times the mass of
    a positive memory block, even when that block is subnormalized. -/
theorem fresh_memoryOutput_distance (s : Finset α) (hs : s.card < Fintype.card α)
    (T : CMatrix a) (hT : T.PosSemidef) :
    normalizedTraceDistance (memoryOutput (FreshOutputDistance.uniformOutside s) T)
      (memoryOutput (fun _ => 1 / (Fintype.card α : ℝ)) T) =
      ((s.card : ℝ) / (Fintype.card α : ℝ)) * T.trace.re := by
  rw [memoryOutput_distance _ _ T hT, FreshOutputDistance.totalVariation_uniformOutside s hs]

omit [DecidableEq ι] in
/-- Finite mixing cannot increase trace distance beyond the sum of the
    individual, unnormalized distances. -/
theorem distance_sum_le (A B : ι → CMatrix a) :
    normalizedTraceDistance (∑ i, A i) (∑ i, B i) ≤
      ∑ i, normalizedTraceDistance (A i) (B i) := by
  unfold normalizedTraceDistance traceNormDistance
  rw [← Finset.sum_sub_distrib]
  have h := QIT.traceNorm_sum_le_sum_traceNorm Finset.univ (fun i => A i - B i)
  simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)

omit [DecidableEq ι] in
/-- The positive record-block mixture estimate. The total memory mass is at
    most one; every record forbids at most `m` output labels. -/
theorem fresh_record_mixture_distance (forbidden : ι → Finset α)
    (T : ι → CMatrix a) (hT : ∀ i, (T i).PosSemidef)
    (hmass : ∑ i, (T i).trace.re ≤ 1) (m : ℕ)
    (hsize : ∀ i, (forbidden i).card ≤ m) (hmd : m < Fintype.card α) :
    normalizedTraceDistance
      (∑ i, memoryOutput (FreshOutputDistance.uniformOutside (forbidden i)) (T i))
      (∑ i, memoryOutput (fun _ : α => 1 / (Fintype.card α : ℝ)) (T i)) ≤
      (m : ℝ) / (Fintype.card α : ℝ) := by
  calc
    _ ≤ ∑ i, normalizedTraceDistance
        (memoryOutput (FreshOutputDistance.uniformOutside (forbidden i)) (T i))
        (memoryOutput (fun _ : α => 1 / (Fintype.card α : ℝ)) (T i)) :=
      distance_sum_le _ _
    _ = ∑ i, ((forbidden i).card : ℝ) / (Fintype.card α : ℝ) * (T i).trace.re := by
      apply Finset.sum_congr rfl
      intro i _
      exact fresh_memoryOutput_distance _ (lt_of_le_of_lt (hsize i) hmd) _ (hT i)
    _ ≤ ∑ i, ((m : ℝ) / (Fintype.card α : ℝ)) * (T i).trace.re := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right
      · exact div_le_div_of_nonneg_right (by exact_mod_cast hsize i) (Nat.cast_nonneg _)
      · exact (Complex.nonneg_iff.mp (hT i).trace_nonneg).1
    _ = ((m : ℝ) / (Fintype.card α : ℝ)) * ∑ i, (T i).trace.re :=
      (Finset.mul_sum ..).symm
    _ ≤ (m : ℝ) / (Fintype.card α : ℝ) := by
      have hc : 0 ≤ (m : ℝ) / (Fintype.card α : ℝ) := by positivity
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass hc

/-- General Hermitian trace norm is the sum of positive and negative masses. -/
theorem traceNorm_hermitian_parts (H : CMatrix a) (hH : H.IsHermitian) :
    traceNorm H = (H⁺).trace.re + (H⁻).trace.re := by
  have hAbs : H⁺ + H⁻ = CFC.abs H := CFC.posPart_add_negPart H hH.isSelfAdjoint
  have h := congrArg Complex.re (congrArg Matrix.trace hAbs)
  simpa only [Matrix.trace_add, Complex.add_re] using h.symm

/-- Positive trace-nonincreasing maps contract trace norm on every Hermitian
    input, including differences whose traces are unequal. -/
theorem traceNorm_contract_hermitian (Φ : MatrixMap a b)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ) (H : CMatrix a) (hH : H.IsHermitian) :
    traceNorm (Φ H) ≤ traceNorm H := by
  have hp : H⁺.PosSemidef := QIT.posPart_posSemidef H
  have hn : H⁻.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hdecomp : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  rw [← hdecomp, map_sub]
  calc
    traceNorm (Φ H⁺ - Φ H⁻) ≤ traceNorm (Φ H⁺) + traceNorm (Φ H⁻) := by
      simpa only [sub_eq_add_neg, traceNorm_neg] using traceNorm_add_le (Φ H⁺) (-(Φ H⁻))
    _ = (Φ H⁺).trace.re + (Φ H⁻).trace.re := by
      rw [traceNorm_posSemidef_eq_trace_re _ (hΦ.mapsPositive _ hp),
        traceNorm_posSemidef_eq_trace_re _ (hΦ.mapsPositive _ hn)]
    _ ≤ (H⁺).trace.re + (H⁻).trace.re :=
      add_le_add (hΦ.traceNonincreasing _ hp) (hΦ.traceNonincreasing _ hn)
    _ = traceNorm (H⁺ - H⁻) := by rw [hdecomp, traceNorm_hermitian_parts H hH]

/-- Trace-distance contractivity for positive subnormalized states; equal
    traces are not assumed. -/
theorem distance_contract (Φ : MatrixMap a b)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ) (A B : CMatrix a)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    normalizedTraceDistance (Φ A) (Φ B) ≤ normalizedTraceDistance A B := by
  unfold normalizedTraceDistance traceNormDistance
  rw [← map_sub]
  exact mul_le_mul_of_nonneg_left
    (traceNorm_contract_hermitian Φ hΦ _ (hA.isHermitian.sub hB.isHermitian)) (by norm_num)

/-- A hybrid with per-step error `ε i` accumulates the sum of those errors.
    The one-step hypothesis is exposed so the recording-oracle bridge cannot
    be mistaken for a theorem already proved here. -/
theorem distance_hybrid_sum (A B : ℕ → CMatrix a) (ε : ℕ → ℝ)
    (hinit : A 0 = B 0)
    (hstep : ∀ i, normalizedTraceDistance (A (i + 1)) (B (i + 1)) ≤
      normalizedTraceDistance (A i) (B i) + ε i) (n : ℕ) :
    normalizedTraceDistance (A n) (B n) ≤ ∑ i ∈ Finset.range n, ε i := by
  induction n with
  | zero => simp [hinit]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact le_trans (hstep n) (add_le_add ih (le_refl _))

/-- A CP hybrid: each local replacement is evaluated on the actual prefix,
    and the ideal next operation contracts the accumulated distance. -/
theorem distance_hybrid_cp (A B : ℕ → CMatrix a) (Φ : ℕ → MatrixMap a a)
    (hΦ : ∀ i, MatrixMap.TraceNonincreasingCP (Φ i))
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (hinit : A 0 = B 0) (hnext : ∀ i, B (i + 1) = Φ i (B i))
    (ε : ℕ → ℝ)
    (hlocal : ∀ i, normalizedTraceDistance (A (i + 1)) (Φ i (A i)) ≤ ε i)
    (n : ℕ) : normalizedTraceDistance (A n) (B n) ≤ ∑ i ∈ Finset.range n, ε i := by
  apply distance_hybrid_sum A B ε hinit
  intro i
  rw [hnext]
  have ht := normalizedTraceDistance_triangle (A (i + 1)) (Φ i (A i)) (Φ i (B i))
  have hc := distance_contract (Φ i) (hΦ i) (A i) (B i) (hA i) (hB i)
  linarith [hlocal i]

/-- If the lost matrix is positive, its half trace norm is exactly half its
    lost mass. This is the required subnormalization accounting identity. -/
theorem distance_of_positive_loss (A B : CMatrix a) (hloss : (B - A).PosSemidef) :
    normalizedTraceDistance A B = (B.trace.re - A.trace.re) / 2 := by
  unfold normalizedTraceDistance traceNormDistance
  have hneg : A - B = -(B - A) := by abel
  rw [hneg, traceNorm_neg, traceNorm_posSemidef_eq_trace_re _ hloss, Matrix.trace_sub]
  simp only [Complex.sub_re]
  ring

/-- The odd per-wrapper errors sum to `q²/d`; all mass losses telescope. -/
theorem sum_odd_and_mass_loss (mass : ℕ → ℝ) (d : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ((2 * (i : ℝ) + 1) / d + (mass i - mass (i + 1)) / 2)) =
      (n : ℝ) ^ 2 / d + (mass 0 - mass n) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The final lost-mass estimate follows from actual CP contractions and the
    one-wrapper fresh-output/loss estimate; there is no renormalization. -/
theorem distance_hybrid_lost_mass (A B : ℕ → CMatrix a) (Φ : ℕ → MatrixMap a a)
    (hΦ : ∀ i, MatrixMap.TraceNonincreasingCP (Φ i))
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (hinit : A 0 = B 0) (hnext : ∀ i, B (i + 1) = Φ i (B i))
    (mass : ℕ → ℝ) (hmass : mass 0 = 1) (d : ℝ)
    (hlocal : ∀ i, normalizedTraceDistance (A (i + 1)) (Φ i (A i)) ≤
      (2 * (i : ℝ) + 1) / d + (mass i - mass (i + 1)) / 2) (n : ℕ) :
    normalizedTraceDistance (A n) (B n) ≤ (n : ℝ) ^ 2 / d + (1 - mass n) / 2 := by
  have h := distance_hybrid_cp A B Φ hΦ hA hB hinit hnext _ hlocal n
  rwa [sum_odd_and_mass_loss, hmass] at h

/-- A local trace-nonincreasing operation can only decrease the untouched
    memory marginal in PSD order. The proof realizes the lost marginal as a
    completely positive effect map tensored with the memory identity. -/
theorem local_contraction_loses_positive_memory (Φ : MatrixMap a b)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ) (ρ : CMatrix (a × ι))
    (hρ : ρ.PosSemidef) :
    (QIT.partialTraceA ρ - QIT.partialTraceA
      (MatrixMap.kron Φ (Channel.idChannel ι).map ρ)).PosSemidef := by
  let E := hΦ.lossEffect
  let Ψ : MatrixMap a PUnit.{1} := MatrixMap.traceEffectToUnit E
  have hE : E.PosSemidef := hΦ.lossEffect_posSemidef
  have hΨ : MatrixMap.IsCompletelyPositive Ψ := MatrixMap.ofKraus_completelyPositive _
  have hTensor : MatrixMap.IsCompletelyPositive
      (MatrixMap.kron Ψ (Channel.idChannel ι).map) :=
    MatrixMap.isCompletelyPositive_kron _ _ hΨ (Channel.idChannel ι).completelyPositive
  have hPos := QIT.partialTraceA_posSemidef
    (MatrixMap.isCompletelyPositive_mapsPositive _ hTensor ρ hρ)
  have heq : QIT.partialTraceA (MatrixMap.kron Ψ (Channel.idChannel ι).map ρ) =
      QIT.partialTraceA ρ - QIT.partialTraceA
        (MatrixMap.kron Φ (Channel.idChannel ι).map ρ) := by
    ext i j
    let X : CMatrix a := fun x y => ρ (x, i) (y, j)
    have hBefore : QIT.partialTraceA ρ i j = X.trace := rfl
    have hAfter : QIT.partialTraceA
        (MatrixMap.kron Φ (Channel.idChannel ι).map ρ) i j = (Φ X).trace := by
      simp only [QIT.partialTraceA, MatrixMap.kron_idChannel_apply_slice, Matrix.trace,
        Matrix.diag, X]
    have hLost : QIT.partialTraceA
        (MatrixMap.kron Ψ (Channel.idChannel ι).map ρ) i j = (X * E).trace := by
      simp only [QIT.partialTraceA, MatrixMap.kron_idChannel_apply_slice, Ψ]
      simp_rw [MatrixMap.traceEffectToUnit_apply_of_posSemidef hE]
      simp [X]
    have hdual := MatrixMap.ofKraus_trace_duality hΦ.kraus X (1 : CMatrix b)
    rw [hΦ.ofKraus_kraus, Matrix.mul_one] at hdual
    simp only [Matrix.sub_apply]
    rw [hLost, hBefore, hAfter]
    change (X * (1 - MatrixMap.krausAdjoint hΦ.kraus (1 : CMatrix b))).trace = _
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one, ← hdual]
  rwa [heq] at hPos

/-- A scalar PSD upper bound remains an expectation bound with any entangled
    memory. The memory dimension does not enter the constant. -/
theorem bounded_effect_with_memory (K : CMatrix a) (c : ℝ)
    (hK : ((c : ℂ) • (1 : CMatrix a) - K).PosSemidef)
    (ρ : CMatrix (a × ι)) (hρ : ρ.PosSemidef) :
    ((Matrix.kronecker K (1 : CMatrix ι) * ρ).trace).re ≤ c * ρ.trace.re := by
  have hTensor := hK.kronecker (Matrix.PosSemidef.one : (1 : CMatrix ι).PosSemidef)
  have heq : Matrix.kronecker ((c : ℂ) • (1 : CMatrix a) - K) (1 : CMatrix ι) =
      (c : ℂ) • (1 : CMatrix (a × ι)) - Matrix.kronecker K (1 : CMatrix ι) := by
    ext u v
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, sub_mul]
    congr 1
    rw [mul_assoc]
    congr 1
    exact congrFun (congrFun (Matrix.one_kronecker_one (m := a) (n := ι) (α := ℂ)) u) v
  change (Matrix.kronecker ((c : ℂ) • (1 : CMatrix a) - K) (1 : CMatrix ι)).PosSemidef
    at hTensor
  rw [heq] at hTensor
  have hp := QIT.cMatrix_trace_mul_posSemidef_re_nonneg hTensor hρ
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul] at hp
  simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hp
  linarith

end
end ICO.RecordingDistance
