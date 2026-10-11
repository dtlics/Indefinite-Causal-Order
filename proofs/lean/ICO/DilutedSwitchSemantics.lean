import ICO.DilutedSwitchTarget

namespace ICO.DilutedSwitchTarget
open ICO.QubitCircuitLink ICO.QubitCircuitMatrix ICO.QubitLink
open ICO.ExactTensorCertificates ICO.ExactSeparation ICO.PositiveSupport
open Matrix
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
def targetGram (lambda mu : ℝ) : Matrix (Fin 25) (Fin 25) ℝ :=
  Matrix.diagonal (fun a => targetEntry lambda mu a.val a.val)

theorem targetGram_entry (lambda mu : ℝ) (a b : Fin 25) :
    targetGram lambda mu a b = targetEntry lambda mu a.val b.val := by
  by_cases hab : a = b
  · subst b; simp [targetGram, targetEntry]
  · have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)
    simp [targetGram, Matrix.diagonal_apply, targetEntry, hab, hn]

def targetSupport : Matrix (Fin 128) (Fin 25) ℝ :=
  fun i a => basisEntry i.val a.val

theorem targetChoi_real_factor (lambda mu : ℝ) :
    (fun i j : Fin 128 => (targetChoi lambda mu i j).re) =
      targetSupport * targetGram lambda mu * targetSupport.transpose := by
  ext i j
  simp [targetChoi, rankOne, Matrix.vecMulVec_apply, basisVector, targetGram, targetSupport,
    Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sum_apply, Complex.re_sum,
    Complex.mul_re, mul_assoc, mul_left_comm, mul_comm]

theorem targetGram_symmetric (lambda mu : ℝ) (a b : Fin 25) :
    targetGram lambda mu a b = targetGram lambda mu b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp [targetGram, Matrix.diagonal_apply, h, Ne.symm h]

theorem linked_target (lambda mu : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    linkMatrix U V * targetChoi lambda mu * (linkMatrix U V)ᴴ =
      ((((1-lambda)*(1-mu)/8 : ℝ) : ℂ) * frobeniusMass U * frobeniusMass V) •
        rankOne (outputVector U V 0) +
      ((((lambda*(1-mu)/4 : ℝ) : ℂ) * frobeniusMass V) • rankOne (outputVector U V 1)) +
      (((((1-lambda)*mu/4 : ℝ) : ℂ) * frobeniusMass U) • rankOne (outputVector U V 2)) +
      (((lambda*mu/2 : ℝ) : ℂ) • rankOne (outputVector U V 3)) := by
  rw [linked_target_columns]
  ext o p
  simp [Fin.sum_univ_succ, columnScale, columnGroup, targetEntry, QubitLink.bit,
    Matrix.sum_apply, Matrix.smul_apply, frobeniusMass, smul_eq_mul]
  ring

theorem frobeniusMass_trace (U : Matrix (Fin 2) (Fin 2) ℂ) :
    frobeniusMass U = Matrix.trace (Uᴴ * U) := by
  simp [frobeniusMass, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

theorem frobeniusMass_unitary (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    frobeniusMass U = 2 := by
  rw [frobeniusMass_trace, hU]
  simp [Matrix.trace]

theorem frobeniusMass_kraus {I : Type*} [Fintype I]
    (U : I → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∑ i, (U i)ᴴ * U i = 1) :
    (∑ i, frobeniusMass (U i)) = 2 := by
  simp_rw [frobeniusMass_trace]
  rw [← Matrix.trace_sum, hU]
  simp [Matrix.trace]

theorem linked_target_unitaries (lambda mu : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    linkMatrix U V * targetChoi lambda mu * (linkMatrix U V)ᴴ =
      ((((1-lambda)*(1-mu)/2 : ℝ) : ℂ) • rankOne (outputVector U V 0)) +
      (((lambda*(1-mu)/2 : ℝ) : ℂ) • rankOne (outputVector U V 1)) +
      ((((1-lambda)*mu/2 : ℝ) : ℂ) • rankOne (outputVector U V 2)) +
      (((lambda*mu/2 : ℝ) : ℂ) • rankOne (outputVector U V 3)) := by
  rw [linked_target, frobeniusMass_unitary U hU, frobeniusMass_unitary V hV]
  push_cast
  congr 2 <;> ring

theorem rankOne_sqrt_scale {I : Type*} (s : ℝ) (hs : 0 ≤ s) (v : I → ℂ) :
    rankOne ((Real.sqrt s : ℂ) • v) = (s : ℂ) • rankOne v := by
  rw [rankOne_scale]
  congr 1
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt hs]

def unitaryWeights (lambda mu : ℝ) : Fin 4 → ℂ :=
  ![Real.sqrt ((1-lambda)*(1-mu)/2), Real.sqrt (lambda*(1-mu)/2),
    Real.sqrt ((1-lambda)*mu/2), Real.sqrt (lambda*mu/2)]

theorem target_unitary_support (lambda mu : ℝ) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1)
    (hm0 : 0 ≤ mu) (hm1 : mu ≤ 1)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    linkMatrix U V * targetChoi lambda mu * (linkMatrix U V)ᴴ =
      ∑ b : Fin 4, rankOne (unitaryWeights lambda mu b • outputVector U V b) := by
  rw [linked_target_unitaries lambda mu U V hU hV]
  have hl : 0 ≤ 1-lambda := sub_nonneg.mpr hl1
  have hm : 0 ≤ 1-mu := sub_nonneg.mpr hm1
  have h00 : 0 ≤ (1-lambda)*(1-mu)/2 := by positivity
  have h10 : 0 ≤ lambda*(1-mu)/2 := by positivity
  have h01 : 0 ≤ (1-lambda)*mu/2 := by positivity
  have h11 : 0 ≤ lambda*mu/2 := by positivity
  simp only [Fin.sum_univ_succ, unitaryWeights, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  rw [rankOne_sqrt_scale _ h00, rankOne_sqrt_scale _ h10,
    rankOne_sqrt_scale _ h01, rankOne_sqrt_scale _ h11]
  simp only [add_assoc]
  rfl

def identityOutput : Fin 8 → ℂ := outputVector 0 0 0
def queryOutput (U : Matrix (Fin 2) (Fin 2) ℂ) : Fin 8 → ℂ := outputVector U 0 1

theorem output_zero (U V : Matrix (Fin 2) (Fin 2) ℂ) : outputVector U V 0 = identityOutput := by
  funext o; simp [outputVector, identityOutput]

theorem output_one (U V : Matrix (Fin 2) (Fin 2) ℂ) : outputVector U V 1 = queryOutput U := by
  funext o; simp [outputVector, queryOutput]

theorem output_two (U V : Matrix (Fin 2) (Fin 2) ℂ) : outputVector U V 2 = queryOutput V := by
  funext o; simp [outputVector, queryOutput]

/-- The normalized output Choi matrix of the standard switch with control
fixed to |+>, for arbitrary Kraus lists for its two input channels. -/
def switchChoi {I J : Type*} [Fintype I] [Fintype J]
    (U : I → Matrix (Fin 2) (Fin 2) ℂ) (V : J → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  (1/2 : ℂ) • ∑ i, ∑ j, rankOne (outputVector (U i) (V j) 3)

def queryChoi {I : Type*} [Fintype I] (U : I → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 8) (Fin 8) ℂ := (1/2 : ℂ) • ∑ i, rankOne (queryOutput (U i))

def identityChoi : Matrix (Fin 8) (Fin 8) ℂ := (1/2 : ℂ) • rankOne identityOutput

/-- Canonical diagonal target coordinates implement the identity-diluted
switch on every pair of trace-preserving Kraus channels, not only unitaries. -/
theorem linked_target_kraus {I J : Type*} [Fintype I] [Fintype J]
    (lambda mu : ℝ) (U : I → Matrix (Fin 2) (Fin 2) ℂ) (V : J → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) :
    (∑ i, ∑ j, linkMatrix (U i) (V j) * targetChoi lambda mu * (linkMatrix (U i) (V j))ᴴ) =
      (((1-lambda)*(1-mu) : ℝ) : ℂ) • identityChoi +
      ((lambda*(1-mu) : ℝ) : ℂ) • queryChoi U +
      (((1-lambda)*mu : ℝ) : ℂ) • queryChoi V +
      ((lambda*mu : ℝ) : ℂ) • switchChoi U V := by
  simp_rw [linked_target, output_zero, output_one, output_two]
  ext o p
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, switchChoi, queryChoi, identityChoi]
  try simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  rw [frobeniusMass_kraus U hU, frobeniusMass_kraus V hV]
  push_cast
  ring


#print axioms linked_target
end
end ICO.DilutedSwitchTarget

