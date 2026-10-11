import ICO.MHPurifiedFourier
import ICO.MHHaarAbsorption

/-! Concrete phase-permutation blocks, uniform purification, and Haar absorption. -/
namespace ICO.MHPhasePermutation
open Matrix QIT ICO.MHTernaryCompression ICO.MHTernaryFourier
  ICO.MHPurifiedOracle ICO.MHPurifiedFourier
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem phase_star_self (z : ZMod 3) : star (ZMod.stdAddChar z)*ZMod.stdAddChar z = 1 := by
  have h : star (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    simpa [Complex.star_def] using (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := 3)) z).symm
  rw [h,← AddChar.map_add_eq_mul]
  simp

def phaseOracle (e : Environment A) : CMatrix A :=
  ICO.MemoryEmbedding.embedding ⟨e.1,e.1.injective⟩ *
    Matrix.diagonal (fun x => ZMod.stdAddChar (e.2 x))

theorem phaseOracle_entry (e : Environment A) (y x : A) :
    phaseOracle e y x = if y=e.1 x then ZMod.stdAddChar (e.2 x) else 0 := by
  simp [phaseOracle,Matrix.mul_diagonal,ICO.MemoryEmbedding.embedding]

theorem phaseOracle_isometry (e : Environment A) :
    (phaseOracle e).conjTranspose * phaseOracle e = 1 := by
  let P := ICO.MemoryEmbedding.embedding ⟨e.1,e.1.injective⟩
  let D := Matrix.diagonal (fun x => ZMod.stdAddChar (e.2 x))
  have hP : P.conjTranspose*P=1 := ICO.MemoryEmbedding.embedding_isometry _
  change (P*D).conjTranspose*(P*D)=1
  calc
    _ = D.conjTranspose*(P.conjTranspose*P)*D := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = D.conjTranspose*D := by rw [hP,Matrix.mul_one]
    _ = 1 := by
      simp only [D,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
      simpa only [Function.comp_apply,Pi.star_apply,phase_star_self] using (Matrix.diagonal_one (n := A) (α := ℂ))

def phaseOracleUnitary (e : Environment A) : Matrix.unitaryGroup A ℂ :=
  ⟨phaseOracle e,Matrix.mem_unitaryGroup_iff'.mpr (phaseOracle_isometry e)⟩

theorem controlled_blocks (e e' : Environment A) (y x : A) :
    phaseQuery (y,e) (x,e') = if e=e' then phaseOracle e y x else 0 := by
  by_cases h : e=e'
  · subst e'
    simp [phaseQuery_entry,phaseEquiv,phaseOracle_entry]
  · have hne : (y,e) ≠ phaseEquiv (x,e') := by
      intro he
      exact h (congrArg Prod.snd he)
    simp [phaseQuery_entry,hne,h]

def uniformAmplitude : ℂ :=
  coefficient (A := A) * (((Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ : ℝ) : ℂ)

theorem fourier_initial (e : Environment A) :
    ((environmentFourier (A := A)) *ᵥ initialVector) e = uniformAmplitude (A := A) := by
  rcases e with ⟨π,f⟩
  change (∑ e, environmentFourier (π,f) e * initialVector e) = _
  simp [environmentFourier,Matrix.kronecker,Matrix.one_apply,
    Fintype.sum_prod_type,initialVector_entry,fourierMatrix,character,pairing,uniformAmplitude]

theorem uniformAmplitude_square :
    star (uniformAmplitude (A := A))*uniformAmplitude (A := A) =
      (Fintype.card (Environment A) : ℂ)⁻¹ := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤Fintype.card (Equiv.Perm A) by positivity)
  have hr : (Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ *
      (Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ =
        (Fintype.card (Equiv.Perm A) : ℝ)⁻¹ := by
    rw [← mul_inv,← pow_two,hs]
  have hc : ((((Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ : ℝ) : ℂ)) *
      ((((Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ : ℝ) : ℂ)) =
        (Fintype.card (Equiv.Perm A) : ℂ)⁻¹ := by
    simpa using congrArg Complex.ofReal hr
  have hstar : star ((((Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ : ℝ) : ℂ)) =
      ((((Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ : ℝ) : ℂ)) := by simp
  simp only [uniformAmplitude,star_mul,coefficient_star,hstar]
  calc
    _ = (coefficient (A := A)*coefficient (A := A)) *
      (((((Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ : ℝ) : ℂ)) *
       ((((Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ : ℝ) : ℂ))) := by ring
    _ = _ := by
      rw [coefficient_square,hc]
      simp [Environment,Fintype.card_prod,Nat.cast_mul,mul_comm,mul_inv]

theorem phase_permutation_haar [Nonempty A]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Matrix.unitaryGroup A ℂ → E) :
    (Fintype.card (Environment A) : ℝ)⁻¹ •
      (∑ e : Environment A, ∫ D, ∫ C, f (D*phaseOracleUnitary e*C)
        ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) =
      ∫ U, f U ∂unitaryHaarMeasure (a := A) :=
  ICO.MHHaarAbsorption.finite_mixture_absorption phaseOracleUnitary f

#print axioms controlled_blocks
#print axioms fourier_initial
#print axioms phase_permutation_haar
end
end ICO.MHPhasePermutation
