import ICO.C6FockCompression
import ICO.MHRectangularAction

/-! Pure-query preparation on the actual Fock register is an isometry for
every normalized vector. This preserves arbitrary entanglement with memory. -/
namespace ICO.C6QueryPreparation
open Matrix QIT ICO.C6FockCompression ICO.MHBoundedRecording ICO.MHFockKnownOperation
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {A : Type*} [Fintype A] [DecidableEq A]

def queryRecordEquiv (T : ℕ) : InputCutoff (α:=A) T ≃ A×Records (α:=A) T where
  toFun i := (i.2.1,records i)
  invFun p := ⟨⟨p.2.1,p.2.2.2⟩,(p.1,p.2.2.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem query_gram (T : ℕ) (ψ : A→ℂ) (hψ : ∑a,‖ψ a‖^2=1) :
    (fockQuery T ψ).conjTranspose*fockQuery T ψ=1 := by
  have hc : (∑a,star (ψ a)*ψ a)=(1:ℂ) := by
    calc
      _ = ((∑a,‖ψ a‖^2:ℝ):ℂ) := by
        simp [Complex.star_def,Complex.conj_mul',Complex.ofReal_sum]
      _ = 1 := by rw [hψ]; norm_num
  ext R S
  rw [Matrix.mul_apply]
  have he : (∑i:InputCutoff (α:=A) T,
      (fockQuery T ψ).conjTranspose R i*fockQuery T ψ i S)=
      ∑p:A×Records (α:=A) T,
        (fockQuery T ψ).conjTranspose R ((queryRecordEquiv T).symm p)*
        fockQuery T ψ ((queryRecordEquiv T).symm p) S :=
    ((queryRecordEquiv T).symm.sum_comp _).symm
  rw [he]
  by_cases h : R=S
  · subst S
    simpa [Matrix.conjTranspose_apply,fockQuery,queryRecordEquiv,records,
      Fintype.sum_prod_type] using hc
  · simp [Matrix.conjTranspose_apply,fockQuery,queryRecordEquiv,records,
      Fintype.sum_prod_type,Matrix.one_apply,h,Ne.symm h]

variable {M : Type*} [Fintype M] [DecidableEq M]

theorem query_memory_gram (T : ℕ) (ψ : A→ℂ) (hψ : ∑a,‖ψ a‖^2=1) :
    (Matrix.kronecker (fockQuery T ψ) (1:CMatrix M)).conjTranspose*
      Matrix.kronecker (fockQuery T ψ) (1:CMatrix M)=1 := by
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ←Matrix.mul_kronecker_mul,Matrix.mul_one]
  rw [query_gram T ψ hψ,Matrix.one_kronecker_one]

theorem prepared_mass (T : ℕ) (ψ : A→ℂ) (hψ : ∑a,‖ψ a‖^2=1)
    (v : Records (α:=A) T×M→ℂ) :
    (∑i:InputCutoff (α:=A) T×M,
      ‖(Matrix.kronecker (fockQuery T ψ) (1:CMatrix M)*ᵥv) i‖^2)=
        ∑R:Records (α:=A) T×M,‖v R‖^2 := by
  have hh := ICO.MHRectangularAction.rectAct_norm
    (Matrix.kronecker (fockQuery T ψ) (1:CMatrix M)) (query_memory_gram T ψ hψ)
    (WithLp.toLp 2 v)
  have hs := congrArg (fun z:ℝ => z^2) hh
  simpa only [ICO.MHRectangularAction.rectAct,Matrix.toEuclideanLin_apply,
    PiLp.norm_sq_eq_of_L2,WithLp.ofLp_toLp] using hs

#print axioms query_memory_gram
#print axioms prepared_mass
end
end ICO.C6QueryPreparation
