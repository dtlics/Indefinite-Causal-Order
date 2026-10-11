import ICO.MHPhasePermutation
import ICO.PureHybrid

/-! Exact fiber semantics of coherent classical oracle labels, with arbitrary
rectangular operations and changing accessible dimensions. -/
namespace ICO.MHControlledMixture
open Matrix QIT ICO.PureHybrid ICO.MHPhasePermutation
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
variable {E A B : Type*} [Fintype E] [DecidableEq E]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def controlledMatrix (V : E → Matrix B A ℂ) : Matrix (B × E) (A × E) ℂ :=
  fun o i => if o.2=i.2 then V o.2 o.1 i.1 else 0

theorem controlled_mulVec (V : E → Matrix B A ℂ) (x : A × E → ℂ) (o : B) (e : E) :
    (controlledMatrix V *ᵥ x) (o,e) = ∑ i : A, V e o i * x (i,e) := by
  simp [controlledMatrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type]

theorem controlled_adjoint (V : E → Matrix B A ℂ) :
    (controlledMatrix V).conjTranspose = controlledMatrix (fun e => (V e).conjTranspose) := by
  ext o i
  by_cases h : o.2=i.2
  · simp [controlledMatrix,Matrix.conjTranspose_apply,h,eq_comm]
  · simp [controlledMatrix,Matrix.conjTranspose_apply,h,Ne.symm h]

theorem controlled_constant (V : Matrix B A ℂ) :
    controlledMatrix (fun _ : E => V) = Matrix.kronecker V (1 : CMatrix E) := by
  ext o i
  simp [controlledMatrix,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]

def fiberTrajectory {H : ℕ → Type*} [∀ n, Fintype (H n)] [∀ n, DecidableEq (H n)]
    (V : (n : ℕ) → E → Matrix (H (n+1)) (H n) ℂ)
    (x : E → H 0 → ℂ) : (n : ℕ) → E → H n → ℂ
  | 0 => x
  | n+1 => fun e => V n e *ᵥ fiberTrajectory V x n e

def controlledTrajectory {H : ℕ → Type*} [∀ n, Fintype (H n)] [∀ n, DecidableEq (H n)]
    (V : (n : ℕ) → E → Matrix (H (n+1)) (H n) ℂ)
    (x : E → H 0 → ℂ) (a : ℂ) : (n : ℕ) → H n × E → ℂ
  | 0 => fun o => a*x o.2 o.1
  | n+1 => controlledMatrix (V n) *ᵥ controlledTrajectory V x a n

theorem trajectory_fibers {H : ℕ → Type*} [∀ n, Fintype (H n)] [∀ n, DecidableEq (H n)]
    (V : (n : ℕ) → E → Matrix (H (n+1)) (H n) ℂ)
    (x : E → H 0 → ℂ) (a : ℂ) (n : ℕ) (o : H n) (e : E) :
    controlledTrajectory V x a n (o,e) = a*fiberTrajectory V x n e o := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [controlledTrajectory,controlled_mulVec]
    simp_rw [ih]
    simp only [fiberTrajectory,Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem erase_uniform_fibers (v : E → A → ℂ) (a : ℂ) :
    partialTraceB (outer (WithLp.toLp 2 (fun o : A × E => a*v o.2 o.1))
      (WithLp.toLp 2 (fun o : A × E => a*v o.2 o.1))) =
      (star a*a) • ∑ e : E, outer (WithLp.toLp 2 (v e)) (WithLp.toLp 2 (v e)) := by
  ext i j
  simp only [partialTraceB,outer,Matrix.vecMulVec_apply,PiLp.toLp_apply,
    Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,star_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem erase_trajectory {H : ℕ → Type*} [∀ n, Fintype (H n)] [∀ n, DecidableEq (H n)]
    (V : (n : ℕ) → E → Matrix (H (n+1)) (H n) ℂ)
    (x : E → H 0 → ℂ) (a : ℂ) (n : ℕ) :
    partialTraceB (outer (WithLp.toLp 2 (controlledTrajectory V x a n))
      (WithLp.toLp 2 (controlledTrajectory V x a n))) =
      (star a*a) • ∑ e : E, outer (WithLp.toLp 2 (fiberTrajectory V x n e))
        (WithLp.toLp 2 (fiberTrajectory V x n e)) := by
  have hf : controlledTrajectory V x a n = fun o => a*fiberTrajectory V x n o.2 o.1 := by
    funext o
    exact trajectory_fibers V x a n o.1 o.2
  rw [hf,erase_uniform_fibers]

theorem phase_query_controlled {Q : Type*} [Fintype Q] [DecidableEq Q] :
    ICO.MHPurifiedFourier.phaseQuery (A := Q) =
      controlledMatrix (ICO.MHPhasePermutation.phaseOracle (A := Q)) := by
  ext o i
  exact controlled_blocks o.2 i.2 o.1 i.1

theorem erase_phase_trajectory {Q : Type*} [Fintype Q] [DecidableEq Q]
    {H : ℕ → Type*} [∀ n, Fintype (H n)] [∀ n, DecidableEq (H n)]
    (V : (n : ℕ) → ICO.MHTernaryCompression.Environment Q → Matrix (H (n+1)) (H n) ℂ)
    (x : ICO.MHTernaryCompression.Environment Q → H 0 → ℂ) (n : ℕ) :
    partialTraceB (outer (WithLp.toLp 2 (controlledTrajectory V x (uniformAmplitude (A := Q)) n))
      (WithLp.toLp 2 (controlledTrajectory V x (uniformAmplitude (A := Q)) n))) =
      (Fintype.card (ICO.MHTernaryCompression.Environment Q) : ℂ)⁻¹ •
        ∑ e, outer (WithLp.toLp 2 (fiberTrajectory V x n e))
          (WithLp.toLp 2 (fiberTrajectory V x n e)) := by
  rw [erase_trajectory,uniformAmplitude_square]

#print axioms trajectory_fibers
#print axioms erase_phase_trajectory
end
end ICO.MHControlledMixture

