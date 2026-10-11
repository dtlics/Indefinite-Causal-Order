import ICO.C6TwoFockVacuum
import ICO.C6TwoFockMemory

namespace ICO.C6TwoFockVacuumMemory
open QIT Matrix ICO.C6TwoFockVisible ICO.C6TwoFockMemory ICO.C6TwoFockVacuum
  ICO.C6PolarFock ICO.MHBoundedRecording
open scoped Matrix
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem memoryJ_vacuum_adjoint {t T r : ℕ} (h : t+1≤T) (hr : r≤T) :
    (Matrix.kronecker (polarLeftOnFock (α := A) h) (1:CMatrix M)).conjTranspose*
      memoryJ (A := A) (M := M) T 0 r (by omega)=0 := by
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  change Matrix.kronecker (polarLeftOnFock (α := A) h).conjTranspose (1:CMatrix M)*
    memoryJ (A := A) (M := M) T 0 r (by omega)=0
  rw [memoryJ_factor,mul_submatrix_id]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
  rw [polarLeft_adjoint_vacuum h hr]
  ext i j
  simp [Matrix.submatrix_apply,Matrix.kroneckerMap_apply]

theorem memoryJ_vacuum_complement {t T r : ℕ} (h : t+1≤T) (hr : r≤T) :
    (1-Matrix.kronecker (polarLeftOnFock (α := A) h) (1:CMatrix M)*
      (Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M)).conjTranspose)*
      memoryJ (A := A) (M := M) T 0 r (by omega)=
      memoryJ (A := A) (M := M) T 0 r (by omega) := by
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,
    memoryJ_vacuum_adjoint h hr,Matrix.mul_zero,sub_zero]

#print axioms memoryJ_vacuum_adjoint
#print axioms memoryJ_vacuum_complement
end
end ICO.C6TwoFockVacuumMemory
