import ICO.C6WeightedModeErasure
import ICO.C6ResidualModes

/-! Instantiate raw image erasure with the actual nested-history residuals.
The orthogonality needed by the symmetric-mode isometry is derived here. -/
namespace ICO.C6HistoryImageErasure
open QIT ICO.C6OrthogonalModeBirth ICO.C6RightImageErasure ICO.C6WeightedModeErasure
  ICO.C6ResidualModes
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A H:Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype H] [DecidableEq H]

theorem residual_eq_norm_smul_mode {q:ℕ} (history:Fin q→EuclideanSpace ℂ A) (i:Fin q) :
    residual history i=(‖residual history i‖:ℂ) • C6ResidualModes.mode history i := by
  by_cases hi:residual history i=0
  · simp [hi,C6ResidualModes.mode]
  · have hn : (‖residual history i‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hi)
    rw [C6ResidualModes.mode,smul_smul,mul_inv_cancel₀ hn,one_smul]

/-- An injective list of accepted birth indices and a different current
accepted index automatically give the required orthonormal mode family. -/
theorem accepted_orthonormal {q n:ℕ} (history:Fin q→EuclideanSpace ℂ A)
    (i:Active history) (old:Fin n→Active history) (hinj:Function.Injective old)
    (hfresh:∀j,old j≠i) :
    Orthonormal ℂ (Fin.cons (C6ResidualModes.mode history i)
      (fun j=>C6ResidualModes.mode history (old j))) := by
  have hc:Function.Injective (Fin.cons i old) := by
    intro a b h
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => rfl
      | succ k => exact False.elim (hfresh k h.symm)
    | succ j =>
      cases b using Fin.cases with
      | zero => exact False.elim (hfresh j h)
      | succ k => exact congrArg Fin.succ (hinj h)
  have hh := (mode_orthonormal history).comp (Fin.cons i old) hc
  convert hh using 1
  funext k
  cases k using Fin.cases <;> rfl

/-- Literal raw-birth reduced matrix on the true residual of a history.
There is no assumed orthogonality or independently specified branch weight. -/
theorem accepted_residual_erasure {q n:ℕ} (history:Fin q→EuclideanSpace ℂ A)
    (i:Active history) (old:Fin n→Active history) (hinj:Function.Injective old)
    (hfresh:∀j,old j≠i) (X:CMatrix (H×(A×(Fin n→A)))) :
    let B:=selectedRaw n (fun x=>residual history i x)*Matrix.kronecker (1:CMatrix A)
      (directEncoding (fun j=>C6ResidualModes.mode history (old j)))
    partialTraceB (Matrix.kronecker (1:CMatrix H) B*X*
      (Matrix.kronecker (1:CMatrix H) B).conjTranspose)=
      (((‖residual history i‖^2/(Fintype.card A:ℝ):ℝ):ℂ)) • partialTraceB X := by
  exact residual_erasure (residual history i) i.property _
    (accepted_orthonormal history i old hinj hfresh) X

theorem inactive_residual_erasure {q n:ℕ} (history:Fin q→EuclideanSpace ℂ A)
    (i:Fin q) (hi:residual history i=0) (old:Fin n→EuclideanSpace ℂ A)
    (X:CMatrix (H×(A×(Fin n→A)))) :
    let B:=selectedRaw n (fun x=>residual history i x)*
      Matrix.kronecker (1:CMatrix A) (directEncoding old)
    partialTraceB (Matrix.kronecker (1:CMatrix H) B*X*
      (Matrix.kronecker (1:CMatrix H) B).conjTranspose)=0 := by
  simp only [hi,PiLp.zero_apply]
  exact zero_residual_erasure old X

#print axioms accepted_residual_erasure
#print axioms inactive_residual_erasure
end
end ICO.C6HistoryImageErasure
