import ICO.C6TwoFockSector

/-! An actual left-record vacuum cannot be retrieved by a polar adjoint. -/
namespace ICO.C6TwoFockVacuum
open QIT Matrix ICO.C6TwoFockSector ICO.C6PolarFock ICO.C6PolarFockEntries
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.RecordingCopyIdentity
open scoped Matrix
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem output_vacuum_disjoint {t T r : ℕ} (h : t+1≤T) (hr : r≤T)
    (o : OutputCutoff (α := A) t) (i : TwoSector (A := A) 0 r) :
    outputEmbed h o≠sectorEmbed T 0 r (by omega) i := by
  intro he
  have hl:=congrArg (fun x : InputCutoff (α := A) T=>x.1.1.val.1.val) he
  change o.1.1.val.1.val+1=0 at hl
  omega

theorem polarLeft_adjoint_vacuum {t T r : ℕ} (h : t+1≤T) (hr : r≤T) :
    (polarLeftOnFock (α := A) h).conjTranspose*J (A := A) T 0 r (by omega)=0 := by
  have hc : (basisEmbedding (outputEmbed (α := A) h)).conjTranspose*
      J (A := A) T 0 r (by omega)=0 := by
    calc
      (basisEmbedding (outputEmbed (α := A) h)).conjTranspose*J (A := A) T 0 r (by omega)=
          (basisEmbedding (outputEmbed (α := A) h)).conjTranspose*
            (1:CMatrix (InputCutoff (α := A) T))*basisEmbedding
              (sectorEmbed (A := A) T 0 r (by omega)) := by rw [Matrix.mul_one]; rfl
      _=(1:CMatrix (InputCutoff (α := A) T)).submatrix
          (outputEmbed h) (sectorEmbed (A := A) T 0 r (by omega)) := embedding_compression _ _ _
      _=0 := by
        ext o i
        simp [Matrix.submatrix_apply,Matrix.one_apply,output_vacuum_disjoint h hr o i]
  simp only [polarLeftOnFock,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [hc,Matrix.mul_zero,Matrix.mul_zero]

theorem polarLeft_complement_vacuum {t T r : ℕ} (h : t+1≤T) (hr : r≤T) :
    (1-polarLeftOnFock (α := A) h*(polarLeftOnFock h).conjTranspose)*
      J (A := A) T 0 r (by omega)=J (A := A) T 0 r (by omega) := by
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,
    polarLeft_adjoint_vacuum h hr,Matrix.mul_zero,sub_zero]

#print axioms polarLeft_adjoint_vacuum
#print axioms polarLeft_complement_vacuum
end
end ICO.C6TwoFockVacuum
