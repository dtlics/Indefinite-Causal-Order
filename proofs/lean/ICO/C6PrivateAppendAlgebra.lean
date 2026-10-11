import ICO.C6PrivateImageAppend

namespace ICO.C6PrivateAppendAlgebra
open Matrix QIT ICO.C6PrivateImageAppend
noncomputable section
set_option maxHeartbeats 1100000
set_option Elab.async false
variable {A H K L:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L]

theorem append_pre (r:ℕ) (F:Matrix (K×A) H ℂ) (G:Matrix H L ℂ) :
    appendPrivate r (F*G)=appendPrivate r F*Matrix.kronecker G (1:CMatrix (Fin r→A)) := by
  have he:Matrix.kronecker (F*G) (1:CMatrix (Fin r→A))=
      Matrix.kronecker F (1:CMatrix (Fin r→A))*Matrix.kronecker G (1:CMatrix (Fin r→A)) := by
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.one_mul]
  unfold appendPrivate
  rw [he]
  ext o i
  rfl

theorem append_known (r:ℕ) (G:Matrix K H ℂ) :
    Matrix.kronecker G (1:CMatrix (Fin (r+1)→A))=
      (Matrix.kronecker (Matrix.kronecker G (1:CMatrix A)) (1:CMatrix (Fin r→A))).submatrix
        (appendEquiv K r) (appendEquiv H r) := by
  ext ⟨k,v⟩ ⟨h,w⟩
  have he : v 0=w 0 ∧ Fin.tail v=Fin.tail w ↔ v=w := by
    constructor
    · rintro ⟨h0,ht⟩
      calc
        v=Fin.cons (v 0) (Fin.tail v) := (Fin.cons_self_tail v).symm
        _=Fin.cons (w 0) (Fin.tail w) := by rw [h0,ht]
        _=w := Fin.cons_self_tail w
    · rintro rfl; exact ⟨rfl,rfl⟩
  simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
    Matrix.submatrix_apply,appendEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.prodAssoc_symm_apply,Fin.consEquiv_symm_apply]
  simp [mul_ite,ite_mul,←ite_and,he]
  have hh : (Fin.tail v=Fin.tail w ∧ v 0=w 0) ↔ v=w := and_comm.trans he
  simp only [hh]

theorem append_post (r:ℕ) (F:Matrix (H×A) L ℂ) (G:Matrix K H ℂ) :
    appendPrivate r (Matrix.kronecker G (1:CMatrix A)*F)=
      Matrix.kronecker G (1:CMatrix (Fin (r+1)→A))*appendPrivate r F := by
  rw [append_known]
  simp only [appendPrivate]
  rw [Matrix.submatrix_mul_equiv _ _ _ (appendEquiv H r)]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.one_mul]

#print axioms append_post
end
end ICO.C6PrivateAppendAlgebra
