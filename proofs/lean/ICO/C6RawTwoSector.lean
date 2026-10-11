import ICO.C6TwoFockSector
import ICO.C6OrthogonalModeBirth

namespace ICO.C6RawTwoSector
open QIT Matrix ICO.C6TwoFockSector ICO.C6BosonicRight ICO.C6OrthogonalModeBirth
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockSwap ICO.MHProfileTranspose
  ICO.MHERecordingApprox ICO.RecordingCopyIdentity ICO.RecordingPureCorrespondence
  ICO.MHEmbeddingProjector ICO.MHFockOracle
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]
theorem boundedSymmetricInsertion_sector (t l r : ℕ) (hs : l+r≤t) :
    boundedSymmetricInsertion (α := A) t*basisEmbedding (sectorEmbed t l r hs) =
      basisEmbedding (targetEmbed t l r hs)*
        Matrix.kronecker (symmetricInsertion (α := A) l) (1 : CMatrix (TensorPowerProfile (A×A) r)) := by
  rw [mul_basisEmbedding]
  ext ⟨⟨s,R⟩,b,L⟩ ⟨⟨a,p⟩,S⟩
  by_cases h : s=lengths t l r hs
  · subst s
    by_cases hRS : R=S
    · subst S
      simp [boundedSymmetricInsertion,sectorEmbed,targetEmbed,basisEmbedding,lengths,
        Matrix.blockDiagonal'_apply_eq,
        Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
        Fintype.sum_prod_type,Sigma.mk.inj_iff,heq_eq_eq,apply_ite,Finset.sum_ite_irrel]
    · have hblock : (⟨lengths t l r hs,R⟩ : Block (α := A) t)≠⟨lengths t l r hs,S⟩ := by
        intro hb
        exact hRS (eq_of_heq (Sigma.mk.inj hb).2)
      have hfull (x : A) (y : TensorPowerProfile (A×A) (l+1)) :
          (⟨⟨lengths t l r hs,R⟩,(b,L)⟩ : OutputCutoff (α := A) t)≠
            ⟨⟨lengths t l r hs,S⟩,(x,y)⟩ := fun he => hblock (congrArg Sigma.fst he)
      simp [boundedSymmetricInsertion,sectorEmbed,targetEmbed,basisEmbedding,hfull,hRS,
        Matrix.blockDiagonal'_apply_ne _ _ _ hblock,
        Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
        Fintype.sum_prod_type,Sigma.mk.inj_iff,heq_eq_eq,apply_ite,Finset.sum_ite_irrel]
  · simp [boundedSymmetricInsertion,sectorEmbed,targetEmbed,basisEmbedding,
      Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
      Fintype.sum_prod_type,Sigma.mk.inj_iff,h]
    exact Matrix.blockDiagonal'_apply_ne _ _ _ (by
      intro hb
      exact h (congrArg Sigma.fst hb))

theorem rawLeft_sector {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    symmetricOnFock (α := A) h*J T l r (by omega) =
      J T (l+1) r (by omega)*
        Matrix.kronecker (symmetricInsertion (α := A) l) (1 : CMatrix (TensorPowerProfile (A×A) r)) := by
  have hj : J (A := A) T l r (by omega) =
      basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))*
        basisEmbedding (sectorEmbed t l r hs) := by
    rw [basisEmbedding_mul,source_composition h hs]
    rfl
  rw [hj,symmetricOnFock]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (basisEmbedding (inputEmbed (α := A)
    (Nat.le_trans (Nat.le_succ t) h))).conjTranspose,
    inputEmbed_gram,Matrix.one_mul,boundedSymmetricInsertion_sector]
  rw [←Matrix.mul_assoc,basisEmbedding_mul,target_composition h hs]
  rfl

def sectorSwap (l r:ℕ) : TwoSector (A:=A) l r≃TwoSector (A:=A) r l where
  toFun x:=((x.1.1,profileTranspose r x.2),profileTranspose l x.1.2)
  invFun x:=((x.1.1,profileTranspose l x.2),profileTranspose r x.1.2)
  left_inv x:=by simp [profileTranspose_involutive]
  right_inv x:=by simp [profileTranspose_involutive]

theorem swap_J (T l r:ℕ) (hs:l+r≤T) :
    swapMatrix T*J (A:=A) T l r hs=
      J T r l (by omega)*basisEmbedding (sectorSwap (A:=A) l r) := by
  rw [J,swapMatrix,basisEmbedding_mul,J,basisEmbedding_mul]
  rfl

theorem reindex_sandwich {a b c d:Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (f:a≃b) (g:c≃d) (M:Matrix b d ℂ) :
    basisEmbedding f.symm*M*basisEmbedding g=M.submatrix f g := by
  have hf:basisEmbedding f.symm=(1:CMatrix b).submatrix f (Equiv.refl b) := by
    ext i j
    simp [basisEmbedding,Matrix.one_apply,f.eq_symm_apply]
  rw [hf,basisEmbedding]
  change (1:CMatrix b).submatrix f (Equiv.refl b)*M*
    (1:CMatrix d).submatrix (Equiv.refl d) g=_
  rw [Matrix.one_submatrix_mul,Matrix.mul_submatrix_one]
  rfl

def rawRightSector (l r:ℕ) : Matrix (TwoSector (A:=A) l (r+1)) (TwoSector (A:=A) l r) ℂ :=
  (Matrix.kronecker (symmetricInsertion (α:=A) r)
    (1:CMatrix (TensorPowerProfile (A×A) l))).submatrix
      (sectorSwap l (r+1)) (sectorSwap l r)

theorem rawRightSector_entry (l r:ℕ) (o:TwoSector (A:=A) l (r+1)) (i:TwoSector (A:=A) l r) :
    rawRightSector l r o i=rightInsertion (A:=A) r (o.1.1,o.2) (i.1.1,i.2)*
      (if o.1.2=i.1.2 then 1 else 0) := by
  rw [rightInsertion_transpose]
  simp only [rawRightSector,Matrix.submatrix_apply,sectorSwap,Equiv.coe_fn_mk,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
    sectorTranspose,Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map_fst,Prod.map_snd,
    (profileTranspose l).injective.eq_iff]
  rfl

theorem rawRight_sector {t T l r:ℕ} (h:t+1≤T) (hs:l+r≤t) :
    symmetricRightOnFock (α:=A) h*J T l r (by omega)=
      J T l (r+1) (by omega)*rawRightSector l r := by
  have hr:r+l≤t:=by omega
  have hp: basisEmbedding (sectorSwap (A:=A) (r+1) l)*
      Matrix.kronecker (symmetricInsertion (α:=A) r) (1:CMatrix (TensorPowerProfile (A×A) l))*
      basisEmbedding (sectorSwap (A:=A) l r)=rawRightSector l r := by
    exact reindex_sandwich (sectorSwap (A:=A) l (r+1)) (sectorSwap (A:=A) l r) _
  rw [symmetricRightOnFock,swapMatrix_selfAdjoint]
  calc
    _ = swapMatrix T*(symmetricOnFock h*(swapMatrix T*J T l r (by omega))) := by
      simp only [Matrix.mul_assoc]
    _ = swapMatrix T*(symmetricOnFock h*(J T r l (by omega)*basisEmbedding (sectorSwap l r))) := by rw [swap_J]
    _ = swapMatrix T*((J T (r+1) l (by omega)*
        Matrix.kronecker (symmetricInsertion (α:=A) r) (1:CMatrix (TensorPowerProfile (A×A) l)))*
        basisEmbedding (sectorSwap l r)) := by
      congr 1
      rw [←Matrix.mul_assoc,rawLeft_sector h hr]
    _ = (swapMatrix T*J T (r+1) l (by omega))*
        (Matrix.kronecker (symmetricInsertion (α:=A) r) (1:CMatrix (TensorPowerProfile (A×A) l))*
        basisEmbedding (sectorSwap l r)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [swap_J];simp only [Matrix.mul_assoc];rw [←Matrix.mul_assoc (basisEmbedding _),hp]

#print axioms rawLeft_sector
#print axioms rawRight_sector
end
end ICO.C6RawTwoSector
