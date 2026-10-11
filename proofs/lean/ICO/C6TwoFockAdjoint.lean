import ICO.C6TwoFockSector

/-! The adjoint and image projector on actual fixed particle sectors. -/
namespace ICO.C6TwoFockAdjoint
open QIT Matrix ICO.C6TwoFockSector ICO.C6PolarFock ICO.C6BosonicPolar
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.RecordingCopyIdentity
  ICO.RecordingPureCorrespondence ICO.MHEmbeddingProjector
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem boundedPolar_adjoint_sector (t l r : ℕ) (hs : l+r≤t) :
    (boundedPolar (α := A) t).conjTranspose*basisEmbedding (targetEmbed t l r hs) =
      basisEmbedding (sectorEmbed t l r hs)*
        Matrix.kronecker (leftPolar (A := A) l).conjTranspose
          (1 : CMatrix (TensorPowerProfile (A×A) r)) := by
  rw [mul_basisEmbedding]
  ext ⟨⟨s,R⟩,b,L⟩ ⟨⟨a,p⟩,S⟩
  by_cases h : s=lengths t l r hs
  · subst s
    by_cases hRS : R=S
    · subst S
      simp [boundedPolar,Matrix.blockDiagonal'_conjTranspose,sectorEmbed,targetEmbed,
        basisEmbedding,lengths,Matrix.blockDiagonal'_apply_eq,
        Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
        Fintype.sum_prod_type,Sigma.mk.inj_iff,heq_eq_eq,apply_ite]
    · have hblock : (⟨lengths t l r hs,R⟩ : Block (α := A) t)≠⟨lengths t l r hs,S⟩ := by
        intro hb
        exact hRS (eq_of_heq (Sigma.mk.inj hb).2)
      simp [boundedPolar,Matrix.blockDiagonal'_conjTranspose,sectorEmbed,targetEmbed,
        basisEmbedding,hRS,Matrix.blockDiagonal'_apply_ne _ _ _ hblock,
        Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
        Fintype.sum_prod_type,Sigma.mk.inj_iff,heq_eq_eq,apply_ite]
  · simp [boundedPolar,Matrix.blockDiagonal'_conjTranspose,sectorEmbed,targetEmbed,
      basisEmbedding,Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.one_apply,Fintype.sum_prod_type,Sigma.mk.inj_iff,h]
    exact Matrix.blockDiagonal'_apply_ne _ _ _ (by
      intro hb
      exact h (congrArg Sigma.fst hb))

theorem polarLeft_adjoint_sector {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    (polarLeftOnFock (α := A) h).conjTranspose*J (A := A) T (l+1) r (by omega) =
      J T l r (by omega)*Matrix.kronecker (leftPolar (A := A) l).conjTranspose
        (1 : CMatrix (TensorPowerProfile (A×A) r)) := by
  have hj : J (A := A) T (l+1) r (by omega) =
      basisEmbedding (outputEmbed h)*basisEmbedding (targetEmbed t l r hs) := by
    rw [basisEmbedding_mul,target_composition h hs]
    rfl
  rw [hj,polarLeftOnFock]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (basisEmbedding (outputEmbed (α := A) h)).conjTranspose,
    outputEmbed_gram,Matrix.one_mul,boundedPolar_adjoint_sector]
  rw [←Matrix.mul_assoc,basisEmbedding_mul,source_composition h hs]
  rfl

theorem polarLeft_image_sector {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    (polarLeftOnFock (α := A) h*(polarLeftOnFock h).conjTranspose)*
        J (A := A) T (l+1) r (by omega) =
      J T (l+1) r (by omega)*
        Matrix.kronecker (leftPolar (A := A) l*(leftPolar l).conjTranspose)
          (1 : CMatrix (TensorPowerProfile (A×A) r)) := by
  rw [Matrix.mul_assoc,polarLeft_adjoint_sector h hs,←Matrix.mul_assoc,polarLeft_sector h hs]
  rw [Matrix.mul_assoc]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]

theorem polarLeft_complement_sector {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    (1-polarLeftOnFock (α := A) h*(polarLeftOnFock h).conjTranspose)*
        J (A := A) T (l+1) r (by omega) =
      J T (l+1) r (by omega)*
        (1-Matrix.kronecker (leftPolar (A := A) l*(leftPolar l).conjTranspose)
          (1 : CMatrix (TensorPowerProfile (A×A) r))) := by
  rw [Matrix.sub_mul,Matrix.one_mul,polarLeft_image_sector h hs,
    Matrix.mul_sub,Matrix.mul_one]

#print axioms polarLeft_adjoint_sector
#print axioms polarLeft_complement_sector
end
end ICO.C6TwoFockAdjoint
