import ICO.C6PolarFockEntries
import ICO.MHEmbeddingProjector
import ICO.RecordingPureCorrespondence

/-! Fixed left/right particle sectors in the literal two-record Fock space.
The query remains the first coordinate; the right record is a spectator for
the left polar creator. -/
namespace ICO.C6TwoFockSector
open QIT Matrix ICO.C6PolarFock ICO.C6PolarFockEntries ICO.C6BosonicPolar
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.RecordingCopyIdentity
  ICO.RecordingPureCorrespondence ICO.MHEmbeddingProjector
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev TwoSector (l r : ℕ) :=
  ICO.C6BosonicPolar.Sector (A := A) l × TensorPowerProfile (A×A) r

def lengths (T l r : ℕ) (h : l+r≤T) : Lengths T :=
  ⟨(⟨l,by omega⟩,⟨r,by omega⟩),h⟩

def sectorEmbed (T l r : ℕ) (h : l+r≤T) (x : TwoSector (A := A) l r) :
    InputCutoff (α := A) T := ⟨⟨lengths T l r h,x.2⟩,x.1⟩

theorem sectorEmbed_injective (T l r : ℕ) (h : l+r≤T) :
    Function.Injective (sectorEmbed (A := A) T l r h) := by
  intro x y he
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun z : InputCutoff (α := A) T => z.2.1) he
    · exact Subtype.ext (congrArg (fun z : InputCutoff (α := A) T => z.2.2.val) he)
  · exact Subtype.ext (congrArg (fun z : InputCutoff (α := A) T => z.1.2.val) he)

def J (T l r : ℕ) (h : l+r≤T) :
    Matrix (InputCutoff (α := A) T) (TwoSector (A := A) l r) ℂ :=
  basisEmbedding (sectorEmbed T l r h)

theorem J_gram (T l r : ℕ) (h : l+r≤T) :
    (J (A := A) T l r h).conjTranspose*J (A := A) T l r h=
      (1 : CMatrix (TwoSector (A := A) l r)) :=
  basisEmbedding_gram (sectorEmbed (A := A) T l r h)
    (sectorEmbed_injective (A := A) T l r h)

def targetEmbed (t l r : ℕ) (h : l+r≤t) (x : TwoSector (A := A) (l+1) r) :
    OutputCutoff (α := A) t := ⟨⟨lengths t l r h,x.2⟩,x.1⟩

theorem source_composition {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    inputEmbed (Nat.le_trans (Nat.le_succ t) h) ∘ sectorEmbed (A := A) t l r hs =
      sectorEmbed T l r (by omega) := rfl

theorem target_composition {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    outputEmbed h ∘ targetEmbed (A := A) t l r hs =
      sectorEmbed T (l+1) r (by omega) := rfl

theorem boundedPolar_sector (t l r : ℕ) (hs : l+r≤t) :
    boundedPolar (α := A) t*basisEmbedding (sectorEmbed t l r hs) =
      basisEmbedding (targetEmbed t l r hs)*
        Matrix.kronecker (leftPolar (A := A) l) (1 : CMatrix (TensorPowerProfile (A×A) r)) := by
  rw [mul_basisEmbedding]
  ext ⟨⟨s,R⟩,b,L⟩ ⟨⟨a,p⟩,S⟩
  by_cases h : s=lengths t l r hs
  · subst s
    by_cases hRS : R=S
    · subst S
      simp [boundedPolar,sectorEmbed,targetEmbed,basisEmbedding,lengths,
        Matrix.blockDiagonal'_apply_eq,
        Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
        Fintype.sum_prod_type,Sigma.mk.inj_iff,heq_eq_eq,apply_ite,Finset.sum_ite_irrel]
    · have hblock : (⟨lengths t l r hs,R⟩ : Block (α := A) t)≠⟨lengths t l r hs,S⟩ := by
        intro hb
        exact hRS (eq_of_heq (Sigma.mk.inj hb).2)
      have hfull (x : A) (y : TensorPowerProfile (A×A) (l+1)) :
          (⟨⟨lengths t l r hs,R⟩,(b,L)⟩ : OutputCutoff (α := A) t)≠
            ⟨⟨lengths t l r hs,S⟩,(x,y)⟩ := fun he => hblock (congrArg Sigma.fst he)
      simp [boundedPolar,sectorEmbed,targetEmbed,basisEmbedding,hfull,hRS,
        Matrix.blockDiagonal'_apply_ne _ _ _ hblock,
        Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
        Fintype.sum_prod_type,Sigma.mk.inj_iff,heq_eq_eq,apply_ite,Finset.sum_ite_irrel]
  · simp [boundedPolar,sectorEmbed,targetEmbed,basisEmbedding,
      Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
      Fintype.sum_prod_type,Sigma.mk.inj_iff,h]
    exact Matrix.blockDiagonal'_apply_ne _ _ _ (by
      intro hb
      exact h (congrArg Sigma.fst hb))

theorem polarLeft_sector {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    polarLeftOnFock (α := A) h*J T l r (by omega) =
      J T (l+1) r (by omega)*
        Matrix.kronecker (leftPolar (A := A) l) (1 : CMatrix (TensorPowerProfile (A×A) r)) := by
  have hj : J (A := A) T l r (by omega) =
      basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))*
        basisEmbedding (sectorEmbed t l r hs) := by
    rw [basisEmbedding_mul,source_composition h hs]
    rfl
  rw [hj,polarLeftOnFock]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (basisEmbedding (inputEmbed (α := A)
    (Nat.le_trans (Nat.le_succ t) h))).conjTranspose,
    inputEmbed_gram,Matrix.one_mul,boundedPolar_sector]
  rw [←Matrix.mul_assoc,basisEmbedding_mul,target_composition h hs]
  rfl

#print axioms J_gram
#print axioms polarLeft_sector
end
end ICO.C6TwoFockSector
