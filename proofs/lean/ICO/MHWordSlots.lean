import ICO.MHWordBellSum
import ICO.MHBellEntries

/-! The Bell sum in symmetric words is the literal sum over finite record slots. -/
namespace ICO.MHWordSlots
open Matrix QIT ICO.MHWordDistinct ICO.MHBellEntries ICO.MHWordRightImage ICO.MHWordBellSum
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype J] [DecidableEq J]

theorem spectator_eq_iff (j : J) (p q : WordBasis A J) :
    (slotEquiv j p).1=(slotEquiv j q).1 ↔
      (p.2 j).2=(q.2 j).2 ∧ ∀ k : J, k≠j → p.2 k=q.2 k := by
  change ((p.2 j).2, fun k : Other j => p.2 k.val)=
    ((q.2 j).2, fun k : Other j => q.2 k.val) ↔ _
  rw [Prod.mk.injEq,funext_iff]
  constructor
  · rintro ⟨h,hk⟩
    exact ⟨h,fun k hk' => hk ⟨k,hk'⟩⟩
  · rintro ⟨h,hk⟩
    exact ⟨h,fun k => hk k.val k.property⟩

def wordEquiv (n : ℕ) : (A × TensorPower (A × A) n) ≃ WordBasis A (Fin n) :=
  (Equiv.refl A).prodCongr (tensorPowerEquiv n)

def wordPermutation (σ : Equiv.Perm J) : WordBasis A J ≃ WordBasis A J where
  toFun p := (p.1,fun j => p.2 (σ⁻¹ j))
  invFun p := (p.1,fun j => p.2 (σ j))
  left_inv p := by ext j <;> simp
  right_inv p := by ext j <;> simp

theorem slotBell_permutation (σ : Equiv.Perm J) (j : J) (p q : WordBasis A J) :
    slotBell j (wordPermutation σ p) (wordPermutation σ q)=slotBell (σ⁻¹ j) p q := by
  simp only [slotBell_apply,spectator_eq_iff]
  change (if ((p.2 (σ⁻¹ j)).2=(q.2 (σ⁻¹ j)).2 ∧
      (∀ k, k≠j → p.2 (σ⁻¹ k)=q.2 (σ⁻¹ k))) ∧
      p.1=(p.2 (σ⁻¹ j)).1 ∧ q.1=(q.2 (σ⁻¹ j)).1 then _ else _) =
    if ((p.2 (σ⁻¹ j)).2=(q.2 (σ⁻¹ j)).2 ∧
      (∀ k, k≠σ⁻¹ j → p.2 k=q.2 k)) ∧
      p.1=(p.2 (σ⁻¹ j)).1 ∧ q.1=(q.2 (σ⁻¹ j)).1 then _ else _
  have he : (∀ k, k≠j → p.2 (σ⁻¹ k)=q.2 (σ⁻¹ k)) ↔
      (∀ k, k≠σ⁻¹ j → p.2 k=q.2 k) := by
    constructor
    · intro h k hk
      have hne : σ k≠j := by
        intro hh
        apply hk
        simpa using congrArg σ.symm hh
      simpa using h (σ k) hne
    · intro h k hk
      apply h
      intro hh
      exact hk (σ.symm.injective hh)
  simp only [he]

theorem tail_eq_iff (n : ℕ) (x y : TensorPower (A × A) (n+1)) :
    (∀ j : Fin (n+1), j≠0 → tensorPowerEquiv (n+1) x j=tensorPowerEquiv (n+1) y j) ↔
      x.2=y.2 := by
  rcases x with ⟨xh,xt⟩
  rcases y with ⟨yh,yt⟩
  constructor
  · intro h
    apply (tensorPowerEquiv n).injective
    funext j
    simpa only [tensorPowerEquiv_succ_succ] using h j.succ (Fin.succ_ne_zero j)
  · intro h j hj
    change xt=yt at h
    subst yt
    obtain ⟨k,rfl⟩ := Fin.exists_succ_eq.mpr hj
    simp only [tensorPowerEquiv_succ_succ]

def slotMatrix (n : ℕ) (j : Fin n) : CMatrix (A × TensorPower (A × A) n) :=
  (slotBell (A := A) j).submatrix (wordEquiv n) (wordEquiv n)

theorem firstBell_eq_slot (n : ℕ) : firstBell (A := A) n=slotMatrix (A := A) (n+1) 0 := by
  ext o i
  rcases o with ⟨qo,⟨ho,tailo⟩⟩
  rcases i with ⟨qi,⟨hi,ti⟩⟩
  simp only [firstBell,slotMatrix,Matrix.submatrix_apply,slotBell_apply,spectator_eq_iff,
    wordEquiv,Equiv.prodCongr_apply,Equiv.refl_apply,tensorPowerEquiv_succ_zero,tail_eq_iff]
  congr 1
  change (qo=ho.1 ∧ qi=hi.1 ∧ ho.2=hi.2 ∧ tailo=ti) =
    ((ho.2=hi.2 ∧ ∀ k : Fin (n+1), k≠0 →
      tensorPowerEquiv (n+1) (ho,tailo) k=tensorPowerEquiv (n+1) (hi,ti) k) ∧
      qo=ho.1 ∧ qi=hi.1)
  rw [tail_eq_iff]
  simp only [Prod.snd]
  apply propext
  tauto

def queryEquiv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (A × TensorPower (A × A) n) ≃ (A × TensorPower (A × A) n) :=
  (Equiv.refl A).prodCongr (permEquiv n σ)

theorem queryPermutation_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    queryPermutation (A := A) n σ=(queryEquiv (A := A) n σ).toPEquiv.toMatrix := by
  ext o i
  simp [queryPermutation,queryEquiv,permutationMatrix,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,PEquiv.toMatrix,Prod.ext_iff]
  split_ifs <;> simp_all

theorem queryPermutation_conjugation (n : ℕ) (σ : Equiv.Perm (Fin n))
    (M : CMatrix (A × TensorPower (A × A) n)) :
    queryPermutation n σ*M*(queryPermutation (A := A) n σ).conjTranspose=
      M.submatrix (queryEquiv n σ) (queryEquiv n σ) := by
  rw [queryPermutation_eq]
  change (queryEquiv n σ).toPEquiv.toMatrix*M*
    ((queryEquiv n σ).toPEquiv.toMatrix).conjTranspose = _
  rw [PEquiv.toMatrix_toPEquiv_mul]
  have ht : ((queryEquiv (A := A) n σ).toPEquiv.toMatrix : CMatrix _).conjTranspose=
      (queryEquiv n σ).symm.toPEquiv.toMatrix := by
    simpa only [Equiv.Perm.permMatrix,Equiv.Perm.inv_def] using
      Matrix.conjTranspose_permMatrix (R := ℂ) (queryEquiv (A := A) n σ)
  rw [ht,PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem wordEquiv_query (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : A × TensorPower (A × A) n) :
    wordEquiv n (queryEquiv n σ p)=wordPermutation σ (wordEquiv (A := A) n p) := by
  apply Prod.ext
  · rfl
  · exact tensorPowerEquiv_permEquiv n σ p.2

theorem rotatedBell_eq_slot (n : ℕ) (j : Fin (n+1)) :
    rotatedBell (A := A) n j=slotMatrix (A := A) (n+1) j := by
  rw [rotatedBell,queryPermutation_conjugation,firstBell_eq_slot]
  ext o i
  simp only [slotMatrix,Matrix.submatrix_apply,wordEquiv_query]
  rw [slotBell_permutation]
  simp

theorem bellSum_eq_slots (n : ℕ) :
    bellSum (A := A) n=∑ j : Fin (n+1), slotMatrix (A := A) (n+1) j := by
  simp only [bellSum,rotatedBell_eq_slot]

#print axioms rotatedBell_eq_slot
#print axioms bellSum_eq_slots
end
end ICO.MHWordSlots
