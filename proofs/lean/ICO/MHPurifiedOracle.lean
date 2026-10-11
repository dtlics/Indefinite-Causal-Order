import ICO.MHTernaryCompression
import ICO.MemoryEmbedding

/-! The actual reversible phase-permutation oracle in the frequency basis. -/
namespace ICO.MHPurifiedOracle
open Matrix QIT ICO.MHTernaryCompression ICO.PathRecordingSupport
  ICO.MHPermutationExtensions ICO.MHTernaryProfile
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 700000
variable {A : Type*} [Fintype A] [DecidableEq A]

def queryEquiv : A × Environment A ≃ A × Environment A where
  toFun i := (i.2.1 i.1, i.2.1, i.2.2 + Pi.single i.1 (1 : ZMod 3))
  invFun o := (o.2.1.symm o.1, o.2.1, o.2.2 - Pi.single (o.2.1.symm o.1) (1 : ZMod 3))
  left_inv i := by rcases i with ⟨x,π,z⟩; simp
  right_inv o := by rcases o with ⟨y,π,z⟩; simp

def queryMatrix : CMatrix (A × Environment A) :=
  ICO.MemoryEmbedding.embedding ⟨queryEquiv, queryEquiv.injective⟩

theorem queryMatrix_entry (o i : A × Environment A) :
    queryMatrix o i = if o = queryEquiv i then 1 else 0 := rfl

theorem queryMatrix_isometry :
    (queryMatrix (A := A)).conjTranspose * queryMatrix (A := A) = 1 :=
  ICO.MemoryEmbedding.embedding_isometry ⟨queryEquiv, queryEquiv.injective⟩

def queryUnitary : Matrix.unitaryGroup (A × Environment A) ℂ :=
  ⟨queryMatrix, Matrix.mem_unitaryGroup_iff'.mpr queryMatrix_isometry⟩

theorem queryMatrix_mulVec (v : A × Environment A → ℂ) (o : A × Environment A) :
    (queryMatrix *ᵥ v) o = v (queryEquiv.symm o) := by
  change (∑ i, queryMatrix o i * v i) = _
  rw [Finset.sum_eq_single (queryEquiv.symm o)]
  · simp [queryMatrix_entry]
  · intro i hi hio
    have hne : o ≠ queryEquiv i := by
      intro h
      apply hio
      apply queryEquiv.injective
      simpa using h.symm
    simp [queryMatrix_entry,hne]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem queryMatrix_conjTranspose_mulVec (v : A × Environment A → ℂ) (o : A × Environment A) :
    ((queryMatrix (A := A)).conjTranspose *ᵥ v) o = v (queryEquiv o) := by
  change (∑ i, star (queryMatrix i o) * v i) = _
  simp [queryMatrix_entry]

def emptyRecord : Record A := ⟨(∅,∅), by
  simp only [Valid,Finset.union_self,Finset.disjoint_empty_left]
  exact ⟨True.intro,leftUnique_empty,rightUnique_empty⟩⟩

def initialVector : Environment A → ℂ := state emptyRecord

theorem initialVector_entry (e : Environment A) :
    initialVector e = if e.2 = 0 then
      (((Real.sqrt (Fintype.card (Equiv.Perm A) : ℝ))⁻¹ : ℝ) : ℂ) else 0 := by
  classical
  have hp : profile (∅ : Relation A A) ∅ = 0 := by
    funext x
    simp [profile,Source]
  simp [initialVector,state,supports,emptyRecord,Compatible,amplitude,count,completions,hp]

theorem initialVector_norm : (∑ e, star (initialVector (A := A) e)*initialVector e)=1 :=
  state_norm emptyRecord

#print axioms queryMatrix_isometry
#print axioms initialVector_norm
end
end ICO.MHPurifiedOracle
