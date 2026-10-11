import ICO.C6RawFlags
import ICO.C6BosonicStageBlocks

/-! Exact fixed-outcome-history slices of the retained coherent branch process. -/
namespace ICO.C6RawFlagSlices
open Matrix QIT ICO.C6RawFlags ICO.C6BosonicStageBlocks ICO.C6BosonicBlocks
  ICO.C6BosonicReencoding ICO.C6FockQueryMatrix ICO.C6RetainedHistory
  ICO.C6PairedTrajectory ICO.C6ChoiceMeasurement ICO.C6PolarFock
  ICO.MHBoundedRecording ICO.MHRectangularAction ICO.RecordingPurifiedProtocol
  ICO.MHFockKnownOperation
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem tensor_product {X M:Type} [Fintype X] [DecidableEq X]
    [Fintype M] [DecidableEq M] (F P J:CMatrix X) (D:CMatrix M) :
    Matrix.kronecker F (1:CMatrix M)*Matrix.kronecker P D*
      Matrix.kronecker J (1:CMatrix M)=Matrix.kronecker (F*P*J) D := by
  simp only [Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]

def smallKnown (K:Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) :
    Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ :=
  fun o x=>K ((o.1,o.2.1),o.2.2) ((x.1,x.2.1),x.2.2)

def choiceProject (b:Bool) (M:Type) [Fintype M] [DecidableEq M] : CMatrix (Bool×M) :=
  fun o x=>if o=x ∧ x.1=b then 1 else 0

def branchMiddle {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (i:ℕ)
    (η:History (A×Bool) i) (j:A) (b f:Bool) :
    CMatrix (InputCutoff (α:=A) T×(Bool×μ i)) :=
    Matrix.kronecker (polarLeftOnFock h) (1:CMatrix (Bool×μ i))*
    Matrix.kronecker (queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (b,j)))) T)
      (choiceProject b (μ i))*
    Matrix.kronecker (rawFlagInverse h H i η f) (1:CMatrix (Bool×μ i))

def branchStage {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (η:History (A×Bool) i) (j:A) (b f:Bool) :
    Matrix (InputCutoff (α:=A) T×(Bool×μ (i+1)))
      (InputCutoff (α:=A) T×(Bool×μ i)) ℂ :=
  known T (smallKnown (K i))*branchMiddle (μ:=μ) h H i η j b f

theorem branchMiddle_tensor {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) (j:A) (b f:Bool) :
    branchMiddle (μ:=μ) h H i η j b f=
      Matrix.kronecker (polarLeftOnFock h*
        queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (b,j)))) T*
        rawFlagInverse h H i η f) (choiceProject b (μ i)) := by
  unfold branchMiddle
  exact tensor_product _ _ _ _

theorem flagStage_block {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (η η':History (A×Bool) i) (j:A) (b f bo bi:Bool)
    (mo:μ (i+1)) (mi:μ i) :
    block (rawFlagStage h H K i f) (bo,(((j,b),η),mo)) (bi,(η',mi))=
      if η=η' ∧ bi=b then
        queryMatrix (fun a x=>K i ((a,bo),mo) ((x,b),mi)) T*
          polarLeftOnFock h*
          queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (b,j)))) T*
          rawFlagInverse h H i η f else 0 := by
  rw [rawFlagStage,controlled_family,block_right_family,Matrix.mul_assoc,block_mul]
  simp only [block_left_tensor,public_block,middle_block]
  change (∑ n:Bool×((A×Bool)×(History (A×Bool) i×μ i)),
    (if ((j,b),η)=(n.2.1,n.2.2.1) then
      queryMatrix (fun a x=>K i ((a,bo),mo) ((x,n.1),n.2.2.2)) T else 0)*
    (polarLeftOnFock h*(if n.1=n.2.1.2 ∧ bi=n.2.1.2 ∧ n.2.2=(η',mi) then
      queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (n.2.1.2,n.2.1.1)))) T else 0)))*
      rawFlagInverse h H i η' f=_
  have hs (n:Bool×((A×Bool)×(History (A×Bool) i×μ i))) :
    (if ((j,b),η)=(n.2.1,n.2.2.1) then
      queryMatrix (fun a x=>K i ((a,bo),mo) ((x,n.1),n.2.2.2)) T else 0)*
    (polarLeftOnFock h*(if n.1=n.2.1.2 ∧ bi=n.2.1.2 ∧ n.2.2=(η',mi) then
      queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (n.2.1.2,n.2.1.1)))) T else 0))=
      if n=(b,((j,b),(η,mi))) then
        (if η=η' ∧ bi=b then queryMatrix (fun a x=>K i ((a,bo),mo) ((x,b),mi)) T*
          (polarLeftOnFock h*queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (b,j)))) T)
          else 0) else 0 := by
    rcases n with ⟨c,⟨⟨k,e⟩,⟨ζ,u⟩⟩⟩
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all [Matrix.mul_zero,Matrix.zero_mul]
  simp_rw [hs]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,if_pos]
  by_cases he:η=η'
  · subst η'
    by_cases hb:bi=b
    · subst bi
      simp [Matrix.mul_assoc]
    · simp [hb]
  · simp [he]

theorem branchStage_block {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (η:History (A×Bool) i) (j:A) (b f bo bi:Bool) (mo:μ (i+1)) (mi:μ i) :
    block (branchStage h H K i η j b f) (bo,mo) (bi,mi)=
      if bi=b then
        queryMatrix (fun a x=>K i ((a,bo),mo) ((x,b),mi)) T*
          polarLeftOnFock h*
          queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (b,j)))) T*
          rawFlagInverse h H i η f else 0 := by
  have hb (D:CMatrix (InputCutoff (α:=A) T)) (o x:Bool×μ i) :
      block (Matrix.kronecker D (choiceProject b (μ i))) o x=
        if o=x ∧ x.1=b then D else 0 := by
    ext a z
    simp only [block,Matrix.kronecker,Matrix.kroneckerMap_apply,choiceProject]
    split_ifs <;> simp
  rw [branchStage,branchMiddle_tensor]
  rw [block_mul]
  simp only [known_block,smallKnown,hb,mul_ite,Matrix.mul_zero]
  by_cases hbi:bi=b
  · subst bi
    simp [Matrix.mul_assoc]
  · simp [hbi]

theorem flagStage_entry {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (η η':History (A×Bool) i) (j:A) (b f:Bool)
    (o:InputCutoff (α:=A) T×(Bool×μ (i+1)))
    (x:InputCutoff (α:=A) T×(Bool×μ i)) :
    rawFlagStage h H K i f (o.1,(o.2.1,(((j,b),η),o.2.2))) (x.1,(x.2.1,(η',x.2.2)))=
      if η=η' then branchStage h H K i η j b f o x else 0 := by
  have he : block (rawFlagStage h H K i f) (o.2.1,(((j,b),η),o.2.2)) (x.2.1,(η',x.2.2))=
      if η=η' then block (branchStage h H K i η j b f) o.2 x.2 else 0 := by
    rw [flagStage_block,branchStage_block]
    split_ifs <;> simp_all
  have ht := congrFun (congrFun he o.1) x.1
  by_cases hh:η=η'
  · simpa only [if_pos hh,block,Prod.mk.eta] using ht
  · simpa only [if_neg hh,Matrix.zero_apply] using ht

def slice {T i:ℕ} (η:History (A×Bool) i)
    (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ i)) :
    EuclideanSpace ℂ (InputCutoff (α:=A) T×(Bool×μ i)) :=
  WithLp.toLp 2 (fun p=>v (p.1,(p.2.1,(η,p.2.2))))

theorem slice_step {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (η:History (A×Bool) i) (j:A) (b f:Bool)
    (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ i)) :
    slice (A:=A) (μ:=μ) (T:=T) (i:=i+1) ((j,b),η) (rectAct (rawFlagStage h H K i f) v)=
      rectAct (branchStage h H K i η j b f) (slice (i:=i) η v) := by
  ext o
  change (∑x,rawFlagStage h H K i f (o.1,(o.2.1,(((j,b),η),o.2.2))) x*v x)=
    ∑x,branchStage h H K i η j b f o x*v (x.1,(x.2.1,(η,x.2.2)))
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have he (ζ:History (A×Bool) i) :
      rawFlagStage h H K i f (o.1,(o.2.1,(((j,b),η),o.2.2))) (x,(c,(ζ,m)))=
        if η=ζ then branchStage h H K i η j b f o (x,(c,m)) else 0 :=
    flagStage_entry h H K i η ζ j b f o (x,(c,m))
  simp_rw [he,ite_mul,zero_mul]
  simp

theorem flagRun_slice_succ {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0)) (i:ℕ)
    (η:History (A×Bool) i) (κ:History Bool i) (j:A) (b f:Bool) :
    slice (A:=A) (μ:=μ) (T:=T) (i:=i+1) ((j,b),η) (rawFlagRun h H K z (i+1) (f,κ))=
      rectAct (branchStage h H K i η j b f) (slice (i:=i) η (rawFlagRun h H K z i κ)) :=
  slice_step h H K i η j b f _

theorem tensor_identity_entry {X M:Type} [Fintype X] [DecidableEq X]
    [Fintype M] [DecidableEq M] (D:CMatrix X) (v:X×M→ℂ) (x:X) (m:M) :
    (Matrix.kronecker D (1:CMatrix M)*ᵥv) (x,m)=∑y,D x y*v (y,m) := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp

theorem slice_tensor {T i:ℕ} (η:History (A×Bool) i)
    (D:CMatrix (InputCutoff (α:=A) T))
    (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ i)) :
    slice (A:=A) (μ:=μ) (T:=T) (i:=i) η
      (rectAct (Matrix.kronecker D (1:CMatrix (Public (A:=A) μ i))) v)=
    rectAct (Matrix.kronecker D (1:CMatrix (Bool×μ i))) (slice (i:=i) η v) := by
  ext o
  change (Matrix.kronecker D (1:CMatrix (Public (A:=A) μ i))*ᵥWithLp.ofLp v)
      (o.1,(o.2.1,(η,o.2.2)))=
    (Matrix.kronecker D (1:CMatrix (Bool×μ i))*ᵥ
      (fun p=>v (p.1,(p.2.1,(η,p.2.2))))) o
  rw [tensor_identity_entry]
  obtain ⟨x,b,m⟩:=o
  rw [tensor_identity_entry]

#print axioms flagStage_block
#print axioms branchStage_block
#print axioms flagRun_slice_succ
#print axioms slice_tensor
end
end ICO.C6RawFlagSlices



