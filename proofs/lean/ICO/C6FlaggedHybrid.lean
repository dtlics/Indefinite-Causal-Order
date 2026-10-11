import ICO.C6FlagStack
import ICO.C6MatrixLocalHybrid
import ICO.RecordingPurifiedProtocol

/-! A prefix hybrid with an explicit orthogonal register storing every flag. -/
namespace ICO.C6FlaggedHybrid
open QIT ICO.C6FlagStack ICO.MHRectangularAction ICO.MHBlockNorm
  ICO.C6PolarCompression ICO.C6MatrixTrajectory ICO.C6MatrixLocalHybrid
  ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1300000
set_option Elab.async false
variable {X Y J K:Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

def pack (v:K→EuclideanSpace ℂ X) : EuclideanSpace ℂ (K×X) :=
  WithLp.toLp 2 (fun p=>v p.1 p.2)

theorem pack_norm_sq (v:K→EuclideanSpace ℂ X) :
    ‖pack v‖^2=∑k,‖v k‖^2 := by
  simp only [pack,PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type]

theorem pack_sub (v w:K→EuclideanSpace ℂ X) : pack (fun k=>v k-w k)=pack v-pack w := rfl

def carry (F:J→Matrix Y X ℂ) (K:Type*) [DecidableEq K] : Matrix ((J×K)×Y) (K×X) ℂ :=
  fun o i=>if o.1.2=i.1 then F o.1.1 o.2 i.2 else 0

def carryEquiv (J K Y:Type*) : ((J×K)×Y)≃((J×Y)×K) where
  toFun x:=((x.1.1,x.2),x.1.2)
  invFun x:=((x.1.1,x.2),x.1.2)
  left_inv _:=rfl
  right_inv _:=rfl

theorem carry_block (F:J→Matrix Y X ℂ) :
    carry F K=(Matrix.blockDiagonal (fun _:K=>stack F)).submatrix
      (carryEquiv J K Y) (Equiv.prodComm K X) := by
  ext ⟨⟨j,k⟩,y⟩ ⟨l,x⟩
  simp only [carry,Matrix.submatrix_apply,Matrix.blockDiagonal_apply',carryEquiv,
    Equiv.coe_fn_mk,Equiv.prodComm_apply,Prod.swap_prod_mk,stack]

theorem carry_norm (F:J→Matrix Y X ℂ) (b:ℝ) (hb:0≤b) (hF:‖stack F‖≤b) :
    ‖carry F K‖≤b := by
  rw [carry_block]
  apply (rectangular_reindex_norm_le _ _ _).trans
  have hs:Real.sqrt (b^2)=b:=Real.sqrt_sq hb
  have hh:=blockDiagonal_norm_le (fun _:K=>stack F) (b^2) (sq_nonneg b)
    (fun _=>by rw [hs]; exact hF)
  simpa only [hs] using hh

theorem carry_apply (F:J→Matrix Y X ℂ) (v:K→EuclideanSpace ℂ X) :
    rectAct (carry F K) (pack v)=pack (fun p:J×K=>rectAct (F p.1) (v p.2)) := by
  ext ⟨⟨j,k⟩,y⟩
  simp only [rectAct,Matrix.toEuclideanLin_apply,Matrix.mulVec,
    dotProduct,Fintype.sum_prod_type,carry,pack,WithLp.ofLp_toLp]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l hl hne
    simp [Ne.symm hne]
  · simp

theorem carry_sub (F G:J→Matrix Y X ℂ) :
    carry (fun j=>F j-G j) K=carry F K-carry G K := by
  ext o i
  simp only [carry,Matrix.sub_apply]
  split_ifs <;> simp

variable {E:ℕ→Type*} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

def branchRun (F:∀i,Bool→Matrix (E (i+1)) (E i) ℂ) (z:EuclideanSpace ℂ (E 0)) :
    (i:ℕ)→History Bool i→EuclideanSpace ℂ (E i)
  | 0,_=>z
  | i+1,κ=>rectAct (F i κ.1) (branchRun F z i κ.2)

theorem packed_run (F:∀i,Bool→Matrix (E (i+1)) (E i) ℂ) (z:EuclideanSpace ℂ (E 0)) (n:ℕ) :
    pack (branchRun F z n)=
      run (H:=fun i=>History Bool i×E i) (fun i=>carry (F i) (History Bool i))
        (pack (branchRun F z 0)) n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    change pack (fun p:Bool×History Bool n=>rectAct (F n p.1) (branchRun F z n p.2))=_
    rw [←carry_apply,ih]
    rfl

theorem branch_distance (F G:∀i,Bool→Matrix (E (i+1)) (E i) ℂ)
    (z:EuclideanSpace ℂ (E 0)) (ε:ℕ→ℝ) (n:ℕ)
    (hε:∀i<n,0≤ε i) (hG:∀i<n,‖stack (G i)‖≤1)
    (he:∀i<n,∑κ:History Bool i,∑b:Bool,
      ‖rectAct (F i b-G i b) (branchRun F z i κ)‖^2≤(ε i)^2) :
    ‖pack (branchRun F z n)-pack (branchRun G z n)‖≤∑i∈Finset.range n,ε i := by
  have h0:pack (branchRun G z 0)=pack (branchRun F z 0):=rfl
  rw [packed_run F z n,packed_run G z n,h0]
  apply run_distance_upto
  · intro i hi
    exact carry_norm (K:=History Bool i) (G i) 1 (by norm_num) (hG i hi)
  · intro i hi
    rw [←packed_run F z i]
    erw [←carry_sub (K:=History Bool i) (F i) (G i),carry_apply]
    have hh:=he i hi
    have hs:‖pack (fun p:Bool×History Bool i=>
        rectAct (F i p.1-G i p.1) (branchRun F z i p.2))‖^2≤(ε i)^2 := by
      rw [pack_norm_sq,Fintype.sum_prod_type,Finset.sum_comm]
      exact hh
    exact (sq_le_sq₀ (norm_nonneg _) (hε i hi)).mp hs
#print axioms branch_distance
end
end ICO.C6FlaggedHybrid





