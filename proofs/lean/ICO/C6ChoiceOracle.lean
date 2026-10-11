import ICO.AdaptiveSequentialProtocol
import ICO.LabelledCircuitComposition

/-! Preserve the actual classical choice between two channel boxes by placing
that choice in a query tag. The unified oracle privately records the tag as
well as its Kraus outcome. -/
namespace ICO.C6ChoiceOracle
open Matrix QIT ICO.InstrumentCompression ICO.ClassicalDilation
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A M I : Type} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype I] [DecidableEq I]

def taggedKraus (K : Bool→I→CMatrix A) (p : Bool×I) : CMatrix (A×Bool) :=
  Matrix.kronecker (K p.1 p.2) (Matrix.single p.1 p.1 1)

theorem tagged_complete (K : Bool→I→CMatrix A)
    (hK : ∀b,∑i,(K b i)ᴴ*K b i=1) :
    (∑p:Bool×I,(taggedKraus K p)ᴴ*taggedKraus K p)=1 := by
  have hp (p:Bool×I) : (taggedKraus K p)ᴴ*taggedKraus K p =
      Matrix.kronecker ((K p.1 p.2)ᴴ*K p.1 p.2)
        (Matrix.single p.1 p.1 (1:ℂ)) := by
    unfold taggedKraus
    have hs : (Matrix.kronecker (K p.1 p.2) (Matrix.single p.1 p.1 (1:ℂ)))ᴴ =
        Matrix.kronecker (K p.1 p.2)ᴴ (Matrix.single p.1 p.1 (1:ℂ)) := by
      simpa [Matrix.kronecker] using
        Matrix.conjTranspose_kronecker (K p.1 p.2) (Matrix.single p.1 p.1 (1:ℂ))
    rw [hs]
    simpa [Matrix.kronecker] using (Matrix.mul_kronecker_mul (K p.1 p.2)ᴴ
      (K p.1 p.2) (Matrix.single p.1 p.1 (1:ℂ)) (Matrix.single p.1 p.1 (1:ℂ))).symm
  simp_rw [hp]
  ext x y
  rcases x with ⟨a,b⟩
  rcases y with ⟨a',c⟩
  have ht := congrFun (congrFun (hK b) a) a'
  simp only [Matrix.sum_apply] at ht
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single]
  cases b <;> cases c <;>
    simp [ht, Matrix.one_apply, Prod.mk.injEq]

def choiceEmbedding (b : Bool) : Matrix ((A×Bool)×M) (A×M) ℂ :=
  ICO.MemoryEmbedding.embedding ⟨fun p => ((p.1,b),p.2), by
    intro x y h
    exact Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z : ((A×Bool)×M) => z.2) h)⟩

theorem choiceEmbedding_isometry (b : Bool) :
    (choiceEmbedding (A:=A) (M:=M) b)ᴴ*choiceEmbedding (A:=A) (M:=M) b=1 :=
  ICO.MemoryEmbedding.embedding_isometry _

theorem choiceEmbedding_orthogonal (b c : Bool) :
    (choiceEmbedding (A:=A) (M:=M) c)ᴴ*choiceEmbedding (A:=A) (M:=M) b=
      if c=b then 1 else 0 := by
  by_cases h:c=b
  · subst c
    simp [choiceEmbedding_isometry]
  · ext x y
    rcases x with ⟨a,m⟩
    rcases y with ⟨a',m'⟩
    simp [choiceEmbedding, ICO.MemoryEmbedding.embedding, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Prod.mk.injEq,
      ite_and, h, Ne.symm h]

theorem choiceEmbedding_complete :
    (∑b:Bool,choiceEmbedding (A:=A) (M:=M) b*(choiceEmbedding (A:=A) (M:=M) b)ᴴ)=1 := by
  ext x y
  rcases x with ⟨⟨a,b⟩,m⟩
  rcases y with ⟨⟨a',c⟩,m'⟩
  by_cases ha:a=a' <;> by_cases hm:m=m' <;> cases b <;> cases c <;>
    simp [choiceEmbedding, ICO.MemoryEmbedding.embedding, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.sum_apply, Fintype.sum_prod_type,
      Matrix.one_apply, Prod.mk.injEq, ite_and, apply_ite, eq_comm, ha, hm]

def embedChoice (b : Bool) : Channel (A×M) ((A×Bool)×M) :=
  isometryChannel (choiceEmbedding (A:=A) (M:=M) b) (choiceEmbedding_isometry b)

def eraseChoice : Channel ((A×Bool)×M) (A×M) where
  map := MatrixMap.ofKraus (fun b : Bool => (choiceEmbedding (A:=A) (M:=M) b)ᴴ)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  mapsPositive := MatrixMap.ofKraus_mapsPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _ (by
    simpa [MatrixMap.krausAdjoint] using choiceEmbedding_complete (A:=A) (M:=M))

theorem erase_embed (b : Bool) (X : CMatrix (A×M)) :
    eraseChoice.map ((embedChoice b).map X)=X := by
  rw [embedChoice, isometryChannel_apply]
  change (∑c:Bool, (choiceEmbedding (A:=A) (M:=M) c)ᴴ*(choiceEmbedding (A:=A) (M:=M) b*X*(choiceEmbedding (A:=A) (M:=M) b)ᴴ)*
    ((choiceEmbedding (A:=A) (M:=M) c)ᴴ)ᴴ)=X
  have he (c:Bool) : (choiceEmbedding (A:=A) (M:=M) c)ᴴ*(choiceEmbedding (A:=A) (M:=M) b*X*(choiceEmbedding (A:=A) (M:=M) b)ᴴ)*
      ((choiceEmbedding (A:=A) (M:=M) c)ᴴ)ᴴ = if c=b then X else 0 := by
    rw [Matrix.conjTranspose_conjTranspose]
    calc
      _ = ((choiceEmbedding (A:=A) (M:=M) c)ᴴ*choiceEmbedding (A:=A) (M:=M) b)*X*((choiceEmbedding (A:=A) (M:=M) b)ᴴ*choiceEmbedding (A:=A) (M:=M) c) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        by_cases hc:c=b
        · subst c; simp [choiceEmbedding_isometry]
        · simp [choiceEmbedding_orthogonal,hc,Ne.symm hc]
  simp only [he]
  simp

theorem tagged_on_embedding (K : Bool→I→CMatrix A) (b c : Bool) (i : I) :
    Matrix.kronecker (taggedKraus K (c,i)) (1:CMatrix M)*choiceEmbedding (A:=A) (M:=M) b =
      if c=b then choiceEmbedding (A:=A) (M:=M) b*Matrix.kronecker (K b i) (1:CMatrix M) else 0 := by
  ext o p
  rcases o with ⟨⟨a,e⟩,m⟩
  rcases p with ⟨a',m'⟩
  by_cases h:c=b
  · subst c
    by_cases he:e=b <;> by_cases hm:m=m' <;>
      simp [taggedKraus, choiceEmbedding, ICO.MemoryEmbedding.embedding,
      Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.single, Fintype.sum_prod_type, Prod.mk.injEq, ite_and, he, hm, eq_comm] <;> aesop
  · simp [taggedKraus, choiceEmbedding, ICO.MemoryEmbedding.embedding,
      Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.single, Fintype.sum_prod_type, Prod.mk.injEq, ite_and,h,Ne.symm h]

theorem tagged_oracle_embedding (K : Bool→I→CMatrix A) (b : Bool)
    (X : CMatrix (A×M)) :
    ICO.AllChannelDilation.oracleMap (taggedKraus K) ((embedChoice b).map X)=
      (embedChoice b).map (ICO.AllChannelDilation.oracleMap (K b) X) := by
  simp only [embedChoice, isometryChannel_apply]
  change (∑p:Bool×I, Matrix.kronecker (taggedKraus K p) (1:CMatrix M)*
    (choiceEmbedding (A:=A) (M:=M) b*X*(choiceEmbedding (A:=A) (M:=M) b)ᴴ)*
      (Matrix.kronecker (taggedKraus K p) (1:CMatrix M))ᴴ)=_
  have he (p:Bool×I) : Matrix.kronecker (taggedKraus K p) (1:CMatrix M)*
      (choiceEmbedding (A:=A) (M:=M) b*X*(choiceEmbedding (A:=A) (M:=M) b)ᴴ)*
        (Matrix.kronecker (taggedKraus K p) (1:CMatrix M))ᴴ =
      if p.1=b then choiceEmbedding (A:=A) (M:=M) b*(Matrix.kronecker (K b p.2) (1:CMatrix M)*X*
        (Matrix.kronecker (K b p.2) (1:CMatrix M))ᴴ)*(choiceEmbedding (A:=A) (M:=M) b)ᴴ else 0 := by
    rw [show Matrix.kronecker (taggedKraus K p) (1:CMatrix M)*
      (choiceEmbedding (A:=A) (M:=M) b*X*(choiceEmbedding (A:=A) (M:=M) b)ᴴ)*
        (Matrix.kronecker (taggedKraus K p) (1:CMatrix M))ᴴ =
      (Matrix.kronecker (taggedKraus K p) (1:CMatrix M)*choiceEmbedding (A:=A) (M:=M) b)*X*
        (Matrix.kronecker (taggedKraus K p) (1:CMatrix M)*choiceEmbedding (A:=A) (M:=M) b)ᴴ by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [tagged_on_embedding]
    by_cases h:p.1=b <;> simp [h,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  simp only [he,Fintype.sum_prod_type]
  simp only [ICO.AllChannelDilation.oracleMap, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem tagged_retraction (K : Bool→I→CMatrix A) (b : Bool) :
    (eraseChoice (A:=A) (M:=M)).map.comp
      ((ICO.AllChannelDilation.oracleMap (taggedKraus K)).comp (embedChoice b).map)=
        ICO.AllChannelDilation.oracleMap (K b) := by
  ext X
  simp only [LinearMap.comp_apply,tagged_oracle_embedding,erase_embed]

#print axioms tagged_retraction
end
end ICO.C6ChoiceOracle
