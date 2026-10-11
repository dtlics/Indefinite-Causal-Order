import ICO.C6GradedCache
import ICO.C6ReindexChannel

/-! The cache oracle with a classically selected box. The Bool tag is
explicitly pinched and retained; the physical query dimension remains card A.
The construction is CPTP on every input, including coherent tag inputs. -/
namespace ICO.C6ChoiceCache
open QIT Matrix ICO.C6GradedCache ICO.C6CacheDecode ICO.C6CacheMap
  ICO.C6MatrixCovariance ICO.C6SectorChannel ICO.RecordingCopyIdentity
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
universe u
variable {A M:Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def choiceEquiv (Q:ℕ) : (Σ _:Bool,Graded (A:=A) Q M)≃Graded (A:=A) Q (Bool×M) where
  toFun x:=⟨x.2.1,(x.2.2.1,(x.1,x.2.2.2))⟩
  invFun x:=⟨x.2.2.1,⟨x.1,(x.2.1,x.2.2.2)⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

def choiceInjection (Q:ℕ) (b:Bool) (x:Graded (A:=A) Q M) : Graded (A:=A) Q (Bool×M) :=
  choiceEquiv Q ⟨b,x⟩

theorem choiceInjection_injective (Q:ℕ) (b:Bool) :
    Function.Injective (choiceInjection (A:=A) (M:=M) Q b) := by
  intro x y h
  have he:((⟨b,x⟩:Σ _:Bool,Graded (A:=A) Q M))=⟨b,y⟩ := (choiceEquiv Q).injective h
  exact eq_of_heq (Sigma.mk.inj he).2

def choiceEmbed (Q:ℕ) (b:Bool) :
    Matrix (Graded (A:=A) Q (Bool×M)) (Graded (A:=A) Q M) ℂ :=
  basisEmbedding (choiceInjection Q b)

theorem choiceEmbed_gram (Q:ℕ) (b:Bool) :
    (choiceEmbed (A:=A) (M:=M) Q b).conjTranspose*choiceEmbed (A:=A) (M:=M) Q b=1 :=
  basisEmbedding_gram _ (choiceInjection_injective (A:=A) (M:=M) Q b)

def choiceBlock (Q:ℕ) (b:Bool) (X:CMatrix (Graded (A:=A) Q (Bool×M))) :
    CMatrix (Graded (A:=A) Q M) := X.submatrix (choiceInjection Q b) (choiceInjection Q b)

theorem choiceBlock_eq (Q:ℕ) (b:Bool) (X:CMatrix (Graded (A:=A) Q (Bool×M))) :
    choiceBlock Q b X=(choiceEmbed Q b).conjTranspose*X*choiceEmbed Q b :=
  (basisEmbedding_compression _ X).symm

def localChoice (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (D:Bool→Option (Matrix.unitaryGroup A ℂ)) (b:Bool) :
    Channel (Graded (A:=A) Q M) (Graded (A:=A) Q (Bool×M)) :=
  (isometryChannel (choiceEmbed Q b) (choiceEmbed_gram Q b)).comp
    (ICO.C6GradedCache.query Q hpos hQ (D b))

def query (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (D:Bool→Option (Matrix.unitaryGroup A ℂ)) :
    Channel (Graded (A:=A) Q (Bool×M)) (Graded (A:=A) Q (Bool×M)) :=
  (sectorChannel (localChoice Q hpos hQ D)).comp (ICO.C6ReindexChannel.channel (choiceEquiv Q))

theorem choice_input_block (Q:ℕ) (b:Bool) (X:CMatrix (Graded (A:=A) Q (Bool×M))) :
    (inclusion (H:=fun _:Bool=>Graded (A:=A) Q M) b).conjTranspose*
      X.submatrix (choiceEquiv Q) (choiceEquiv Q)*inclusion b=choiceBlock Q b X := by
  rw [inclusion,basisEmbedding_compression]
  rfl

theorem query_apply (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (D:Bool→Option (Matrix.unitaryGroup A ℂ))
    (X:CMatrix (Graded (A:=A) Q (Bool×M))) :
    (query Q hpos hQ D).map X=∑b:Bool,choiceEmbed Q b*
      (ICO.C6GradedCache.query Q hpos hQ (D b)).map (choiceBlock Q b X)*(choiceEmbed Q b).conjTranspose := by
  change (sectorChannel (localChoice Q hpos hQ D)).map
    ((ICO.C6ReindexChannel.channel (choiceEquiv Q)).map X)=_
  rw [ICO.C6ReindexChannel.apply,sector_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [choice_input_block]
  simp only [localChoice,Channel.comp,LinearMap.comp_apply,isometryChannel,conjugate_apply]

theorem choiceBlock_positive (Q:ℕ) (b:Bool)
    (X:CMatrix (Graded (A:=A) Q (Bool×M))) (hX:X.PosSemidef) :
    (choiceBlock Q b X).PosSemidef := hX.submatrix _

def tagInjection (b:Bool) (i:A×M) : A×(Bool×M) := (i.1,(b,i.2))

theorem choiceEmbed_known (Q:ℕ) (b:Bool) :
    choiceEmbed (A:=A) (M:=M) Q b=
      known Q (basisEmbedding (tagInjection (A:=A) (M:=M) b)) := by
  ext o i
  rcases o with ⟨r,⟨⟨a,p⟩,⟨c,m⟩⟩⟩
  rcases i with ⟨s,⟨⟨a',p'⟩,m'⟩⟩
  by_cases hrs:r=s
  · subst s
    simp [choiceEmbed,choiceInjection,choiceEquiv,known,ICO.C6CacheKnownOperation.externalLift,
      ICO.C6CacheKnownOperation.externalEquiv,basisEmbedding,tagInjection,
      Matrix.one_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Sigma.mk.inj_iff,
      Prod.mk.injEq,and_assoc,and_left_comm,and_comm,ite_and]
  · have ho : (⟨r,((a,p),(c,m))⟩:Graded (A:=A) Q (Bool×M))≠
        choiceInjection Q b ⟨s,((a',p'),m')⟩ := by
      intro he
      exact hrs (congrArg Sigma.fst he)
    rw [known,Matrix.blockDiagonal'_apply_ne _ _ _ hrs]
    simp [choiceEmbed,basisEmbedding,Matrix.one_apply,ho]

theorem choiceEmbed_covariance (U:Matrix.unitaryGroup A ℂ) (Q:ℕ) (b:Bool) :
    (rotation (M:=Bool×M) U Q:CMatrix (Graded (A:=A) Q (Bool×M)))*choiceEmbed Q b=
      choiceEmbed Q b*(rotation (M:=M) U Q:CMatrix (Graded (A:=A) Q M)) := by
  rw [choiceEmbed_known]
  exact known_covariance U Q _

#print axioms query
#print axioms query_apply
end
end ICO.C6ChoiceCache
