import ICO.EmbeddingChannels

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.QubitEmbedding ICO.EmbeddedSwitch ICO.EmbeddingChannels

namespace ICO.EmbeddingSwitchChannels
set_option maxHeartbeats 800000
noncomputable section
variable {A B I J : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
  [DecidableEq A] [DecidableEq B] [DecidableEq I] [DecidableEq J]

theorem control_complete (K : I → Matrix B A ℂ) (hK : ∑ i,(K i)ᴴ*K i=1) :
    (∑ i,(Matrix.kronecker (1 : CMatrix (Fin 2)) (K i))ᴴ*
      Matrix.kronecker (1 : CMatrix (Fin 2)) (K i))=1 := by
  have hp (i : I) : (Matrix.kronecker (1 : CMatrix (Fin 2)) (K i))ᴴ*
      Matrix.kronecker (1 : CMatrix (Fin 2)) (K i)=
      Matrix.kronecker (1 : CMatrix (Fin 2)) ((K i)ᴴ*K i) := by
    have hs : (Matrix.kronecker (1 : CMatrix (Fin 2)) (K i))ᴴ =
        Matrix.kronecker (1 : CMatrix (Fin 2)) (K i)ᴴ := by
      simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker (1 : CMatrix (Fin 2)) (K i)
    rw [hs]
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul (1 : CMatrix (Fin 2)) 1 (K i)ᴴ (K i)).symm
  simp_rw [hp]
  ext x y
  have ht := congrFun (congrFun hK x.2) y.2
  simp only [Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap_apply] at *
  rw [← Finset.mul_sum,ht]
  simp only [Matrix.one_apply,Prod.ext_iff,ite_and]
  split_ifs <;> simp_all

def outputDecodeChannel {d : Nat} (hd : 2≤d) : Channel (Fin 2 × Fin d) (Fin 2 × Fin 2) :=
  krausChannel (outputDecode hd) (control_complete (decode hd) (decode_complete hd))

def switchMap {d : Nat} (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d)) :
    MatrixMap (Fin d) (Fin 2 × Fin d) :=
  MatrixMap.ofKraus (fun ij : I × J => switchKraus (U ij.1) (V ij.2))

/-- The entire channel identity for encoding into any d>=2, applying the
extended noisy-channel switch, and decoding the target while retaining control. -/
theorem decoded_switchMap {d : Nat} (hd : 2≤d)
    (U : I → CMatrix (Fin 2)) (V : J → CMatrix (Fin 2)) :
    (outputDecodeChannel hd).map.comp
      ((switchMap (extendedFamily hd U) (extendedFamily hd V)).comp (encodeChannel hd).map) =
        switchMap U V := by
  simp only [outputDecodeChannel,krausChannel,switchMap,encodeChannel,
    ICO.ClassicalDilation.isometryChannel,MatrixMap.ofKraus_comp_ofKraus]
  ext X a b
  simp only [MatrixMap.ofKraus,LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_prod_type,
    extendedFamily,← Matrix.mul_assoc]
  simp_rw [decoded_switchKraus]
  simp [Fintype.sum_option]

#print axioms decoded_switchMap
end
end ICO.EmbeddingSwitchChannels
