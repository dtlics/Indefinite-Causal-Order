import ICO.C6ActualAcceptedModes
import ICO.C6DirectBirthFactorization

namespace ICO.C6AcceptedBirthFactor
open Matrix QIT ICO.C6ActualAcceptedModes ICO.C6AcceptedModes ICO.C6AcceptedIndices
  ICO.C6FlagCount ICO.C6ResidualModes ICO.C6RetainedHistory ICO.C6HistoryConjugation
  ICO.C6DirectBirthFactorization ICO.C6RightImageErasure ICO.C6WeightedModeErasure
  ICO.C6OrthogonalModeBirth ICO.C6ActualResidualWeight ICO.C6CacheWeights
  ICO.C6CacheSpanProjection ICO.RecordingPurifiedProtocol ICO.RecordingCopyIdentity
noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def nextResidual (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n) (b:Bool) (j:A) :
    EuclideanSpace ℂ A := residual (rightVectors H (n+1) ((j,b),η)) (Fin.last n)

def birthAmplitude (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n) (b:Bool) (j:A) : ℂ :=
  (‖nextResidual H n η b j‖:ℂ)/(Real.sqrt (Fintype.card A):ℂ)

theorem rightModes_false (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (b:Bool) (j:A) :
    (fun k:Fin (flagCount n κ)=>modes (rightVectors H (n+1) ((j,b),η)) (n:=n+1) (false,κ)
      (Fin.cast (flagCount_false n κ).symm k))=modes (rightVectors H n η) κ := by
  funext k
  rw [rightVectors_snoc,modes_false]

theorem rightModes_true (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (b:Bool) (j:A) :
    (fun k:Fin (flagCount n κ+1)=>modes (rightVectors H (n+1) ((j,b),η)) (n:=n+1) (true,κ)
      (Fin.cast (flagCount_true n κ).symm k))=
      Fin.cons (normalized (nextResidual H n η b j)) (modes (rightVectors H n η) κ) := by
  funext k
  rw [rightVectors_snoc,modes_true]
  simp only [ICO.C6ResidualModes.mode,normalized,nextResidual,rightVectors_snoc]

theorem actual_factorization (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (b:Bool) (j:A) :
    selectedRaw (flagCount n κ) (fun x=>nextResidual H n η b j x)*
      Matrix.kronecker (1:CMatrix A) (directEncoding (modes (rightVectors H n η) κ))=
      birthAmplitude H n η b j •
        (directEncoding (fun k:Fin (flagCount n κ+1)=>
          modes (rightVectors H (n+1) ((j,b),η)) (n:=n+1) (true,κ)
            (Fin.cast (flagCount_true n κ).symm k))*basisEmbedding imageCons) := by
  rw [rightModes_true]
  exact normalized_factorization _ _

theorem birthAmplitude_square (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (b:Bool) (j:A) :
    birthAmplitude H n η b j*star (birthAmplitude H n η b j)=
      ((overlapWeight (outcomeBasis H b) (historyProjection (vectors H n η)) j/
        (Fintype.card A:ℝ):ℝ):ℂ) := by
  have he:‖nextResidual H n η b j‖^2=
      overlapWeight (outcomeBasis H b) (historyProjection (vectors H n η)) j :=
    actual_next_weight H n η b j
  simp only [birthAmplitude,star_div₀,Complex.star_def,Complex.conj_ofReal]
  rw [div_mul_div_comm,←Complex.ofReal_mul,←Complex.ofReal_mul,
    ←pow_two,Real.mul_self_sqrt (Nat.cast_nonneg _),he,Complex.ofReal_div]

#print axioms actual_factorization
#print axioms birthAmplitude_square
end
end ICO.C6AcceptedBirthFactor
