import ICO.RecordingPartialIsometry

/-!
# Algebra of the bidirectional recording oracle

This module separates the finite projection identities from the generic
star-algebra argument showing that the two recording branches form a partial
isometry. No Haar comparison bound is assumed here.
-/

namespace ICO.RecordingOracleAlgebra

section StarAlgebra

variable {R : Type*} [Ring R] [StarRing R]

theorem image_projection (A P : R) (hA : star A * A = P) (hAP : A * P = A) :
    IsStarProjection (A * star A) := by
  refine ⟨?_, ?_⟩
  · change (A * star A) * (A * star A) = A * star A
    calc
      (A * star A) * (A * star A) = A * (star A * A) * star A := by noncomm_ring
      _ = A * star A := by rw [hA, hAP]
  · simp only [IsSelfAdjoint, star_mul, star_star]

theorem compressed_projection (B P Q : R) (hB : star B * B = P)
    (hBP : B * P = B) (hQ : IsStarProjection Q)
    (hPQ : Commute P Q) : IsStarProjection (B * Q * star B) := by
  refine ⟨?_, ?_⟩
  · change (B * Q * star B) * (B * Q * star B) = B * Q * star B
    calc
      (B * Q * star B) * (B * Q * star B) =
          B * (Q * (star B * B) * Q) * star B := by noncomm_ring
      _ = B * (Q * P * Q) * star B := by rw [hB]
      _ = B * (P * (Q * Q)) * star B := by rw [← hPQ.eq]; noncomm_ring
      _ = B * Q * star B := by rw [hQ.isIdempotentElem.eq, ← mul_assoc, hBP]
  · change star (B * Q * star B) = B * Q * star B
    simp only [star_mul, star_star, hQ.isSelfAdjoint.star_eq, mul_assoc]

/-- The source's overlap-removing construction is a partial isometry once
    the common initial projection commutes with both image projections. -/
theorem oracle_initial_projection (A B P : R)
    (hP : IsStarProjection P) (hA : star A * A = P) (hB : star B * B = P)
    (hAP : A * P = A) (hBP : B * P = B)
    (hPA : Commute P (A * star A)) (hPB : Commute P (B * star B)) :
    IsStarProjection
      (star (A * (1 - B * star B) + (1 - A * star A) * star B) *
        (A * (1 - B * star B) + (1 - A * star A) * star B)) := by
  let Q := A * star A
  let S := B * star B
  have hQ : IsStarProjection Q := image_projection A P hA hAP
  have hS : IsStarProjection S := image_projection B P hB hBP
  have hPcS : Commute P (1 - S) := (Commute.one_right P).sub_right hPB
  have hPcQ : Commute P (1 - Q) := (Commute.one_right P).sub_right hPA
  have hX : IsStarProjection (P * (1 - S)) := hP.mul hS.one_sub hPcS
  have hY : IsStarProjection (B * (1 - Q) * star B) :=
    compressed_projection B P (1 - Q) hB hBP hQ.one_sub hPcQ
  have hcSB : (1 - S) * B = 0 := by
    dsimp only [S]
    rw [sub_mul, one_mul, mul_assoc, hB, hBP, sub_self]
  have hAdQ : star A * (1 - Q) = 0 := by
    have hPAd : P * star A = star A := by
      simpa only [star_mul, hP.isSelfAdjoint.star_eq, star_star] using congrArg star hAP
    dsimp only [Q]
    rw [mul_sub, mul_one, ← mul_assoc, hA, hPAd, sub_self]
  have hXY : (P * (1 - S)) * (B * (1 - Q) * star B) = 0 := by
    calc
      (P * (1 - S)) * (B * (1 - Q) * star B) =
          P * ((1 - S) * B) * (1 - Q) * star B := by noncomm_ring
      _ = 0 := by rw [hcSB]; simp
  have hEq :
      star (A * (1 - S) + (1 - Q) * star B) *
        (A * (1 - S) + (1 - Q) * star B) =
      P * (1 - S) + B * (1 - Q) * star B := by
    have hC : star (A * (1 - S)) * ((1 - Q) * star B) = 0 := by
      rw [star_mul, hS.one_sub.isSelfAdjoint.star_eq]
      calc
        ((1 - S) * star A) * ((1 - Q) * star B) =
            (1 - S) * (star A * (1 - Q)) * star B := by noncomm_ring
        _ = 0 := by rw [hAdQ]; simp
    have hC' : star ((1 - Q) * star B) * (A * (1 - S)) = 0 := by
      simpa only [star_mul, star_star, star_zero] using congrArg star hC
    have hXX : star (A * (1 - S)) * (A * (1 - S)) = P * (1 - S) := by
      rw [star_mul, hS.one_sub.isSelfAdjoint.star_eq]
      calc
        ((1 - S) * star A) * (A * (1 - S)) =
            (1 - S) * (star A * A) * (1 - S) := by noncomm_ring
        _ = (1 - S) * P * (1 - S) := by rw [hA]
        _ = P * (1 - S) := by rw [← hPcS.eq, mul_assoc, hS.one_sub.isIdempotentElem.eq]
    have hYY : star ((1 - Q) * star B) * ((1 - Q) * star B) =
        B * (1 - Q) * star B := by
      rw [star_mul, star_star, hQ.one_sub.isSelfAdjoint.star_eq]
      calc
        (B * (1 - Q)) * ((1 - Q) * star B) =
            B * ((1 - Q) * (1 - Q)) * star B := by noncomm_ring
        _ = B * (1 - Q) * star B := by rw [hQ.one_sub.isIdempotentElem.eq]
    rw [star_add, add_mul, mul_add, mul_add, hXX, hC, hC', hYY]
    simp
  change IsStarProjection (star (A * (1 - S) + (1 - Q) * star B) * _)
  rw [hEq]
  exact hX.add hY hXY

end StarAlgebra

section FiniteOracle

open ICO.RecordingOperatorSupport ICO.RecordingPartialIsometry
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def forwardRecording : Matrix (Basis α) (Basis α) ℂ :=
  leftInsertion * (1 - rightInsertion * rightInsertion.conjTranspose) +
    (1 - leftInsertion * leftInsertion.conjTranspose) * rightInsertion.conjTranspose

theorem forward_initial_projection :
    IsStarProjection ((forwardRecording (α := α)).conjTranspose * forwardRecording) :=
  oracle_initial_projection leftInsertion rightInsertion domainProjection
    domainProjection_isStarProjection left_gram_eq_projection right_gram_eq_projection
    left_domain_identity right_domain_identity
    domain_commutes_left_image domain_commutes_right_image

theorem forwardRecording_norm_le : ‖forwardRecording (α := α)‖ ≤ 1 := by
  have h := IsStarProjection.norm_le _ (forward_initial_projection (α := α))
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg (forwardRecording (α := α))]

theorem inverseRecording_eq_adjoint :
    inverseRecording (α := α) = forwardRecording.conjTranspose := by
  simp only [forwardRecording, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose,
    inverseRecording]
  noncomm_ring

theorem inverseRecording_norm_le : ‖inverseRecording (α := α)‖ ≤ 1 := by
  rw [inverseRecording_eq_adjoint]
  change ‖star (forwardRecording (α := α))‖ ≤ 1
  rw [norm_star]
  exact forwardRecording_norm_le

theorem inverse_initial_projection :
    IsStarProjection ((inverseRecording (α := α)).conjTranspose * inverseRecording) := by
  have h := oracle_initial_projection rightInsertion leftInsertion domainProjection
    (domainProjection_isStarProjection (α := α)) right_gram_eq_projection left_gram_eq_projection
    right_domain_identity left_domain_identity
    domain_commutes_right_image domain_commutes_left_image
  have he : inverseRecording (α := α) =
      rightInsertion * (1 - leftInsertion * leftInsertion.conjTranspose) +
        (1 - rightInsertion * rightInsertion.conjTranspose) * leftInsertion.conjTranspose := by
    unfold inverseRecording
    noncomm_ring
  rw [he]
  exact h

end
end FiniteOracle

end ICO.RecordingOracleAlgebra
