import ICO.C6ModeBirthProduct
import ICO.C6PrivateIsometry

/-! The actual raw right creator appends an inert image factor.  Erasing that
factor is exact for every matrix, so it remains valid with mixed input and
arbitrary entangled accessible or inaccessible spectators. -/
namespace ICO.C6RightImageErasure
open QIT ICO.C6ModeEncoding ICO.C6OrthogonalModeBirth ICO.C6OrthogonalFrame
  ICO.C6ModeBirthProduct ICO.C6PrivateIsometry ICO.MHCreationCovariance
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

def mode (v:EuclideanSpace ℂ A) (y:A) : A×A→ℂ :=
  fun z=>v z.1 * if z.2=y then 1 else 0

def directProduct : (n:ℕ)→(Fin n→EuclideanSpace ℂ A)→(Fin n→A)→TensorPowerProfile (A×A) n→ℂ
  | 0, _, images => fun p=>encode (fun i:Fin 0=>i.elim0) p images
  | n+1, v, images => creationOccupation n (mode (v 0) (images 0))*ᵥ
      directProduct n (Fin.tail v) (Fin.tail images)

theorem directProduct_eq (U:Matrix.unitaryGroup A ℂ) (n:ℕ)
    (labels:Fin n→A) (v:Fin n→EuclideanSpace ℂ A)
    (h:∀i x,(U:CMatrix A) x (labels i)=v i x) (images:Fin n→A) :
    directProduct n v images=birthProduct U n labels images := by
  induction n with
  | zero =>
    have hl : labels=(fun i:Fin 0=>i.elim0) := by funext i; exact i.elim0
    simp only [directProduct,birthProduct,hl]
  | succ n ih =>
    have hm : mode (v 0) (images 0)=modeVector U (labels 0) (images 0) := by
      funext z
      simp only [mode,modeVector,h]
    rw [directProduct,birthProduct,hm,ih (Fin.tail labels) (Fin.tail v)
      (fun i x=>h i.succ x) (Fin.tail images)]

def directEncoding {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) :
    Matrix (TensorPowerProfile (A×A) n) (Fin n→A) ℂ := fun p images=>directProduct n v images p

/-- The creator product itself, for the supplied orthonormal modes, is an
isometry; no unspecified embedding or scalar norm premise is used. -/
theorem directEncoding_gram {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (hv:Orthonormal ℂ v) :
    (directEncoding v).conjTranspose*directEncoding v=1 := by
  obtain ⟨U,labels,hl,he⟩ := unitary_extension v hv
  have hh : directEncoding v=productEncoding U n labels := by
    ext p images
    exact congrFun (directProduct_eq U n labels v he images) p
  rw [hh,productEncoding_gram U n labels hl]

variable {H:Type*} [Fintype H] [DecidableEq H]

theorem directEncoding_erasure {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (hv:Orthonormal ℂ v)
    (X:CMatrix (H×(Fin n→A))) :
    partialTraceB (Matrix.kronecker (1:CMatrix H) (directEncoding v)*X*
      (Matrix.kronecker (1:CMatrix H) (directEncoding v)).conjTranspose)=partialTraceB X :=
  private_erasure_matrix _ (directEncoding_gram v hv) X

theorem scaled_private_erasure {R E:Type*} [Fintype R] [DecidableEq R]
    [Fintype E] [DecidableEq E] (J:Matrix E R ℂ) (hJ:J.conjTranspose*J=1)
    (s:ℂ) (X:CMatrix (H×R)) :
    partialTraceB (Matrix.kronecker (1:CMatrix H) (s • J)*X*
      (Matrix.kronecker (1:CMatrix H) (s • J)).conjTranspose)=
      (s*star s) • partialTraceB X := by
  simp only [Matrix.kronecker,Matrix.kronecker_smul,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,partialTraceB_smul]
  change (star s*s) • partialTraceB (Matrix.kronecker (1:CMatrix H) J*X*
    (Matrix.kronecker (1:CMatrix H) J).conjTranspose)=(s*star s) • partialTraceB X
  rw [private_erasure_matrix J hJ X]
  rw [mul_comm (star s) s]

variable [Nonempty A]

theorem inverse_sqrt_square :
    (Real.sqrt (Fintype.card A):ℂ)⁻¹*star (Real.sqrt (Fintype.card A):ℂ)⁻¹=
      (Fintype.card A:ℂ)⁻¹ := by
  simp only [star_inv₀,Complex.star_def,Complex.conj_ofReal]
  rw [←mul_inv_rev,←Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rfl

/-- The selected physical raw birth consumes the incoming query as a new
private image. Its reduced effect is exactly `1/d` times erasing that query
and the older image registers, even on arbitrary entangled mixed inputs. -/
theorem raw_birth_erasure (U:Matrix.unitaryGroup A ℂ) {n:ℕ}
    (labels:Fin n→A) (a:A) (hl:Function.Injective labels) (ha:∀i,labels i≠a)
    (X:CMatrix (H×(A×(Fin n→A)))) :
    let B:=selectedRaw n (fun x=>(U:CMatrix A) x a)*
      Matrix.kronecker (1:CMatrix A) (rotatedEncode U labels)
    partialTraceB (Matrix.kronecker (1:CMatrix H) B*X*
      (Matrix.kronecker (1:CMatrix H) B).conjTranspose)=
      (Fintype.card A:ℂ)⁻¹ • partialTraceB X := by
  dsimp only
  rw [raw_birth_factorization U labels a ha,
    scaled_private_erasure _ (encodedBirth_gram U labels a hl ha) _,inverse_sqrt_square]

/-- Coordinate-free form of the physical erasure identity.  The only
geometric premise concerns the actual supplied old and new label vectors. -/
theorem fresh_mode_erasure {n:ℕ} (v:EuclideanSpace ℂ A)
    (w:Fin n→EuclideanSpace ℂ A) (horth:Orthonormal ℂ (Fin.cons v w))
    (X:CMatrix (H×(A×(Fin n→A)))) :
    let B:=selectedRaw n (fun x=>v x)*Matrix.kronecker (1:CMatrix A) (directEncoding w)
    partialTraceB (Matrix.kronecker (1:CMatrix H) B*X*
      (Matrix.kronecker (1:CMatrix H) B).conjTranspose)=
      (Fintype.card A:ℂ)⁻¹ • partialTraceB X := by
  obtain ⟨U,labels,hl,he⟩ := unitary_extension (Fin.cons v w) horth
  let ls:Fin n→A:=Fin.tail labels
  have hls : Function.Injective ls := fun i j h=>Fin.succ_injective n (hl h)
  have hla : ∀i,ls i≠labels 0 := by
    intro i h
    exact Fin.succ_ne_zero i (hl h)
  have hcols : ∀i x,(U:CMatrix A) x (ls i)=w i x := fun i x=>he i.succ x
  have hhead : (fun x=>v x)=(fun x=>(U:CMatrix A) x (labels 0)) :=
    funext (fun x=>(he 0 x).symm)
  have henc : directEncoding w=rotatedEncode U ls := by
    ext p images
    change directProduct n w images p=rotatedEncode U ls p images
    rw [directProduct_eq U n ls w hcols images,birthProduct_eq U n ls images hls]
  dsimp only
  rw [hhead,henc]
  exact raw_birth_erasure U ls (labels 0) hls hla X

#print axioms directEncoding_gram
#print axioms directEncoding_erasure
#print axioms raw_birth_erasure
#print axioms fresh_mode_erasure
end
end ICO.C6RightImageErasure
