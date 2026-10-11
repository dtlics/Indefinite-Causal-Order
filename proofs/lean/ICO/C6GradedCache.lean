import ICO.C6SectorChannel
import ICO.C6CacheSectorBound
import ICO.C6CacheKnownOperation
import ICO.MHFockRotation

/-! The finite ambient private cache register and its actual CPTP queries.
The terminal sector uses a common identity extension, so the channel exists
on every matrix, including states absent from earlier histories. -/
namespace ICO.C6GradedCache
open QIT Matrix ICO.C6CacheReference ICO.C6CacheReferenceStep ICO.C6CacheQueryBound
  ICO.C6CacheDecode ICO.C6CacheMap ICO.C6MatrixCovariance ICO.C6SectorChannel
  ICO.C6CacheKnownOperation ICO.RecordingCopyIdentity ICO.MHFockRotation
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
universe u
variable {A M N : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

abbrev Graded (Q : ℕ) (M : Type u) := Σr : Fin (Q+1),Cache (A := A) (M := M) r.val

def embed (Q : ℕ) (r : Fin (Q+1)) :
    Matrix (Graded (A := A) Q M) (Cache (A := A) (M := M) r.val) ℂ :=
  inclusion (H := fun r : Fin (Q+1) => Cache (A := A) (M := M) r.val) r

theorem embed_gram (Q : ℕ) (r : Fin (Q+1)) :
    (embed (A := A) (M := M) Q r).conjTranspose*embed (A := A) (M := M) Q r=1 := inclusion_gram r

def sumInjection (Q : ℕ) (r s : Fin (Q+1)) :
    Cache (A := A) (M := M) r.val ⊕ Cache (A := A) (M := M) s.val → Graded (A := A) Q M
  | Sum.inl x => ⟨r,x⟩
  | Sum.inr x => ⟨s,x⟩

theorem sumInjection_injective (Q : ℕ) (r s : Fin (Q+1)) (h : r≠s) :
    Function.Injective (sumInjection (A := A) (M := M) Q r s) := by
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (eq_of_heq (Sigma.mk.inj hxy).2)
    | inr y => exact (h (congrArg Sigma.fst hxy)).elim
  | inr x =>
    cases y with
    | inl y => exact (h (congrArg Sigma.fst hxy).symm).elim
    | inr y => exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj hxy).2)

def sumEmbed (Q : ℕ) (r s : Fin (Q+1)) :
    Matrix (Graded (A := A) Q M)
      (Cache (A := A) (M := M) r.val ⊕ Cache (A := A) (M := M) s.val) ℂ :=
  basisEmbedding (sumInjection Q r s)

theorem sumEmbed_gram (Q : ℕ) (r s : Fin (Q+1)) (h : r≠s) :
    (sumEmbed (A := A) (M := M) Q r s).conjTranspose*sumEmbed (A := A) (M := M) Q r s=1 :=
  basisEmbedding_gram _ (sumInjection_injective Q r s h)

def rotation (U : Matrix.unitaryGroup A ℂ) (Q : ℕ) :
    Matrix.unitaryGroup (Graded (A := A) Q M) ℂ :=
  blockUnitary (fun r : Fin (Q+1) => storedRotation U r.val)

def Invariant (Q : ℕ) (X : CMatrix (Graded (A := A) Q M)) : Prop :=
  ∀U : Matrix.unitaryGroup A ℂ,(rotation (M := M) U Q : CMatrix (Graded (A := A) Q M))*X =
    X*(rotation (M := M) U Q : CMatrix (Graded (A := A) Q M))

def known (Q : ℕ) (K : Matrix (A×N) (A×M) ℂ) :
    Matrix (Graded (A := A) Q N) (Graded (A := A) Q M) ℂ :=
  Matrix.blockDiagonal' (fun r : Fin (Q+1) => externalLift r.val K)

theorem known_gram (Q : ℕ) (K : Matrix (A×N) (A×M) ℂ) (hK : K.conjTranspose*K=1) :
    (known Q K).conjTranspose*known Q K=1 := by
  rw [known, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp only [externalLift_gram _ _ hK]
  exact Matrix.blockDiagonal'_one

theorem known_covariance (U : Matrix.unitaryGroup A ℂ) (Q : ℕ)
    (K : Matrix (A×N) (A×M) ℂ) :
    (rotation (M := N) U Q : CMatrix (Graded (A := A) Q N))*known Q K =
      known Q K*(rotation (M := M) U Q : CMatrix (Graded (A := A) Q M)) := by
  simp only [rotation, blockUnitary, known, ← Matrix.blockDiagonal'_mul,
    externalLift_covariance]

theorem known_preserves (Q : ℕ) (K : Matrix (A×N) (A×M) ℂ)
    (X : CMatrix (Graded (A := A) Q M)) (hi : Invariant Q X) :
    Invariant Q (known Q K*X*(known Q K).conjTranspose) := by
  intro U
  exact encode_invariant _ (rotation U Q) (rotation U Q) (known_covariance U Q K) X (hi U)

def localQuery (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (D : Option (Matrix.unitaryGroup A ℂ)) (r : Fin (Q+1)) :
    Channel (Cache (A := A) (M := M) r.val) (Graded (A := A) Q M) := by
  rcases r with ⟨r,hr⟩
  cases r with
  | zero =>
    exact (isometryChannel (embed Q ⟨1,by omega⟩) (embed_gram Q _)).comp
      (vacuumStep (by omega))
  | succ n =>
    by_cases hn : n+1<Q
    · let r : Fin (Q+1) := ⟨n+1,hr⟩
      let s : Fin (Q+1) := ⟨n+2,by omega⟩
      have hrs : r≠s := by intro h; have := congrArg Fin.val h; dsimp [r,s] at this; omega
      let step := match D with
        | none => referenceStep (M := M) (by omega : n<Fintype.card A) (by omega : n+1<Fintype.card A)
        | some U => cacheStep U (M := M) (by omega : n<Fintype.card A) (by omega : n+1<Fintype.card A)
      exact (isometryChannel (sumEmbed Q r s) (sumEmbed_gram Q r s hrs)).comp step
    · exact isometryChannel (embed Q ⟨n+1,hr⟩) (embed_gram Q _)

def query (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (D : Option (Matrix.unitaryGroup A ℂ)) : Channel (Graded (A := A) Q M) (Graded (A := A) Q M) :=
  sectorChannel (H := fun r : Fin (Q+1) => Cache (A := A) (M := M) r.val)
    (localQuery (A := A) (M := M) Q hpos hQ D)

#print axioms query
#print axioms known_preserves
end
end ICO.C6GradedCache
